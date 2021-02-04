(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

(* Preprocess AutoCorres translation of Cogent compiler's output code. *)
theory Tidy
  imports
    "AutoCorres.AutoCorres"
    "Cogent.ML_Old"
begin

(* Each Cogent_Corres rule expects (at most) one guard *)
lemma join_guards:
  "do g1 <- guard G1; g2 <- guard G2; P g1 g2 od
    =
   do g1 <- guard (\<lambda>s. G1 s \<and> G2 s); P g1 g1 od"
  by monad_eq

(* C-parser function epilogue *)
lemma return_exn_simp:
  "do ret <- A;
      _ <- gets (\<lambda>_. x :: c_exntype);
      _ <- gets (\<lambda>_. ());
      gets (\<lambda>_. ret) od = A"
  by simp

(* Cogent function epilogue *)
lemma return_cogent_simp:
  "do a \<leftarrow> A;
      r \<leftarrow> gets (\<lambda>_. a);
      gets (\<lambda>_. r) od = A"
  by simp

lemma simp_unit_return:
  "\<And>A. (do (x::unit) \<leftarrow> A; gets (\<lambda>_. ()) od) = A"
  by simp

(* Compose variant constructor with the gets immediately after it *)
(* TODO: this should be more specific, and only instantiated when variant_init is an actual variant constructor *)
lemma compose_gets_variant_con:
  "do a \<leftarrow> select UNIV;
      b \<leftarrow> gets (\<lambda>_. payload_update (\<lambda>_. payload) (tag_update (\<lambda>_. tag) variant_init));
      c \<leftarrow> gets (\<lambda>_. b);
      A c
   od =
   do
      b \<leftarrow> gets (\<lambda>_. payload_update (\<lambda>_. payload) (tag_update (\<lambda>_. tag) variant_init));
      A b
  od"
  by monad_eq
lemma compose_gets_variant_con_2:
  "do a \<leftarrow> select UNIV;
      b \<leftarrow> gets (\<lambda>_. payload_update (\<lambda>_. payload) (tag_update (\<lambda>_. tag) variant_init));
      gets (\<lambda>_. b)
   od =
      gets (\<lambda>_. payload_update (\<lambda>_. payload) (tag_update (\<lambda>_. tag) variant_init))"
  by monad_eq

(* Cogent compiler adds one assignment at the end of every block; remove it *)
definition "simp_last_bind = id"

lemma simp_last_bind:
  "\<And>A B C. simp_last_bind (do x \<leftarrow> A; y \<leftarrow> B x; C x y od) = do x \<leftarrow> A; simp_last_bind (do y \<leftarrow> B x; C x y od) od"
  "\<And>A. simp_last_bind (do x \<leftarrow> A; gets (\<lambda>_. x) od) = A"
  "\<And>A. simp_last_bind A = A"
  by (simp_all add: simp_last_bind_def)

lemma simp_last_bindI:
  "simp_last_bind A = B \<Longrightarrow> A = B"
  by (simp add: simp_last_bind_def)
lemma simp_last_bind_recI:
  "condition C (simp_last_bind L) R = B \<Longrightarrow> condition C L R = B"
  by (simp add: simp_last_bind_def)

(* Simplify uninitialised variables. *)
lemma unknown_bind_ignore:
  "select UNIV >>= (\<lambda>_. A) = A"
  by monad_eq

(* The True condition will also be instantiated with LET_TRUE and LET_BANG_TRUE per program *)
lemma unknown_bind_if_True:
  "do x \<leftarrow> select UNIV;
      condition (\<lambda>_. True) T (F x) >>= R od
   = condition (\<lambda>_. True) T (F undefined) >>= R"
  by monad_eq

ML \<open>
fun tidy_C_fun_def f ctxt = let
  val fun_term = Syntax.read_term ctxt (f ^ "'")
  (* Guess whether the function is recursive.
   * FIXME: use AutoCorresFunctionInfo instead *)
  val ([fun_def], fun_rec) = (Proof_Context.get_thms ctxt (f ^ "'.simps"), true)
                             handle ERROR _ => (Proof_Context.get_thms ctxt (f ^ "'_def"), false)

  (* Helper theorems for LET_TRUE and LETBANG_TRUE, if they exist *)
  val unknown_bind_more_thms = ["LET_TRUE", "LETBANG_TRUE"]
        |> maps (fn c => case Syntax.read_term ctxt c of
                             c' as Const _ => [Goal.prove ctxt [] []
                                                (@{mk_term "True \<equiv> (?c \<noteq> 0)" (c)} c')
                                                (K (simp_tac (ctxt addsimps (Proof_Context.get_thms ctxt (c ^ "_def"))) 1))]
                           | _ => [])
        |> map (fn thm => Simplifier.rewrite_rule ctxt [thm] @{thm unknown_bind_if_True})

  (* Use a schematic lemma to rewrite AutoCorres function defs.
   * We can assume the Cogent compiler generates all functions with only one argument. *)
  val prop = if fun_rec then @{mk_term "Trueprop (?f m a = ?A)" f} fun_term
                        else @{mk_term "Trueprop (?f a = ?A)" f} fun_term

  fun subst thms = EqSubst.eqsubst_tac ctxt [0] thms 1

  (* clarsimp won't touch the schematic ?A *)
  fun subst' thms = Clasimp.clarsimp_tac (put_simpset HOL_basic_ss ctxt addsimps thms) 1

  val tacs = subst [fun_def] (* get function definition *)
             THEN subst' @{thms bind_assoc}          (* normalise binds *)
             THEN subst' @{thms join_guards}         (* normalise guards *)
             THEN subst' @{thms simp_thms(21-22,25)} (* simplify conj in guards *)
             THEN subst' @{thms guard_True_bind}     (* remove unnecessary guards *)
             THEN subst @{thms return_exn_simp}      (* remove C parser's function epilogue *)
             (* Remove exactly one bind-gets from the end of the program,
              * which is inserted by the Cogent code generator *)
             THEN rtac (if fun_rec then @{thm simp_last_bind_recI} else @{thm simp_last_bindI}) 1
             THEN subst' @{thms simp_last_bind(1-2) simp_unit_return}
             (* Cleanup any remaining @{term simp_last_bind}s *)
             THEN subst' @{thms simp_last_bind(3)}
             (* Compose variant constructor with the gets immediately after it *)
             THEN subst' @{thms compose_gets_variant_con compose_gets_variant_con_2}
             (* Simplify uninitialised variables *)
             THEN subst' (@{thms unknown_bind_ignore unknown_bind_if_True} @ unknown_bind_more_thms)
             THEN rtac @{thm refl} 1 (* final definition *)
  in Goal.prove ctxt (if fun_rec then ["m", "a"] else ["a"]) [] prop (K tacs) end

fun tidy_C_fun_def' f ctxt =
  Utils.define_lemmas (f ^ "'_def'") [tidy_C_fun_def f ctxt] ctxt |> snd
\<close>

end

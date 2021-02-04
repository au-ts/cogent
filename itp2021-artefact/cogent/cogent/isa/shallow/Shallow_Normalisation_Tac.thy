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

theory Shallow_Normalisation_Tac imports
  "Cogent.ML_Old"
  ShallowUtil
begin

(*
 * Unlike the other provers, this isn't really a "tactic".
 * Rather, it implements partial A-normalisation as a verified program conversion.
 * If we did this correctly, then we should be able to transform the source ("Desugar")
 * version of the program into one that exactly matches the normalised ("Normal") version
 * (modulo alpha-renaming and some other things).
 *
 *
 * The cogent compiler's A-normalisation steps can be divided into two types.
 *
 * Firstly, nested sub-expressions are floated out into additional let-bindings, e.g.
 *     1 + 2 * 3
 * becomes something like
 *     let an\<^sub>1 = 2
 *     and an\<^sub>2 = 3
 *     and an\<^sub>3 = an\<^sub>1 * an\<^sub>2
 *     and an\<^sub>4 = 1
 *     in an\<^sub>4 + an\<^sub>3
 * The compiler always names these temporary variables an\<^sub>X\<^sub>X.
 * We can easily restore the original expressions by inlining these let-bindings.
 * This is done by anormal_let_conv.
 *
 * The more complicated step is continuation-passing transform of if- and case-expressions.
 * In ANF, if- and case-expressions may occur only in continuation position of a subexpression.
 * Thus, in
 *     if (if a1 then a2 else a3) then (if b1 then b2 else b3) else c
 * the subexpression "if a1 then a2 else a3" is not in continuation position, but
 * "if b1 then b2 else b3" is. So, the compiler's ANF transform moves the outer if-expression
 * into the continuation of the inner one, resulting in
 *     if a1 then if a2 then (if b1 then b2 else b3) else c
 *           else if a3 then (if b1 then b2 else b3) else c
 * It turns out that we can implement this using a small set of first-order rewrite rules.
 * We need rules for let-, if- and case-expressions only.
 * To force first-order pattern matching, anormal_prepare_FO_conv wraps all term applications
 * with @{term "op $"} as the term head. Most continuations in the shallow embedding are binders
 * that introduce a new variable, e.g.
 *   let v = e1 in e2
 * the continuation e2 is actually encoded
 *   Let e1 (\<lambda>v. e2)
 * which would get first-orderised into
 *   (Let $ e1_FO) $ (\<lambda>v. e2_FO)
 * Thus we can avoid rewriting expressions that are already in continuation position for free,
 * by making our rules omit the \<lambda>-abstraction. (See the comment for anormal_prepare_FO_conv.)
 *)

ML \<open>
(* Inline an\<^sub>X\<^sub>X variables. *)
fun anormal_let_conv ctxt thm =
  Conv.bottom_conv (fn _ => fn ct => case Thm.term_of ct of
            Const ("HOL.Let", _) $ _ $ Abs (v, _, _) =>
              if String.isPrefix "an\<^sub>" v then Conv.rewr_conv @{thm Let_def} ct else Conv.all_conv ct
          (* XXX: I think this constant name is wrong. Let_{ds} isn't defined in HOL, it's defined in ShallowUtil *)
          (* If this tactic worked before, does that mean this case is not necessary? *)
          | Const ("HOL.Let\<^sub>d\<^sub>s", _) $ _ $ Abs (v, _, _) =>
              if String.isPrefix "an\<^sub>" v then Conv.rewr_conv @{thm Let\<^sub>d\<^sub>s_def} ct else Conv.all_conv ct
          | _ => Conv.all_conv ct)
    ctxt
  |> (fn conv => Conv.fconv_rule conv thm)
\<close>

ML \<open>
(* Like above, but only inline lets introduced as case expression continuations *)
(* This is a separate function because we need to do it on both levels *)
(* TODO: might need to change compiler to generate a fresher name than v_g prefix *)
fun inline_case_continuation_conv ctxt thm =
  Conv.bottom_conv (fn _ => fn ct => case Thm.term_of ct of
            Const ("HOL.Let", _) $ _ $ Abs (v, _, _) =>
              if String.isPrefix "ccase\<^sub>G" v then Conv.rewr_conv @{thm Let_def} ct else Conv.all_conv ct
          | _ => Conv.all_conv ct)
    ctxt
  |> (fn conv => Conv.fconv_rule conv thm)
\<close>

(* Various utilities. *)
lemmas meta_ext = eq_reflection [OF ext]
ML \<open>
(*
 * Add @{term "op $"} to all function applications in the given term,
 * except those that are in continuation position of @{term If}.
 * For example, in @{term "If b then t else f"}, @{term t} and @{term f}
 * are the continuations. The output in this case would look like
 *   @{term "(If $ b') t' f'"}
 * Note that the inside of @{term t} may still be rewritten.
 *
 * Adding @{term "op $"} enables CPS ("A-normalisation") rewrite rules, which should
 * not be applied to things that are already continuations.
 *
 * @{term If} is a special case because its continuations do not introduce new bindings.
 * In other constructs, the continuations are wrapped in \<lambda>-abstractions, so
 * we can just blindly rewrite those without triggering the rewrite rules.
 *)

(* The LHS of our conv is @{term "?a ?b"}. To avoid surprises during matching,
 * we instantiate the term and type variables directly. *)
fun anormal_prepare_FO_conv ctxt ct = let
  fun dest_fun_ctyp cT = case Thm.typ_of cT of
        Type ("fun", _) =>
          let val [cTf, cTx] = Thm.dest_ctyp cT
          in (cTf, cTx) end
      | _ => raise TYPE ("dest_fun_ctyp", [Thm.typ_of cT], [])
  val [aT, bT] = map (fn v => Thm.ctyp_of @{context} (TVar ((v, 0), ["HOL.type"]))) ["'a", "'b"]
  val [avar, bvar] = map (fn (v, T) => Thm.cterm_of @{context} (Var ((v, 0), T)))
                         [("a", Thm.typ_of aT --> Thm.typ_of bT), ("b", Thm.typ_of aT)]
  fun fun_app_eqn (f, x) = let
        val rule = @{lemma "(a :: 'a \<Rightarrow> 'b) (b :: 'a) == (a $ b)" by simp}
        val (aT', bT') = dest_fun_ctyp (Thm.ctyp_of_cterm f)
        val at = Thm.instantiate_cterm ([(Term.dest_TVar (Thm.typ_of aT), aT'), (Term.dest_TVar (Thm.typ_of bT), bT')], []) avar
        val bt = Thm.instantiate_cterm ([(Term.dest_TVar (Thm.typ_of aT), aT')], []) bvar
        in Thm.instantiate ([(Term.dest_TVar (Thm.typ_of aT), aT'), (Term.dest_TVar (Thm.typ_of bT), bT')], [(Term.dest_Var (Thm.term_of at), f), (Term.dest_Var (Thm.term_of bt), x)]) rule end
  fun expand_conv ct =
    case Thm.term_of ct of
        (Const (@{const_name "fun_app"}, _) $ Const ("HOL.If", _) $ _ $ _) => Conv.no_conv ct
      | (Const (@{const_name "fun_app"}, _) $ Const ("HOL.If", _) $ _ $ _ $ _) => Conv.no_conv ct
      | _ $ _ => fun_app_eqn (Thm.dest_comb ct)
      | _ => Conv.no_conv ct
in
  Conv.bottom_conv (K (Conv.try_conv expand_conv)) ctxt ct
end

(* Remove the @{term "op $"}. Code nicked from AutoCorres. *)
fun dest_first_order ctxt ct =
  Conv.bottom_conv (K (Conv.try_conv (Conv.rewr_conv
    @{lemma "($) == (%a b. a b)" by (rule meta_ext, rule ext, simp)}))) ctxt ct

fun conv_to_simproc conv = fn _ => fn _ => fn ct => let
  val dummy_thm = @{thm TrueI}
  val thm = ct |> Conv.else_conv (conv, K dummy_thm)
  in if Thm.eq_thm (thm, dummy_thm) then NONE else SOME thm end
\<close>

(* Conditional normalisation rules for Let and If; guarded by in_continuation *)
lemma cogent_anormal_if_distribs:
  "\<And>f a b c. (f $ (If $ a) b c) \<equiv> (If $ a) (f $ b) (f $ c)"
  "\<And>x a b c. ((If $ a) b c $ x) \<equiv> (If $ a) (b $ x) (c $ x)"
  by (auto intro!: eq_reflection)

lemma cogent_anormal_let_distrib:
  "\<And>f x y. f $ ((Let $ x) $ (case_prod $ (\<lambda>u v. y u v))) \<equiv> (Let $ x) $ (case_prod $ (\<lambda>u v. f $ y u v))"
  "\<And>f x y. f $ ((Let $ x) $ (case_prod $ y)) \<equiv> (Let $ x) $ (case_prod $ (\<lambda>u v. f $ y u v))"
  "\<And>f x y. f $ ((Let $ x) $ (\<lambda>v. y v)) \<equiv> (Let $ x) $ (\<lambda>v. f $ y v)"
  "\<And>f x y. f $ ((Let\<^sub>d\<^sub>s $ x) $ (\<lambda>v. y v)) \<equiv> (Let\<^sub>d\<^sub>s $ x) $ (\<lambda>v. f $ y v)"
  "\<And>f x y. f $ ((Let $ x) $ y) \<equiv> (Let $ x) $ (\<lambda>v. f $ y v)"
  "\<And>f x y. f $ ((Let\<^sub>d\<^sub>s $ x) $ y) \<equiv> (Let\<^sub>d\<^sub>s $ x) $ (\<lambda>v. f $ y v)"
  "\<And>x y z. ((Let $ x) $ case_prod $ y) $ z \<equiv> (Let $ x) $ case_prod $ (\<lambda>u v. y u v $ z)"
  "\<And>x y z. ((Let\<^sub>d\<^sub>s $ x) $ case_prod $ y) $ z \<equiv> (Let\<^sub>d\<^sub>s $ x) $ case_prod $ (\<lambda>u v. y u v $ z)"
  "\<And>x y z. ((Let $ x) $ y) $ z \<equiv> (Let $ x) $ (\<lambda>v. y v $ z)"
  "\<And>x y z. ((Let\<^sub>d\<^sub>s $ x) $ y) $ z \<equiv> (Let\<^sub>d\<^sub>s $ x) $ (\<lambda>v. y v $ z)"
  by (auto simp: Let\<^sub>d\<^sub>s_def)

ML \<open>
(* Apply rules only in non-continuation position. *)
fun in_continuation (t as _ $ _) = (case t of
        Const (@{const_name fun_app}, _) $
          (Const (@{const_name fun_app}, _) $
            Const ("HOL.Let", _) $ _) $ _ =>
          true
      | Const (@{const_name fun_app}, _) $
          (Const (@{const_name fun_app}, _) $
            Const (@{const_name Let\<^sub>d\<^sub>s}, _) $ _) $ _ =>
          true
      | Const (@{const_name fun_app}, _) $
          Const ("HOL.If", _) $ _ $ _ =>
          true
      | Const (@{const_name fun_app}, _) $
          Const ("HOL.If", _) $ _ $ _ $ _ =>
          true
      | _ => false)
  | in_continuation _ = false

fun make_net eqns = fold (Net.insert_term Thm.eq_thm)
      (map (fn eqn => (Thm.term_of (Thm.dest_equals (Thm.cprop_of eqn) |> fst), eqn)) eqns)
      Net.empty

(* A-normalisation as a simproc.
 * The simplifier ensures for us that the rewrite rules are applied fully
 * to the input term.
 * extra_rules are rules generated by the compiler for each case matching *)
fun anormal_proc_net extra_rules = make_net (@{thms cogent_anormal_let_distrib cogent_anormal_if_distribs} @ extra_rules)

fun anormal_proc extra_rules = fn _ => fn ctxt => fn ct =>
  let val t = Thm.term_of ct
  in if in_continuation t then NONE else (
    case Net.match_term (anormal_proc_net extra_rules) t of
      [] => NONE
      | (eqn::_) => SOME eqn)
  end

fun anormal_simproc extra_rules =
  cert_simproc @{theory} "cogent_anormal"
  { lhss = [@{schematic_term "_ $ _"}]
  , proc = anormal_proc extra_rules
  }


(* Prove equation of the form "source_f = normal_f".
 * "callees" is expected to have similar equations for called functions. *)
local
  fun TIME_TAC msg tac = fn st => let
        val start = Timing.start ()
        val r = case Seq.pull (tac st) of
                NONE => Seq.empty
              | SOME (x, xs) => Seq.cons x xs
        val _ = tracing (msg ^ ": " ^ Timing.message (Timing.result start))
        in r end
in
fun normalisation_tac ctxt
      (src_thy: string) (norm_thy: string)
      (promote_rules : thm list) (case_distribs : thm list)
      (callees: thm list)
      (f: string) = let
  val src_name = src_thy ^ "." ^ f
  val norm_name = norm_thy ^ "." ^ f
  val (src_term, src_typ) = case Syntax.read_term ctxt src_name of
            t as Const (_, ty) => (t, ty)
          | _ => error ("Failed to find constant: " ^ src_name)
  val norm_term = case Syntax.read_term ctxt norm_name of
            t as Const _ => t
          | _ => error ("Failed to find constant: " ^ norm_name)
  val src_def = Proof_Context.get_thm ctxt (src_name ^ "_def")
  val norm_def = Proof_Context.get_thm ctxt (norm_name ^ "_def")
  val prop = Const ("HOL.eq", src_typ --> src_typ --> @{typ bool}) $ src_term $ norm_term

  (* Do A-normalisation (and a couple of other things...) on the given function def.
   * Unfortunately, the compiler's current shallow embedding has special-cased
   * promotions of numeric and variant literals e.g.
   *     3 :: U16   ==>   promote (literal 3 :: U8) :: U16
   *     A x :: <A x | B y>   ==>   promote (A x :: <A x>) :: <A x | B y>
   * and these special cases only apply to the non-normalised code.
   * so we apply them to both versions of the code to "normalise"
   * (in the confluent rewriting sense) them together.
   *
   * In fact, we just apply all of anormal_conv to both src_def and norm_def instead
   * of just src_def. This is because norm_def might not be completely in ANF
   * (--fnormalisation=knf). Again, CPS conversion should be reasonably confluent
   * so we don't need to be too conservative about where we apply it.
   *)
  fun anormal_conv def = def
      (* Rewrite variant literal promotions.
       * After inlining A-normal bindings (anormal_let_conv), these will match
       * the promote_rules generated by the compiler, of the form
       *     (case A a of A x \<Rightarrow> B x) \<equiv> B a
       *)
      |> Simplifier.rewrite_rule ctxt promote_rules
      |> Conv.fconv_rule (anormal_prepare_FO_conv ctxt)
      |> Conv.fconv_rule (Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimprocs [anormal_simproc case_distribs]))
      |> Conv.fconv_rule (dest_first_order ctxt)
      (* Rewrite numeric literal promotions.
       * These always appear as "ucast n" where n is a HOL numeric literal. *)
      |> Conv.fconv_rule (Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimprocs
          [ Simplifier.cert_simproc @{theory} "ucast_simproc"
            { lhss = [ @{schematic_term "ucast (numeral _)"}
                     , @{schematic_term "ucast zero_class.zero"}
                     , @{schematic_term "ucast one_class.one"}
                     ]
            , proc = conv_to_simproc
                (fn ct : cterm => Simplifier.rewrite ctxt ct) (* NB: outer ctxt to avoid recursion *)
            }
          ]))

  (* tac is a function so that anormal_conv (the bulk of the work) is run inside the future *)
  fun tac st = st |> (
        (* add function arguments *)
        REPEAT (rtac @{thm ext} 1)
        (* unfold functions *)
        THEN EqSubst.eqsubst_tac ctxt [0] [anormal_conv (inline_case_continuation_conv ctxt src_def)] 1
        THEN EqSubst.eqsubst_tac ctxt [0] [anormal_conv (inline_case_continuation_conv ctxt (anormal_let_conv ctxt norm_def))] 1
        (* add callee proofs -- should get trivial equality at this point *)
        THEN simp_tac (put_simpset HOL_basic_ss ctxt addsimps callees addsimps @{thms take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def Let\<^sub>d\<^sub>s_def Let_def}) 1)
  val thm = Goal.prove_future ctxt [] [] (@{term Trueprop} $ prop)
              (K (TIME_TAC ("normalisation_tac: proof for " ^ f) tac))
  in thm end

fun normalisation_tac_all ctxt
      (src_thy: string) (norm_thy: string)
      (promote_rules : thm list) (case_distribs : thm list)
      (functions: string list)
      : thm Symtab.table =
  functions ~~
  rev (fold (fn f => fn thms => let
        val thm = normalisation_tac ctxt src_thy norm_thy promote_rules case_distribs thms f
        in thm :: thms end) functions [])
  |> Symtab.make
end
\<close>

end

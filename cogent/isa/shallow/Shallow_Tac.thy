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

theory Shallow_Tac
imports Shallow "Cogent.ML_Old"
begin

locale shallow = value_sem

context shallow
begin


ML \<open>
val scorres_abs_assmsN = "scorres_abs_assms"

fun SOLVE_GOAL tac = tac THEN_MAYBE no_tac

infix 1 XTHEN
fun t1 XTHEN t2 = (DETERM t1) THEN (DETERM t2)

fun add_thm thm atts name lthy =
  Local_Theory.notes [((Binding.name name, atts), [([thm], atts)])] lthy |> #2

fun mk_goal ctxt str =
let
  val prop = Syntax.parse_term ctxt str |> Syntax.check_term ctxt
  val ctxt = Variable.auto_fixes prop ctxt
in
  (ctxt, prop)
end

fun mk_scorres_nm fn_name = "scorres_" ^ fn_name

(* Compute all the abstract function dependencies for a cogent function*)
fun gen_afun_deps xs ctxt =
let
  fun strip_listcons (_ $ x $ y) = (x |> Term.strip_comb |> snd) :: strip_listcons y
   |  strip_listcons _ = [];

  (* Convert binary representation of a number to an integer *)
  fun bin_to_num xs = 
    fold (fn x => fn y => if x = (Const ("HOL.True", @{typ "bool"})) then 2 * y + 1 else  2 * y) 
         (rev xs) 0;
  
  fun app2 (xs1, xs2) (ys1, ys2) = (xs1 @ ys1, xs2 @ ys2);

  fun last_period [] i _ = i
   |  last_period (x::xs) i j = 
    if x = "." then last_period xs (j+1) (j+1) else last_period xs i (j+1);
  
  fun get_after_period s =
    let
      val x = raw_explode s;
      val i = last_period x 0 0;
    in x |> drop i |> implode
    end

  (* Get the abstract and Cogent function dependencies *)
  fun find_deps (Const ("Cogent.expr.AFun", _) $ x) = 
    ([x |> strip_listcons |> map (chr o bin_to_num)|> implode], [])
   |  find_deps (Const ("Cogent.expr.Fun", _) $ Const (x, _) $ _) = ([], [get_after_period x])
   |  find_deps (x $ y) = app2 (find_deps x) (find_deps y)
   |  find_deps _ = ([], []);

  (* Get the definition of each Cogent function *)
  val xs' = xs |> map (fn x => Proof_Context.get_thm ctxt (x ^ "_def") 
                  |> Thm.cprop_of 
                  |> Thm.term_of 
                  |> Term.dest_comb |> snd)
  val (ys1, ys2) = map find_deps xs' |> split_list;
  val deps = xs ~~ ys1 |> Symtab.make;
  val deps' = xs ~~ ys2 |> Symtab.make;
  
  fun app_op xs NONE = xs
   |  app_op xs (SOME ys) = xs @ ys;

  fun all_deps [] (_ : string list) d = d
   |  all_deps (x::xs) seen d = 
    if member (fn (a,b) => a = b) seen x 
      then all_deps xs seen d 
    else 
      all_deps (x |> Symtab.lookup deps' |> app_op xs) 
               (x::seen) (x |> Symtab.lookup deps |> app_op d);

  fun eq_str (a, b) = (a = b);

  val deps_deep = xs ~~ ys2 |> map 
    (fn (x,ys) => Symtab.lookup deps x 
      |> app_op (all_deps ys [x] [])
      |> distinct eq_str);

in
  xs ~~ deps_deep |> Symtab.make 
end

(* Make the proposition for the assumption about abstract functions.
   Note that the \<gamma> and ts are turned into quantified variables *)
fun gen_scorres_abs_assm lthy Aname abs_name =
let
  val prop = betapply (Syntax.read_term lthy
                          ("\<lambda>(n::string). scorres " ^ Aname ^ "." ^ abs_name ^ " (AFun n ts) \<gamma> \<xi>"),
                       HOLogic.mk_string abs_name) 
             |> HOLogic.mk_Trueprop 
             |> Logic.all (Free ("\<gamma>", @{typ "(char list, 'a) vval list"}))
             |> Logic.all (Free ("ts", @{typ "Cogent.type list"}))
             
  val ctxt = Variable.auto_fixes prop lthy
in
  (ctxt, prop)
end

fun gen_scorres_lemma skip Absname Aname Dname generic_step fn_deps fn_name (result_thms, callee_thms, lthy) =
let
  val str = "valRel \<xi> v v' \<Longrightarrow> " ^
            "scorres (" ^ Aname ^ "." ^ fn_name ^ " (shallow_tac__var v)) " ^
                    "(specialise ts " ^ Dname ^ "." ^ fn_name ^ ") [v'] \<xi>"
  val nm = mk_scorres_nm fn_name
  val _ = tracing (nm ^ ": \"" ^ str ^ "\"")
  val (ctxt, prop) = mk_goal lthy str

  fun mk_assm ctxt props x =
    let
      val (ctxt, prop) = gen_scorres_abs_assm ctxt Absname x
    in (ctxt, prop :: props) end
  fun mk_assms ctxt xs = fold (fn x => fn (ctxt, props) => mk_assm ctxt props x) xs (ctxt, [])
  val (ctxt, abs_assms) = (case Symtab.lookup fn_deps fn_name of SOME xs => xs | _ => [])
                |> mk_assms ctxt 

  val unfold_A = Proof_Context.get_thms lthy (Aname ^ "." ^ fn_name ^ "_def")
  val unfold_D = Proof_Context.get_thms lthy (Dname ^ "." ^ fn_name ^ "_def")
  val thm = Goal.prove_future ctxt [] abs_assms prop (fn args => fn st => let
    val abs_thms = #prems args
    val abs_app_thms = abs_thms RL @{thms scorres_app}
    val start = Timing.start () in
    case st |>
      (if skip
      then Skip_Proof.cheat_tac ctxt 1
      else
         ((resolve_tac ctxt result_thms 1 THEN atac 1) ORELSE
          (Local_Defs.unfold_tac ctxt unfold_D
          XTHEN Local_Defs.unfold_tac ctxt unfold_A
          XTHEN simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms specialise.simps list.map fun_app_def}) 1
          XTHEN REPEAT_DETERM (
            (*(print_tac ctxt "" THEN no_tac) ORELSE*)
            generic_step ctxt 1
            ORELSE resolve_tac ctxt (callee_thms @ abs_thms @ abs_app_thms) 1
            ))))
         |> Seq.pull of
        NONE => Seq.empty
      | SOME (t, ts) => (tracing (nm ^ ": " ^ Timing.message (Timing.result start)); Seq.cons t ts)
    end)
  val thm = Simplifier.rewrite_rule lthy @{thms shallow_tac__var_def} thm
  val thm' = hd ((map (Goal.norm_result lthy) o Proof_Context.export ctxt lthy) [thm])
  val _ = tracing ("thm: " ^ (@{make_string} thm'))
  val (ctxt, callee_prop) = mk_goal lthy
        ("Trueprop (scorres " ^ Aname ^ "." ^ fn_name ^ " " ^
            "(Fun " ^ Dname ^ "." ^ fn_name ^ " ts) \<gamma> \<xi>)")
  val callee_thm = Goal.prove ctxt [] abs_assms callee_prop
                   (fn args => (rtac @{thm scorres_fun} 1
                       THEN asm_full_simp_tac (lthy delsimprocs [Simplifier.the_simproc lthy "Product_Type.unit_eq"] addsimps ([thm'] @ (#prems args))) 1))
  val callee_thm = hd ((map (Goal.norm_result lthy) o Proof_Context.export ctxt lthy) [callee_thm])
  val callee_fun_app = callee_thm RS @{thm scorres_app}

  val lthy' = add_thm thm' [] nm lthy
in
  (thm'::result_thms, callee_thm::callee_fun_app::callee_thms, lthy')
end

fun gen_scorres_lemmas skip fun_thms Absname Aname Dname generic_step fn_names fn_deps lthy =
  fold (gen_scorres_lemma skip Absname Aname Dname generic_step fn_deps) fn_names ([], fun_thms, lthy) |> #3

fun gen_scorres_lemmas' skip (Absname : string) Aname Dname (fn_anames : string list)fn_dnames lthy =
let
  
  val fn_deps =  gen_afun_deps fn_dnames lthy
  val read_buckets = maps (fn n => Proof_Context.get_thms lthy n handle ERROR _ => [])

  (* Prioritise flattened cases over everything else, as the unflattened case rule might work locally
     even if the shallow representation is flattened *)
  val flat_case_net =
        Tactic.build_net (read_buckets ["scorres_flat_cases"])
  (* flat_case lemmas have some cruft like "if tag_1 = ''Tag1''" in their assumptions,
     and applying the rule should instantiate tag_1 to a constant string,
     so we want to do just enough simplification to check whether two strings are equal
     and commit to one branch of the if. *)
  (* Need to mess a bit with the simpset, can't just use the lthy context in full_simp_tac:
     apparently it's not a super context? *)
  val flat_case_simp_ss =
        simpset_of ((clear_simpset @{context})
        addsimps  @{thms char.inject list.inject if_True if_False HOL.simp_thms})
  fun flat_case_tac ctxt =
        resolve_from_net_tac ctxt flat_case_net
        THEN_ALL_NEW (full_simp_tac (put_simpset flat_case_simp_ss ctxt))

  val step_net =
        Tactic.build_net (@{thms scorres_simple_step} @
                          read_buckets ["scorres_cases", "scorres_esacs", "scorres_cons",
                                        "scorres_structs"])
  val step_simp_net = Tactic.build_net @{thms scorres_var scorres_app[OF scorres_var] scorres_lit}
  val struct_op_net = Tactic.build_net @{thms scorres_take scorres_put scorres_member}
  val struct_field_net = Tactic.build_net (read_buckets ["scorres_rec_fields"])
  fun generic_step ctxt n =
        flat_case_tac ctxt n
        ORELSE (resolve_from_net_tac ctxt step_net n)
        ORELSE (resolve_from_net_tac ctxt step_simp_net n THEN SOLVE_GOAL (full_simp_tac ctxt n))
        ORELSE (resolve_from_net_tac ctxt struct_op_net n THEN resolve_from_net_tac ctxt struct_field_net n)
  val lthy = gen_scorres_lemmas skip ([]) Absname Aname Dname generic_step fn_dnames fn_deps lthy;
in lthy end

val gen_scorres_lemmas = gen_scorres_lemmas' false
\<close>

(* TODO:

- make \<xi> a definition
- get rid of cheat_tac, using above to prove AFuns

*)

end

end


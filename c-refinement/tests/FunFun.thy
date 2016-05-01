(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

(*
 * Program specifications generated from:
 *   cogent --type-proof=FunFun --fml-typing-tree fun.cogent
 *   cogent -gfun_dsl --infer-c-func=fun.ac fun.cogent && cat fun_dsl.c fun_pp_inferred.c > fun.c
 *)
theory FunFun
imports
  "../COGENT_Corres"
  "../TypeProofGen"
  "../Corres_Tac"
  "../Tidy"
begin

lemmas abbreviated_type_defs =
  TrueI

definition
  "abs_type \<equiv> ([], (TUnit, TFun TUnit TUnit))"

definition
  "i_type \<equiv> ([], (TUnit, TUnit))"

definition
  "i \<equiv> Let (Var 0) (Var 0)"

definition
  "i2_type \<equiv> ([], (TUnit, TUnit))"

definition
  "i2 \<equiv> Let (Var 0) (App (Fun i []) (Var 0))"

definition
  "f_type \<equiv> ([], (TUnit, TUnit))"

definition
  "f \<equiv> Let (Var 0) (Let (App (AFun ''abs'' []) (Var 0)) (App (Var 0) (Var 1)))"

definition
  "\<Xi> func_name' \<equiv> case func_name' of ''abs'' \<Rightarrow> abs_type | ''i'' \<Rightarrow> i_type | ''i2'' \<Rightarrow> i2_type | ''f'' \<Rightarrow> f_type"

definition
  "\<xi> func_name' \<equiv> case func_name' of ''abs'' \<Rightarrow> undefined"

definition
  "i_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some TUnit] TyTrLeaf"

definition
  "i2_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some TUnit] TyTrLeaf"

definition
  "f_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some TUnit] (TyTrSplit (Cons (Some TSK_S) (Cons None [])) [] TyTrLeaf [Some (TFun TUnit TUnit)] TyTrLeaf)"

ML {* open TTyping_Tactics *}

ML_quiet {*
val typing_helper_1_script : tac list = [
(RTac @{thm kind_tunit[where k = "{E,S,D}"]})
] *}


lemma typing_helper_1[unfolded abbreviated_type_defs] :
  "kinding [] TUnit {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_1_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_2_script : tac list = [
(SimpTac ([],[(nth @{thms HOL.simp_thms} (25-1)),(nth @{thms HOL.simp_thms} (26-1))]))
] *}


lemma typing_helper_2[unfolded abbreviated_type_defs] :
  "list_all2 (kinding []) [] []"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_2_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_3_script : tac list = [
(RTac @{thm kind_tfun[where k = "{E,S,D}"]}),
(RTac @{thm typing_helper_1}),
(RTac @{thm typing_helper_1})
] *}


lemma typing_helper_3[unfolded abbreviated_type_defs] :
  "kinding [] (TFun TUnit TUnit) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_3_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_4_script : tac list = [
(RTac @{thm kind_tfun[where k = "{E,S,D}"]}),
(RTac @{thm typing_helper_1}),
(RTac @{thm typing_helper_3})
] *}


lemma typing_helper_4[unfolded abbreviated_type_defs] :
  "kinding [] (TFun TUnit (TFun TUnit TUnit)) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_4_script |> EVERY *})
  done

ML_quiet {*
val i_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_1})],
KindingTacs [(RTac @{thm typing_helper_1})],
TypingTacs [],
TypingTacs []
] *}


ML_quiet {*
val i_ttyping_details_future = get_all_typing_details_future @{context} "i"
   i_typecorrect_script*}


lemma i_typecorrect :
  "\<Xi>, fst i_type, (i_typetree, [Some (fst (snd i_type))]) T\<turnstile> i : snd (snd i_type)"
  apply (tactic {* resolve_future_typecorrect @{context} i_ttyping_details_future *})
  done

ML_quiet {*
val i2_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_1})],
KindingTacs [(RTac @{thm typing_helper_1})],
TypingTacs [],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (2,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_1})])])),(RTac @{thm typing_fun'}),(RTac @{thm i_typecorrect[simplified i_type_def i_typetree_def, simplified]}),(RTac @{thm typing_helper_2}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm typing_helper_1}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_1}]),(SimpTac ([],[]))]
] *}


ML_quiet {*
val i2_ttyping_details_future = get_all_typing_details_future @{context} "i2"
   i2_typecorrect_script*}


lemma i2_typecorrect :
  "\<Xi>, fst i2_type, (i2_typetree, [Some (fst (snd i2_type))]) T\<turnstile> i2 : snd (snd i2_type)"
  apply (tactic {* resolve_future_typecorrect @{context} i2_ttyping_details_future *})
  done

ML_quiet {*
val f_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_1})],
KindingTacs [(RTac @{thm typing_helper_1})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (2,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_1})])])),(RTac @{thm typing_afun'}),(SimpTac ([@{thm \<Xi>_def},@{thm abs_type_def}],[])),(RTac @{thm typing_helper_2}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm typing_helper_4}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_1}]),(SimpTac ([],[]))],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (3,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})]),(1,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_1})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_1}]),(SimpTac ([],[]))]
] *}


ML_quiet {*
val f_ttyping_details_future = get_all_typing_details_future @{context} "f"
   f_typecorrect_script*}


lemma f_typecorrect :
  "\<Xi>, fst f_type, (f_typetree, [Some (fst (snd f_type))]) T\<turnstile> f : snd (snd f_type)"
  apply (tactic {* resolve_future_typecorrect @{context} f_ttyping_details_future *})
  done

ML_quiet {*
val (_, i_typing_tree, i_typing_bucket)
= Future.join i_ttyping_details_future
*}


ML_quiet {*
val (_, i2_typing_tree, i2_typing_bucket)
= Future.join i2_ttyping_details_future
*}


ML_quiet {*
val (_, f_typing_tree, f_typing_bucket)
= Future.join f_ttyping_details_future
*}


new_C_include_dir "../../cogent/tests"
install_C_file "fun.c"
autocorres [ts_rules = nondet, no_opt, skip_word_abs] "fun.c"

instantiation bool_t_C :: cogent_C_val
begin
definition type_rel_bool_t_C_def:
  "type_rel typ (_ :: bool_t_C itself) \<equiv> (typ = RPrim Bool)"

definition val_rel_bool_t_C_def:
  "val_rel uv (x :: bool_t_C) \<equiv> uv = UPrim (LBool (bool_t_C.boolean_C x \<noteq> 0))"
instance ..
end

instantiation unit_t_C :: cogent_C_val begin
  definition type_rel_unit_t_C: "type_rel r (_ :: unit_t_C itself) \<equiv> r = RUnit"
  definition val_rel_unit_t_C: "val_rel uv (_ :: unit_t_C) \<equiv> uv = UUnit"
  instance ..
end


(* [abs, f] is a non-terminating program, so we cannot prove correspondence. *)
context "fun" begin
  thm abs'_def
  thm f'.simps dispatch_t1'.simps
end


(* [i, i2] is a terminating program. *)
locale fun_u_sem = "fun" + update_sem_init
begin

local_setup {* fold tidy_C_fun_def' ["i", "i2"] *}
thm i_def i'_def' i2_def i2'_def'

lemmas corres_nested_let = TrueI (* unused *)

lemma i_corres: "val_rel a a' \<Longrightarrow> corres srel i (i' a') \<xi> [a] \<Xi> [Some TUnit] \<sigma> s"
  apply (tactic {* corres_tac @{context}
    (peel_two i_typing_tree)
    @{thms i_def i'_def' i_type_def abbreviated_type_defs} [] []
    @{thm TrueI} [] [] [] [] @{thm LETBANG_TRUE_def} [] true *})
  done

lemma i2_corres: "val_rel a a' \<Longrightarrow> corres srel i2 (i2' a') \<xi> [a] \<Xi> [Some TUnit] \<sigma> s"
  apply (tactic {* corres_tac @{context}
    (peel_two i2_typing_tree)
    @{thms i2_def i2'_def' i2_type_def abbreviated_type_defs} [] @{thms i_corres}
    @{thm TrueI} [] [] [] [] @{thm LETBANG_TRUE_def} [] true *})
  done

end

end

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
 *   cogent --type-proof=FunFun2 --fml-typing-tree fun2.cogent
 *   cogent -gfun2 --table-c-types=fun2.table fun2.cogent
 *)
theory FunFun2
imports
  "../COGENT_Corres"
  "../Corres_Tac"
  "../TypeProofGen"
  "../Type_Relation_Generation"
  "../Deep_Embedding_Auto"
  "../Tidy"
begin

definition
  "abbreviatedType1 \<equiv> TRecord [(TPrim (Num U32), False), (TPrim (Num U32), False)] Unboxed"

lemmas abbreviated_type_defs =
  abbreviatedType1_def

definition
  "foo_type \<equiv> ([], (TPrim (Num U16), abbreviatedType1))"

definition
  "foo \<equiv> Let (Var 0) (Let (Cast U32 (Var 0)) (Let (Cast U32 (Var 1)) (Struct [TPrim (Num U32), TPrim (Num U32)] [Var 1, Var 0])))"

definition
  "bar_type \<equiv> ([], (TUnit, TUnit))"

definition
  "bar \<equiv> Let (Var 0) (Let (Lit (LU8 32)) (Let (Cast U16 (Var 0)) (Let (App (Fun foo []) (Var 0)) (Take (Var 0) 0 (Take (Var 1) 1 Unit)))))"

definition
  "\<Xi> func_name' \<equiv> case func_name' of ''foo'' \<Rightarrow> foo_type | ''bar'' \<Rightarrow> bar_type"

definition
  "foo_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some (TPrim (Num U16))] (TyTrSplit (Cons (Some TSK_S) (Cons None [])) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (Cons None (Cons (Some TSK_L) (Cons None []))) [] TyTrLeaf [Some (TPrim (Num U32))] TyTrLeaf))"

definition
  "bar_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some TUnit] (TyTrSplit (Cons (Some TSK_L) (Cons None [])) [] TyTrLeaf [Some (TPrim (Num U8))] (TyTrSplit (Cons (Some TSK_L) (append (replicate 2 None) [])) [] TyTrLeaf [Some (TPrim (Num U16))] (TyTrSplit (Cons (Some TSK_L) (append (replicate 3 None) [])) [] TyTrLeaf [Some abbreviatedType1] (TyTrSplit (Cons (Some TSK_L) (append (replicate 4 None) [])) [] TyTrLeaf [Some (TPrim (Num U32)), Some (TRecord [(TPrim (Num U32), True), (TPrim (Num U32), False)] Unboxed)] (TyTrSplit (Cons (Some TSK_L) (Cons (Some TSK_L) (append (replicate 5 None) []))) [] TyTrLeaf [Some (TPrim (Num U32)), Some (TRecord [(TPrim (Num U32), True), (TPrim (Num U32), True)] Unboxed)] TyTrLeaf)))))"

ML {* open TTyping_Tactics *}

ML_quiet {*
val typing_helper_1_script : tac list = [
(RTac @{thm kind_tprim[where k = "{E,S,D}"]})
] *}


lemma typing_helper_1[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim (Num U16)) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_1_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_2_script : tac list = [
(RTac @{thm kind_tprim[where k = "{E,S,D}"]})
] *}


lemma typing_helper_2[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim (Num U32)) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_2_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_3_script : tac list = [
(RTac @{thm kind_tunit[where k = "{E,S,D}"]})
] *}


lemma typing_helper_3[unfolded abbreviated_type_defs] :
  "kinding [] TUnit {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_3_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_4_script : tac list = [
(RTac @{thm kind_tprim[where k = "{E,S,D}"]})
] *}


lemma typing_helper_4[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim (Num U8)) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_4_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_5_script : tac list = [
(RTac @{thm kind_trec[where k = "{E,S,D}"]}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_2}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_2}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_5[unfolded abbreviated_type_defs] :
  "kinding [] abbreviatedType1 {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_5_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_6_script : tac list = [
(SimpTac ([],[(nth @{thms HOL.simp_thms} (25-1)),(nth @{thms HOL.simp_thms} (26-1))]))
] *}


lemma typing_helper_6[unfolded abbreviated_type_defs] :
  "list_all2 (kinding []) [] []"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_6_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_7_script : tac list = [
(RTac @{thm kind_trec[where k = "{E,S,D}"]}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_2}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_2}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_7[unfolded abbreviated_type_defs] :
  "kinding [] (TRecord [(TPrim (Num U32), True), (TPrim (Num U32), False)] Unboxed) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_7_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_8_script : tac list = [
(RTac @{thm kind_trec[where k = "{E,S,D}"]}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_2}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_2}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_8[unfolded abbreviated_type_defs] :
  "kinding [] (TRecord [(TPrim (Num U32), True), (TPrim (Num U32), True)] Unboxed) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_8_script |> EVERY *})
  done

ML_quiet {*
val foo_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_1})],
KindingTacs [(RTac @{thm typing_helper_1})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_2})],
TypingTacs [(RTac @{thm typing_cast}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_1}]),(SimpTac ([],[])),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_2})],
TypingTacs [(RTac @{thm typing_cast}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_1}]),(SimpTac ([],[])),(SimpTac ([],[]))],
TypingTacs []
] *}


ML_quiet {*
val foo_ttyping_details_future = get_all_typing_details_future @{context} "foo"
   foo_typecorrect_script*}


lemma foo_typecorrect :
  "\<Xi>, fst foo_type, (foo_typetree, [Some (fst (snd foo_type))]) T\<turnstile> foo : snd (snd foo_type)"
  apply (tactic {* resolve_future_typecorrect @{context} foo_ttyping_details_future *})
  done

ML_quiet {*
val bar_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_4})],
TypingTacs [(RTac @{thm typing_lit'}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_1})],
TypingTacs [(RTac @{thm typing_cast}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_4}]),(SimpTac ([],[])),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (4,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_1})])])),(RTac @{thm typing_fun'}),(RTac @{thm foo_typecorrect[simplified foo_type_def foo_typetree_def abbreviated_type_defs, simplified]}),(RTac @{thm typing_helper_6}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm typing_helper_1}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_1}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_2})],
KindingTacs [(RTac @{thm typing_helper_7})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_2})],
KindingTacs [(RTac @{thm typing_helper_2})],
KindingTacs [(RTac @{thm typing_helper_8})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_2})],
TypingTacs [(RTac @{thm typing_unit}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_2},@{thm typing_helper_8}])]
] *}


ML_quiet {*
val bar_ttyping_details_future = get_all_typing_details_future @{context} "bar"
   bar_typecorrect_script*}


lemma bar_typecorrect :
  "\<Xi>, fst bar_type, (bar_typetree, [Some (fst (snd bar_type))]) T\<turnstile> bar : snd (snd bar_type)"
  apply (tactic {* resolve_future_typecorrect @{context} bar_ttyping_details_future *})
  done

ML_quiet {*
val (_, foo_typing_tree, foo_typing_bucket)
= Future.join foo_ttyping_details_future
*}


ML_quiet {*
val (_, bar_typing_tree, bar_typing_bucket)
= Future.join bar_ttyping_details_future
*}


new_C_include_dir "../../cogent/tests"
install_C_file "fun2.c"
autocorres [ts_rules = nondet, no_opt, skip_word_abs] "fun2.c"

(* C type and value relations *)
instantiation unit_t_C :: cogent_C_val begin
  definition type_rel_unit_t_C_def: "type_rel r (_ :: unit_t_C itself) \<equiv> r = RUnit"
  definition val_rel_unit_t_C_def: "val_rel uv (_ :: unit_t_C) \<equiv> uv = UUnit"
  instance ..
end

instantiation bool_t_C :: cogent_C_val
begin
definition type_rel_bool_t_C_def:
  "type_rel typ (_ :: bool_t_C itself) \<equiv> (typ = RPrim Bool)"

definition val_rel_bool_t_C_def:
  "val_rel uv (x :: bool_t_C) \<equiv> uv = UPrim (LBool (bool_t_C.boolean_C x \<noteq> 0))"
instance ..
end

local_setup{* local_setup_val_rel_type_rel_put_them_in_buckets "fun2.c" *}

locale fun_u_sem = "fun2" + update_sem_init
begin

(* Define specialised take and put rules *)
local_setup{* local_setup_take_put_member_case_esac_specialised_lemmas "fun2.c" *}
print_theorems

(* Preprocess AutoCores output *)
local_setup {* fold tidy_C_fun_def' ["foo", "bar"] *}
thm foo_def foo'_def' bar_def bar'_def'

lemmas val_rel_simps = val_rel_word val_rel_ptr_def val_rel_unit_t_C_def
lemmas type_rel_simps = type_rel_word type_rel_ptr_def type_rel_unit_t_C_def

lemmas corres_nested_let = TrueI (* unused *)

lemma foo_corres: "val_rel a a' \<Longrightarrow> corres srel foo (foo' a') \<xi> [a] \<Xi> [Some (TPrim (Num U16))] \<sigma> s"
  apply (tactic {* corres_tac @{context}
    (peel_two foo_typing_tree)
    @{thms foo_def foo'_def' foo_type_def abbreviated_type_defs} [] []
    @{thm TrueI} [] [] [] [] @{thm LETBANG_TRUE_def}
    @{thms list_to_map_more[where f=Var] list_to_map_singleton[where f=Var]} true *})
  done

lemma bar_corres: "val_rel a a' \<Longrightarrow> corres srel bar (bar' a') \<xi> [a] \<Xi> [Some TUnit] \<sigma> s"
  apply (tactic {* corres_tac @{context}
    (peel_two bar_typing_tree)
    @{thms bar_def bar'_def' bar_type_def abbreviated_type_defs} [] @{thms foo_corres}
    @{thm TrueI} [] @{thms val_rel_simps} @{thms type_rel_simps} [] @{thm LETBANG_TRUE_def}
    @{thms list_to_map_more[where f=Var] list_to_map_singleton[where f=Var]} true *})
  done

end

end

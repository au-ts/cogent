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
 * Source: pass_simple-case3.cogent
 * To generate:
 *   cogent -gpass_simple-case3 --table-c-types=pass_simple-case3.table pass_simple-case3.cogent
 *   cogent --type-proof=Case --fml-typing-tree pass_simple-case3.cogent
*)
theory Case
imports 
  "../COGENT_Corres"
  "../TypeProofGen" 
  "../Heap_Relation_Generation" "../Type_Relation_Generation"
  "../Deep_Embedding_Auto"
  "../Corres_Tac"
  "../Tidy"
begin

definition
  "abbreviatedType1 \<equiv> TSum [(''Atag'', TPrim (Num U8)), (''Btag'', TPrim (Num U8)), (''Ctag'', TPrim (Num U8))]"

lemmas abbreviated_type_defs =
  abbreviatedType1_def

definition
  "foo_type \<equiv> ([], (abbreviatedType1, TPrim (Num U8)))"

definition
  "foo \<equiv> Case (Var 0) ''Atag'' (Var 0) (Case (Var 0) ''Btag'' (Var 0) (Let (Esac (Var 0)) (Var 0)))"

definition
  "\<Xi> func_name' \<equiv> case func_name' of ''foo'' \<Rightarrow> foo_type"

definition
  "foo_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [] (TyTrSplit (Cons None []) [Some (TPrim (Num U8))] TyTrLeaf [Some (TSum [(''Btag'', TPrim (Num U8)), (''Ctag'', TPrim (Num U8))])] (TyTrSplit (Cons (Some TSK_L) (Cons None [])) [] TyTrLeaf [] (TyTrSplit (append (replicate 2 None) []) [Some (TPrim (Num U8))] TyTrLeaf [Some (TSum [(''Ctag'', TPrim (Num U8))])] (TyTrSplit (Cons (Some TSK_L) (append (replicate 2 None) [])) [] TyTrLeaf [Some (TPrim (Num U8))] TyTrLeaf))))"

ML {* open TTyping_Tactics *}

ML_quiet {*
val typing_helper_1_script : tac list = [
(RTac @{thm kind_tprim})
] *}


lemma typing_helper_1[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim (Num U8)) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_1_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_2_script : tac list = [
(RTac @{thm kind_tsum[where k = "{E,S,D}"]}),
(SimpTac ([],[])),
(SimpTac ([],[])),
(RTac @{thm kind_all_cons}),
(RTac @{thm typing_helper_1}),
(RTac @{thm kind_all_cons}),
(RTac @{thm typing_helper_1}),
(RTac @{thm kind_all_cons}),
(RTac @{thm typing_helper_1}),
(RTac @{thm kind_all_empty})
] *}


lemma typing_helper_2[unfolded abbreviated_type_defs] :
  "kinding [] abbreviatedType1 {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_2_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_3_script : tac list = [
(RTac @{thm kind_tsum[where k = "{E,S,D}"]}),
(SimpTac ([],[])),
(SimpTac ([],[])),
(RTac @{thm kind_all_cons}),
(RTac @{thm typing_helper_1}),
(RTac @{thm kind_all_cons}),
(RTac @{thm typing_helper_1}),
(RTac @{thm kind_all_empty})
] *}


lemma typing_helper_3[unfolded abbreviated_type_defs] :
  "kinding [] (TSum [(''Btag'', TPrim (Num U8)), (''Ctag'', TPrim (Num U8))]) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_3_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_4_script : tac list = [
(RTac @{thm kind_tsum[where k = "{E,S,D}"]}),
(SimpTac ([],[])),
(SimpTac ([],[])),
(RTac @{thm kind_all_cons}),
(RTac @{thm typing_helper_1}),
(RTac @{thm kind_all_empty})
] *}


lemma typing_helper_4[unfolded abbreviated_type_defs] :
  "kinding [] (TSum [(''Ctag'', TPrim (Num U8))]) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_4_script |> EVERY *})
  done

ML_quiet {*
val foo_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_2})],
KindingTacs [(RTac @{thm typing_helper_1})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_1})],
KindingTacs [(RTac @{thm typing_helper_4})],
TypingTacs [],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_1})],
TypingTacs [(RTac @{thm typing_esac}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_4}]),(SimpTac ([],[]))],
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
val (_, foo_typing_tree, foo_typing_bucket)
= Future.join foo_ttyping_details_future
*}


new_C_include_dir "../../cogent/lib"
install_C_file "pass_simple-case3.c"
autocorres [ts_rules=nondet, no_opt, skip_word_abs] "pass_simple-case3.c"

instantiation bool_t_C :: cogent_C_val
begin
definition type_rel_bool_t_C_def:
  "type_rel typ (_ :: bool_t_C itself) \<equiv> (typ = RPrim Bool)"

definition val_rel_bool_t_C_def:
  "val_rel uv (x :: bool_t_C) \<equiv> uv = UPrim (LBool (bool_t_C.boolean_C x \<noteq> 0))"
instance ..
end

(* C type and value relations *)
instantiation unit_t_C :: cogent_C_val 
begin
  definition type_rel_unit_t_C_def: "type_rel r (_ :: unit_t_C itself) \<equiv> r = RUnit"
  definition val_rel_unit_t_C_def: "val_rel uv (_ :: unit_t_C) \<equiv> uv = UUnit"
  instance ..
end

(* Automatically generated relations *)
local_setup{* local_setup_val_rel_type_rel_put_them_in_buckets "pass_simple-case3.c" *}
print_theorems

(* Manually written relations *)
lemmas type_rel_simps = 
  type_rel_word type_rel_ptr_def type_rel_unit_def type_rel_unit_t_C_def

lemmas val_rel_simps = 
  val_rel_word val_rel_ptr_def val_rel_unit_def val_rel_unit_t_C_def

context update_sem_init
begin

(* Automatically generate specialised lemmas and store them in buckets.*)
local_setup{* local_setup_take_put_member_case_esac_specialised_lemmas "pass_simple-case3.c" *}

end
locale case_cogent = "pass_simple-case3" + update_sem_init
begin

find_theorems TAG_ENUM_Btag corres
thm corres_case_t2_1th_field[no_vars]

(* Preprocess AutoCorres output *)
local_setup {* tidy_C_fun_def' "foo" *}

lemmas list_to_map_simps = list_to_map_more[where f=Var] list_to_map_singleton[where f=Var]

(* TODO: automate this. Do not include LETBANG_TRUE_def in the same bucket.*)
lemmas tag_enum_defs = 
  TAG_ENUM_Atag_def 
  TAG_ENUM_Btag_def 
  TAG_ENUM_Ctag_def

lemmas corres_nested_let = TrueI (* unused *)
lemmas corres_if = TrueI (* unused *)

lemma foo_corres:
  "val_rel (\<gamma> ! 0) a1 \<Longrightarrow>
   corres state_rel foo (foo' a1) \<xi> \<gamma> \<Xi> [Some (fst (snd foo_type))] \<sigma> s"
  apply (tactic {* corres_tac @{context} (peel_two foo_typing_tree)
                   @{thms foo_def foo'_def' foo_type_def abbreviated_type_defs} [] []
                   @{thm corres_if} @{thms corres_esacs} @{thms val_rel_simps} @{thms type_rel_simps}
                   @{thms tag_enum_defs} @{thm LETBANG_TRUE_def} @{thms list_to_map_simps} true *})
  done

end
end

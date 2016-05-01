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
Program specifications generated from:
  cogent --type-proof=Split --fml-typing-tree pass_very-simple-split.cogent
  cogent -gpass_very-simple-split --table-c-types=pass_very-simple-split.table --fno-tuples-as-sugar pass_very-simple-split.cogent
*)
theory Split
imports 
  "../TypeProofGen"
  "../Deep_Embedding_Auto"
  "../Corres_Tac"
  "../Tidy"
begin

lemmas abbreviated_type_defs =
  TrueI

definition
  "foo_type \<equiv> ([], (TProduct (TPrim (Num U32)) (TPrim (Num U16)), TPrim (Num U32)))"

definition
  "foo \<equiv> Split (Var 0) (Var 0)"

definition
  "\<Xi> func_name' \<equiv> case func_name' of ''foo'' \<Rightarrow> foo_type"

definition
  "foo_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some (TPrim (Num U32)), Some (TPrim (Num U16))] TyTrLeaf"

ML {* open TTyping_Tactics *}

ML_quiet {*
val typing_helper_1_script : tac list = [
(RTac @{thm kind_tprim})
] *}


lemma typing_helper_1[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim (Num U32)) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_1_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_2_script : tac list = [
(RTac @{thm kind_tprim})
] *}


lemma typing_helper_2[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim (Num U16)) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_2_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_3_script : tac list = [
(RTac @{thm kind_tprod[where k = "{E,S,D}"]}),
(RTac @{thm typing_helper_1}),
(RTac @{thm typing_helper_2})
] *}


lemma typing_helper_3[unfolded abbreviated_type_defs] :
  "kinding [] (TProduct (TPrim (Num U32)) (TPrim (Num U16))) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_3_script |> EVERY *})
  done

ML_quiet {*
val foo_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_1})],
KindingTacs [(RTac @{thm typing_helper_2})],
TypingTacs [],
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


new_C_include_dir "../../cogent/tests"
install_C_file "pass_very-simple-split.c"

autocorres [ts_rules=nondet, no_opt] "pass_very-simple-split.c"

instantiation unit_t_C :: cogent_C_val
begin
 definition type_rel_unit_t_C_def:
  "type_rel typ (_ :: unit_t_C itself) \<equiv> typ = RUnit"
 definition val_rel_unit_t_C_def:
  "val_rel uv (x :: unit_t_C) \<equiv> uv = UUnit"
instance ..
end

instantiation bool_t_C :: cogent_C_val
begin
definition type_rel_bool_t_C_def:
  "type_rel typ (_ :: bool_t_C itself) \<equiv> (typ = RPrim Bool)"

definition val_rel_bool_t_C_def:
  "val_rel uv (x :: bool_t_C) \<equiv> (boolean_C x = 0 \<or> boolean_C x = 1) \<and>
                                uv = UPrim (LBool (boolean_C x \<noteq> 0))"
instance ..
end

local_setup{* local_setup_val_rel_type_rel_put_them_in_buckets "pass_very-simple-split.c" *}

class cogent_C_heap =  
  fixes is_valid    :: "lifted_globals \<Rightarrow> 'a ptr \<Rightarrow> bool"
  fixes heap        :: "lifted_globals \<Rightarrow> 'a ptr \<Rightarrow> 'a"

lemmas val_rel_simps = val_rel_word val_rel_ptr_def val_rel_unit_t_C_def
lemmas type_rel_simps = type_rel_word_def type_rel_ptr_def type_rel_unit_t_C_def

locale split_cogent = "pass_very-simple-split" + update_sem_init
begin
definition
  heap_rel_ptr ::
  "(funtyp, abstyp, ptrtyp) store \<Rightarrow> lifted_globals \<Rightarrow>
   ('a :: {cogent_C_heap,cogent_C_val}) ptr \<Rightarrow> bool"
where
  "heap_rel_ptr \<sigma> h p \<equiv>
   (\<forall>uv.
     \<sigma> (ptr_val p) = Some uv \<longrightarrow>
     type_rel (uval_repr uv) TYPE('a) \<longrightarrow>
     is_valid h p \<and> val_rel uv (heap h p))"

local_setup {* tidy_C_fun_def' "foo" *}
print_theorems

lemmas corres_nested_let = TrueI (* dummy *)

lemma foo_corres:
  "val_rel (\<gamma> ! 0) input \<Longrightarrow>
  corres state_rel (foo) (foo' input) \<xi> \<gamma> \<Xi> [Some (TProduct (TPrim (Num U32)) (TPrim (Num U16)))] \<sigma> s"
  apply (tactic {* corres_tac @{context}
    (peel_two foo_typing_tree)
    @{thms foo_def foo'_def' foo_type_def abbreviated_type_defs} [] []
    @{thm TrueI} [] @{thms val_rel_simps} @{thms type_rel_simps} []
    @{thm TrueI} @{thms TrueI} true *})
  done

end
end

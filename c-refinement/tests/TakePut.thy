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
 *   cogent --type-proof=TakePut --fml-typing-tree pass_simple-take-letput.cogent
 *   cogent -gpass_simple-take-letput --table-c-types=pass_simple-take-letput pass_simple-take-letput.cogent
 *)
theory TakePut
imports 
  "../Deep_Embedding_Auto"
  "../COGENT_Corres"
  "../Corres_Tac"
  "TakePut_TP"
  "../Tidy"
begin

new_C_include_dir "../../cogent/tests"
install_C_file "pass_simple-take-letput.c"
autocorres [ts_rules=nondet, no_opt, skip_word_abs] "pass_simple-take-letput.c"

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

(* Relation between COGENT and C data *)
local_setup{* local_setup_val_rel_type_rel_put_them_in_buckets "pass_simple-take-letput.c" *}
print_theorems

class cogent_C_heap = cogent_C_val +
  fixes is_valid    :: "lifted_globals \<Rightarrow> 'a ptr \<Rightarrow> bool"
  fixes heap        :: "lifted_globals \<Rightarrow> 'a ptr \<Rightarrow> 'a"

local_setup{* local_setup_instantiate_cogent_C_heaps_store_them_in_buckets "pass_simple-take-letput.c"*}

locale take_cogent = "pass_simple-take-letput" + update_sem_init
begin
(* Relation between program heaps *)
definition
  heap_rel_ptr ::
  "(funtyp, abstyp, ptrtyp) store \<Rightarrow> lifted_globals \<Rightarrow>
   ('a :: cogent_C_heap) ptr \<Rightarrow> bool"
where
  "heap_rel_ptr \<sigma> h p \<equiv>
   (\<forall>uv.
     \<sigma> (ptr_val p) = Some uv \<longrightarrow>
     type_rel (uval_repr uv) TYPE('a) \<longrightarrow>
     is_valid h p \<and> val_rel uv (heap h p))"

lemma heap_rel_ptr_meta:
  "heap_rel_ptr = heap_rel_meta is_valid heap"
  by (simp add: heap_rel_ptr_def[abs_def] heap_rel_meta_def[abs_def])

local_setup{* local_setup_heap_rel "pass_simple-take-letput.c" *}
print_theorems

definition state_rel :: "((funtyp, abstyp, ptrtyp) store\<times> lifted_globals) set"
where
  "state_rel = {(\<sigma>, h). heap_rel \<sigma> h}"

lemmas val_rel_simps[ValRelSimp] = val_rel_word val_rel_bool_t_C_def val_rel_ptr_def val_rel_unit_t_C_def
lemmas type_rel_simps[TypeRelSimp] = type_rel_word type_rel_bool_t_C_def type_rel_ptr_def type_rel_unit_t_C_def


(* Generating the specialised take and put lemmas *)

local_setup{* local_setup_take_put_member_case_esac_specialised_lemmas "pass_simple-take-letput.c" *}
print_theorems

thm take_cogent.corres_let_put_t1_C_y_C_writable[[no_vars]]

local_setup {* tidy_C_fun_def' "foo" *}

(* Corres tactic *)
lemmas list_to_map_simps = list_to_map_more[where f=Var] list_to_map_singleton[where f=Var]

lemmas corres_case = 
  TrueI
lemmas corres_esac = 
  TrueI

thm tag_enum_defs

lemmas corres_nested_let = TrueI
find_theorems name:foo_ name:"_def"
(* Corres lemma *)
lemma foo_corres:
  "val_rel a (a':: t2_C ptr) \<Longrightarrow> 
  corres state_rel foo (foo' a') \<xi> [a] \<Xi> [Some (fst (snd foo_type))] \<sigma> s"
  apply (tactic {* corres_tac @{context}
    (peel_two foo_typing_tree)
    @{thms foo_def foo'_def' foo_type_def abbreviated_type_defs} [] []
    @{thm TrueI} @{thms corres_esac} @{thms val_rel_simps} @{thms type_rel_simps}
    @{thms tag_enum_defs} @{thm LETBANG_TRUE_def}
    @{thms list_to_map_simps} true *})
  done

end

end

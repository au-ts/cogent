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

theory Cogent_C_Val_Auto
imports
 Value_Relation_Generation
 Type_Relation_Generation
begin

ML\<open> fun local_setup_val_rel_type_rel_put_them_in_buckets file_nm ctxt =
(* local_setup_val_rel_type_rel defines and registers all the necessary val_rels and type_rels.*)
 let
  fun val_rel_type_rel_def uval lthy = lthy |> type_rel_def file_nm uval |> val_rel_def file_nm uval;

  (* FIXME: This recursion is pretty bad, I think.*)
  fun local_setup_val_rel_type_rel' [] lthy = lthy
   |  local_setup_val_rel_type_rel' (uval::uvals) lthy =
       local_setup_instantiation_definition_instance ([get_ty_nm_C uval],[],"cogent_C_val")
       (val_rel_type_rel_def uval) (local_setup_val_rel_type_rel' uvals lthy);

  fun is_notin_ignore _ [] = true
   |  is_notin_ignore x (y::ys) = if x <> y then is_notin_ignore x ys else false;

  val thy = Proof_Context.theory_of ctxt;

  val ign = [UAbstract "WordArray_u32"];

  val uvals' = read_table file_nm (Proof_Context.theory_of ctxt);
  val uvals = uvals' |> map (unify_usum_tys o unify_sigils) |> rm_redundancy |> rev |>
               get_uvals_for_which_ac_mk_st_info file_nm thy |> filter (fn x => is_notin_ignore x ign);
  (* FIXME: Currently explicitly removing 32-bit word arrays from this so that I can do this manually *)

  val lthy' = local_setup_val_rel_type_rel' uvals ctxt;
 in
  lthy'
 end;
\<close>

end

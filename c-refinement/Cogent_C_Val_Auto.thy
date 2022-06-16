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

ML\<open> fun local_setup_val_rel_type_rel_put_them_in_buckets file_nm ign ctxt =
(* local_setup_val_rel_type_rel defines and registers all the necessary val_rels and type_rels.*)
 let
  fun val_rel_type_rel_def uval lthy = lthy |> type_rel_def file_nm uval |> val_rel_def file_nm uval;

  (* FIXME: This recursion is pretty bad, I think.*)
  fun local_setup_val_rel_type_rel' [] lthy = lthy
   |  local_setup_val_rel_type_rel' (uval::uvals) lthy =
        local_setup_instantiation_definition_instance_if_needed
      (get_ty_nm_C uval) "cogent_C_val" is_cogent_C_val      
       (val_rel_type_rel_def  uval) (local_setup_val_rel_type_rel' uvals lthy);

  val thy = Proof_Context.theory_of ctxt;

  fun notin_ign_list' [] _ = true
   |  notin_ign_list' (x::xs) y = if x <> y then notin_ign_list' xs y else false;

  val notin_ign_list = filter (fn x => notin_ign_list' ign x);
  val uvals' =
    (case get_uvals file_nm (Proof_Context.theory_of ctxt) of
      NONE => raise ERROR (prefix "no uvals for " file_nm)
    | SOME uvals' => uvals');

  val uvals = uvals' |> map (unify_usum_tys o unify_sigils) |> rm_redundancy |> rev |>
               get_uvals_for_which_ac_mk_st_info file_nm thy |> notin_ign_list;

  val lthy' = local_setup_val_rel_type_rel' uvals ctxt;
 in
  lthy'
 end;
\<close>

end

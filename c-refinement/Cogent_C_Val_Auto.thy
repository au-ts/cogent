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

ML \<open>
fun test_read_term lthy (s : string) : bool =
 (  Proof_Context.read_term_pattern lthy s ; true)
handle ERROR _ => false

fun is_cogent_C_val lthy (typ : string) : bool =
  test_read_term lthy ("type_rel _ TYPE(" ^ typ ^ ")")

\<close>
ML\<open> fun local_setup_val_rel_type_rel_put_them_in_buckets file_nm ctxt =
(* local_setup_val_rel_type_rel defines and registers all the necessary val_rels and type_rels.*)
 let
  fun val_rel_type_rel_def uval lthy = lthy |> type_rel_def file_nm uval |> val_rel_def file_nm uval;

  (* FIXME: This recursion is pretty bad, I think.*)
  fun local_setup_val_rel_type_rel' [] lthy = lthy
   |  local_setup_val_rel_type_rel' (uval::uvals) lthy =
       let 
         val C_typ = get_ty_nm_C uval
         val is_already_C_val = is_cogent_C_val lthy C_typ
         val lthy = local_setup_val_rel_type_rel' uvals lthy
       in        
        if is_already_C_val then 
           (tracing (C_typ ^ " is already a cogent_C_val");
           lthy )
        else
         local_setup_instantiation_definition_instance ([get_ty_nm_C uval],[],"cogent_C_val")
         (val_rel_type_rel_def uval) lthy
      end

  val thy = Proof_Context.theory_of ctxt;

  val uvals' = read_table file_nm (Proof_Context.theory_of ctxt);
  val uvals = uvals' |> map (unify_usum_tys o unify_sigils) |> rm_redundancy |> rev |>
               get_uvals_for_which_ac_mk_st_info file_nm thy;

  val lthy' = local_setup_val_rel_type_rel' uvals ctxt;
 in
  lthy'
 end;
\<close>

end

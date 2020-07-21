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

theory Cogent_C_Heap_Auto
imports Read_Table
begin

text\<open> Instantiation of cogent_C_heap. is_valid_def and heap_def. \<close>

ML\<open> fun is_valid_def uval ctxt =
 let
  val ty_name_C    = get_ty_nm_C uval;
  val lhs          = Syntax.read_term ctxt "is_valid";
  val rhs          = Syntax.read_term ctxt ("is_valid_" ^ ty_name_C);
  val equ          = mk_eq_tm lhs rhs ctxt;
  val is_valid_name = "is_valid_" ^ ty_name_C ^"_def";
  val spec_def = Specification.definition NONE [] [] ((Binding.name is_valid_name, []), equ) ctxt;
  val thm      = spec_def |> fst |> snd |> snd;
  val lthy     = snd spec_def;
  val lthy'    = IsValidSimp.add_local thm lthy;
  val _ = tracing ("generating is_valid_def for " ^ (get_uval_name uval))
 in lthy' end;
\<close>

ML\<open> fun heap_def uval ctxt =
 let
  val ty_name_C = get_ty_nm_C uval;
  val lhs       = Syntax.read_term ctxt "heap";
  val rhs       = Syntax.read_term ctxt ("heap_" ^ ty_name_C);
  val equ       = mk_eq_tm lhs rhs ctxt;
  val is_valid_name = "heap_" ^ ty_name_C ^"_def";
  val spec_def = Specification.definition NONE [] [] ((Binding.name is_valid_name, []), equ) ctxt;
  val thm      = spec_def |> fst |> snd |> snd;
  val lthy     = snd spec_def;
  val lthy'    = HeapSimp.add_local thm lthy;
  val _ = tracing ("generating heap_def for " ^ (get_uval_name uval))
 in lthy' end;
\<close>

ML\<open> fun local_setup_instantiate_cogent_C_heaps_store_them_in_buckets file_nm lthy =
 let
  fun define_cogent_C_heap uval ctxt = ctxt |> is_valid_def uval |> heap_def uval;

  fun local_setup' _ [] lthy = lthy
   |  local_setup' file_nm (uval::uvals) lthy =
       local_setup_instantiation_definition_instance_if_needed
      (get_ty_nm_C uval) "cogent_C_heap" is_cogent_C_heap      
       (define_cogent_C_heap  uval) (local_setup' file_nm uvals lthy);

  val thy = Proof_Context.theory_of lthy;

  val uvals'  = (case get_uvals file_nm thy of
      NONE => raise ERROR (prefix "no uvals for " file_nm)
    | SOME uvals' => uvals');
  val uvals  = uvals' |>
               map (unify_usum_tys o unify_sigils) |> rm_redundancy |>
               get_uvals_for_which_ac_mk_heap_getters file_nm thy
 in
  local_setup' file_nm (List.rev uvals) lthy
 end;
\<close>

end

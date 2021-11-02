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

theory Heap_Relation_Generation
imports Read_Table
begin

ML\<open> (* local_setup_heap_rel *)
local

fun mk_heap_rel ctxt (uvals:'a uval list) other prims =


(* mk_heap_rel makes the equation that defines heap relation for a given type.
 * For example, "heap_rel \<sigma> h \<equiv> (\<forall>(p :: t2_C ptr). heap_rel_ptr \<sigma> h p)". *)

 let
  fun mk_pointed_ty ty_nm_C = Syntax.read_typ ctxt ty_nm_C;
  fun mk_pointer_ty ty_nm_C = Type ("CTypesBase.ptr", [mk_pointed_ty ty_nm_C]);
  fun mk_a_conjct ty_nm_C =
   Const ("HOL.All", dummyT) $
    Abs ("p", mk_pointer_ty ty_nm_C,
     (Syntax.read_term ctxt "heap_rel_ptr" $
       Free ("\<sigma>", dummyT) $ Free ("h", dummyT) $ Bound 0));
  fun mk_conjcts [] = []
   |  mk_conjcts (ty_nm_C::ty_nm_Cs) = mk_a_conjct ty_nm_C :: mk_conjcts ty_nm_Cs;

  fun mk_a_conjct' (ty, nm)  =
   Const ("HOL.All", dummyT) $
    Abs ("p", mk_pointer_ty ty,
     (Syntax.read_term ctxt "heap_rel_meta" $
       Syntax.read_term ctxt ("is_valid_" ^ nm) $
       Syntax.read_term ctxt ("heap_" ^ nm) $ 
       Free ("\<sigma>", dummyT) $ Free ("h", dummyT) $ Bound 0));
  fun mk_conjcts' [] = []
   |  mk_conjcts' (ty_nm_C::ty_nm_Cs) = mk_a_conjct' ty_nm_C :: mk_conjcts' ty_nm_Cs;
  val rhs' = mk_conjcts' prims

  (* We have heap_rels for URecords only.*)
  val ty_nm_Cs = uvals |> get_urecords |> map get_ty_nm_C;
  val rhs'' = mk_conjcts (ty_nm_Cs @ other)

  (* FIXME later: hey, Yutaka. rhs is a bit stupid.*)
  val rhs= if (rhs' = []) orelse (rhs'' = []) then @{term "True"} else rhs'' @ rhs' |>mk_HOL_conjs ;
  val heap_rel = Free ("heap_rel", dummyT);
  val lhs = strip_atype @{term "\<lambda> heap_rel . heap_rel \<sigma> h"} $ heap_rel |> strip_atype;
 in
  mk_eq_tm lhs rhs ctxt
 end : term;

in

fun local_setup_heap_rel file_nm other other' lthy =
(* local_setup_heap_rels defines and register a number of heap_rels
 * when called inside local_setup quotation.*)
 let
  val thy   = Proof_Context.theory_of lthy;
  val uvals = get_uvals file_nm thy |> the
             |> map (unify_usum_tys o unify_sigils)
             |> rm_redundancy
             |> get_uvals_for_which_ac_mk_heap_getters file_nm thy;
  val heap_rel = mk_heap_rel lthy uvals other other';
  val lthy' = Specification.definition NONE [] [] ((Binding.name ("heap_rel_def"), []), heap_rel) lthy |> snd;
 in lthy' end;

end;
\<close>
end

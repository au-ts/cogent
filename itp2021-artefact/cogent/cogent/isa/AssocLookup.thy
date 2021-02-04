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

(*
 * Given a list of mappings "[(k1, v1), (k2, v2), ...]", define a function that performs the mapping.
 * If none of the keys match, the default value is returned.
 * If multiple keys match, the first one is used. (So having duplicate keys is useless.)
 *
 * Analogue of C-parser's StaticFun but without the linorder requirement.
 * Uses an assoc-list instead of binary tree. This makes the setup cost O(n^2) but
 * the lookup cost is unchanged (we prove the same equations as StaticFun does).
 *
 * TODO: move to l4v/lib (or further upstream)
 *)
theory AssocLookup imports
  Main
begin

fun assoc_lookup :: "('a \<times> 'b) list \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b" where
    "assoc_lookup [] def _ = def"
  | "assoc_lookup ((k, v) # ls) def x = (if x = k then v else assoc_lookup ls def x)"

(* These versions are better for simp performance *)
lemma assoc_lookup_simps[simp]:
  "assoc_lookup [] def x = def"
  "assoc_lookup ((k, v) # ls) def k = v"
  (* make_assoc_fun shouldn't need this one *)
  (*"x = k \<Longrightarrow> assoc_lookup ((k, v) # ls) def x = v"*)
  "x \<noteq> k \<Longrightarrow> assoc_lookup ((k, v) # ls) def x = assoc_lookup ls def x"
  by simp_all
declare assoc_lookup.simps[simp del]

(*
 * Main interface.
 * Note that all types in "assocs" and "default" need to match,
 * this procedure doesn't do type unification. *)
ML \<open>
structure AssocLookup = struct

fun make_assoc_fun
        (assocs: (term*term) list) (default: term)
        (name: string) (eqn_names: string list)
        ctxt = let
  (* define lookup function *)
  val [key_typ, val_typ] = case assocs of ((k, v) :: _) => map type_of [k, v]
                                        | _ => error "make_assoc_fun: empty list"
  val alist_term = HOLogic.mk_list (HOLogic.mk_prodT (key_typ, val_typ)) (map HOLogic.mk_prod assocs)
  val assoc_lookupT = HOLogic.listT (HOLogic.mk_prodT (key_typ, val_typ)) --> val_typ --> key_typ --> val_typ
  val defn = Const (@{const_name assoc_lookup}, assoc_lookupT) $ alist_term $ default
  val ((f_term, (_, f_def)), ctxt) =
          Local_Theory.define ((Binding.name name, NoSyn),
                              ((Thm.def_binding (Binding.name name), []), defn)) ctxt
  val proof_ctxt = ctxt addsimps [f_def]
  (* generate lookup equations for function *)
  val eqns = eqn_names ~~ assocs
        |> Par_List.map (fn (name, (k, v)) => let
            val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (betapply (f_term, k), v))
            val thm = Goal.prove ctxt [] [] prop (K (
                        simp_tac proof_ctxt 1))
            in (name, thm)
            end)
  (* store the equations by eqn_names *)
  val grouped_eqns = eqns
        |> sort_by fst
        |> partition_eq (fn (e1, e2) => fst e1 = fst e2)
  val (_, ctxt) = Local_Theory.notes (map (fn eqns =>
        ((Binding.name (fst (hd eqns)), []), [(map snd eqns, [])])) grouped_eqns) ctxt
  in ctxt end

end
\<close>

(* Test: *)
(*
local_setup \<open>
AssocLookup.make_assoc_fun
  [(@{term "(''S'', 1::nat)"}, @{term "2::nat"}),
   (@{term "(''P'', 2::nat)"}, @{term "1::nat"}),
   (@{term "(''S'', 3::nat)"}, @{term "2+2::nat"})]
  @{term "42::nat"}
  "foo" ("foo1_simp" :: replicate 2 "foo23_simps")
\<close>
print_theorems
*)

end

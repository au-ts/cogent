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

(* Verify compiler's monomorphisation pass *)
theory Mono_Tac imports
  "Mono"
  "AssocLookup"
begin

context value_sem begin

(*
 * Define poly-to-mono name mapping.
 * The mapping should be defined as an assoc-list
 *   mapping_assocs :: ((string \<times> type list) \<times> string) list
 *   mapping_assocs \<equiv> ...
 * and this code generates the corresponding
 *   mapping :: (string \<times> type list) \<Rightarrow> string
 * If x \<notin> mapping_assocs, mapping x = ''''.
 *)
ML \<open>
fun gen_mono_rename
      (Cogent_functions: string list) (* exclude these non-abstract functions, for performance *)
      (mapping_assocs: thm)
      (mapping_name: string)
      = let
  val assocs = snd (Logic.dest_equals (Thm.prop_of mapping_assocs))
               |> map HOLogic.dest_prod o HOLogic.dest_list
               |> filter (fn (k, _) => HOLogic.dest_prod k |> fst |> HOLogic.dest_string
                                       |> not o member op= Cogent_functions)
  in if null assocs
     then Local_Theory.define ((Binding.name mapping_name, NoSyn),
                              ((Thm.def_binding (Binding.name mapping_name), []),
                                @{term "(\<lambda>_. []) :: (string \<times> type list) \<Rightarrow> string"})) #> snd
     else AssocLookup.make_assoc_fun assocs @{term "[] :: string"}
             mapping_name (replicate (length assocs) (mapping_name ^ "_simps"))
  end
\<close>

(*
 * Prove equalities of the form
 *   rename_expr rename_fn (monoexpr poly_f) = mono_f
 * for each deeply-embedded Cogent function f \<rightarrow> (poly_f, mono_f).
 * "callees" is assumed to be a list of such equalities for
 * the functions called by f.
 *
 * "extra_simps" can be used to give:
 *  - simps for rename_fn
 *  - type abbreviations used in mono_f and poly_f
 *)
ML \<open>
fun gen_monoexpr_thm
      (poly_thy: string) (mono_thy: string)
      (rename_fn: term)
      (rename_inv: (string * term) Symtab.table) (* mono name -> poly inst *)
      (callees: thm list) (f: string)
      (extra_simps: thm list) ctxt = let
  val (poly_name, type_inst) = case Symtab.lookup rename_inv f of
              SOME x => x
            | NONE => raise ERROR ("gen_monoexpr_thm: " ^ f ^ ": couldn't find polymorphic source")
  val poly_f = Syntax.read_term ctxt (poly_thy ^ "." ^ poly_name)
  val mono_f = Syntax.read_term ctxt (mono_thy ^ "." ^ f)
  val poly_def = Proof_Context.get_thm ctxt (poly_thy ^ "." ^ poly_name ^ "_def")
  val mono_def = Proof_Context.get_thm ctxt (mono_thy ^ "." ^ f ^ "_def")
  val poly_f_spec = if null (HOLogic.dest_list type_inst) then poly_f else @{term specialise} $ type_inst $ poly_f
  val prop = @{term "(=)"} $ (@{term "rename_expr"} $ rename_fn $ (@{term "monoexpr"} $ poly_f_spec))
                            $ mono_f
             |> map_types (K dummyT) |> Syntax.check_term ctxt
  val thm = Timing.timeap_msg ("gen_monoexpr_thm: " ^ poly_name ^ " -> " ^ f)
              (Goal.prove ctxt [] [] (HOLogic.mk_Trueprop prop))
              (K (simp_tac (ctxt addsimps ([poly_def, mono_def] @ extra_simps @ callees)) 1))
  in thm end
\<close>

end

end

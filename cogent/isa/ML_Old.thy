(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

(*
 * FIXME:
 *
 * This file re-implements old (deprecated!) methods that were used in the ML parts of the Cogent
 * proofs from circa 2015. Eventually we should rewrite these proofs in a more modern style.
 *)

theory ML_Old
  imports Pure
begin
  ML {*

  val term_pat_setup =
  let
    val name_inner_syntax = Args.name_token >> Token.inner_syntax_of
    val parser = Args.context -- Scan.lift name_inner_syntax

    fun term_pat (ctxt, str) =
      str |> Proof_Context.read_term_pattern ctxt
          |> ML_Syntax.print_term
          |> ML_Syntax.atomic

  in
    ML_Antiquotation.inline @{binding "term_pat"} (parser >> term_pat)
  end
  *}

setup {* term_pat_setup *}

ML {*
  fun rtac rl = resolve0_tac [rl]

  fun atac i = PRIMSEQ (Thm.assumption NONE i);
*}

ML {*
  fun gen_all maxidx0 th =
  let
    val thy = Thm.theory_of_thm th;
    val maxidx = Thm.maxidx_thm th maxidx0;
    val prop = Thm.prop_of th;
    fun elim (x, T) =
      Thm.forall_elim (Thm.global_cterm_of thy (Var ((x, maxidx + 1), T)));
  in fold elim (Drule.outer_params prop) th end;
*}

end
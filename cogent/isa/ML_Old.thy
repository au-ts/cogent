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
 * FIXME:
 *
 * This file re-implements old (deprecated!) methods that were used in the ML parts of the Cogent
 * proofs from circa 2015. Eventually we should rewrite these proofs in a more modern style.
 *)

theory ML_Old
  imports Pure
begin
  ML {*

  val schematic_term_setup =
  let
    val name_inner_syntax = Args.name_token >> Token.inner_syntax_of
    val parser = Args.context -- Scan.lift name_inner_syntax

    fun schematic_term (ctxt, str) =
      str |> Proof_Context.read_term_pattern ctxt
          |> ML_Syntax.print_term
          |> ML_Syntax.atomic

  in
    ML_Antiquotation.inline @{binding "schematic_term"} (parser >> schematic_term)
  end
  *}

setup {* schematic_term_setup *}

ML {*
  fun rtac rl = resolve0_tac [rl];
  fun etac rl = eresolve0_tac [rl];

  fun atac i = PRIMSEQ (Thm.assumption NONE i);

  fun forward0_tac rls = resolve0_tac (map make_elim rls) THEN' atac;
  fun ftac rl = forward0_tac [rl];
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

ML {*
fun debug_print_to_file pathstr s = File.write (Path.explode pathstr) s
*}

end
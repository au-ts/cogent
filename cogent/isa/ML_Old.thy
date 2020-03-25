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
  imports Main
begin

declare [[ML_debugger=true]]

ML \<open>
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
  \<close>

setup \<open> schematic_term_setup \<close>

ML \<open>
  fun rtac rl = resolve0_tac [rl];
  fun etac rl = eresolve0_tac [rl];

  fun atac i = PRIMSEQ (Thm.assumption NONE i);

  fun forward0_tac rls = resolve0_tac (map make_elim rls) THEN' atac;
  fun ftac rl = forward0_tac [rl];
\<close>

ML \<open>
  fun gen_all maxidx0 th =
  let
    val thy = Thm.theory_of_thm th;
    val maxidx = Thm.maxidx_thm th maxidx0;
    val prop = Thm.prop_of th;
    fun elim (x, T) =
      Thm.forall_elim (Thm.global_cterm_of thy (Var ((x, maxidx + 1), T)));
  in fold elim (Drule.outer_params prop) th end;
\<close>

ML \<open>
fun debug_print_to_file pathstr s = File.write (Path.explode pathstr) s

val LOG_FILE = Path.basic "TypeProofTactic.json"
fun log_to_file strs = File.append LOG_FILE (YXML.content_of (strs^"\n"))
fun log_error str = log_to_file ("!!! " ^ str)
fun log_info str  = log_to_file ("    " ^ str)
fun raise_error err =
  let
    val _   = log_error err
  in
     raise ERROR err
  end

(* 
 * Logs a Timing.timing in LOG_FILE in JSON format:
 * {
 *   tacticName: "string"
 *   time: { elapsed: float, cpu: float, gc: float }
 * }
 *)
fun logTime tacName ({elapsed, cpu, gc} : Timing.timing) =
  File.append LOG_FILE (
    "{ \"tacticName\": \"" ^ tacName ^ "\"," ^
    " \"time\": { "
      ^ "\"elapsed\": " ^ (Int.toString (Time.toMicroseconds elapsed)) ^ ", "
      ^ "\"cpu\": "     ^ (Int.toString (Time.toMicroseconds cpu)) ^ ", "
      ^ "\"gc\": "      ^ (Int.toString (Time.toMicroseconds gc))
      ^ "}"
  ^ "}\n"
  )

(* 
 * Runs a tactic, logging it's total time in LOG_FILE
 *)
fun logTacticOnUse (tacName : string) (tac : unit -> 'a) =
  let 
    val s = Timing.start ();
    val res = tac ();
    val _ = logTime tacName (Timing.result s)
  in
     res
  end
\<close>

ML \<open>

val permute_tac = PRIMITIVE oo Thm.permute_prems;

fun distinct_tac (i, k) =
  permute_tac 0 (i - 1) THEN
  permute_tac 1 (k - 1) THEN
  PRIMITIVE (fn st => Drule.comp_no_flatten (st, 0) 1 Drule.distinct_prems_rl) THEN
  permute_tac 1 (1 - k) THEN
  permute_tac 0 (1 - i);

fun distinct_subgoal_tac i st =
  (case drop (i - 1) (Thm.prems_of st) of
    [] => no_tac st
  | A :: Bs =>
      st |> EVERY (fold (fn (B, k) =>
        if A aconv B then cons (distinct_tac (i, k)) else I) (Bs ~~ (1 upto length Bs)) []));

(* 
 * Logs a Timing.timing in LOG_FILE in JSON format:
 * {
 *   tacticName: "string"
 *   time: { elapsed: float, cpu: float, gc: float }
 * }
 *)
fun logTime tacName ({elapsed, cpu, gc} : Timing.timing) =
  File.append LOG_FILE (
    "{ \"tacticName\": \"" ^ tacName ^ "\"," ^
    " \"time\": { "
      ^ "\"elapsed\": " ^ (Int.toString (Time.toMicroseconds elapsed)) ^ ", "
      ^ "\"cpu\": "     ^ (Int.toString (Time.toMicroseconds cpu)) ^ ", "
      ^ "\"gc\": "      ^ (Int.toString (Time.toMicroseconds gc))
      ^ "}"
  ^ "}\n"
  )

(* 
 * Runs a tactic, logging it's total time in LOG_FILE
 *)
fun logTacticOnUse (tacName : string) (tac : unit -> 'a) =
  let 
    val s = Timing.start ();
    val res = tac ();
    val _ = logTime tacName (Timing.result s)
  in
     res
  end
\<close>

end
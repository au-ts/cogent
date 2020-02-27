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

theory SpecialisedLemmaTactic
  imports
    "Cogent.CogentHelper"
    "Cogent.ML_Old"
    "Cogent_Corres"
    "Specialised_Lemma_Utils"
begin

context update_sem_init
begin

ML\<open> fun corres_take_boxed_tac ctxt = let
    val val_rels   = ValRelSimp.get ctxt;
    val type_rels  = TypeRelSimp.get ctxt;
    val is_valids  = IsValidSimp.get ctxt;
    val heap_simps = HeapSimp.get ctxt;
    val gets = Proof_Context.get_thms ctxt
    val get  = Proof_Context.get_thm ctxt
    val facts' = maps gets
        ["state_rel_def", "heap_rel_def", "val_rel_ptr_def", "type_rel_ptr_def", "heap_rel_ptr_meta"]
    val facts = facts' @ is_valids @ heap_simps
  in EVERY' [
    asm_full_simp_tac ((put_simpset HOL_basic_ss ctxt) addsimps [get "val_rel_ptr_def"]),
    REPEAT_ALL_NEW (etac @{thm exE}),
    ((rtac (get "corres_take_boxed") ORELSE' rtac (get "corres_member_boxed"))
        THEN_ALL_NEW (TRY o atac)
        THEN_ALL_NEW asm_full_simp_tac ctxt
        THEN_ALL_NEW clarsimp_tac (ctxt addsimps facts)
        THEN_ALL_NEW (rtac (get "u_t_p_recE") THEN' atac)
        THEN_ALL_NEW clarsimp_tac (ctxt addSDs (gets "type_repr_uval_repr"))
        THEN_ALL_NEW (ftac (get "all_heap_rel_ptrD") THEN' atac)
        THEN_ALL_NEW clarsimp_tac (ctxt addsimps type_rels addsimps val_rels)
    ) ] end
\<close>

ML\<open> fun corres_put_boxed_tac ctxt = let
    val gets = Proof_Context.get_thms ctxt
    val get  = Proof_Context.get_thm ctxt
    val type_rels  = TypeRelSimp.get ctxt;
    val val_rels   = ValRelSimp.get ctxt;
    val is_valids  = IsValidSimp.get ctxt;
    val heap_simps = HeapSimp.get ctxt;
    val facts1 = get "val_rel_ptr_def" :: @{thms gets_to_return return_bind}
    val facts2 = maps gets
        ["state_rel_def", "heap_rel_def", "val_rel_ptr_def", "type_rel_ptr_def", "heap_rel_ptr_meta"]
    val facts3 = facts2 @ is_valids @ heap_simps
    fun trace str i t = (@{print tracing} str; @{print tracing} t; Seq.succeed t)
  in
    EVERY' [
    asm_full_simp_tac ((put_simpset HOL_basic_ss ctxt) addsimps facts1),
    REPEAT_ALL_NEW (etac @{thm exE}),
    ((rtac (get "corres_put_boxed" |> Simplifier.rewrite_rule ctxt @{thms gets_to_return[THEN eq_reflection]})
        THEN' simp_tac ctxt
        THEN' atac THEN' atac THEN' atac)
        THEN_ALL_NEW asm_full_simp_tac ctxt),
    clarsimp_tac (ctxt addsimps facts3),
    (rtac (get "u_t_p_recE") THEN' atac) THEN_ALL_NEW asm_full_simp_tac ctxt,
    clarsimp_tac (ctxt addSDs (gets "type_repr_uval_repr")
        addsimps type_rels),
    (ftac (get "all_heap_rel_ptrD") THEN' atac)
        THEN_ALL_NEW asm_full_simp_tac (ctxt addsimps type_rels),
    clarsimp_tac ctxt,
    REPEAT_ALL_NEW (rtac @{thm conjI})
        THEN_ALL_NEW ((rtac (get "all_heap_rel_updE") THEN' atac THEN' atac)
            THEN_ALL_NEW distinct_subgoal_tac
            THEN_ALL_NEW asm_simp_tac (ctxt addsimps val_rels @ type_rels)
            THEN_ALL_NEW asm_simp_tac (ctxt addsimps @{thms map_update list_update_eq_id}
                delsimps @{thms length_0_conv length_greater_0_conv})
            THEN_ALL_NEW clarsimp_tac (ctxt addsimps val_rels @ type_rels)
        )
    ]
    ORELSE'
    EVERY' [
    asm_full_simp_tac ((put_simpset HOL_basic_ss ctxt) addsimps facts1),
    REPEAT_ALL_NEW (etac @{thm exE}),
    ((rtac (get "corres_put_boxed" |> Simplifier.rewrite_rule ctxt @{thms gets_to_return[THEN eq_reflection]})
        THEN' simp_tac ctxt
        THEN' atac THEN' atac THEN' atac)
        THEN_ALL_NEW asm_full_simp_tac ctxt),
    clarsimp_tac (ctxt addsimps facts3),
    (rtac (get "u_t_p_recE") THEN' atac) THEN_ALL_NEW asm_full_simp_tac ctxt,
    clarsimp_tac (ctxt addSDs (gets "type_repr_uval_repr")
        addsimps type_rels),
    (ftac (get "all_heap_rel_ptrD") THEN' atac)
        THEN_ALL_NEW asm_full_simp_tac (ctxt addsimps type_rels),
    ((rtac (get "all_heap_rel_updE") THEN' atac THEN' atac)
        THEN_ALL_NEW distinct_subgoal_tac
        THEN_ALL_NEW asm_simp_tac (ctxt addsimps val_rels @ type_rels)
        THEN_ALL_NEW asm_simp_tac (ctxt addsimps @{thms map_update list_update_eq_id}
            delsimps @{thms length_0_conv length_greater_0_conv})
        THEN_ALL_NEW clarsimp_tac (ctxt addsimps val_rels @ type_rels)
     )
    ]
  end
\<close>

ML\<open> fun corres_let_put_boxed_tac ctxt = let
    val gets = Proof_Context.get_thms ctxt
    val get  = Proof_Context.get_thm ctxt
    val type_rels  = TypeRelSimp.get ctxt;
    val val_rels   = ValRelSimp.get ctxt;
    val is_valids  = IsValidSimp.get ctxt;
    val heap_simps = HeapSimp.get ctxt;
    val facts1 = get "val_rel_ptr_def" :: @{thms gets_to_return return_bind}
    val facts2 = maps gets
        ["state_rel_def", "heap_rel_def", "val_rel_ptr_def", "type_rel_ptr_def", "heap_rel_ptr_meta"]
    val facts3 = facts2 @ is_valids @ heap_simps
  in
    EVERY' [
    asm_full_simp_tac ((put_simpset HOL_basic_ss ctxt) addsimps facts1),
    REPEAT_ALL_NEW (etac @{thm exE}),
    ((rtac (get "corres_let_put_boxed") THEN' simp_tac ctxt THEN' atac THEN' atac THEN' atac)
        THEN_ALL_NEW asm_full_simp_tac ctxt),
    clarsimp_tac (ctxt addsimps facts3),
    (rtac (get "u_t_p_recE") THEN' atac) THEN_ALL_NEW asm_full_simp_tac ctxt,
    clarsimp_tac (ctxt addSDs (gets "type_repr_uval_repr")
        addsimps type_rels),
    (ftac (get "all_heap_rel_ptrD") THEN' atac)
        THEN_ALL_NEW asm_full_simp_tac (ctxt addsimps type_rels),
    clarsimp_tac ctxt,
    REPEAT_ALL_NEW (rtac @{thm conjI})
        THEN_ALL_NEW ((rtac (get "all_heap_rel_updE") THEN' atac THEN' atac)
            THEN_ALL_NEW distinct_subgoal_tac
            THEN_ALL_NEW asm_simp_tac (ctxt addsimps val_rels @ type_rels)
            THEN_ALL_NEW asm_simp_tac (ctxt addsimps @{thms map_update list_update_eq_id}
                delsimps @{thms length_0_conv length_greater_0_conv})
            THEN_ALL_NEW clarsimp_tac (ctxt addsimps val_rels @ type_rels)
        )
    ]
    ORELSE'
        EVERY' [
    asm_full_simp_tac ((put_simpset HOL_basic_ss ctxt) addsimps facts1),
    REPEAT_ALL_NEW (etac @{thm exE}),
    ((rtac (get "corres_let_put_boxed") THEN' simp_tac ctxt THEN' atac THEN' atac THEN' atac)
        THEN_ALL_NEW asm_full_simp_tac ctxt),
    clarsimp_tac (ctxt addsimps facts3),
    (rtac (get "u_t_p_recE") THEN' atac) THEN_ALL_NEW asm_full_simp_tac ctxt,
    clarsimp_tac (ctxt addSDs (gets "type_repr_uval_repr")
        addsimps type_rels),
    (ftac (get "all_heap_rel_ptrD") THEN' atac)
        THEN_ALL_NEW asm_full_simp_tac (ctxt addsimps type_rels),
    ((rtac (get "all_heap_rel_updE") THEN' atac THEN' atac)
        THEN_ALL_NEW distinct_subgoal_tac
        THEN_ALL_NEW asm_simp_tac (ctxt addsimps val_rels @ type_rels)
        THEN_ALL_NEW asm_simp_tac (ctxt addsimps @{thms map_update list_update_eq_id}
            delsimps @{thms length_0_conv length_greater_0_conv})
        THEN_ALL_NEW clarsimp_tac (ctxt addsimps val_rels @ type_rels)
     )
    ]
  end
\<close>

ML\<open> fun corres_take_unboxed_tac ctxt = let
      val get = Proof_Context.get_thm ctxt
  in asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps (ValRelSimp.get ctxt)) 1
     THEN (REPEAT_ALL_NEW (eresolve_tac ctxt @{thms exE conjE}) 1)
     THEN rtac (get "corres_take_unboxed") 1
     THEN ALLGOALS (TRY o atac)
     THEN ALLGOALS (clarsimp_tac (ctxt addsimps ValRelSimp.get ctxt @ TypeRelSimp.get ctxt))
  end
\<close>

ML\<open> fun corres_case_tac ctxt = SUBGOAL (fn (t, i) => let
    val vr_simps = ValRelSimp.get ctxt
    val vr_simp_idx = make_thm_index scrape_C_types vr_simps
    val vr_simps = lookup_thm_index vr_simp_idx (scrape_C_types_term t)
    val thm = Proof_Context.get_thm ctxt "corres_case"
    val xs = Term.add_frees t [] |> filter (fn (s, _) => s = "x'")
    val xrawvar = case xs of [] => raise TERM ("corres_case_tac: no x'", [t])
        | _ => hd xs
    val x = Thm.cterm_of ctxt (Free xrawvar)
    val thm = Drule.infer_instantiate ctxt [(("x'", 0), x)] thm   (* TODO check 0 is the one we want here! It should be, hopefully. *)
    val tag_simps = Proof_Context.get_thms ctxt "tag_t_defs"
  in rtac thm
    THEN_ALL_NEW (TRY o atac)
    THEN_ALL_NEW asm_full_simp_tac (ctxt addsimps vr_simps)
    THEN_ALL_NEW clarsimp_tac ctxt
    THEN_ALL_NEW (TRY o REPEAT_ALL_NEW (etac @{thm disjE}))
    THEN_ALL_NEW clarsimp_tac (ctxt addsimps vr_simps addsimps tag_simps)
    end i)
\<close>

end

end

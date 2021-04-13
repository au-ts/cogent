From Coq Require Import List String ZArith.

From ITree Require Import ITree ITreeFacts.
From Vellvm Require Import LLVMAst LLVMEvents TopLevel Handlers InterpreterMCFG TopLevelRefinements
  DynamicTypes CFG TypToDtyp InterpretationStack SymbolicInterpreter DenotationTheory ScopeTheory
  DynamicValues ExpLemmas Coqlib NoFailure AListFacts.

From Checker Require Import Denotation DenotationTheory Cogent Compiler Utils.Tactics Invariants
  HelixLib.Correctness_Prelude HelixLib.BidBound HelixLib.IdLemmas HelixLib.VariableBinding Types.

Import ListNotations.
Import AlistNotations.

Import ExpTactics.
Import ProofMode.

Section BidBoundExtra.

  (* From Helix, but adjusted for Cogent - are these definitely still true? *)

  Lemma inputs_bound_between :
    forall (e : expr) (s1 s2 : IRState) (v : im)
           (next_bid entry_bid : block_id) (blks : ocfg typ),
      compile_expr e next_bid s1 ≡ inr (s2, (v, entry_bid, blks)) ->
      Forall (bid_bound_between s1 s2) (inputs (convert_typ [] blks)).
  Admitted.

  Lemma inputs_not_earlier_bound :
    forall (e : expr) (s1 s2 s3 : IRState) (v : im)
           (bid next_bid entry_bid : block_id) (blks : ocfg typ),
      bid_bound s1 bid ->
      (block_count s1 <= block_count s2)%nat ->
      compile_expr e next_bid s2 ≡ inr (s3, (v, entry_bid, blks)) ->
      Forall (fun x => x ≢ bid) (inputs (convert_typ [] blks)).
  Admitted.

  Lemma entry_bound_between :
    forall (e : expr) (s1 s2 : IRState) (v : im)
          (next_bid entry_bid : block_id) (blks : ocfg typ),
      compile_expr e next_bid s1 ≡ inr (s2, (v, entry_bid, blks)) ->
      bid_bound_between s1 s2 entry_bid \/ entry_bid ≡ next_bid.
  Admitted.

  Lemma outputs_bound_between :
    forall (e : expr) (s1 s2 : IRState) (v : im)
           (next_bid entry_bid : block_id) (blks : ocfg typ),
      compile_expr e next_bid s1 ≡ inr (s2, (v, entry_bid, blks)) ->
      Forall (fun bid => bid_bound_between s1 s2 bid \/ bid ≡ next_bid) (outputs (convert_typ [] blks)).
  Admitted.

  Lemma incBlockNamed_count_gen_mono :
    count_gen_mono block_count incBlockNamed.
  Proof.
    unfold count_gen_mono, incBlockNamed.
    intros.
    inv H. 
    auto.
  Qed.

End BidBoundExtra.

Section Block.

  (* wasn't sure how to do this rewrite *)
  Lemma cons_app :
    forall {A} (x : A) (xs : list A),
      x :: xs ≡ app [x] xs.
  Proof.
      unfold app; reflexivity.
  Qed.

End Block.

Section Expressions.

  Definition ocfg_res : Type := (block_id * block_id) + uvalue. 

  (* From Helix *)
  Definition branches (to : block_id) : Rel_cfg_T uval ocfg_res :=
    fun _ '(m, (l, (g, res))) => exists from, res ≡ inl (from, to).

  Definition compile_expr_post (i : im) (γ : ctx) (s1 s2 : IRState) (to : block_id)
                               (l : local_env) : Rel_cfg_T uval ocfg_res :=
    lift_Rel_cfg (state_invariant γ s2) ⩕
    correct_result_T γ s1 s2 i ⩕
    branches to ⩕
    (fun _ '(_, (l', _)) => local_scope_modif s1 s2 l l').

  (* like break_match_hyp but don't destruct field type matches *)
  Ltac break_match_hyp_defer_ft :=
    match goal with
      | [ H : context [ match ?X with _ => _ end ] |- _] =>
        match type of X with
          | sumbool _ _ => destruct X
          | FieldType => idtac
          | _ => destruct X eqn:?
        end
    end.

  Lemma compile_expr_correct :
    forall (e : expr) (γ : ctx) (s1 s2 : IRState)
           (v : im) (next_bid entry_bid prev_bid : block_id) (blks : ocfg typ)
           (memC : memoryC) (g : global_env) (l : local_env) (memV : memoryV),
      compile_expr e next_bid s1 ≡ inr (s2, (v, entry_bid, blks)) ->
      no_failure (interp_expr (E := E_cfg) (denote_expr γ e) memC) ->
      bid_bound s1 next_bid ->
      state_invariant γ s1 memC (memV, (l, g)) ->
      eutt
        (succ_cfg (compile_expr_post v γ s1 s2 next_bid l))
        (interp_expr (denote_expr γ e) memC)
        (interp_cfg (denote_ocfg (convert_typ [] blks) (prev_bid, entry_bid)) g l memV).
  Proof.
    induction e using expr_ind'; intros * COMP NOFAIL NEXT PRE.
    - (* Unit *)
      cbn* in *; simp.
      cbn*.
      rewrite denote_ocfg_unfold_not_in.
      cvred.
      apply eutt_Ret; split; [ | split; [ | split]]; cbn; eauto.
      intros.
      typ_to_dtyp_simplify.
      unfold denote_exp; cbn.
      go; reflexivity.
      apply local_scope_modif_refl.
      apply find_block_nil.
    - (* Lit l *)
      cbn* in *; simp.
      cbn*.
      rewrite denote_ocfg_unfold_not_in.
      cvred.
      apply eutt_Ret; split; [ | split; [ | split]]; cbn; eauto.
      intros.
      destruct l;
        simpl; typ_to_dtyp_simplify;
        unfold denote_exp; cbn;
        go; reflexivity.
      apply local_scope_modif_refl.
      apply find_block_nil.
    - (* LVar i *)
      cbn* in *; simp.
      rewrite denote_ocfg_unfold_not_in.
      cvred.
      unfold option_throw in *. simp.
      cbn; cred.
      apply eutt_Ret; split; [ | split; [ | split]]; cbn; eauto.
      intros.
      unfold id in *.
      cbn* in *.
      destruct PRE as [MEM WF].
      unfold memory_invariant in MEM.
      specialize (MEM _ _ _ Heqo0 Heqo).
      unfold correct_result in MEM.
      specialize (MEM l' H H0).
      assumption.
      apply local_scope_modif_refl.
      apply failure_expr_throw in NOFAIL.
      contradiction.
      apply find_block_nil.
    - (* Let e1 e2 *)
      pose proof COMP as COMP'.
      cbn* in COMP'; simp.
      rename s1 into pre_state, i into mid_state, i1 into post_state.
      rename l0 into e1_blks, l1 into e2_blks.
      rename b0 into e2_entry, entry_bid into e1_entry.
      rename t into e1_im_t, e into e1_im, t0 into e2_im_t, e0 into e2_im.
      rename t1 into new_var, l2 into cur_vars.
      rename Heqs into COMP_e1, Heqs1 into COMP_e2, Heql3 into BIND.
      cbn.
      clean_goal.

      (* deal with the first blocks *)
      rewrite convert_typ_ocfg_app.
      rewrite denote_ocfg_app; eauto.
      2 : {
        unfold no_reentrance.
        pose proof COMP_e1 as COMP_e1'.
        apply (inputs_not_earlier_bound _ _ _ _ _ _ _ _ _ NEXT) in COMP_e1'.
        pose proof COMP_e2 as COMP_e2'.
        apply entry_bound_between in COMP_e2'.
        apply inputs_bound_between in COMP_e1.
        apply outputs_bound_between in COMP_e2.
        pose proof (Forall_and COMP_e1 COMP_e1') as INPUTS.
        cbn in INPUTS.
        eapply Forall_disjoint.
        rewrite convert_typ_outputs in *.
        rewrite outputs_cons.
        simpl.
        apply Forall_cons; [ | exact COMP_e2].
        cbn.
        auto.
        exact INPUTS.
        intros x OUT_PRED [IN_BOUND IN_NEXT].
        destruct OUT_PRED as [OUT_PRED | OUT_PRED]; auto.
        unfold bid_bound_between in OUT_PRED, IN_BOUND.
        eapply state_bound_between_id_separate with (s4 := post_state).
        apply incBlockNamed_count_gen_injective.
        apply incBlockNamed_count_gen_mono.
        eassumption.
        eassumption.
        solve_block_count.
        solve_block_count.
      }
      cvred.
      cbn in *.
      pose proof PRE as PRE'.
      eapply eutt_clo_bind_returns.
      {
        eapply IHe1; eauto.
        - eapply no_failure_expr_bind_prefix; exact NOFAIL.
        - eapply bid_bound_incBlockNamed with (name := "Let"); solve_prefix.
        - apply state_invariant_new_block; assumption.
      }
      clear IHe1.
      introR.
      intros RET _; eapply no_failure_expr_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in PRE0; destruct PRE0 as [INV2 [COR [[from2 BRANCH2] POST]]].
      cbn in INV2.
      subst.

      (* middle block *)
      unfold fmap, Fmap_block; cbn.
      vjmp.
      apply find_block_eq; auto.
      repeat vred.
      rewrite (cons_app _ (convert_typ [] e2_blks)).
      rewrite denote_ocfg_app_no_edges.
      3: {
        unfold no_reentrance.
        simpl.
        eapply Forall_disjoint.
        apply outputs_bound_between in COMP_e2.
        exact COMP_e2.
        apply Forall_cons; auto.
        eapply bid_bound_incBlockNamed with (name := "Let"); solve_prefix.
        cbn.
        admit. (* TODO: Doesn't look true - this is a bit different to how it was above *)
      }
      2: {
        cbn.
        apply entry_bound_between in COMP_e2.
        destruct COMP_e2 as [OUT_PRED | OUT_PRED].
        - admit. (* TODO: because e2_entry bound after mid_state, can't be = pre_state *)
        - admit. (* TODO: becayse e2_entry = next_bid, can't be pre_state *)
      }

      (* last blocks *)
      eapply eqit_mon; auto.
      2: {
        eapply IHe2.
        exact COMP_e2.
        auto.
        eapply bid_bound_mono.
        eassumption.
        cbn.
        admit. (* TODO: prove bid_bound pre_state => bid_bound mid_state *)
        admit. (* TODO: prove state_invariant s => state_invariant with new variable *)
      }
      clear IHe2.
      intros [[memC1 ?]|] (memV1 & l1 & g1 & res1) PR; [| inv PR].
      destruct PR as [S1 [C1 [B1 L1]]].
      cbn in S1.
      split; cbn.
      admit. (* TODO: state_invariant *)
      split; cbn.
      admit. (* TODO: correct result *)
      split; auto.
      admit. (* TODO: local scope modif *)
    - (* Prim op os *)
      cbn* in *; simp.
      admit.
    - (* If e1 e2 e3 *)
      admit.
    - (* Cast t e*)
      admit.
    - (* Struct ts es *)
      cbn* in *; simp.
      admit.
    - (* Member e f *) 
      pose proof COMP as COMP'.
      cbn* in COMP.
      Opaque field_type.
      repeat (inv_sum || inv_option || break_and || break_match_hyp_defer_ft).
      rename Heqs0 into COMP_e.
      cbn in *.
      clean_goal.
      unfold ITree.map in *.
      rewrite convert_typ_ocfg_app.
      rewrite denote_ocfg_app; eauto.
      2: {
        unfold no_reentrance.
        pose proof COMP_e as COMP_e'.
        apply (inputs_not_earlier_bound _ _ _ _ _ _ _ _ _ NEXT) in COMP_e'.
        apply inputs_bound_between in COMP_e.
        pose proof (Forall_and COMP_e COMP_e') as INPUTS.
        cbn in INPUTS.
        eapply Forall_disjoint.
        rewrite convert_typ_outputs in *.
        unfold code_block.
        rewrite outputs_cons.
        unfold outputs.
        simpl.
        apply Forall_cons; [ | apply Forall_nil].
        exact NEXT.
        exact INPUTS.
        intros x OUT_PRED [IN_BOUND IN_NEXT].
        unfold bid_bound in OUT_PRED.
        eapply state_bound_before_not_bound_between in OUT_PRED.
        unfold bid_bound_between in IN_BOUND.
        apply OUT_PRED.
        exact IN_BOUND.
        apply incBlockNamed_count_gen_injective.
        apply incBlockNamed_count_gen_mono.
        solve_block_count.
        solve_block_count.
      }
      cvred.
      rewrite bind_bind.
      cbn in *.
      eapply eutt_clo_bind_returns.
      {
        eapply IHe; eauto.
        - eapply no_failure_expr_bind_prefix.
          eapply no_failure_expr_bind_prefix in NOFAIL.
          exact NOFAIL.
        - eapply bid_bound_incBlockNamed with (name := "Field"); solve_prefix.
        - apply state_invariant_new_block; assumption.
      }
      clear IHe.
      introR.
      intros RET _; eapply no_failure_expr_bind_continuation in NOFAIL.
      2: {
        rewrite interp_expr_bind.
        eapply Returns_bind.
        eassumption.
        cbn.
        rewrite interp_expr_bind.
        eapply Returns_bind.
        simp; cbn in Heqf0.
          - (* TODO: boxed case*)
            admit.
          - rewrite Heqf1 in Heqf0; discriminate.
          - rewrite Heqf1 in Heqf0; discriminate.
          - (* TODO: unboxed case*)
            admit.
          - (* TODO: should fall out*)
            admit.
      }
      cbn in PRE0; destruct PRE0 as [INV2 [COR [[from2 BRANCH2] POST]]].
      cbn in INV2.
      subst.

      (* might need to do same Heqf1 things as above *)

      (* then split middle block like in Let *)
      

      
      admit.
    - (* Take e1 f e2 *)
      admit.
    - (* Put e1 f e2 *)
      admit.
    - (* Con ts n e *)
      admit.
    - (* Promote t e *)
      eauto.
    - (* Esac ts e *)
      admit.
    - (* Case ts e1 n e2 e3 *)
      admit.
    - (* Fun e *)
      cbn* in *; simp.
    - (* App e1 e2 *)
      pose proof COMP as COMP'.
      cbn* in COMP'; simp.
      rename e into body_expr, e2 into arg_expr.
      rename s1 into pre_state, i into mid_state, i0 into post_state.
      rename l0 into arg_code, l1 into body_code.
      rename b0 into body_entry.
      rename Heqs into COMP_arg, Heqs1 into COMP_body.
      rename IHe1 into IH_fun, IHe2 into IH_arg.

      rewrite convert_typ_ocfg_app.
      rewrite denote_ocfg_app.
      2 : {
        (* try do similar to Let *)
        admit.
      }
      cvred.
      cbn in *.
      pose proof PRE as SINV.
      simp.
      rewrite interp_expr_bind.
      eapply eutt_clo_bind_returns.
      {
        (* line 204 in GenIR for a better way *)
        eapply IH_arg; eauto.
        eapply no_failure_expr_bind_prefix; exact NOFAIL.
        apply bid_bound_incBlockNamed with (name := "App") (s1 := pre_state).
        solve_prefix.
        reflexivity.
        apply state_invariant_new_block.
        assumption.
      }
      clear IH_arg.
      introR.
      intros RET _; eapply no_failure_expr_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in PRE0; destruct PRE0 as [INV2 [COR [[from2 BRANCH2] POST]]].
      cbn in INV2.
      subst.
      eapply eqit_mon; auto.
      2: {
        (* need some IH about body of function *)
        admit.
      }
      clear IH_fun.
      intros [[memC1 ?]|] (memV1 & l1 & g1 & res1) PR.
      exact PR.
      inv PR.
  Admitted.

End Expressions.

Section TopLevel.

  Definition vellvm_prog : Type := toplevel_entities typ (LLVMAst.block typ * list (LLVMAst.block typ)).
  Definition semantics_cogent (p : cogent_prog) : failT (itree E_mcfg) (memoryC * uval) := 
    interp_cogent (denote_program p) "main" UUnit empty_memory.

  (* placeholder *)
  Definition TT {A B} (x: A) (y: B):= True.

  Lemma compiler_correct :
    forall (c : cogent_prog) (ll : vellvm_prog),
      compile_cogent c ≡ inr ll ->
      eutt TT (semantics_cogent c) (semantics_llvm ll).
  Proof.
  Abort.

End TopLevel.

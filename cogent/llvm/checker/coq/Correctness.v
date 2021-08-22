From Coq Require Import List String ZArith.

From ITree Require Import ITree ITreeFacts.
From Vellvm Require Import LLVMAst LLVMEvents TopLevel Handlers InterpreterMCFG TopLevelRefinements
  DynamicTypes CFG TypToDtyp InterpretationStack SymbolicInterpreter DenotationTheory ScopeTheory
  DynamicValues ExpLemmas Coqlib NoFailure AListFacts.

From Checker Require Import Denotation DenotationTheory Cogent Compiler Utils.Tactics Invariants
  HelixLib.Correctness_Prelude HelixLib.BidBound HelixLib.IdLemmas HelixLib.VariableBinding Types
HelixLib.StateCounters.

Import ListNotations.
Import AlistNotations.

Import ExpTactics.
Import ProofMode.
Import LidBound.

(* The following sections should be put in the relevant files in HelixLib/ *)
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

Section InvariantExtra.
Definition gamma_bound (s : IRState) : Prop :=
  forall n id τ,
    nth_error (Γ s) n ≡ Some (τ, EXP_Ident (ID_Local id)) ->
    lid_bound s id.

Lemma in_gamma_not_in_neq :
  forall σ s id r,
    in_Gamma σ s id ->
    ~ in_Gamma σ s r ->
    id ≢ r.
Proof.
  intros σ s id r GAM NGAM.
  destruct (Eqv.eqv_dec_p r id) as [EQ | NEQ].
  - do 2 red in EQ.
    subst.
    contradiction.
  - unfold Eqv.eqv, eqv_raw_id in NEQ.
    eauto.
Qed.
(* TODO: move this? *)
Lemma incLocal_id_neq :
  forall s1 s2 s3 s4 id1 id2,
    incLocal s1 ≡ inr (s2, id1) ->
    incLocal s3 ≡ inr (s4, id2) ->
    local_count s1 ≢ local_count s3 ->
    id1 ≢ id2.
Proof.
Admitted.

Lemma incBlockNamed_id_neq :
  forall s1 s2 s3 s4 id1 id2 n1 n2,
    incBlockNamed n1 s1 ≡ inr (s2, id1) ->
    incBlockNamed n2 s3 ≡ inr (s4, id2) ->
    is_correct_prefix n1 ->
    is_correct_prefix n2 ->
    block_count s1 ≢ block_count s3 ->
    id1 ≢ id2.
Proof.
  intros s1 s2 s3 s4 id1 id2 n1 n2 GEN1 GEN2 PRE1 PRE2 COUNT.
  eapply incBlockNamed_count_gen_injective; eauto.
Qed.


(*
Ltac solve_id_neq :=
  first [ solve [eapply incLocal_id_neq; eauto; solve_local_count]
        | solve [eapply incBlockNamed_id_neq; eauto; solve_block_count]
        | solve [eapply in_gamma_not_in_neq; [solve_in_gamma | solve_not_in_gamma]]
        | solve [eapply lid_bound_earlier; [ solve_lid_bound | solve_lid_bound_between  | solve_local_count ]]
        | solve [eapply state_bound_between_separate; [eapply incLocalNamed_count_gen_injective
                                                      | solve_lid_bound_between
                                                      | solve_lid_bound_between
                                                      | cbn; solve_local_count]]
        | solve [let CONTRA := fresh "CONTRA" in intros CONTRA; symmetry in CONTRA; revert CONTRA; solve_id_neq]
        ].
*)
Lemma state_invariant_escape_scope:
  ∀ (σ : list _) v x (s1 s2 : IRState) stH 
    (stV : config_cfg),
    Γ s1 ≡ x :: Γ s2 → gamma_bound s2 → state_invariant (v :: σ) s1 stH stV → state_invariant σ s2 stH stV.
  Admitted.

Lemma lid_bound_between_shrink_up:
  ∀ (s1 s2 s3 : IRState) (id : local_id), s2 <<= s3 → lid_bound_between s1 s2 id → lid_bound_between s1 s3 id.
  Admitted.
Lemma lid_bound_between_shrink_down:
  ∀ (s1 s2 s3 : IRState) (id : local_id), s1 <<= s2 → lid_bound_between s2 s3 id → lid_bound_between s1 s3 id.
  Admitted.
Lemma lid_bound_between_shrink:
  ∀ (s1 s2 s3 s4 : IRState) (id : local_id),
    lid_bound_between s2 s3 id → s1 <<= s2 → s3 <<= s4 → lid_bound_between s1 s4 id.
  Admitted.

(* This lemma is not in helix *)
Lemma local_scope_preserved_mono pre_state mid_state post_state l1 l2 :
  pre_state <<= mid_state -> 
  mid_state <<= post_state -> 
  local_scope_preserved pre_state post_state l1 l2 
  -> local_scope_preserved mid_state post_state l1 l2.
  intros le_pre le_mid h id hid.
  apply h.
  eapply lid_bound_between_shrink_down; eassumption.
Qed.

  (* Given a range defined by [s1;s2], ensures that the whole range is irrelevant to the memory invariant *)
  Definition Gamma_safe σ (s1 s2 : IRState) : Prop :=
    forall id, lid_bound_between s1 s2 id ->
               ~ in_Gamma σ s1 id.

  Lemma Gamma_preserved_if_safe:
  ∀ (σ : ctx) (s1 s2 : IRState) (l1 l2 : local_env),
    Gamma_safe σ s1 s2 → local_scope_modif s1 s2 l1 l2 → Gamma_preserved σ s1 l1 l2.
Admitted.

  (* is it really true? *)
  Lemma Gamma_safe_Context_extend:
  ∀ (σ : ctx) (s1 s2 : IRState),
    Gamma_safe σ s1 s2
    → ∀ (s1' s2' : IRState) (x : raw_id) (v : typ) (xτ : _ ),
        s1 <<= s1'
        → local_count s2 ≥ local_count s2'
          → Γ s1' ≡ (v, EXP_Ident (ID_Local x)) :: Γ s1
            → Γ s2' ≡ (v, EXP_Ident (ID_Local x)) :: Γ s2
              → (∀ id : local_id, lid_bound_between s1' s2' id → x ≢ id) → Gamma_safe (xτ :: σ) s1' s2'.
  Admitted.

  Lemma Gamma_safe_Context_extend':
  ∀ (σ : ctx) (s1 s2 : IRState),
    Gamma_safe σ s1 s2
    → ∀ (s1' s2' : IRState) y  (xτ : _ ),
        s1 <<= s1'
        → local_count s2 ≥ local_count s2'
          → Γ s1' ≡ y :: Γ s1
            → Γ s2' ≡ y :: Γ s2
            -> (forall (x : raw_id)(v : typ), y ≡ (v, EXP_Ident (ID_Local x)) ->
                                        (∀ id : local_id, lid_bound_between s1' s2' id → x ≢ id)
              )
              → Gamma_safe (xτ :: σ) s1' s2'.
    intros ??? safe .
    intros .
    intros ?? h.  
    inversion h; subst; cbn in *.

    rewrite H1 in H6.
    destruct n; revgoals; cbn in *.
    - unfold Gamma_safe in safe.
      unfold not in safe.
      eapply safe.
      eapply lid_bound_between_shrink; eassumption.
      econstructor; eassumption.
    - destruct y as [ y w ].
      injection H6.
      intros hw hy.

      destruct w; try discriminate.
      subst .
      injection hw.
      intro; subst id0.
      eapply Gamma_safe_Context_extend; try eassumption.
      eapply H3.
      reflexivity.
    Qed.

  (* Not in Helix because not needed there *)
  Lemma Gamma_preserved_Context_extend:
  ∀ (σ : ctx) (s1 s2 : IRState)xτ l1 l2 y,
    Gamma_preserved σ s1 l1 l2 ->
          Γ s2 ≡ y :: Γ s1
            -> (forall (x : raw_id)(v : typ), y ≡ (v, EXP_Ident (ID_Local x)) -> l1 @ x ≡ l2 @ x)
              
              -> Gamma_preserved (xτ :: σ) s2 l1 l2.
    Proof.
      intros * Gp eqG eqid.
      unfold Gamma_preserved.
      intro id.
      intro h.
      inversion h; subst; cbn in *.
      rewrite eqG in H0.
      destruct n; revgoals; cbn in *.
      - eapply Gp.
        econstructor; eassumption.
      - destruct y as [ y w ].
        injection H0.
        intros hw hy.
        destruct w; try discriminate.
        subst .
        injection hw.
        intro; subst id0.
        eapply eqid.
        reflexivity.
    Qed.

Lemma Gamma_safe_shrink:
  ∀ (σ : ctx) (s1 s2 s3 s4 : IRState),
    Gamma_safe σ s1 s4 → Γ s1 ≡ Γ s2 → s1 <<= s2 → s3 <<= s4 → Gamma_safe σ s2 s3.
  Admitted.

Lemma local_scope_modif_trans:
  ∀ (s1 s2 s3 : IRState) (l1 l2 l3 : local_env),
    s1 <<= s2
    → s2 <<= s3 → local_scope_modif s1 s2 l1 l2 → local_scope_modif s2 s3 l2 l3 → local_scope_modif s1 s3 l1 l3.
  Admitted.

Lemma st_gamma_bound:
  ∀ (σ : ctx) (s : IRState) (memH : _) (configV : config_cfg),
    state_invariant σ s memH configV → gamma_bound s.
Admitted.
Lemma gamma_bound_mono: ∀ s1 s2 : IRState, gamma_bound s1 → s1 <<= s2 → Γ s1 ≡ Γ s2 → gamma_bound s2.
Admitted.
End InvariantExtra.


Section ContextExtra.

Lemma compile_expr_Γ :
 ∀ (op : Cogent.expr) (s1 s2 : IRState) (nextblock b : block_id) (bk_op : list (LLVMAst.block typ)) r,
  compile_expr op nextblock s1 ≡ inr (s2, (r, b, bk_op)) → Γ s1 ≡ Γ s2.
Admitted.

End ContextExtra.

Section Correctness_NExpr_Extra.
(* originally: genNExpr_ident_bound *)
Lemma compile_expr_ident_bound :
  ∀ (nexp : Cogent.expr) (s1 s2 : IRState) b (id : raw_id) t  bentry c,
    compile_expr nexp b s1 ≡ inr (s2, ((t, EXP_Ident (ID_Local id)), bentry, c)) → gamma_bound s1 → lid_bound s2 id.
Admitted.
End Correctness_NExpr_Extra.




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
    (* inspired by genNExpr_post *)
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

  (* should be an easier way to do this case analysis *)
  Lemma unbox_field_type :
    forall t f x,
      field_type t f ≡ UnboxField x ->
      exists flds,
        t ≡ TYPE_Struct flds /\ nth_error flds f ≡ Some x.
  Proof.
    intros.
    unfold field_type in H.
    destruct t; try discriminate.
    destruct t; try discriminate.
    destruct nth_error; try discriminate.
    eexists.
    split.
    reflexivity.
    destruct nth_error eqn:?; inversion H.
    reflexivity.
  Qed.

  Lemma compile_expr_correct :
    forall (e : expr) (γ : ctx) (s1 s2 : IRState)
           (v : im) (next_bid entry_bid prev_bid : block_id) (blks : ocfg typ)
           (memC : memoryC) (g : global_env) (l : local_env) (memV : memoryV),
      compile_expr e next_bid s1 ≡ inr (s2, (v, entry_bid, blks)) ->
      no_failure (interp_expr (E := E_cfg) (denote_expr γ e) memC) ->
      bid_bound s1 next_bid ->
      state_invariant γ s1 memC (memV, (l, g)) ->
      Gamma_safe γ s1 s2 ->
      eutt
        (succ_cfg (compile_expr_post v γ s1 s2 next_bid l))
        (interp_expr (denote_expr γ e) memC)
        (interp_cfg (denote_ocfg (convert_typ [] blks) (prev_bid, entry_bid)) g l memV).
  Proof.
    induction e using expr_ind'; intros * COMP NOFAIL NEXT PRE GAM.
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
    - (* Var i *)
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
      destruct MEM as [COR MEM].
      unfold correct_result in COR.
      specialize (COR l' H H0).
      assumption.
      apply local_scope_modif_refl.
      apply failure_expr_throw in NOFAIL.
      contradiction.
      apply find_block_nil.
    - (* Let e1 e2 *)
      cbn* in COMP.
      simp.
      rename s1 into pre_state, i into mid_state, i1 into post_state.
      rename l0 into e1_blks, l1 into e2_blks.
      rename b0 into e2_entry, entry_bid into e1_entry.
      rename t into e1_im_t, e into e1_im, t0 into e2_im_t, e0 into e2_im.
      rename t1 into new_var, l2 into cur_vars.
      rename Heqs into COMP_e1, Heqs1 into COMP_e2, Heql3 into BIND.
      assert (Γeq := COMP_e2).
      apply compile_expr_Γ in Γeq.
      cbn in Γeq.
      rewrite BIND in Γeq.
      injection Γeq.
      intros ??; subst cur_vars new_var.
      clear Γeq.

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
        reflexivity.
        cbn.
        auto.
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
        - eapply Gamma_safe_shrink; eauto.
          cbn.
          solve_local_count.
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
      set (let_bid := ("Let" @@ string_of_nat (block_count pre_state))) in *.
      assert (Let_bid_bond :   bid_bound
                                 {|
                                   block_count := S (block_count pre_state);
                                   local_count := local_count pre_state;
                                   void_count := void_count pre_state;
                                   Γ := Γ pre_state |} let_bid).
      {
        apply bid_bound_incBlockNamed with (name := "Let") (s1 := pre_state).
        solve_prefix.
        reflexivity.
      }
      assert(Let_bid_bond_mid :
               bid_bound
                 {|
                   block_count := block_count mid_state;
                   local_count := local_count mid_state;
                   void_count := void_count mid_state;
                   Γ := (e1_im_t, e1_im) :: Γ mid_state |} let_bid
            ).
      {
        
        eapply bid_bound_mono.
        + exact Let_bid_bond. 
        + solve_block_count. 
      }           
      assert(neq_let_next_bid : Name let_bid ≢ next_bid).
      {
        
        intro.
        subst next_bid.
        apply bid_bound_name in NEXT.
        revert NEXT.
        lia.
        solve_prefix.
      }

      (* like helix/Correctness_GenIR *)
      rewrite denote_ocfg_app; eauto.
      2: {
        unfold no_reentrance.
        assert (GEN_OP1 := COMP_e1).
        assert (GEN_OP2 := COMP_e2).
        pose proof GEN_OP1 as GEN_OP1'.
        pose proof GEN_OP2 as GEN_OP2'.
        
        apply (inputs_not_earlier_bound _ _ _ _ _ _ _ _ _ NEXT) in GEN_OP1'.
        apply (inputs_not_earlier_bound _ _ _ _ _ _ _ _ _ NEXT) in GEN_OP2'.
        apply inputs_bound_between in GEN_OP1.
        apply outputs_bound_between in GEN_OP2.

        pose proof (Forall_and GEN_OP1 GEN_OP1') as INPUTS.
        cbn in INPUTS.
        cbn.
        

        apply list_disjoint_singleton_right.
        intro hin.
        rewrite Forall_forall in GEN_OP2.
        specialize (GEN_OP2 _ hin).
        revert GEN_OP2.
        intro OUT_PRED .
        cbn in OUT_PRED.
        destruct OUT_PRED as [OUT_PRED | OUT_PRED]; revgoals.
        revert OUT_PRED; exact neq_let_next_bid.
        revert OUT_PRED.
        eapply not_bid_bound_between.
        assumption.
        solve_block_count.
        solve_block_count.
      }
      

      
      rewrite interp_cfg3_bind.
      rewrite denote_ocfg_unfold_not_in; revgoals.
        {
          cbn.
          rewrite find_block_ineq.
          reflexivity.
          cbn.
          intro heq.
          subst e2_entry.
          apply entry_bound_between in COMP_e2.
          case COMP_e2.
          - apply not_bid_bound_between.
            assumption.
          - assumption.
        }
        vred.

        assert (Gamma_safe_mid_post :
                  Gamma_safe (vC :: γ)
                             {|
                               block_count := block_count mid_state;
                               local_count := local_count mid_state;
                               void_count := void_count mid_state;
                               Γ := (e1_im_t, e1_im) :: Γ mid_state |} post_state
               ).
        {
            eapply Gamma_safe_Context_extend'; eauto.
            cbn.
            solve_local_count.
            cbn.
            f_equal.
            assert (h1 := COMP_e1).
            apply compile_expr_Γ in h1.
            revert h1.
            cbn.
            auto.
            intros x v eq.
            injection eq.
            intros ??; subst v.
            subst e1_im.
            rename x into e1_im.
            cbn.
            intros id h.
            (* following Helix/Correct_Alloc *)
            revert h.
            eapply lid_bound_fresh; eauto.
            eapply compile_expr_ident_bound in COMP_e1.
            exact COMP_e1.
            eapply gamma_bound_mono.
            eapply st_gamma_bound.
            exact PRE.
            cbn.
            reflexivity.
            reflexivity.
        }
        assert (INV_mid_ext :
                  state_invariant
                    (vC :: γ)
                    {|
                      block_count := block_count mid_state;
                      local_count := local_count mid_state;
                      void_count := void_count mid_state;
                      Γ := (e1_im_t, e1_im) :: Γ mid_state |}
                    memH (memV0, (l0, g0))
               ).
        {
          (* probably apply some Lemma similar to Helix' state_invariant_enter_scope_* *)
            admit. (* TODO: prove state_invariant s => state_invariant with new variable *)
        }

        eassert (IHe2'' :
                   eutt
                     _
                     (interp_expr (denote_expr (_ :: γ) e2) _)
                     (interp_cfg3(denote_ocfg (convert_typ [] _) (_, _))
                                 g0 l0 memV0
                     )
).
        {
          apply (IHe2 (_ :: γ)).
          * exact COMP_e2.
          * exact NOFAIL.
          * cbn.
            eapply bid_bound_mono.
            -- exact NEXT.
            -- cbn.
               solve_block_count.
          * cbn.
            exact INV_mid_ext.
          * exact Gamma_safe_mid_post.
        }

     assert(Gamma_bound_mid_post :
                   gamma_bound
    {|
    block_count := block_count post_state;
    local_count := local_count post_state;
    void_count := void_count post_state;
    Γ := Γ mid_state |}
           ).
     {
       eapply gamma_bound_mono.
       eapply st_gamma_bound.
       exact INV2.
       cbn.
       solve_local_count.
       reflexivity.
     }

      (* last blocks *)
      eapply eqit_mon; auto.
      2: exact IHe2''. 
      clear IHe2 IHe2''.
      intros [[memC1 ?]|] (memV1 & l1 & g1 & res1) PR; [| inv PR].
      destruct PR as [S1 [C1 [B1 L1]]].
      cbn in S1.
      split; [| split]; [| |  split]; cbn ;eauto.
      + cbn.
        revert S1.
        eapply state_invariant_escape_scope.
        exact BIND.
        cbn.
        exact Gamma_bound_mid_post.
      + intros.
        cbn in C1.
        rewrite C1.
        reflexivity.
        all:clear C1.
        * eapply local_scope_preserved_mono; revgoals; cbn.
           exact H.
          -- apply compile_expr_local_count in COMP_e2.
             exact COMP_e2.
          -- apply compile_expr_local_count in COMP_e1.
             exact COMP_e1.
        * cbn.
(* I currently don't know how to prove this goal.
In Helix, they use some tactic solve_gamma_preserved:

Hint Immediate Gamma_preserved_refl : SolveGammaPreserved.
Hint Extern 1 (~ (in_Gamma _ _ _)) => solve_not_in_gamma : SolveGammaPreserved.
Hint Resolve Gamma_preserved_add_not_in_Gamma : SolveGammaPreserved.
Hint Resolve Gamma_preserved_if_safe : SolveGammaPreserved.
Hint Extern 1 (local_scope_modif _ _ _ _) => solve_local_scope_modif : SolveGammaPreserved.
Hint Extern 1 (Gamma_safe _ _ _) => solve_gamma_safe : SolveGammaPreserved.

Ltac solve_gamma_preserved :=
  solve [eauto with SolveGammaPreserved].

 *)
          (*

If the identifier e1_im was explicitly created for the variable in the
Let case, would it be work better?
*)
          eapply Gamma_preserved_Context_extend.
          eassumption.
          cbn.
          apply compile_expr_Γ in COMP_e1; cbn in COMP_e1; rewrite COMP_e1.
          reflexivity.
          intros x v eq.
          injection eq.
          intros ??; subst v.
          subst e1_im.
          rename x into e1_im.
          Search e1_im.
(* In Helix, γ only contains identifiers, rather than expressions. 
   (this is an optimisation in case the variable's value is a constant) *)

          (* here I work on hypothesis S1, but I am not sure it is useful *)
          apply mem_is_inv in S1.
          red in S1.
          specialize (S1 (O : nat)).
          rewrite BIND in S1.
          specialize (S1 _ _ eq_refl eq_refl).
          cbn in S1.

          (* I am tempted to apply hypothesis H *)
          symmetry.
          apply H.
          assert (he1 := COMP_e1).
          eapply compile_expr_ident_bound in he1.
          revert he1.
          Search e1_im.
          (*
I think lid_bound mid_state e1_im (the last reverted assumption) implies either
1) either lid_bound pre_state,
2) either lid_bound_between pre_state mid_state

2) easily implies the goal, but 1) is contradicts the goal...
So, why 1) is false? Maybe it was a wrong to apply H.
           *)
          revert COMP_e1.
          admit.
          eapply st_gamma_bound.
          eapply state_invariant_new_block.
          eassumption.
      + revert POST L1.
        apply compile_expr_local_count in COMP_e1.
        apply compile_expr_local_count in COMP_e2.
        eapply (@local_scope_modif_trans pre_state mid_state post_state); eassumption.
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
        - admit. (* TODO: gamma safe *)
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
      simp; cbn in Heqf0.
      2 : rewrite Heqf1 in Heqf0; discriminate.
      2 : rewrite Heqf1 in Heqf0; discriminate.
      all: unfold fmap, Fmap_block; cbn; cvred.
      +
        admit.
      +
        idtac.
        apply unbox_field_type in Heqf0.
        destruct Heqf0 as [t2_flds [TYPING ACCESS]].
        rewrite TYPING.
        cbn.
        vjmp.
        repeat vred.
        vstep.
        {
          admit. (* need lemma for OP_ExtractValue *)
        }
        vred.
        vjmp_out.
        admit.
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
        admit. (* TODO: Gamma_safe *)
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
  Definition R {A B} (x: A) (y: B):= True.

  (* Correctness_NExpr describes some tactics *)
  Theorem compiler_correct :
    forall (c : cogent_prog) (ll : vellvm_prog),
      compile_cogent c ≡ inr ll ->
      eutt R (semantics_cogent c) (semantics_llvm ll).
  Proof.
  Abort.

End TopLevel.

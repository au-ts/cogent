From ITree Require Import ITree Events.State Events.Exception Events.FailFacts Events.StateFacts
  Interp.TranslateFacts Eq.Eq.

From Vellvm Require Import Utils.NoFailure Utils.PropT.

From Checker Require Import Denotation.

Local Open Scope itree_scope.

Section InterpTheory.

  Lemma interp_mem_Ret :
    forall T mem x,
      @interp_mem T (Ret x) mem ≅ Ret (mem, x).
  Proof.
    intros T mem x.
    unfold interp_mem.
    apply interp_state_ret.
  Qed.

  Lemma interp_mem_bind :
    forall T U mem (t : itree CogentL0 T) (k : T -> itree CogentL0 U),
      interp_mem (ITree.bind t k) mem ≈ 
        ITree.bind (interp_mem t mem) (fun '(mem', v) => interp_mem (k v) mem').
  Proof.
    intros; unfold interp_mem.
    rewrite interp_state_bind.
    apply eutt_eq_bind; intros []; reflexivity.
  Qed.

  Lemma interp_Mem_vis_eqit :
    forall T R mem (e : CogentL0 T) (k : T -> itree CogentL0 R),
      interp_mem (vis e k) mem ≅ ITree.bind ((case_ handle_mem pure_state) T e mem) (fun sx => Tau (interp_mem (k (snd sx)) (fst sx))).
  Proof.
    intros T R mem e k.
    unfold interp_mem.
    apply interp_state_vis.
  Qed.

  Lemma interp_expr_Ret :
    forall E mem x,
      @interp_expr E (Ret x) mem ≅ Ret (Some (mem, x)).
  Proof.
    intros.
    unfold interp_expr.
    rewrite interp_mem_Ret, interp_fail_Ret, translate_ret.
    reflexivity.
  Qed.

  Lemma interp_expr_bind :
    forall E mem (t : itree CogentL0 uval) (k : uval -> itree CogentL0 uval),
      @interp_expr E (ITree.bind t k) mem ≈ 
        ITree.bind (interp_expr t mem) (fun mx => 
          match mx with 
          (* | (a, b) => Ret None *)
          | None => Ret None
          | Some x => 
              let '(mem',v) := x in 
                interp_expr (k v) mem'
          end).
  Proof.
    intros; unfold interp_expr.
    rewrite interp_mem_bind, interp_fail_bind, translate_bind.
    eapply eutt_eq_bind; intros [[]|]; cbn.
    reflexivity.
    rewrite translate_ret; reflexivity.
  Qed.

End InterpTheory.

Section NoFailure.

  Lemma no_failure_expr_Ret : forall E x m,
    no_failure (interp_expr (E := E) (Ret x) m).
  Proof.
    intros.
    rewrite interp_expr_Ret. apply eutt_Ret; intros abs; inv abs.
  Qed.

  Lemma failure_expr_throw : forall E s m,
    ~ no_failure (interp_expr (E := E) (throw s) m).
  Proof.
    intros * abs.
    unfold Exception.throw in *.
    unfold interp_expr in *.
    setoid_rewrite interp_Mem_vis_eqit in abs.
    unfold pure_state in *; cbn in *.
    rewrite interp_fail_bind in abs.
    rewrite interp_fail_vis in abs.
    cbn in *.
    rewrite Eq.bind_bind, !bind_ret_l in abs.
    rewrite translate_ret in abs.
    eapply eutt_Ret in abs.
    apply abs; auto.
  Qed.

  Lemma failure_expr_throw' : forall E s (k : uval -> _) m,
    ~ no_failure (interp_expr (E := E) (ITree.bind (throw s) k) m).
  Proof.
    intros * abs.
    rewrite interp_expr_bind in abs.
    eapply no_failure_bind_prefix, failure_expr_throw in abs; auto.
  Qed.

  Lemma no_failure_expr_bind_prefix : forall {E} (t : itree _ uval) (k : uval -> itree _ uval) m,
    no_failure (interp_expr (E := E) (ITree.bind t k) m) ->
    no_failure (interp_expr (E := E) t m).
  Proof.
    intros * NOFAIL.
    rewrite interp_expr_bind in NOFAIL.
    eapply no_failure_bind_prefix; eapply NOFAIL.
  Qed.
  
  Lemma no_failure_expr_bind_continuation :
    forall {E} (t : itree _ uval) (k : uval -> itree _ uval) m,
      no_failure (interp_expr (E := E) (ITree.bind t k) m) ->
      forall u m', Returns (E := E) (Some (m',u)) (interp_expr t m) -> 
        no_failure (interp_expr (E := E) (k u) m').
  Proof.
    intros * NOFAIL * ISRET.
    rewrite interp_expr_bind in NOFAIL.
    eapply no_failure_bind_cont in NOFAIL; eauto.
    apply NOFAIL.
  Qed.

End NoFailure.
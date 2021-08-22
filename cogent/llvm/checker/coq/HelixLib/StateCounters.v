(* Taken from Helix's LLVMGen.StateCounters.v *)

(** * Compilation units and IRState

  This file contains a bunch of lemmas describing how various compilation subroutines
  impact the freshness part of the [IRState].
  The file [Context.v] is the pendant for the context part of the [IRState].
*)

Require Import HelixLib.Correctness_Prelude.
Require Import Compiler.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Section BlockCount.

  Lemma incVoid_block_count :
    forall s1 s2 bid,
      incVoid s1 ≡ inr (s2, bid) ->
      block_count s1 ≡ block_count s2.
  Admitted.

  Lemma incLocal_block_count :
    forall s1 s2 bid,
      incLocal s1 ≡ inr (s2, bid) ->
      block_count s1 ≡ block_count s2.
  Admitted.

  Lemma incLocalNamed_block_count :
    forall s s1 s2 bid,
      incLocalNamed s s1 ≡ inr (s2, bid) ->
      block_count s1 ≡ block_count s2.
  Admitted.

  Lemma incBlockNamed_block_count:
    forall s s' msg id,
      incBlockNamed msg s ≡ inr (s', id) ->
      block_count s' ≡ S (block_count s).
  Admitted.

  Lemma dropVars_block_count :
    ∀ (s1 s2 : IRState) bid x,
      dropVars x s1 ≡ inr (s2, bid) →
      block_count s1 ≡ block_count s2.
  Admitted.

  Ltac __local_ltac' := (repeat
      (match goal with
      | H: inl _ ≡ inr _ |- _ =>
        inversion H
      | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
        destruct (nth_error (Γ s1) n) eqn:?; inversion H; subst
      | H : incLocal ?s1 ≡ inr (?s2, _) |- _ =>
        apply incLocal_block_count in H
      | H : incVoid ?s1 ≡ inr (?s2, _) |- _ =>
        apply incVoid_block_count in H
      | H : incBlockNamed _ _ ≡ inr _ |- _ =>
        apply incBlockNamed_block_count in H
      | H : incBlock _ ≡ inr _ |- _ =>
        apply incBlockNamed_block_count in H
      end; cbn in *)).

  Opaque incLocal.
  Opaque incVoid.
  Opaque incBlockNamed.
  Lemma compile_expr_block_count :
    forall op s1 s2 nextblock b bk_op,
      compile_expr op nextblock s1 ≡ inr (s2, (b, bk_op)) ->
      block_count s2 ≥ block_count s1.
  Proof.
  Admitted.

End BlockCount.
      
Section LocalCount.

  Lemma incBlockNamed_local_count:
    forall s s' msg id,
      incBlockNamed msg s ≡ inr (s', id) ->
      local_count s' ≡ local_count s.
  Admitted.

  Lemma incVoid_local_count:
    forall s s' id,
      incVoid s ≡ inr (s', id) ->
      local_count s' ≡ local_count s.
  Admitted.

  Lemma incLocal_local_count: forall s s' x,
      incLocal s ≡ inr (s',x) ->
      local_count s' ≡ S (local_count s).
  Admitted.

  Lemma dropVars_local_count:
    forall s s' k,
      dropVars k s ≡ inr (s', tt) ->
      local_count s' ≡ local_count s.
  Admitted.

  Lemma incLocalNamed_local_count: forall s s' msg x,
      incLocalNamed msg s ≡ inr (s',x) ->
      local_count s' ≡ S (local_count s).
  Admitted.

  Opaque incLocal.
  Opaque incVoid.
  Opaque incBlockNamed.
  Arguments append: simpl never.

  Ltac __local_ltac :=
    repeat
      (match goal with
      | H: inl _ ≡ inr _ |- _ =>
        inversion H
      | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
        destruct (nth_error (Γ s1) n) eqn:?; inversion H; subst
      | H : incLocal ?s1 ≡ inr (?s2, _) |- _ =>
        apply incLocal_local_count in H
      | H : incVoid ?s1 ≡ inr (?s2, _) |- _ =>
        apply incVoid_local_count in H
        | H : incBlockNamed _ _ ≡ inr _ |- _ =>
        apply incBlockNamed_local_count in H
      | H : incBlock _ ≡ inr _ |- _ =>
        apply incBlockNamed_local_count in H
      end; cbn in *).

  Lemma compile_expr_local_count:
  ∀ (op : Cogent.expr) (s1 s2 : IRState) (nextblock b : block_id) (bk_op : list (LLVMAst.block typ)) o,
    compile_expr op nextblock s1 ≡ inr (s2, (o, b, bk_op)) → local_count s2 ≥ local_count s1.
  Admitted.

End LocalCount.

  (* (* We define the obvious total order on IRStates *) *)
  (* Definition IRState_lt (s1 s2 : IRState) : Prop := *)
  (*   (local_count s1 < local_count s2)%nat. *)
  (* Infix "<<" := IRState_lt (at level 10). *)

  (* Definition IRState_le (s1 s2 : IRState) : Prop := *)
  (*   (local_count s1 <= local_count s2)%nat. *)
  (* Infix "<<=" := IRState_le (at level 10). *)

  (* Lemma incLocal_lt : forall s1 s2 x, *)
  (*     incLocal s1 ≡ inr (s2,x) -> *)
  (*     s1 << s2. *)
  (* Proof. *)
  (*   intros s1 s2 x INC. *)
  (*   apply incLocal_local_count in INC. *)
  (*   unfold IRState_lt. *)
  (*   lia. *)
  (* Qed. *)

  (* Create HintDb irs_lt. *)
  (* Hint Resolve incLocal_lt : irs_lt. *)


  (* Tactics *)

Ltac get_local_count_hyps :=
  repeat
    match goal with
    | H: incBlockNamed ?n ?s1 ≡ inr (?s2, _) |- _ =>
      apply incBlockNamed_local_count in H; cbn in H
    | H: incLocalNamed ?n ?s1 ≡ inr (?s2, _) |- _ =>
      apply incLocalNamed_local_count in H; cbn in H
    | H: incVoid ?s1 ≡ inr (?s2, _) |- _ =>
      apply incVoid_local_count in H; cbn in H
    | H: incLocal ?s1 ≡ inr (?s2, _) |- _ =>
      apply incLocal_local_count in H; cbn in H
    | H: dropVars _ ?s1 ≡ inr (?s2, _) |- _ =>
      apply dropVars_local_count in H; cbn in H
    | H:compile_expr ?op ?id ?s1 ≡ inr (?s2, _) |- _ =>
      apply compile_expr_local_count in H; cbn in H
    end.

Ltac get_block_count_hyps :=
  repeat
    match goal with
    | H: incBlockNamed ?n ?s1 ≡ inr (?s2, _) |- _ =>
      apply incBlockNamed_block_count in H; cbn in H
    | H: incLocalNamed ?n ?s1 ≡ inr (?s2, _) |- _ =>
      apply incLocalNamed_block_count in H; cbn in H
    | H: incVoid ?s1 ≡ inr (?s2, _) |- _ =>
      apply incVoid_block_count in H; cbn in H
    | H: incLocal ?s1 ≡ inr (?s2, _) |- _ =>
      apply incLocal_block_count in H; cbn in H
    | H: dropVars _ ?s1 ≡ inr (?s2, _) |- _ =>
      apply dropVars_block_count in H; cbn in H
    | H:compile_expr ?op ?id ?s1 ≡ inr (?s2, _) |- _ =>
      apply compile_expr_block_count in H; cbn in H
    end.

Ltac solve_local_count := try solve [ cbn; get_local_count_hyps; lia
                                    | reflexivity
                                    ].

Ltac solve_block_count := try solve [ cbn; get_block_count_hyps; lia
                                    | reflexivity
                                    ].

Notation "s1 << s2" := (local_count s1 < local_count s2) (at level 50).
Notation "s1 <<= s2" := (local_count s1 <= local_count s2) (at level 50).

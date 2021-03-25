(* Taken from Helix's LLVMGen.BidBound.v *)

(** * Block labels and freshness frames

    Specialization of [VariableBinding] to block labels.
 *)
Require Import HelixLib.Correctness_Prelude.
Require Import HelixLib.VariableBinding.
Require Import HelixLib.IdLemmas.
Require Import HelixLib.StateCounters.

From Coq Require Import ZArith.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.

Section BidBound.
  (* Block id has been generated by an earlier IRState *)
  Definition bid_bound (s : IRState) (bid: block_id) : Prop
    := state_bound block_count incBlockNamed s bid.

  (* If an id has been bound between two states.

    The primary use for this is in lemmas like, bid_bound_fresh,
    which let us know that since a id was bound between two states,
    it can not possibly collide with an id from an earlier state.
  *)
  Definition bid_bound_between (s1 s2 : IRState) (bid : block_id) : Prop
    := state_bound_between block_count incBlockNamed s1 s2 bid.

  Lemma incBlockNamed_count_gen_injective :
    count_gen_injective block_count incBlockNamed.
  Admitted.

  Lemma bid_bound_only_block_count :
    forall s lc vc γ bid,
      bid_bound s bid ->
      bid_bound {| block_count := block_count s; local_count := lc; void_count := vc; Γ := γ |} bid.
  Admitted.

  Lemma bid_bound_between_only_block_count_r :
    forall s1 s2 lc vc γ bid,
      bid_bound_between s1 s2 bid ->
      bid_bound_between s1 {| block_count := block_count s2; local_count := lc; void_count := vc; Γ := γ |} bid.
  Admitted.

  Lemma bid_bound_mono : forall s1 s2 b,
      bid_bound s1 b ->
      (block_count s1 <= block_count s2)%nat ->
      bid_bound s2 b.
  Admitted.

  Lemma bid_bound_fresh :
    forall (s1 s2 : IRState) (bid bid' : block_id),
      bid_bound s1 bid ->
      bid_bound_between s1 s2 bid' ->
      bid ≢ bid'.
  Admitted.

  Lemma bid_bound_fresh' :
    forall (s1 s2 s3 : IRState) (bid bid' : block_id),
      bid_bound s1 bid ->
      (block_count s1 <= block_count s2)%nat ->
      bid_bound_between s2 s3 bid' ->
      bid ≢ bid'.
  Admitted.

  Lemma bid_bound_bound_between :
    forall (s1 s2 : IRState) (bid : block_id),
      bid_bound s2 bid ->
      ~(bid_bound s1 bid) ->
      bid_bound_between s1 s2 bid.
  Admitted.

  Lemma bid_bound_between_bound_earlier :
    forall s1 s2 bid,
      bid_bound_between s1 s2 bid ->
      bid_bound s2 bid.
  Admitted.

  Lemma not_bid_bound_incBlockNamed :
    forall s1 s2 n bid,
      is_correct_prefix n ->
      incBlockNamed n s1 ≡ inr (s2, bid) ->
      ~ (bid_bound s1 bid).
  Admitted.

  Lemma bid_bound_name :
    forall s1 n x,
      is_correct_prefix n ->
      bid_bound s1 (Name (n @@ string_of_nat x)) ->
      (x < block_count s1)%nat.
  Admitted.

  Lemma bid_bound_incBlockNamed :
    forall name s1 s2 bid,
      is_correct_prefix name ->
      incBlockNamed name s1 ≡ inr (s2, bid) ->
      bid_bound s2 bid.
  Admitted.

  Lemma incBlockNamed_bound_between :
    forall s1 s2 n bid,
      is_correct_prefix n ->
      incBlockNamed n s1 ≡ inr (s2, bid) ->
      bid_bound_between s1 s2 bid.
  Admitted.

  (* TODO: typeclasses for these mono lemmas to make automation easier? *)
  Lemma bid_bound_incVoid_mono :
    forall s1 s2 bid bid',
      bid_bound s1 bid ->
      incVoid s1 ≡ inr (s2, bid') ->
      bid_bound s2 bid.
  Admitted.

  Lemma bid_bound_incLocal_mono :
    forall s1 s2 bid bid',
      bid_bound s1 bid ->
      incLocal s1 ≡ inr (s2, bid') ->
      bid_bound s2 bid.
  Admitted.

  Lemma bid_bound_between_sep :
    ∀ (bid : block_id) s1 s2 s3,
      bid_bound_between s1 s2 bid → ¬ (bid_bound_between s2 s3 bid).
  Admitted.

  Lemma not_bid_bound_between :
    forall bid s1 s2, bid_bound s1 bid -> not (bid_bound_between s1 s2 bid).
  Admitted.

  Lemma bid_bound_incBlock_neq:
    forall i i' bid bid',
      incBlock i ≡ inr (i', bid) ->
      bid_bound i bid' ->
      bid ≢ bid'.
  Admitted.

Lemma bid_bound_incBlockNamed_mono :
    forall name s1 s2 bid bid',
      bid_bound s1 bid ->
      incBlockNamed name s1 ≡ inr (s2, bid') ->
      bid_bound s2 bid.
  Admitted.

End BidBound.

Hint Resolve incBlockNamed_count_gen_injective : CountGenInj.

Ltac solve_bid_bound :=
  repeat
    match goal with
    | H: incBlockNamed ?msg ?s1 ≡ inr (?s2, ?bid) |-
      bid_bound ?s2 ?bid =>
      eapply bid_bound_incBlockNamed; try eapply H; solve_prefix
    | H: incBlock ?s1 ≡ inr (?s2, ?bid) |-
      bid_bound ?s2 ?bid =>
      eapply bid_bound_incBlockNamed; try eapply H; solve_prefix

    | H: incBlockNamed ?msg ?s1 ≡ inr (_, ?bid) |-
      ~(bid_bound ?s1 ?bid) =>
      eapply gen_not_state_bound; try eapply H; solve_prefix
    | H: incBlock ?s1 ≡ inr (_, ?bid) |-
      ~(bid_bound ?s1 ?bid) =>
      eapply gen_not_state_bound; try eapply H; solve_prefix

    (* Monotonicity *)
    | |- bid_bound {| block_count := block_count ?s; local_count := ?lc; void_count := ?vc; Γ := ?γ |} ?bid =>
      apply bid_bound_only_block_count

    | H: incVoid ?s1 ≡ inr (?s2, _) |-
      bid_bound ?s2 _ =>
      eapply bid_bound_incVoid_mono; try eapply H
    | H: incLocal ?s1 ≡ inr (?s2, _) |-
      bid_bound ?s2 _ =>
      eapply bid_bound_incLocal_mono; try eapply H
    | H: incBlockNamed _ ?s1 ≡ inr (?s2, _) |-
      bid_bound ?s2 _ =>
      eapply bid_bound_incBlockNamed_mono; try eapply H
    | H: incBlock ?s1 ≡ inr (?s2, _) |-
      bid_bound ?s2 _ =>
      eapply bid_bound_incBlockNamed_mono; try eapply H
    end.


Ltac invert_err2errs :=
  match goal with
  | H : ErrorWithState.err2errS (inl _) _ ≡ inr _ |- _ =>
    inversion H
  | H : ErrorWithState.err2errS (inr _) _ ≡ inr _ |- _ =>
    inversion H; subst
  end.

Ltac block_count_replace :=
  repeat match goal with
        | H : incVoid ?s1 ≡ inr (?s2, ?bid) |- _
          => apply incVoid_block_count in H; cbn in H
        | H : incBlockNamed ?name ?s1 ≡ inr (?s2, ?bid) |- _
          => apply incBlockNamed_block_count in H; cbn in H
        | H : incBlock ?s1 ≡ inr (?s2, ?bid) |- _
          => apply incBlockNamed_block_count in H; cbn in H
        | H : incLocal ?s1 ≡ inr (?s2, ?bid) |- _
          => apply incLocal_block_count in H; cbn in H
        end.

Ltac solve_block_count :=
  match goal with
  | |- (block_count ?s1 <= block_count ?s2)%nat
    => block_count_replace; cbn; lia
  | |- (block_count ?s1 >= block_count ?s2)%nat
    => block_count_replace; cbn; lia
  end.

Ltac solve_not_bid_bound :=
  match goal with
  | H: incBlockNamed ?name ?s1 ≡ inr (?s2, ?bid) |-
    ~(bid_bound ?s3 ?bid) =>
    eapply (not_id_bound_gen_mono incBlockNamed_count_gen_injective); [eassumption |..]
  | H: incBlock ?s1 ≡ inr (?s2, ?bid) |-
    ~(bid_bound ?s3 ?bid) =>
    eapply (not_id_bound_gen_mono incBlockNamed_count_gen_injective); [eassumption |..]
  end.

Ltac solve_count_gen_injective :=
  match goal with
  | |- count_gen_injective _ _
    => eauto with CountGenInj
  end.

Ltac big_solve :=
  repeat
    (try invert_err2errs;
    try solve_block_count;
    try solve_not_bid_bound;
    try solve_prefix;
    try solve_count_gen_injective;
    try match goal with
        | |- Forall _ (?x::?xs) =>
          apply Forall_cons; eauto
        | |- bid_bound_between ?s1 ?s2 ?bid =>
          eapply bid_bound_bound_between; solve_bid_bound
        | |- bid_bound_between ?s1 ?s2 ?bid ∨ ?bid ≡ ?nextblock =>
          try auto; try left
        end).

Ltac get_block_count_hyps :=
  repeat
    match goal with
    (* | H: incBlockNamed ?n ?s1 ≡ inr (?s2, _) |- _ => *)
      (* apply incBlockNamed_block_count in H *)
    (* | H: incLocalNamed ?n ?s1 ≡ inr (?s2, _) |- _ => *)
    (* apply incLocalNamed_block_count in H *)
    | H: incVoid ?s1 ≡ inr (?s2, _) |- _ =>
      apply incVoid_block_count in H
    | H: incLocal ?s1 ≡ inr (?s2, _) |- _ =>
      apply incLocal_block_count in H
    end.

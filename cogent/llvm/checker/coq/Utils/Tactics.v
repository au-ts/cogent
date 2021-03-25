From Checker Require Import DenotationTheory HelixLib.Correctness_Prelude.

(* From Helix *)

Ltac unfolder_cogent       := unfold ErrorWithState.option2errS, ErrorWithState.err2errS.
Ltac unfolder_cogent_hyp h := unfold ErrorWithState.option2errS, ErrorWithState.err2errS in h.
Ltac unfolder_cogent_all   := unfold ErrorWithState.option2errS, ErrorWithState.err2errS in *.

Tactic Notation "unfolder" := unfolder_cogent; unfolder_vellvm.
Tactic Notation "unfolder" "in" hyp(h) := unfolder_cogent_hyp h; unfolder_vellvm_hyp h.
Tactic Notation "unfolder" "in" "*" := unfolder_cogent_all; unfolder_vellvm_all.

Tactic Notation "cbn*" := (repeat (cbn; unfolder)).
Tactic Notation "cbn*" "in" hyp(h) := (repeat (cbn in h; unfolder in h)).
Tactic Notation "cbn*" "in" "*" := (repeat (cbn in *; unfolder in *)).

Ltac cred :=
  let R := fresh
  in eutt_hide_rel_named R;
    let X := fresh
    in eutt_hide_right_named X;
      repeat (rewrite ?interp_expr_bind, ?interp_expr_Ret, ?bind_ret_l);
      subst R; subst X.

Ltac vred := vred_r.
Ltac cvred := cred; vred_r.

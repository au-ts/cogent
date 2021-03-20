(* From Helix. To clean up *)

From Coq Require Export Arith List String BinNums BinInt.
Require Export Psatz.

From Vellvm Require Export Syntax.Traversal Utils.Error Utils.Tactics.

From Checker Require Import Utils.Codegen Utils.ErrorWithState.


(* Introduction pattern useful after [eutt_clo_bind] *)
(* Ltac introR :=
  intros [[?memH ?vH] |] (?memV & ?l & ?g & ?vV) ?PRE; [| now inv PRE]. *)

(** Proof automation *)

Ltac unfolder_vellvm       := unfold Traversal.Endo_id.
Ltac unfolder_vellvm_hyp h := unfold Traversal.Endo_id in h.
Ltac unfolder_vellvm_all   := unfold Traversal.Endo_id in *.

Ltac unfolder_helix       := unfold option2errS, err2errS, trywith.
Ltac unfolder_helix_hyp h := unfold option2errS, err2errS, trywith in h.
Ltac unfolder_helix_all   := unfold option2errS, err2errS, trywith in *.

(**
     Better solution (?): use
     `Argument myconstant /.`
     to force `cbn` to unfold `myconstant`
 *)
Tactic Notation "unfolder" := unfolder_helix; unfolder_vellvm.
Tactic Notation "unfolder" "in" hyp(h) := unfolder_helix_hyp h; unfolder_vellvm_hyp h.
Tactic Notation "unfolder" "in" "*" := unfolder_helix_all; unfolder_vellvm_all.

Tactic Notation "cbn*" := (repeat (cbn; unfolder)).
Tactic Notation "cbn*" "in" hyp(h) := (repeat (cbn in h; unfolder in h)).
Tactic Notation "cbn*" "in" "*" := (repeat (cbn in *; unfolder in *)).

(* This tactic is quite dumb, and should be refined if needed, but does a good job at
   reducing the success of a compilation unit to the success of all of its sub-operations.
 *)
Ltac simp := repeat (inv_sum || inv_option || break_and || break_match_hyp).




From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts
     InterpFacts
     Eq.Eq.

From Vellvm Require Import
     Utils.Tactics
     Utils.Util
     Syntax.LLVMAst
     Syntax.Traversal
     Syntax.AstLib
     Syntax.DynamicTypes
     Syntax.CFG
     Syntax.TypToDtyp
     Semantics.LLVMEvents
     Semantics.DynamicValues
     Semantics.TopLevel
     Semantics.InterpretationStack
     Handlers.Handlers
     Theory.Refinement
     Theory.DenotationTheory
     Theory.InterpreterCFG.

From ExtLib Require Import
     Structures.Functor.

From Coq Require Import
     Strings.String
     Logic
     Morphisms
     Relations
     List.

Require Import Ceres.Ceres.
Import BinInt.
Import ListNotations.
Import ITree.Basics.Basics.Monads.

From Vellvm Require Import Util.
Require Import ITree.Events.State.

Require Import ITree.Eq.Eq.

From Vellvm Require Import Utils.AListFacts.

Import Traversal.

(* YZ: Should they be Opaque or simpl never? *)
Global Opaque denote_ocfg.
Global Opaque assoc.
Global Opaque denote_instr.
Global Opaque denote_terminator.
Global Opaque denote_phi.
Global Opaque denote_code.

Ltac typ_to_dtyp_simplify :=
  repeat
    (try rewrite typ_to_dtyp_I in *;
     try rewrite typ_to_dtyp_D in *;
     try rewrite typ_to_dtyp_D_array in *;
     try rewrite typ_to_dtyp_P in *).

From Paco Require Import paco.
Lemma eutt_mon {E R1 R2} (RR RR' : R1 -> R2 -> Prop)
      (LERR: RR <2= RR') :
  @eutt E R1 R2 RR <2= eutt RR'.
Proof.
  eapply eqit_mon; eauto.
Qed.

From Vellvm Require Import Syntax.Scope.

(* Enforcing these definitions to be unfolded systematically by [cbn] *)
Arguments endo /.
Arguments Endo_id /.
Arguments Endo_ident /.

Arguments find_block : simpl never.

From Vellvm Require Import Theory.SymbolicInterpreter.

Module eutt_Notations.
  Notation "t '======================' '======================' u '======================' '{' R '}'"
    := (eutt R t u)
         (only printing, at level 200,
          format "'//' '//' t '//' '======================' '======================' '//' u '//' '======================' '//' '{' R '}'"
         ).
End eutt_Notations.

Import D. 
Module VIR_denotation_Notations.
  (* Notation "'ℐ' '(' t ')' g l m" := (interp_cfg_to_L3 _ t g l m) (only printing, at level 10). *)
  Notation "'global.' g 'local.' l 'memory.' m 'ℐ' t" :=
    (interp_cfg3 t g l m)
      (only printing, at level 10,
       format "'global.'  g '//' 'local.'  l '//' 'memory.'  m '//' 'ℐ'  t").
  
  Notation "⟦ c ⟧" := (denote_code c) (only printing, at level 10).
  Notation "⟦ i ⟧" := (denote_instr i) (only printing, at level 10).
  Notation "⟦ t ⟧" := (denote_terminator t) (only printing, at level 10).
  Notation "⟦ e ⟧" := (denote_exp None e) (only printing, at level 10).
  Notation "⟦ τ e ⟧" := (denote_exp (Some τ) e) (only printing, at level 10).
  Notation "x" := (translate exp_to_instr x) (only printing, at level 10).

  Notation "'λ' a b c d ',' k" := (fun '(a,(b,(c,d))) => k) (only printing, at level 0, format "'λ'  a  b  c  d ',' '[' '//' k ']'").

End VIR_denotation_Notations.

Import ITreeNotations.

From Vellvm Require Import InstrLemmas ExpLemmas.

Ltac vred_r :=
  let R := fresh
  in eutt_hide_rel_named R;
     let X := fresh
     in eutt_hide_left_named X; vred_C3;
        subst X; subst R.

Ltac vred_l :=
  let R := fresh
  in eutt_hide_rel_named R;
     let X := fresh
     in eutt_hide_right_named X; vred_C3;
        subst X; subst R.

Ltac vstep := vstep3.

Ltac tred := autorewrite with itree.

Arguments denote_exp : simpl never.
(* TODO: fmap (mk_block _ _ _ _ _) does not reduce, although we would like.
   However if I do the following to force the unfolding, then fmap always
   unfolds even in many other cases where we don't want it to do so.
   Solution?
 *)
(* Arguments fmap /. *)
(* Arguments Fmap_block /. *)
Arguments denote_phis : simpl never.
Arguments denote_code : simpl never.
Arguments denote_terminator : simpl never.
Arguments denote_block : simpl never.

From Vellvm Require Import
     Utils.TFor
     Utils.NoFailure
     Utils.PropT
.
Require Export ITree.Events.FailFacts.

From Coq Require Import Lia.

From Checker Require Import Denote.

Ltac hred :=
    let R := fresh
    in eutt_hide_rel_named R;
        let X := fresh
        in eutt_hide_right_named X;
            repeat (rewrite ?interp_expr_bind, ?interp_expr_Ret, ?bind_ret_l);
            subst R; subst X.
    
    (* Ltac hstep := first [rewrite interp_helix_MemSet | rewrite interp_helix_MemLU; cycle 1 | idtac]. *)
    
Ltac vred := vred_r.
Ltac hvred := hred; vred_r.

Ltac introR :=
  intros [[?memC ?vC] |] (?memV & ?l & ?g & ?vV) ?PRE; [| now inv PRE].
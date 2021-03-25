(* Taken from Helix's LLVMGen.Vellvm_Utils.v *)

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

(* TODO: tactics? *)
Ltac solve_allocated :=
  solve [ eauto
        | eapply dtyp_fits_allocated; eauto
        | eapply handle_gep_addr_allocated; cycle 1; [solve [eauto] | solve_allocated]
        | eapply write_preserves_allocated; cycle 1; [solve [eauto] | solve_allocated]
        ].

Ltac solve_read :=
  solve [ eauto
        (* This is largely for cases where sizeof_dtyp t <> 0 -> read ... *)
        | match goal with
          | H: _ |- _ => apply H
          end; cbn; lia
        | (* read from an array *)
        erewrite read_array; cycle 2; [solve [eauto] | | solve_allocated]; eauto
        ].

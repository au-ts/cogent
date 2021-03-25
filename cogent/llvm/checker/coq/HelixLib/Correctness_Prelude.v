(* Taken from Helix's LLVMGen.Correctness_Prelude.v *)

(** * Correctness of the pass of compilation from FSHCOL to VIR

We prove the correctness of the pass of compilation defined in the
_Correctness.v_. The Admitted.is based on the Interaction Trees approach: the
semantics of both languages are denoted in terms of trees further interpreted
into a monad built atop of the itree one.

The semantic equivalence is expressed in terms of a weak bisimulation over the
resulting monad.

**)

(** * Prelude
  This file essentially:
  - setup export the module shared over the whole proof
  - define the semantic domains over which we work
  - define conveniences to work with relations involved in the proof
  - define notations and automations easing the Admitted.effort
*)

Require Export Coq.Arith.Arith.
Require Export Coq.Lists.List.
Require Export Coq.Strings.String.
Require Export Coq.Numbers.BinNums. (* for Z scope *)
Require Export Coq.ZArith.BinInt.
Require Export Psatz.

Require Export HelixLib.Codegen.
Require Export HelixLib.Vellvm_Utils.

Require Export Vellvm.Utils.Tactics.
Require Export Vellvm.Utils.AListFacts.
Require Export Vellvm.Utils.Util.
Require Export Vellvm.Utils.PostConditions.
Require Export Vellvm.Utils.NoFailure.
Require Export Vellvm.Utils.PropT.
Require Export Vellvm.Utils.TFor.
Require Export Vellvm.Syntax.LLVMAst.
Require Export Vellvm.Syntax.AstLib.
Require Export Vellvm.Syntax.Scope.
Require Export Vellvm.Syntax.DynamicTypes.
Require Export Vellvm.Syntax.TypToDtyp.
Require Export Vellvm.Syntax.CFG.
Require Export Vellvm.Syntax.Traversal.
Require Export Vellvm.Syntax.SurfaceSyntax.
Require Export Vellvm.Syntax.ScopeTheory.
Require Export Vellvm.Semantics.Denotation.
Require Export Vellvm.Semantics.LLVMEvents.
Require Export Vellvm.Semantics.InterpretationStack.
Require Export Vellvm.Semantics.TopLevel.
Require Export Vellvm.Handlers.Handlers.
Require Export Vellvm.Theory.InterpreterMCFG.
Require Export Vellvm.Theory.InterpreterCFG.
Require Export Vellvm.Theory.TopLevelRefinements.
Require Export Vellvm.Theory.DenotationTheory.
Require Export Vellvm.Theory.InstrLemmas.
Require Export Vellvm.Theory.ExpLemmas.
Require Export Vellvm.Theory.SymbolicInterpreter.

Require Export ExtLib.Structures.Monads.
Require Export ExtLib.Data.Map.FMapAList.
Require Export ExtLib.Core.RelDec.

Require Export ITree.Interp.TranslateFacts.
Require Export ITree.Basics.CategoryFacts.
Require Export ITree.Events.State.
Require Export ITree.Events.StateFacts.
Require Export ITree.Events.FailFacts.
Require Export ITree.ITree.
Require Export ITree.Eq.Eq.
Require Export ITree.Basics.Basics.
Require Export ITree.Events.Exception.
Require Export ITree.Interp.InterpFacts.

Require Export MathClasses.interfaces.canonical_names.
Require Export MathClasses.misc.decision.

Import AlistNotations.

Open Scope string_scope.
Open Scope char_scope.

Set Implicit Arguments.
Set Strict Implicit.

Export D.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Open Scope string_scope.
Open Scope char_scope.
Open Scope nat_scope.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

(** Semantic domains

  - Facilities to work with the same interface of events on both sides through an outer trivial translation.
  - Definition of the top level definition of FSHCOL's semantics by performing the initialization of the
  state at a meta level.
  TODO: Move this semantic component out of the Admitted.


*)

(* A couple of notations to avoid ambiguities while not having to worry about imports and qualified names *)
Notation memoryV := memory_stack.

Section EventTranslation.

  (* We relate Helix trees and Vellvm trees at a point where their event signatures are still not empty.
  To do so, we therefore relate them at the join of these signature, using [translate] to do so.
  Unfortunately, since [vellvm] works over two different set of signatures depending whether
  function calls are already resolved or not, we also need two joins here.

  TODOYZ: Principle the approach and move it to [itrees]

  NOTEYZ: An alternative would be to translate everything that remains into failure. That could also be
          part of the library as a generic handler.
  *)

  (* Joined set of residual events for full programs *)
  Definition E_mcfg : Type -> Type := (ExternalCallE +' PickE +' UBE +' DebugE +' FailureE).
  (* Joined set of residual events for cfgs *)
  Definition E_cfg : Type -> Type := (CallE +' PickE +' UBE +' DebugE +' FailureE). 

  (* We therefore have the following resulting denotation functions. *)
  (* On the Vellvm side, for [mcfg]: *)
  Definition semantics_llvm_mcfg p : itree E_mcfg _ := model_to_L3 DTYPE_Void "main" main_args p.
  (* Which get lifted to [toplevel_entity] as usual: *)
  Definition semantics_llvm (prog: list (toplevel_entity typ (LLVMAst.block typ * list (LLVMAst.block typ)))) :=
    semantics_llvm_mcfg (convert_types (mcfg_of_tle prog)).

  Definition inject_signature {E} : void1 ~> E := fun _ (x:void1 _) => match x with end.
  Hint Unfold inject_signature : core.

End EventTranslation.

Notation "'interp_cfg'"  := interp_cfg3. 
Notation "'interp_mcfg'" := interp_mcfg3. 

(** Smart constructors for states, predicates, relations  *)

(* Facilities to refer to the return types of the various pieces of denotations we manipulate *)

Section StateTypes.

  Local Open Scope type_scope.

  (* Return state of a denoted and interpreted [cfg].
    Note the lack of local stack *)
  Definition config_cfg
    := memoryV * (local_env * (global_env)).

  (* Constructor to avoid having to worry about the nesting *)
  Definition mk_config_cfg m l g: config_cfg := (m,(l,g)).

  (* Return state of a denoted and interpreted [mcfg] *)
  Definition config_mcfg
    := memoryV *
      (local_env * @Stack.stack (local_env) * (global_env)).

  (* Return state and value of a denoted and interpreted (open) [cfg].
    Note the lack of local stack.
    Note that we may return a [block_id] alternatively to a [uvalue]
  *)
  Definition config_cfg_T (T:Type): Type
    := memoryV * (local_env * (global_env * T)).
  Definition config_res_cfg
    := config_cfg_T (block_id + uvalue).

  (* Return state and value of a denoted and interpreted [mcfg]. *)
  Definition config_mcfg_T (T:Type): Type
    := memoryV * (local_env * @Stack.stack (local_env) * (global_env * T)).
  Definition config_res_mcfg :=
    config_mcfg_T uvalue.

  (* -- Injections -- *)
  (* The nested state transformers associate the products the other way,
    we therefore define injections of memory states and values into return
    types of computations.
  *)
  Definition mk_config_cfg_T (T:Type) (v:T): config_cfg -> (config_cfg_T T)
    := fun '(m, (ρ, g)) => (m, (ρ, (g, v))).

  Definition mk_config_mcfg_T (T:Type) (v:T): config_mcfg -> (config_mcfg_T T)
    := fun '(m, (ρ, g)) => (m, (ρ, (g, v))).

End StateTypes.

(* TODOYZ : MOVE *)
Definition conj_rel {A B : Type} (R S: A -> B -> Prop): A -> B -> Prop :=
  fun a b => R a b /\ S a b.
Infix "⩕" := conj_rel (at level 85, right associativity).

(* Introduction pattern useful after [eutt_clo_bind] *)
Ltac introR :=
  intros [[?memH ?vH] |] (?memV & ?l & ?g & ?vV) ?PRE; [| now inv PRE].

(** Admitted.automation *)

Ltac unfolder_vellvm       := unfold Traversal.Endo_id.
Ltac unfolder_vellvm_hyp h := unfold Traversal.Endo_id in h.
Ltac unfolder_vellvm_all   := unfold Traversal.Endo_id in *.

(* This tactic is quite dumb, and should be refined if needed, but does a good job at
  reducing the success of a compilation unit to the success of all of its sub-operations.
*)
Ltac simp := repeat (inv_sum || inv_option || break_and || break_match_hyp).

Section Add_Comment.

  (* NOTEYZ:
    Move this or a similar facility to Vellvm
  *)
  Lemma add_comment_preserves_num_blocks :
    forall l comments blocks,
      add_comment l comments ≡ blocks ->
      List.length l ≡ List.length blocks.
  Admitted.

  Lemma add_comment_singleton :
    forall l comments block,
      add_comment l comments ≡ [block] ->
      exists b, l ≡ [b].
  Admitted.

  Lemma add_comment_inputs :
    forall (bs : ocfg typ) (comments : list string),
      inputs (add_comment bs comments) ≡ inputs bs.
  Admitted.

  Lemma add_comment_outputs :
    forall (bs : ocfg typ) (comments : list string),
      outputs (add_comment bs comments) ≡ outputs bs.
  Admitted.

  Lemma add_comment_inputs_typ :
    forall (bs : list (LLVMAst.block typ)) env (comments : list string),
      inputs (convert_typ env (add_comment bs comments)) ≡ inputs (convert_typ env bs).
  Admitted.

  Lemma add_comment_outputs_typ :
    forall (bs : list (LLVMAst.block typ)) env (comments : list string),
      outputs (convert_typ env (add_comment bs comments)) ≡ outputs (convert_typ env bs).
  Admitted.

  Lemma wf_ocfg_bid_add_comment :
    forall bks s,
      wf_ocfg_bid (add_comment bks s) ->
      wf_ocfg_bid bks.
  Admitted.

  Lemma denote_ocfg_eutt_bk :
    forall b b' bk x,
      blk_id b ≡ blk_id b' ->
      (forall bid_from, denote_block b bid_from ≈ denote_block b' bid_from) ->
      denote_ocfg (b::bk) x ≈ denote_ocfg (b'::bk) x.
  Admitted.
  Global Opaque denote_ocfg.

  (* Lemma add_comment_eutt :
    forall comments bks ids,
      denote_ocfg (convert_typ [] (add_comment bks comments)) ids ≈ denote_ocfg (convert_typ [] bks) ids.
  Proof.
    intros comments bks ids.
    destruct bks as [| b bks].
    - cbn; reflexivity.
    - simpl add_comment.
      cbn.
      apply denote_ocfg_eutt_bk; [reflexivity |].
      intros.
      destruct b.
      unfold fmap, Fmap_block.
      cbn.
      rewrite 2 denote_block_unfold.
      reflexivity.
  Qed. *)

End Add_Comment.

Global Opaque interp_cfg3.

(* Autorewrite and hint databases for more modular rewriting. *)
(* "Normalizing" rewriting hint database. *)
Hint Rewrite @translate_bind : itree.
Hint Rewrite @interp_bind : itree.
Hint Rewrite @bind_bind : itree.
Hint Rewrite @bind_ret_l : itree.

Hint Rewrite @translate_ret : itree.
Hint Rewrite @interp_ret : itree.

Hint Rewrite @translate_trigger : itree.
Hint Rewrite @interp_trigger : itree.

Hint Rewrite @interp_cfg3_bind : vellvm.
Hint Rewrite interp_cfg3_ret : vellvm.
Hint Rewrite interp_cfg3_GR : vellvm.
Hint Rewrite interp_cfg3_LR : vellvm.

Hint Rewrite @LU_to_exp_Global : vellvm.
Hint Rewrite @LU_to_exp_Local : vellvm.
Hint Rewrite @subevent_subevent : vellvm.
Hint Rewrite @exp_to_instr_Global : vellvm.
Hint Rewrite @exp_to_instr_Local : vellvm.
Hint Rewrite @typ_to_dtyp_equation : vellvm.
Hint Rewrite denote_code_nil : vellvm.
Hint Rewrite denote_code_singleton : vellvm.

Tactic Notation "rauto:R" :=
  repeat (
      match goal with
      | |- eutt _ ?t _ => let x := fresh in remember t as x;
                                          autorewrite with itree;
                                          autorewrite with vellvm;
                                          autorewrite with helix; subst x
      end
    ).

Tactic Notation "rauto:L" :=
  repeat (
      match goal with
      | |- eutt _ _ ?t => let x := fresh in remember t as x;
                                          autorewrite with itree;
                                          autorewrite with vellvm;
                                          autorewrite with helix; subst x
      end
    ).

Tactic Notation "rauto" := (repeat (autorewrite with itree; autorewrite with vellvm; autorewrite with helix)).
Tactic Notation "rauto" "in" hyp(h) :=
  (repeat (autorewrite with itree in h; autorewrite with vellvm in h; autorewrite with helix in h)).

Module ProofMode.

  (* Include ITreeNotations. *)
  Notation "t1 ;; k" := (ITree.bind t1 k) (format "t1 ;; '//' k", at level 61, right associativity, only printing) : itree_scope.
  Include VIR_Notations.
  Include VIR_denotation_Notations.
  Include eutt_Notations.
  Notation "g '[' r ':' x ']'" := (alist_add r x g) (only printing, at level 10). 

  (* Notation "⟦ b , p , c , t ⟧" := (fmap _ (mk_block b p c t _)) (only printing).  *)
  (* Notation "'denote_blocks' '...' id " := (denote_bks _ id) (at level 10,only printing).  *)
  (* Notation "'IRS' ctx" := (mkIRState _ _ _ ctx) (only printing, at level 10).  *)
  (* Notation "x" := (with_cfg x) (only printing, at level 10).  *)
  (* Notation "x" := (with_mcfg x) (only printing, at level 10).  *)
  (* (* Notation "'CODE' c" := (denote_code c) (only printing, at level 10, format "'CODE' '//' c"). *) *)
  (* Notation "c" := (denote_code c) (only printing, at level 10). *)
  (* (* Notation "'INSTR' i" := (denote_instr i) (only printing, at level 10, format "'INSTR' '//' i"). *) *)
  (* Notation "i" := (denote_instr i) (only printing, at level 10). *)
  (* Notation "x" := (translate exp_E_to_instr_E (denote_exp _ x)) (only printing, at level 10).  *)
  
End ProofMode.

Ltac vred := vred_r.

Require Import LibHyps.LibHyps.

Ltac clean_goal :=
  try match goal with
      | h1 : incVoid _ ≡ _,
            h2 : incVoid _ ≡ _,
                  h3 : incVoid _ ≡ _
        |- _ => move h1 at top; move h2 at top; move h3 at top
      | h1 : incVoid _ ≡ _, h2 : incVoid _ ≡ _ |- _ => move h1 at top; move h2 at top
      | h : incVoid _ ≡ _ |- _ => move h at top
      end;

  try match goal with
      | h1 : incLocal _ ≡ _,
            h2 : incLocal _ ≡ _,
                  h3 : incLocal _ ≡ _
        |- _ => move h1 at top; move h2 at top; move h3 at top
      | h1 : incLocal _ ≡ _, h2 : incLocal _ ≡ _ |- _ => move h1 at top; move h2 at top
      | h : incLocal _ ≡ _ |- _ => move h at top
      end;

  try match goal with
      | h1 : incBlockNamed _ _ ≡ _,
            h2 : incBlockNamed _ _ ≡ _,
                  h3 : incBlockNamed _ _ ≡ _
        |- _ => move h1 at top; move h2 at top; move h3 at top
      | h1 : incBlockNamed _ _ ≡ _, h2 : incBlockNamed _ _ ≡ _ |- _ => move h1 at top; move h2 at top
      | h : incBlockNamed _ _ ≡ _ |- _ => move h at top
      end;

  onAllHyps move_up_types.

Arguments alist_add : simpl never.
Arguments String.append : simpl never.

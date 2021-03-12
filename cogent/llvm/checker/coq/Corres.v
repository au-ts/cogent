From Coq Require Import List String ZArith.

From ITree Require Import ITree ITreeFacts.

From Vellvm Require Import LLVMAst LLVMEvents TopLevel Handlers InterpreterMCFG TopLevelRefinements DynamicTypes
  CFG TypToDtyp InterpretationStack.

From Checker Require Import Denote Cogent Compiler Utils.Fail.

Import ListNotations.


Definition vellvm_prog : Type := toplevel_entities typ (block typ * list (block typ)).

(* Lifted from Helix *)
Definition E_mcfg : Type -> Type := (ExternalCallE +' PickE +' UBE +' DebugE +' FailureE).
(* Definition E_cfg : Type -> Type := (CallE +' PickE +' UBE +' DebugE +' FailureE).  *)
Definition semantics_llvm_mcfg p : itree E_mcfg _ := model_to_L3 DTYPE_Void "main" [DV.UVALUE_I32 (DynamicValues.Int32.zero)] p.
Definition semantics_llvm (p : vellvm_prog) : itree E_mcfg _ :=
  semantics_llvm_mcfg (convert_types (mcfg_of_tle p)).

Definition semantics_cogent (p : cogent_prog) : failT (itree E_mcfg) (memory * (locals * uval)) := 
  interp_cogent (prog_to_module p) (UFunction "main") UUnit empty_locals dummy_memory.

Section TopLevel.

  (* placeholder *)
  Definition TT {A B} (x: A) (y: B):= True.

  Lemma compiler_correct :
    forall (c : cogent_prog) (ll : vellvm_prog),
      compile_cogent c = inr ll -> eutt TT (semantics_cogent c) (semantics_llvm ll).
  Proof.
  Abort.

End TopLevel.

(* Definition vellvm_env : Type := memory_stack * (local_env * global_env).
Definition interp_vellvm (t : itree L0 uvalue) (e : vellvm_env) : itree L3 res_L3 :=
  interp_mcfg3 t (snd (snd e)) (fst (snd e), []) (fst e).

Definition relate_env (c_env : locals) (v_env : vellvm_env) : Prop := True. *)

(* Section RAB.

  Context {A B : Type}.
  Context (RAB : A -> B -> Prop).

  Definition  state_invariant (a : locals * A) (b : vellvm_env * B) : Prop := 
    relate_env (fst a) (fst b) /\ (RAB (snd a) (snd b)).

  Definition bisimilar {E} (t1 : itree (VarE +' E) A) (t2 : itree E_mcfg B) := 
    forall c_env v_env,
      relate_env c_env v_env ->
        eutt state_invariant (interp_cogent t1 c_env) (interp_vellvm t2 v_env).

End RAB.

Definition TT {A B} : A -> B -> Prop  := fun _ _ => True.
Hint Unfold TT : core.

Definition equivalent (c : cogent_prog) (l : vellvm_prog) : Prop :=
   bisimilar TT (denote_cogent c) (denote_vellvm l).

Theorem compile_correct (c : cogent_prog) : equivalent c (compile_cogent c). *)

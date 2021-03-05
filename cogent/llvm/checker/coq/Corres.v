From Coq Require Import List String ZArith.

From Checker Require Import Denote Cogent Compiler.

From ITree Require Import ITree ITreeFacts.

From Vellvm Require Import LLVMAst LLVMEvents TopLevel Handlers InterpreterMCFG TopLevelRefinements DynamicTypes
  CFG TypToDtyp InterpretationStack.

Import ListNotations.


Definition vellvm_prog : Type := list (toplevel_entity typ (block typ * list (block typ))).

(* Lifted from Helix *)
Definition E_mcfg : Type -> Type := (ExternalCallE +' PickE +' UBE +' DebugE +' FailureE).
Definition E_cfg : Type -> Type := (CallE +' PickE +' UBE +' DebugE +' FailureE). 
Definition semantics_llvm_mcfg p : itree E_mcfg _ := model_to_L3 DTYPE_Void "main" main_args p.
Definition semantics_llvm (prog : list (toplevel_entity typ (LLVMAst.block typ * list (LLVMAst.block typ)))) :=
  semantics_llvm_mcfg (convert_types (mcfg_of_tle prog)).

Definition vellvm_env : Type := memory_stack * (local_env * global_env).
Definition interp_vellvm (t : itree L0 uvalue) (e : vellvm_env) : itree L3 res_L3 :=
  interp_mcfg3 t (snd (snd e)) (fst (snd e), []) (fst e).

Definition relate_env (c_env : local_vars) (v_env : vellvm_env) : Prop := True.

Section Simple.

  (* want to try and relate a CFG to a function *)
  
  Definition TT {A B} (x: A) (y: B):= True.

  Lemma correct :
    forall
      (n : name) (t rt : type) (b : expr) 
      (d : definition typ (block typ * list (block typ))),
      compile_fun n t rt b = inr d ->
        eutt TT (interp_cogent (denote_expr b) []) (interp_cfg2 (denote_cfg (convert_typ [] (cfg_of_definition typ d))) [] []).
  Proof.
  Abort.

End Simple.

(* Section RAB.

  Context {A B : Type}.
  Context (RAB : A -> B -> Prop).

  Definition  state_invariant (a : local_vars * A) (b : vellvm_env * B) : Prop := 
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

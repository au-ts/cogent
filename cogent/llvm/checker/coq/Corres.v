From Coq Require Import List String ZArith.

From ITree Require Import ITree ITreeFacts.

From Vellvm Require Import LLVMAst LLVMEvents TopLevel Handlers InterpreterMCFG TopLevelRefinements DynamicTypes
  CFG TypToDtyp InterpretationStack.

From Checker Require Import Denote Cogent Compiler Utils.Codegen Utils.Fail.

Import ListNotations.

Definition vellvm_prog : Type := toplevel_entities typ (block typ * list (block typ)).

(* Lifted from Helix *)
Definition E_mcfg : Type -> Type := ExternalCallE +' PickE +' UBE +' DebugE +' FailureE.
Definition E_cfg : Type -> Type := CallE +' PickE +' UBE +' DebugE +' FailureE. 
Definition semantics_llvm_mcfg p : itree E_mcfg _ := model_to_L3 DTYPE_Void "main" [DV.UVALUE_I32 (DynamicValues.Int32.zero)] p.
Definition semantics_llvm (p : vellvm_prog) : itree E_mcfg _ :=
  semantics_llvm_mcfg (convert_types (mcfg_of_tle p)).

Definition semantics_cogent (p : cogent_prog) : failT (itree E_mcfg) (memory * uval) := 
  interp_cogent (denote_program p) "main" UUnit dummy_memory.

Section TopLevel.

  (* placeholder *)
  Definition TT {A B} (x: A) (y: B):= True.

  Lemma compiler_correct :
    forall (c : cogent_prog) (ll : vellvm_prog),
      compile_cogent c = inr ll ->
        eutt TT (semantics_cogent c) (semantics_llvm ll).
  Proof.
  Abort.

End TopLevel.

Section Expressions.

  Lemma compile_expr_correct :
    forall (s1 s2 : CodegenState) (v : texp typ)
           (e : expr) (γ : ctx) (cogent_mem : memory)
           (next_blk blk prev_blk : block_id) (blks : ocfg typ)
           (g : global_env) (l : local_env) (vellvm_mem : memory_stack),
      compile_expr e next_blk s1 = inr (s2, (v, blk, blks)) ->
        eutt
          TT
          (interp_expr (denote_expr γ e) cogent_mem)
          (interp_cfg3 (denote_ocfg (convert_typ [] blks) (prev_blk, next_blk)) g l vellvm_mem).
  Proof.
  Abort.

(* we want something like Lemma genNExpr_correct mixed with DSHAssign_correct *)

End Expressions.

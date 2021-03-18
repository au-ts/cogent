From Coq Require Import List String ZArith.

From ITree Require Import ITree ITreeFacts.

From Vellvm Require Import LLVMAst LLVMEvents TopLevel Handlers InterpreterMCFG TopLevelRefinements
  DynamicTypes CFG TypToDtyp InterpretationStack SymbolicInterpreter DenotationTheory ScopeTheory
  DynamicValues ExpLemmas Scope.

From Checker Require Import Denote Cogent Compiler Utils.Codegen Utils.Fail Utils.Tactics.

Import ListNotations.

Definition vellvm_prog : Type := toplevel_entities typ (block typ * list (block typ)).

(* Lifted from Helix *)
Definition E_mcfg : Type -> Type := ExternalCallE +' PickE +' UBE +' DebugE +' FailureE.
Definition E_cfg : Type -> Type := CallE +' PickE +' UBE +' DebugE +' FailureE. 
Definition semantics_llvm_mcfg p : itree E_mcfg _ := model_to_L3 DTYPE_Void "main" [DV.UVALUE_I32 (DynamicValues.Int32.zero)] p.
Definition semantics_llvm (p : vellvm_prog) : itree E_mcfg _ :=
  semantics_llvm_mcfg (convert_types (mcfg_of_tle p)).
Notation "'interp_cfg'"  := interp_cfg3. 
Notation "'interp_mcfg'" := interp_mcfg3. 

Definition semantics_cogent (p : cogent_prog) : failT (itree E_mcfg) (memory * uval) := 
  interp_cogent (denote_program p) "main" UUnit empty_memory.

Section StateRel.

  (* do things the helix way *)
  Local Open Scope type_scope.

  Definition state_cogent := memory.
  Definition state_cogent_H := option memory.
  Definition state_cogent_T (T : Type) := memory * T.
  Definition state_cogent_OT (T : Type) := option (memory * T).

  Definition state_cfg := memory_stack * (local_env * global_env).
  Definition state_cfg_T (T : Type) := memory_stack * (local_env * (global_env * T)).
  Definition state_cfg_res := state_cfg_T (block_id + uvalue).  
  
  Definition Rel_cfg : Type := state_cogent -> state_cfg -> Prop.
  Definition Rel_cfg_T (A B : Type) : Type := state_cogent_T A -> state_cfg_T B -> Prop.
  Definition Rel_cfg_OT (A B : Type) : Type := state_cogent_OT A -> state_cfg_T B -> Prop.

  Definition lift_Rel_cfg {A B} (R : Rel_cfg) : Rel_cfg_T A B :=
    fun '(c_mem, _) '(v_mem, (l, (g, _))) => R c_mem (v_mem, (l, g)).

  Definition succ_rel_l {A B} (R : A -> B -> Prop) : option A -> B -> Prop :=
    fun ma b => match ma with | Some a => R a b | _ => False end.
  Definition succ_cfg {A B}: Rel_cfg_T A B -> Rel_cfg_OT A B := succ_rel_l.

  Definition conj_rel {A B : Type} (R S: A -> B -> Prop): A -> B -> Prop :=
    fun a b => R a b /\ S a b.

  Record state_invariant (γ : ctx) (s : CodegenState) (cogent_mem : memory)
                         (vellvm : state_cfg) : Prop :=
  {}.

End StateRel.

Infix "⩕" := conj_rel (at level 85, right associativity).

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

Import ExpTactics.

Section Expressions.

  Definition convert_uval (u : uval) : uvalue :=
    match u with
    | UPrim (LBool b) => UVALUE_I1 (Int1.repr (if b then 1 else 0))
    | UPrim (LU8 w) => UVALUE_I8 (Int8.repr w)
    | UPrim (LU32 w) => UVALUE_I32 (Int32.repr w)
    | UPrim (LU64 w) => UVALUE_I64 (Int64.repr w)
    | UUnit => UVALUE_I8 (Int8.repr 0)
    end.

  Definition compile_expr_res (v : texp typ) (γ : ctx) (s1 s2 : CodegenState) 
                            : Rel_cfg_T uval (block_id * block_id + uvalue) :=
    fun '(_, u) '(m,(l,(g,_))) =>
      interp_cfg
        (translate exp_to_instr (denote_exp (Some (typ_to_dtyp [] (fst v))) (convert_typ [] (snd v))))
        g l m ≈ Ret (m, (l, (g, convert_uval u))).
    

  Record compile_expr_post (v : texp typ) (γ : ctx) (s1 s2 : CodegenState)
                           (cogent_i: state_cogent) (vellvm_i : state_cfg)
                           (cogent_f : state_cogent_T uval)
                           (vellvm_f : state_cfg_T (block_id * block_id + uvalue)) : Prop :=
  {
    correct_result : compile_expr_res v γ s1 s2 cogent_f vellvm_f
  }.

  Lemma compile_expr_correct :
    forall (s1 s2 : CodegenState) (v : texp typ)
           (e : expr) (γ : ctx) (cogent_mem : memory)
           (next_blk blk prev_blk : block_id) (blks : ocfg typ)
           (g : global_env) (l : local_env) (vellvm_mem : memory_stack),
      compile_expr e next_blk s1 = inr (s2, (v, blk, blks)) ->
      state_invariant γ s1 cogent_mem (vellvm_mem, (l, g)) ->
        eutt (
          succ_cfg (
            lift_Rel_cfg (state_invariant γ s1) ⩕ 
            compile_expr_post v γ s1 s2 cogent_mem (vellvm_mem, (l, g))
          ))
          (interp_expr (denote_expr γ e) cogent_mem)
          (interp_cfg (denote_ocfg (convert_typ [] blks) (prev_blk, next_blk)) g l vellvm_mem).
  Proof.
    induction e; intros * COMPILE PRE.
    -
      cbn* in COMPILE; simp.
      unfold denote_expr in *; cbn*.
      unfold option_bind.
      destruct (nth_error γ i).
      + admit.
      +
    admit.
    -
    admit.
    -
      cbn* in COMPILE; simp.
      unfold denote_expr in *; cbn*.
      rewrite interp_expr_Ret.
      rewrite denote_ocfg_unfold_not_in.
      vred.
      apply eutt_Ret; split; [| split]; cbn; eauto.
      typ_to_dtyp_simplify.
      unfold denote_exp; cbn.
      go; reflexivity.
      apply find_block_nil.
    -
      cbn* in COMPILE; simp.
      unfold denote_expr in *; cbn*.
      rewrite interp_expr_Ret.
      rewrite denote_ocfg_unfold_not_in.
      vred.
      apply eutt_Ret; split; [| split]; cbn; eauto.
      destruct l;
        simpl;
        typ_to_dtyp_simplify;
        unfold denote_exp; cbn;
        go; reflexivity.
      apply find_block_nil.
    - 
      cbn* in COMPILE; simp.
      rename e1 into bind, e2 into body.
      rename l0 into bind_blks, l1 into body_blks.
      rename b0 into body_entry.
      unfold code_block.
      rewrite convert_typ_ocfg_app.
      rewrite denote_ocfg_app; eauto.
      2: {
        unfold no_reentrance.

        
        

        

      }

      admit.
  Qed.

(* we want something like Lemma genNExpr_correct mixed with DSHAssign_correct *)

End Expressions.

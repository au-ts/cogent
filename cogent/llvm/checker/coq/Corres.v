From Coq Require Import List String ZArith.

From ITree Require Import ITree ITreeFacts.
From RecordUpdate Require Import RecordSet.
From Vellvm Require Import LLVMAst LLVMEvents TopLevel Handlers InterpreterMCFG TopLevelRefinements
  DynamicTypes CFG TypToDtyp InterpretationStack SymbolicInterpreter DenotationTheory ScopeTheory
  DynamicValues ExpLemmas Coqlib NoFailure AListFacts.

From Checker Require Import Denote Cogent Compiler Utils.Fail Utils.Tactics.

Import ListNotations.
Import RecordSetNotations.
Import AlistNotations.

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

Section Relations.

  (* do things the helix way *)
  Local Open Scope type_scope.

  Definition state_cogent := memory.
  Definition state_cogent_H := option memory.
  Definition state_cogent_T (T : Type) := memory * T.
  Definition state_cogent_OT (T : Type) := option (memory * T).

  Definition state_cfg := memory_stack * (local_env * global_env).
  Definition state_cfg_T (T : Type) := memory_stack * (local_env * (global_env * T)).
  
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

End Relations.

Coercion succ_cfg : Rel_cfg_T >-> Rel_cfg_OT.
Infix "⩕" := conj_rel (at level 85, right associativity).

Section State.

  (* eventually will need more here which will make state_invariant_new_var nontrivial *)
  Definition state_wf (γ : ctx) (s : CodegenState) : Prop := True.

End State.

Section Scope.
  (* ideas from helix *)

  Definition in_vars (γ : ctx) (s : CodegenState) (id : raw_id) : Prop :=
    state_wf γ s /\
    forall t n v,
      nth_error γ n = Some v /\
      nth_error (vars s) n = Some (t, EXP_Ident (ID_Local id)).
  
  Lemma in_vars_eq :
    forall (γ : ctx) (s1 s2 : CodegenState) (id : raw_id),
      vars s1 = vars s2 ->
      in_vars γ s1 id ->
      in_vars γ s2 id.
  Proof.
    intros * EQ IN; inv IN.
    constructor; auto.
    rewrite <- EQ.
    auto.
  Qed.

  Definition local_scope_preserved (s1 s2 : CodegenState) (l l' : local_env) : Prop :=
    True. (* TODO *)
  
  Lemma local_scope_preserved_empty :
    forall (s : CodegenState) (l l' : local_env),
     local_scope_preserved s s l l'.
  Proof.
    intros.
    unfold local_scope_preserved.
    trivial.
  Qed.
  

  Definition vars_preserved (γ : ctx) (s : CodegenState) (l l' : local_env) : Prop :=
    forall id, in_vars γ s id -> l @ id = l' @ id.

  Lemma vars_preserved_eq :
    forall (γ : ctx) (s1 s2 : CodegenState) (l l' : local_env),
      vars s1 = vars s2 ->
      vars_preserved γ s1 l l' ->
      vars_preserved γ s2 l l'.
  Proof.
    intros * EQ PRE.
    unfold vars_preserved in *.
    eauto using in_vars_eq.
  Qed.

End Scope.

Section Values.

  Definition convert_uval (u : uval) : uvalue :=
    match u with
    | UPrim (LBool b) => UVALUE_I1 (Int1.repr (if b then 1 else 0))
    | UPrim (LU8 w) => UVALUE_I8 (Int8.repr w)
    | UPrim (LU32 w) => UVALUE_I32 (Int32.repr w)
    | UPrim (LU64 w) => UVALUE_I64 (Int64.repr w)
    | UUnit => UVALUE_I8 (Int8.repr 0)
    end.

  Definition equivalent_values (γ : ctx) (s1 s2 : CodegenState)
                               (i : im) (u : uval) (vellvm : state_cfg) : Prop :=
    let '(m, (l, g)) := vellvm in
      forall l',
        local_scope_preserved s1 s2 l l' ->
        vars_preserved γ s1 l l' ->
        interp_cfg
          (translate exp_to_instr (denote_exp (Some (typ_to_dtyp [] (fst i))) (convert_typ [] (snd i))))
          g l' m ≈ Ret (m, (l', (g, convert_uval u))).
  
  Lemma equivalent_values_new_var :
    forall (γ : ctx) (s : CodegenState) (i : im) (u : uval) (vellvm : state_cfg)
           (i' : im) (u' : uval),
      let s' := (s<|vars := i' :: vars s|>) in
        equivalent_values γ s s i u vellvm ->
        equivalent_values γ s s i' u' vellvm ->
        equivalent_values (u' :: γ) s' s' i u vellvm.
  Proof.
  Admitted.

End Values.

Section Memory.

  Definition memory_invariant (γ : ctx) (s : CodegenState) (cogent : state_cogent)
                              (vellvm : state_cfg) : Prop :=
    forall (n : nat) (i : im) (u : uval),
      nth_error γ n = Some u ->
      nth_error (vars s) n = Some i ->
      equivalent_values γ s s i u vellvm.

  Lemma memory_invariant_new_var : 
    forall (γ : ctx) (s : CodegenState) (cogent : state_cogent) (vellvm : state_cfg)
          (u : uval) (i : im),
      memory_invariant γ s cogent vellvm ->
      equivalent_values γ s s i u vellvm ->
      memory_invariant (u :: γ) (s<|vars := i :: vars s|>) cogent vellvm.
  Proof.
    intros * MEM EQ.
    unfold memory_invariant in *.
    simpl.
    induction n; simpl; intros; apply equivalent_values_new_var.
    inversion H. inversion H0. subst i0 u0.
    all: try assumption.
    specialize (MEM _ i0 _ H H0).
    assumption.
  Qed.

End Memory.

Section StateInvariant.

  Record state_invariant (γ : ctx) (s : CodegenState) (cogent : state_cogent)
                         (vellvm : state_cfg) : Prop :=
  {
    memory_agrees : memory_invariant γ s cogent vellvm
  ; state_is_wf : state_wf γ s
  }.

  Lemma state_invariant_new_var :
    forall (γ : ctx) (s : CodegenState) (cogent : state_cogent) (vellvm : state_cfg)
           (u : uval) (i : im),
      state_invariant γ s cogent vellvm ->
      equivalent_values γ s s i u vellvm ->
      state_invariant (u :: γ) (s<|vars := i :: vars s|>) cogent vellvm.
  Proof.
    intros * STATE EQ.
    destruct STATE as [MEM WF]; split.
    unfold state_wf in *.
    apply memory_invariant_new_var.
    all: assumption.
  Qed.

End StateInvariant.

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

  Definition compile_expr_res (i : im) (γ : ctx) (s1 s2 : CodegenState) 
                            : Rel_cfg_T uval unit :=
    fun '(_, u) '(m, (l, (g, _))) => 
      equivalent_values γ s1 s2 i u (m, (l, g)).
  
  Local Open Scope nat_scope.

  Record compile_expr_post (i : im) (γ : ctx) (s1 s2 : CodegenState)
                           (cogent_i: state_cogent) (vellvm_i : state_cfg)
                           (cogent_f : state_cogent_T uval)
                           (vellvm_f : state_cfg_T unit) : Prop :=
  {
    correct_result : compile_expr_res i γ s1 s2 cogent_f vellvm_f
  }.

  Lemma compile_expr_correct :
    forall (e : expr) (γ : ctx) (s1 s2 : CodegenState) (v : im) (c : code typ)
           (cogent_mem : memory) (g : global_env) (l : local_env) (vellvm_mem : memory_stack),
      compile_expr e s1 = inr (s2, (v, c)) ->
      state_invariant γ s1 cogent_mem (vellvm_mem, (l, g)) ->
      no_failure (interp_expr (E := E_cfg) (denote_expr γ e) cogent_mem) ->
      eutt (
        succ_cfg (
          lift_Rel_cfg (state_invariant γ s2) ⩕ 
          compile_expr_post v γ s1 s2 cogent_mem (vellvm_mem, (l, g))
        ))
        (interp_expr (denote_expr γ e) cogent_mem)
        (interp_cfg (denote_code (convert_typ [] c)) g l vellvm_mem).
  Proof.
    induction e; intros * COMPILE PRE NOFAIL.
    -
      cbn* in COMPILE; simp.
      unfold denote_expr, option_bind in *; cbn*; simp.
      2 : apply failure_expr_throw in NOFAIL; contradiction.
      rewrite interp_expr_Ret.
      rewrite denote_code_nil.
      vred.
      apply eutt_Ret; split; [ | split]; cbn; eauto.
      intros.
      unfold id in *; cbn* in *.
      destruct PRE as [MEM WF]; unfold memory_invariant in MEM.
      specialize (MEM _ _ _ Heqo0 Heqo).
      unfold equivalent_values in MEM.
      specialize (MEM l' H H0).
      assumption.
    -
      cbn* in *; simp.
      rename s1 into pre_state, c0 into mid_state, c2 into post_state.
      rename e0 into res_e1, e3 into res_e2, c1 into code_e1, c3 into code_e2.
      rename Heqs into COMPILE_e1, Heqs0 into COMPILE_e2, e into op'.
      vred.

      specialize (IHe1 γ _ _ _ _ cogent_mem g l vellvm_mem COMPILE_e1).
      forward IHe1; auto.
      forward IHe1.
      eapply no_failure_expr_bind_prefix; exact NOFAIL.
      rewrite interp_expr_bind.
      eapply eutt_clo_bind_returns ; [eassumption | clear IHe1].
      introR; destruct_unit.
      intros RET _; eapply no_failure_expr_bind_continuation in NOFAIL; [|eassumption]; clear RET.
      cbn in PRE0.
      destruct PRE0 as (PRE1 & [EXP1]).
      cbn in *.

      specialize (IHe2 γ _ _ _ _ memC g0 l0 memV COMPILE_e2).
      forward IHe2; auto.
      forward IHe2.
      eapply no_failure_expr_bind_prefix; exact NOFAIL.
      rewrite interp_expr_bind.
      vred.
      eapply eutt_clo_bind_returns ; [eassumption | clear IHe2].
      introR; destruct_unit.
      intros RET _; eapply no_failure_expr_bind_continuation in NOFAIL; [| eassumption];  clear RET.
      destruct PRE0 as (PRE2 & [EXP2]).
      cbn* in *.

      specialize (EXP1 l1).
      specialize (EXP2 l1).
      forward EXP2.
      red; reflexivity.
      forward EXP2.
      red; reflexivity.
      forward EXP1.
      {
        admit.
      }
      forward EXP1.
      {
        admit.
      }
      admit.
    -
      cbn* in COMPILE; simp.
      unfold denote_expr in *; cbn*.
      rewrite interp_expr_Ret.
      rewrite denote_code_nil.
      vred.
      apply eutt_Ret; split; [ | split]; cbn; eauto.
      intros.
      typ_to_dtyp_simplify.
      unfold denote_exp; cbn.
      go; reflexivity.
    -
      cbn* in COMPILE; simp.
      unfold denote_expr in *; cbn*.
      rewrite interp_expr_Ret.
      rewrite denote_code_nil.
      vred.
      apply eutt_Ret; split; [ | split]; cbn; eauto.
      intros.
      destruct l;
        simpl;
        typ_to_dtyp_simplify;
        unfold denote_exp; cbn;
        go; reflexivity.
    - 
      cbn* in *; simp.
      rename s1 into pre_state, c0 into mid_state, s2 into post_state.
      rename Heqs into COMPILE_e1, Heqs0 into COMPILE_e2.
      vred.

      specialize (IHe1 γ _ _ _ _ cogent_mem g l vellvm_mem COMPILE_e1).
      forward IHe1; auto.
      forward IHe1.
      eapply no_failure_expr_bind_prefix; exact NOFAIL.
      rewrite interp_expr_bind.

      (* might not need the following 3 *)
      eapply eutt_clo_bind_returns ; [eassumption | clear IHe1].
      introR; destruct_unit.
      intros RET1 _; eapply no_failure_expr_bind_continuation in NOFAIL; [| eassumption]; clear RET1.
      cbn in PRE0.
      destruct PRE0 as (PRE1 & [EXP1]).
      cbn in *.

      specialize (IHe2 (vC :: γ) _ _ _ _ memC g0 l0 memV COMPILE_e2).
      forward IHe2.
      apply state_invariant_new_var; auto.
      unfold equivalent_values.
      intros.
      specialize (EXP1 l').
      
      
      
      
      
      
      
      
      

      

      

      
      
  Admitted.

End Expressions.

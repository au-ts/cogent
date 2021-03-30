From Checker Require Import Cogent Compiler Denotation HelixLib.Correctness_Prelude HelixLib.LidBound.

From Vellvm Require Import DynamicValues.

Set Implicit Arguments.
Set Strict Implicit.

Import ListNotations.
Import AlistNotations.

Notation memoryC := Denotation.memory.

(* Based on Helix's LLVMGen.Correctness_Invariants.v *)
Section HelixInvariantUtils.

  Definition WF_IRState (γ : ctx) (s : IRState) : Prop :=
    True.
    (* evalContext_typechecks σ (Γ s). *)

  (* Predicate stating that an (llvm) local variable is relevant to the memory invariant *)
  Variant in_Gamma : ctx -> IRState -> raw_id -> Prop :=
  | mk_in_Gamma : forall σ s id τ n v,
      nth_error σ n ≡ Some v ->
      nth_error (Γ s) n ≡ Some (τ, EXP_Ident (ID_Local id)) ->
      WF_IRState σ s ->
      in_Gamma σ s id.

  (* Given an initial local env [l1] that reduced to [l2], and a range given by [s1;s2], ensures
  that all modified variables came from this range *)
  Definition local_scope_modif (s1 s2 : IRState) (l1 : local_env) : local_env -> Prop :=
    fun l2 =>
      forall id,
        alist_find id l2 <> alist_find id l1 ->
        lid_bound_between s1 s2 id.
  
  (* Given an initial local env [l1] that reduced to [l2], and a range given by [s1;s2], ensures
  that this range has been left untouched *)
  Definition local_scope_preserved (s1 s2 : IRState) (l1 : local_env) : local_env -> Prop :=
    fun l2 => forall id,
        lid_bound_between s1 s2 id ->
        l2 @ id ≡ l1 @ id.

  (* Given an initial local env [l1] that reduced to [l2], ensures that no variable relevant to the memory invariant has been modified *)
  Definition Gamma_preserved γ s (l1 l2 : local_env) : Prop :=
    forall id,
      in_Gamma γ s id ->
      l1 @ id ≡ l2 @ id.

  (* If no change has been made, all changes are certainly in the interval *)
  Lemma local_scope_modif_refl: forall s1 s2 l, local_scope_modif s1 s2 l l.
  Admitted.

  (* If all changes made are in the empty interval, then no change has been made *)
  Lemma local_scope_modif_empty_scope:
    forall (l1 l2 : local_env) id s,
      local_scope_modif s s l1 l2 ->
      l2 @ id ≡ l1 @ id.
  Admitted.

End HelixInvariantUtils.

(* Based on some more stuff in Helix's Correctness_Prelude.v *)
Section HelixRelations.

  Local Open Scope type_scope.

  Definition config_cogent := memoryC.
  Definition config_cogent_O := option memoryC.

  Definition config_cogent_T (T : Type) := memoryC * T.
  Definition config_cogent_OT (T : Type) := option (memoryC * T).

  Definition Rel_cfg : Type := config_cogent -> config_cfg -> Prop.
  Definition Rel_cfg_T (A B : Type) : Type := config_cogent_T A -> config_cfg_T B -> Prop.
  Definition Rel_cfg_OT (A B : Type) : Type := config_cogent_OT A -> config_cfg_T B -> Prop.

  Definition lift_Rel_cfg {A B} (R : Rel_cfg) : Rel_cfg_T A B :=
    fun '(c_mem, _) '(v_mem, (l, (g, _))) => R c_mem (v_mem, (l, g)).

  Definition succ_rel_l {A B} (R : A -> B -> Prop) : option A -> B -> Prop :=
    fun ma b => match ma with | Some a => R a b | _ => False end.
  Definition succ_cfg {A B}: Rel_cfg_T A B -> Rel_cfg_OT A B := succ_rel_l.

  Definition conj_rel {A B : Type} (R S: A -> B -> Prop): A -> B -> Prop :=
    fun a b => R a b /\ S a b.

End HelixRelations.

Coercion succ_cfg : Rel_cfg_T >-> Rel_cfg_OT.

Section ValueRelation.

  Definition convert_uval (u : uval) : uvalue :=
    match u with
    | UPrim (LBool b) => UVALUE_I1 (Int1.repr (if b then 1 else 0))
    | UPrim (LU8 w) => UVALUE_I8 (Int8.repr w)
    | UPrim (LU32 w) => UVALUE_I32 (Int32.repr w)
    | UPrim (LU64 w) => UVALUE_I64 (Int64.repr w)
    | UUnit => UVALUE_I8 (Int8.repr 0)
    | UPtr a r => UVALUE_Addr a
    (* TODO: aggregate conversion *)
    | URecord us => UVALUE_I8 (Int8.repr 0)
    end.

  Definition correct_result (γ : ctx) (s1 s2 : IRState) (u : uval) (i : im) : config_cfg -> Prop :=
    fun '(memV, (l, g)) =>
      forall l',
        local_scope_preserved s1 s2 l l' ->
        Gamma_preserved γ s1 l l' ->
        interp_cfg
          (translate exp_to_instr (denote_exp (Some (typ_to_dtyp [] (fst i))) (convert_typ [] (snd i))))
          g l' memV ≈
          Ret (memV, (l', (g, convert_uval u))).

  (* correct means: does i evaluate to something equivalent to u *)
  Definition correct_result_T {T} (γ : ctx) (s1 s2 : IRState) (i : im) : Rel_cfg_T uval T :=
    fun '(_, u) '(memV, (l, (g, _))) => correct_result γ s1 s2 u i (memV, (l, g)).

End ValueRelation.

Section Memory.

  Definition memory_invariant (γ : ctx) (s : IRState) (cogent : config_cogent)
                              (vellvm : state_cfg) : Prop :=
    forall (n : nat) (i : im) (u : uval),
      nth_error γ n ≡ Some u ->
      nth_error (Γ s) n ≡ Some i ->
      correct_result γ s s u i vellvm.

End Memory.

Section State.

  Record state_invariant (γ : ctx) (s : IRState) (cogent : config_cogent) (vellvm : config_cfg) : Prop :=
  { mem_is_inv : memory_invariant γ s cogent vellvm
  ; IRState_is_WF : WF_IRState γ s
  }.

  Lemma state_invariant_new_block :
    forall (γ : ctx) (s : IRState) (cogent : config_cogent) (vellvm : config_cfg),
      let s' := {|
        block_count := S (block_count s)
      ; local_count := local_count s
      ; void_count := void_count s
      ; Γ := Γ s |} in
        state_invariant γ s cogent vellvm -> state_invariant γ s' cogent vellvm.
  Proof.
    intros * PRE.
    destruct PRE as [MEM WF].
    split.
    unfold memory_invariant in *.
    cbn in *.
    intros.
    specialize (MEM _ _ _ H H0).
    unfold correct_result in *.
    simp.
    intros.
  Admitted.

End State.

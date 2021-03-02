(*
Definition corres := 
  ((funtyp, abstyp, ptrtyp) store \<times> 's) set \<Rightarrow> (* state relation between cogent and C states*)
  (* convert to function to bool rather than set *)
   funtyp expr \<Rightarrow>                          (* cogent program *)
   ('s,('a::cogent_C_val)) nondet_monad \<Rightarrow> (* monadic autocorres embedding of C program *)
(*
   (funtyp, abstyp, ptrtyp) uabsfuns \<Rightarrow>    (* value environment for abstract functions *)
*)
   (funtyp, abstyp, ptrtyp) uval env \<Rightarrow>    (* value environment for cogent functions *)
(*
   (funtyp \<Rightarrow> poly_type) \<Rightarrow>     (* type environment for abstract functions *)
   ctx \<Rightarrow>                                  (* type environment for cogent functions *)
*)
   (funtyp, abstyp, ptrtyp) store \<Rightarrow>       (* cogent store *)
   's \<Rightarrow>                                   (* C store *)
   bool                                               (* whether refinement holds or not *)
where
  corres srel c m \<gamma> \<sigma> s \<equiv>
    proc_ctx_wellformed \<Xi> \<longrightarrow> \<xi> matches-u \<Xi> \<longrightarrow> (\<sigma>,s) \<in> srel \<longrightarrow>
   (\<exists>r w. \<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>) \<longrightarrow>
   (\<not> snd (m s) \<and>
   (\<forall>r' s'. (r',s') \<in> fst (m s) \<longrightarrow>
     (\<exists>\<sigma>' r.(\<xi>, \<gamma> \<turnstile> (\<sigma>,c)  \<Down>! (\<sigma>',r)) \<and> (\<sigma>',s') \<in> srel \<and> val_rel r r')))
.
*)

From Coq Require Import List String.

From Checker Require Import Denote.

From ITree Require Import ITree ITreeFacts.

From Vellvm Require Import LLVMAst LLVMEvents TopLevel Handlers InterpreterMCFG TopLevelRefinements DynamicTypes
  CFG TypToDtyp InterpretationStack.

Import ListNotations.


Definition vellvm_prog : Type := list (toplevel_entity typ (block typ * list (block typ))).

(* Lifted from Helix *)
Definition E_mcfg : Type -> Type := (ExternalCallE +' PickE +' UBE +' DebugE +' FailureE).
Definition E_cfg : Type -> Type := (CallE +' PickE +' UBE +' DebugE +' FailureE). 
Definition semantics_llvm_mcfg p : itree E_mcfg _ := model_to_L3 DTYPE_Void "main" main_args p.
Definition semantics_llvm (prog: list (toplevel_entity typ (LLVMAst.block typ * list (LLVMAst.block typ)))) :=
  semantics_llvm_mcfg (convert_types (mcfg_of_tle prog)).

Definition vellvm_env : Type := memory_stack * (local_env * global_env).
Definition interp_vellvm (t:itree L0 uvalue) (e:vellvm_env) : itree L3 res_L3 :=
  interp_mcfg3 t (snd (snd e)) (fst (snd e), []) (fst e).

Definition relate_env (c_env : vars) (v_env: vellvm_env) : Prop := True.

Section AB.

  Context {A B : Type}.  

  Definition  state_invariant (a: vars * A) (b: vellvm_env * uvalue) : Prop := 
    relate_env (fst a) (fst b).

  Definition bisimilar (t1: itree VarE A) (t2: itree L0 uvalue) := 
    forall c_env v_env,
      relate_env c_env v_env ->
        eutt state_invariant (interp_cogent t1 c_env) (interp_vellvm t2 v_env).

End AB.

Definition equivalent (c:cogent_prog) (l:vellvm_prog) : Prop :=
   bisimilar (denote_cogent c) (denote_vellvm l).

Theorem compile_correct (c:cogent_prog) : equivalent c (compile_cogent c).

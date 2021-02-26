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

From ITree Require Import ITree Simple.
From Vellvm Require Import LLVMAst LLVMEvents TopLevel Handlers.Handlers InterpreterMCFG TopLevelRefinements DynamicTypes.

Import ListNotations.


Definition vellvm_prog : Type := list (toplevel_entity typ (block typ * list (block typ))).
Definition denote_vellvm (l:vellvm_prog) : itree L0 uvalue :=
  denote_vellvm_main (mcfg_of_tle l).
Definition vellvm_env : Type := memory_stack * (local_env * global_env).
Definition interp_vellvm (t:itree L0 uvalue) (e:vellvm_env) : itree L3 res_L3 :=
  interp_to_L3 [] t (snd (snd e)) (fst (snd e), []) (fst e).

Definition relate_env (c_env : env) (v_env: vellvm_env) : Prop := True.

Section AB.

  Context {A B : Type}.  

  Definition  state_invariant (a: env * A) (b: vellvm_env * uvalue) : Prop := 
    relate_env (fst a) (fst b).

  Definition bisimilar (t1: itree CogentState A) (t2: itree L0 uvalue) := 
    forall c_env v_env,
      relate_env c_env v_env ->
        eutt (interp_cogent t1 c_env) (interp_vellvm t2 v_env).

End AB.

Definition equivalent (c:cogent_prog) (l:vellvm_prog) : Prop :=
   bisimilar (denote_cogent c) (denote_vellvm l).

Theorem compile_correct (c:cogent_prog) : equivalent c (compile_cogent c).

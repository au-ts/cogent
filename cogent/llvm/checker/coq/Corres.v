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

From Checker Require Import Denote.

Definition vellvm_env := Cogent.env. (* TODO: replace with actual vellvm environment *)
Definition vellvm_eff := eff. (* TODO: replace with actual vellvm effects *)


Definition  relate_env (c_env : env) (v_env: vellvm_env) : Prop := True.

Definition  state_invariant (a: env * unit) (b: vellvm_env *) : Prop := 
  relate_env (fst a) (fst b).

Definition bisimilar (t1: itree eff unit) (t2: itree vellvm_eff unit) := 
  forall c_env v_env,
    relate_env c_env v_env ->
      eutt state_invariant
        (interp_cogent t1 c_env)
        (interp_cogent t2 v_env).




Definition equivalent (c:cogent) (l:vellvm) : Prop :=
   bisimilar (denote_cogent c) (denote_llvm l).


Theorem compile_correct (p: cogent) : equivalent p (compile p).
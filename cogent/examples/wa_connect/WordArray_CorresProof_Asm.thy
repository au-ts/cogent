(*
  This file contains the provable assumptions which are required when proving correspondence of
  word array functions.
*)
theory WordArray_CorresProof_Asm
  imports WordArray_Abstractions
begin

context WordArray begin

section "Level 0 Assumptions"

lemma val_wa_length_rename_monoexpr_correct:
  "\<lbrakk>val_wa_length (val.rename_val rename' (val.monoval v)) v'; val.proc_env_matches \<xi>\<^sub>v \<Xi>'; proc_ctx_wellformed \<Xi>'\<rbrakk>
    \<Longrightarrow> v' = val.rename_val rename' (val.monoval v') \<and> val_wa_length v v'"
  apply (clarsimp simp: val_wa_length_def)
  apply (case_tac v; clarsimp)
  done

lemma val_wa_get_rename_monoexpr_correct:
  "\<lbrakk>val_wa_get (val.rename_val rename' (val.monoval v)) v'; val.proc_env_matches \<xi>\<^sub>v \<Xi>'; proc_ctx_wellformed \<Xi>'\<rbrakk>
    \<Longrightarrow> v' = val.rename_val rename' (val.monoval v') \<and> val_wa_get v v'"
  apply (clarsimp simp: val_wa_get_def)
  apply (case_tac v; clarsimp)
  apply (case_tac z; clarsimp)
  apply (case_tac za; clarsimp)
  done

lemma val_wa_put2_rename_monoexpr_correct:
  "\<lbrakk>val_wa_put2 (val.rename_val rename' (val.monoval v)) v'; val.proc_env_matches \<xi>\<^sub>v \<Xi>'; proc_ctx_wellformed \<Xi>'\<rbrakk>
    \<Longrightarrow> v' = val.rename_val rename' (val.monoval v') \<and> val_wa_put2 v v'"
  apply (clarsimp simp: val_wa_put2_def)
  apply (case_tac v; clarsimp)
  apply (case_tac z; clarsimp)
  apply (case_tac za; clarsimp)
  apply (case_tac zb; clarsimp)
  done


lemma value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p: 
  "value_sem.rename_mono_prog wa_abs_typing_v rename \<Xi> \<xi>m \<xi>p"
  apply (clarsimp simp: val.rename_mono_prog_def)
  apply (rule conjI; clarsimp)
   apply (rule_tac x = v' in exI)
   apply (subst (asm) rename_def)
   apply (subst (asm) assoc_lookup.simps)+
   apply (clarsimp split: if_split_asm)
  apply (clarsimp simp: val_wa_length_rename_monoexpr_correct)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x = v' in exI)
   apply (subst (asm) rename_def)
   apply (subst (asm) assoc_lookup.simps)+
   apply (clarsimp split: if_split_asm)
  apply (clarsimp simp: val_wa_get_rename_monoexpr_correct)
  apply clarsimp
  apply (rule_tac x = v' in exI)
  apply (subst (asm) rename_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
  apply (clarsimp simp: val_wa_put2_rename_monoexpr_correct)
  done

lemma val_wa_get_preservation:
  "\<lbrakk>val.vval_typing \<Xi>' v (TRecord [(a, TCon ''WordArray'' [t] (Boxed ReadOnly ptrl), Present),
      (b, TPrim (Num U32), Present)] Unboxed); val_wa_get v v'\<rbrakk>
    \<Longrightarrow> val.vval_typing \<Xi>' v' t"
  apply (clarsimp simp: val_wa_get_def)
  apply (erule val.v_t_recordE; clarsimp)
  apply (erule val.v_t_r_consE; clarsimp)+
  apply (erule val.v_t_abstractE; clarsimp simp: wa_abs_typing_v_def)
  apply (rule val.v_t_prim'; clarsimp)
  done

lemma val_wa_length_preservation:
  "\<lbrakk>val.vval_typing \<Xi>' v (TCon ''WordArray'' [t] (Boxed ReadOnly ptrl)); val_wa_length v v'\<rbrakk>
    \<Longrightarrow> val.vval_typing \<Xi>' v' (TPrim (Num U32))"
  apply (clarsimp simp:  val_wa_length_def)
  apply (rule val.v_t_prim'; clarsimp)
  done

lemma val_wa_put2_preservation:
  "\<lbrakk>val.vval_typing \<Xi>' v (TRecord [(a, TCon ''WordArray'' [t] (Boxed Writable ptrl), Present),
      (b', TPrim (Num U32), Present), (c, t, Present)] Unboxed); val_wa_put2 v v'\<rbrakk>
    \<Longrightarrow> val.vval_typing \<Xi>' v' (TCon ''WordArray'' [t] (Boxed Writable ptrl))"
  apply (clarsimp simp: val_wa_put2_def)
  apply (erule val.v_t_recordE)
  apply (erule val.v_t_r_consE; clarsimp)
  apply (erule val.v_t_abstractE)
  apply (rule val.v_t_abstract; clarsimp)
  apply (clarsimp simp: wa_abs_typing_v_def)
  apply (case_tac "i = unat idx"; clarsimp)
  done

lemma val_proc_env_matches_\<xi>m_\<Xi>:
  "val.proc_env_matches \<xi>m \<Xi>"
  apply (clarsimp simp: val.proc_env_matches_def)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
    apply (clarsimp simp: wordarray_get_0_type_def abbreviatedType3_def)
    apply (drule val_wa_get_preservation; simp?)
   apply (clarsimp simp: wordarray_length_0_type_def)
  apply (drule val_wa_length_preservation; simp?)
  apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType2_def)
  apply (drule val_wa_put2_preservation; simp?)
  done

lemma wa_get_upd_val:
  "\<lbrakk>upd_val_rel \<Xi>' \<sigma> au av (TRecord [(a, TCon ''WordArray'' [t] (Boxed ReadOnly ptrl), Present),
      (b, TPrim (Num U32), Present)] Unboxed) r w; upd_wa_get_0 (\<sigma>, au) (\<sigma>', v)\<rbrakk>
    \<Longrightarrow> (val_wa_get av v' \<longrightarrow> (\<exists>r' w'. upd_val_rel \<Xi>' \<sigma>' v v' t r' w' \<and> r' \<subseteq> r \<and> 
      frame \<sigma> w \<sigma>' w')) \<and> Ex (val_wa_get av)"
 apply (clarsimp simp: upd_wa_get_0_def)
  apply (erule u_v_recE'; clarsimp)
  apply (erule u_v_r_consE'; clarsimp)
  apply (erule u_v_p_absE'[where s = "Boxed ReadOnly _", simplified])
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule u_v_r_emptyE'; clarsimp)
  apply (erule u_v_primE')+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: val_wa_get_def)
   apply (rule_tac x = "{}" in exI)+
   apply (clarsimp simp: wa_abs_upd_val_def frame_def word_less_nat_alt)
   apply (case_tac "unat idx < length xs"; clarsimp)
    apply (erule_tac x = idx in allE; clarsimp)
    apply (rule u_v_prim'; clarsimp)
   apply (rule u_v_prim'; clarsimp)
  apply (clarsimp simp: word_less_nat_alt wa_abs_upd_val_def)
  apply (case_tac a'; clarsimp)
  apply (case_tac x11; clarsimp)
  apply (case_tac x5; clarsimp)
  apply (case_tac "unat idx < length x12"; clarsimp simp: word_less_nat_alt)
   apply (erule_tac x = idx in allE; clarsimp)
   apply (rule_tac x = "VPrim x" in exI)
   apply (clarsimp simp: val_wa_get_def)
  apply (rule_tac x = "VPrim (zero_num_lit ta)" in exI)
  apply (clarsimp simp: val_wa_get_def)
  apply (case_tac ta; clarsimp)
  done

lemma wa_length_upd_val:
  "\<lbrakk>upd_val_rel \<Xi>' \<sigma> au av (TCon ''WordArray'' [t] (Boxed ReadOnly ptrl)) r w;
    upd_wa_length_0 (\<sigma>, au) (\<sigma>', v)\<rbrakk>
    \<Longrightarrow> (val_wa_length av v' \<longrightarrow> (\<exists>r' w'. upd_val_rel \<Xi>' \<sigma>' v v' (TPrim (Num U32)) r' w' \<and> r' \<subseteq> r \<and> 
      frame \<sigma> w \<sigma>' w')) \<and> Ex (val_wa_length av)"
  apply (clarsimp simp: upd_wa_length_0_def)
  apply (erule u_v_p_absE'; clarsimp)
  apply (clarsimp simp: wa_abs_upd_val_def)
  apply (case_tac a'; clarsimp)
  apply (case_tac x11; clarsimp)
  apply (case_tac x5; clarsimp)
  apply (rule conjI)
   apply (clarsimp simp: val_wa_length_def)
   apply (rule_tac x = "{}" in exI)+
   apply (clarsimp simp: frame_def)
   apply (rule u_v_prim'; clarsimp)
  apply (rule_tac x = "VPrim (LU32 len)" in exI)
  apply (clarsimp simp: val_wa_length_def)
  done

inductive_cases u_v_t_prim_tE : "upd_val_rel \<Xi>' \<sigma> u v (TPrim l) r w"

lemma wa_put2_upd_val:
  "\<lbrakk>upd_val_rel \<Xi>' \<sigma> au av (TRecord [(a, TCon ''WordArray'' [t] (Boxed Writable ptrl), Present),
      (b, TPrim (Num U32), Present), (c, t, Present)] Unboxed) r w; upd_wa_put2_0 (\<sigma>, au) (\<sigma>', v)\<rbrakk>
    \<Longrightarrow> (val_wa_put2 av v' \<longrightarrow> 
        (\<exists>r' w'. upd_val_rel \<Xi>' \<sigma>' v v' (TCon ''WordArray'' [t] (Boxed Writable ptrl)) r' w' \<and>
         r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w')) \<and>
      Ex (val_wa_put2 av)"
 apply (clarsimp simp: upd_wa_put2_0_def)
  apply (erule u_v_recE'; clarsimp)
  apply (erule u_v_r_consE'; clarsimp)
  apply (erule u_v_p_absE'[where s = "Boxed Writable _", simplified])
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule u_v_r_emptyE')
  apply (erule u_v_primE')+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (erule type_repr.elims[where y = " RPrim _", simplified]; clarsimp)
  apply (erule u_v_t_prim_tE)
  apply (rule conjI)
   apply clarsimp
   apply (clarsimp simp: val_wa_put2_def)
   apply (rule_tac x = r in exI)
   apply (rule_tac x = "insert p wa" in exI)
   apply clarsimp
   apply (rule conjI)
    apply (rule_tac a = aa and ptrl = ptrl in u_v_p_abs_w[where ts = "[TPrim _]", simplified]; simp?)
     apply (clarsimp simp: wa_abs_upd_val_def)
     apply (case_tac aa; clarsimp)
     apply (case_tac x11; clarsimp)
     apply (case_tac x5; clarsimp)
     apply (rule conjI)
      apply (clarsimp simp: wa_abs_typing_u_def)
     apply (rule conjI)
      apply (clarsimp simp: wa_abs_typing_v_def)
      apply (erule_tac x = i in allE; clarsimp)+
      apply (case_tac "i = unat idx"; clarsimp)
     apply clarsimp
     apply (rule conjI; clarsimp)
      apply (drule distinct_indices)
      apply (erule_tac x = i in allE)+
      apply clarsimp
      apply (erule_tac x = idx in allE)
      apply (clarsimp simp: word_less_nat_alt)
     apply (erule_tac x = i in allE)
     apply clarsimp
     apply (case_tac "unat i = unat idx"; clarsimp simp: wa_abs_typing_u_def)
    apply (clarsimp simp: wa_abs_upd_val_def)
    apply (erule_tac x = idx in allE)
    apply clarsimp
   apply (clarsimp simp: frame_def wa_abs_upd_val_def wa_abs_typing_u_def)
   apply (case_tac aa; clarsimp)
   apply (case_tac x11; clarsimp)
   apply (case_tac x5; clarsimp)
   apply (rule conjI; clarsimp)
    apply (rule conjI)
     apply clarsimp
    apply (rule conjI; clarsimp)
   apply (rule conjI; clarsimp)
  apply clarsimp
  apply (clarsimp simp: wa_abs_upd_val_def)
  apply (case_tac aa; clarsimp simp: wa_abs_typing_u_def)
  apply (case_tac x11; clarsimp)
  apply (case_tac x5; clarsimp)
  apply (case_tac a'; clarsimp)
  apply (case_tac x11; clarsimp)
  apply (case_tac x5; clarsimp)
  apply (rule_tac x = "VAbstract (VWA t (x12a[unat idx := VPrim l]))" in exI)
  apply (clarsimp simp: val_wa_put2_def)
  done

lemma proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>:
  "proc_env_u_v_matches \<xi>0 \<xi>m \<Xi>"
  apply (clarsimp simp: proc_env_u_v_matches_def)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
    apply (clarsimp simp: wordarray_get_0_type_def abbreviatedType3_def)
    apply (drule wa_get_upd_val; simp)
   apply (clarsimp simp: wordarray_length_0_type_def)
   apply (drule wa_length_upd_val; simp)
  apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType2_def)
  apply (drule wa_put2_upd_val; simp)
  done

lemma upd_wa_get_preservation:
  "\<lbrakk>upd.uval_typing \<Xi>' \<sigma> v (TRecord [(a, TCon ''WordArray'' [t] (Boxed ReadOnly ptrl), Present),
      (b, TPrim (Num U32), Present)] Unboxed) r w; upd_wa_get_0 (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi>' \<sigma>' v' t r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
 apply (clarsimp simp:  upd_wa_get_0_def)
  apply (erule upd.u_t_recE; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_p_absE[where s = "Boxed ReadOnly _", simplified])
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)+
  apply (erule upd.u_t_r_emptyE; clarsimp)
  apply (erule upd.u_t_primE; subst (asm) lit_type.simps; clarsimp)+
  apply (rule_tac x = "{}" in exI)+
  apply (clarsimp simp: frame_def wa_abs_typing_u_def)
  apply (erule_tac x = idx in allE)
  apply (case_tac "idx < len"; clarsimp)
   apply (rule upd.u_t_prim'; clarsimp)+
  apply (case_tac ta; clarsimp intro!: upd.u_t_prim')
  done

lemma upd_wa_length_preservation:
  "\<lbrakk>upd.uval_typing \<Xi>' \<sigma> v (TCon ''WordArray'' [t] (Boxed ReadOnly ptrl)) r w;
    upd_wa_length_0 (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi>' \<sigma>' v' (TPrim (Num U32)) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: upd_wa_length_0_def)
  apply (erule upd.u_t_p_absE; clarsimp)
  apply (rule_tac x = "{}" in exI)+
  apply (clarsimp simp: frame_def intro!: upd.u_t_prim')
  done

inductive_cases upd_u_t_prim_tE: "upd.uval_typing \<Xi>' \<sigma> u (TPrim l) r w"

lemma upd_wa_put2_preservation:
  "\<lbrakk>upd.uval_typing \<Xi>' \<sigma> v (TRecord [(a, TCon ''WordArray'' [t] (Boxed Writable ptrl), Present),
      (b, TPrim (Num U32), Present), (c, t, Present)] Unboxed) r w; upd_wa_put2_0 (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi>' \<sigma>' v' (TCon ''WordArray'' [t] (Boxed Writable ptrl)) r' w' \<and>
      r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: upd_wa_put2_0_def)
  apply (erule upd.u_t_recE; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_p_absE[where s = "Boxed Writable _", simplified])
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (subst (asm) type_repr.simps[symmetric])+
  apply clarsimp
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (subst (asm) type_repr.simps[symmetric])+
  apply clarsimp
  apply (erule upd.u_t_r_emptyE)
  apply (erule upd.u_t_primE)+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (drule_tac t = "type_repr _" in sym)+
  apply (erule type_repr.elims[where y = "RPrim _", simplified]; clarsimp)
  apply (erule upd_u_t_prim_tE; clarsimp)
  apply (rule_tac x = r in exI)
  apply (rule_tac x = "insert p wa" in exI)
  apply (rule conjI)
   apply (rule_tac ptrl = ptrl and a = aa in upd.u_t_p_abs_w[where ts = "[TPrim _]", simplified])
      apply simp
     apply (clarsimp simp: wa_abs_typing_u_def)
     apply (case_tac aa; clarsimp)
     apply (case_tac x11; clarsimp)
     apply (case_tac x5; clarsimp)
    apply (drule_tac t = "lit_type _" in sym)+
    apply (clarsimp simp: wa_abs_typing_u_def)
   apply clarsimp
  apply (clarsimp simp: frame_def wa_abs_typing_u_def)
  apply (case_tac aa; clarsimp)
  apply (case_tac x11; clarsimp)
  apply (case_tac x5; clarsimp)
  apply (rule conjI; clarsimp)
   apply (rule conjI)
    apply (erule_tac x = idx in allE; clarsimp)+
   apply (rule conjI; clarsimp)
  apply (rule conjI; clarsimp)
  done

lemma upd_proc_env_matches_ptrs_\<xi>0_\<Xi>:
  "upd.proc_env_matches_ptrs \<xi>0 \<Xi>"
  apply (unfold upd.proc_env_matches_ptrs_def)
  apply clarsimp
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
    apply (clarsimp simp: wordarray_get_0_type_def abbreviatedType3_def)
    apply (drule upd_wa_get_preservation; simp?)
   apply (clarsimp simp: wordarray_length_0_type_def)
  apply (drule upd_wa_length_preservation; simp)
  apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType2_def)
  apply (drule upd_wa_put2_preservation; simp)
  done

lemma proc_ctx_wellformed_\<Xi>:
  "proc_ctx_wellformed \<Xi>"
  apply (clarsimp simp: proc_ctx_wellformed_def \<Xi>_def)
  apply (clarsimp split: if_splits
                  simp: assoc_lookup.simps
                        wordarray_get_0_type_def abbreviatedType3_def wordarray_get_u32_type_def
                        wordarray_length_0_type_def wordarray_length_u32_type_def
                        wordarray_put2_0_type_def abbreviatedType2_def wordarray_put2_u32_type_def
                        wordarray_fold_no_break_0_type_def abbreviatedType1_def
                        sum_type_def sum_arr_type_def
                        mul_type_def mul_arr_type_def)
  done

section "Level 1 Assumptions"

lemma upd_wa_foldnb_bod_preservation:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; upd.proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
    upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv (rb \<union> rc) (\<sigma>', res);
    \<sigma> p = option.Some (UAbstract (UWA t len arr)); 
    wa_abs_typing_u (UWA t len arr) ''WordArray'' [t] (Boxed ReadOnly ptrl) ra wa \<sigma>;
    upd.uval_typing \<Xi>' \<sigma> acc u rb wb; upd.uval_typing \<Xi>' \<sigma> obsv v rc {};  wb \<inter> rc = {};
    \<Xi>', [], [option.Some (TRecord [
      (b0, t, Present), (b1, u, Present), (b2, v, Present)] Unboxed)] \<turnstile> (App f (Var 0)) : u;
    distinct [b0, b1, b2]\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi>' \<sigma>' res u r' w' \<and> r' \<subseteq> (ra \<union> rb \<union> rc) \<and> frame \<sigma> wb \<sigma>' w'"
  apply (induct to arbitrary: \<sigma>' res)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
   apply (rule_tac x = rb in exI)
   apply (rule_tac x = wb in exI)
   apply (clarsimp simp: frame_def)
  apply (case_tac "len < 1 + to")
   apply (drule upd_wa_foldnb_bod_back_step'; simp?)
  apply (case_tac "1 + to \<le> frm")
   apply (frule_tac y = "1 + to" and x = frm in leD)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
   apply (rule_tac x = rb in exI)
   apply (rule_tac x = wb in exI)
   apply (clarsimp simp: frame_def)
  apply (case_tac "frm = to")
   apply (clarsimp simp: not_le not_less)
   apply (frule_tac z = len in less_le_trans, simp)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp simp: add.commute)
   apply (drule_tac ?\<Gamma> = "[option.Some (TRecord [(b0, TPrim (Num ta), Present), (b1, u, Present),
    (b2, v, Present)] Unboxed)]" and r = "rb \<union> rc" and  w = wb and \<tau> = u in upd.preservation_mono(1); simp?)
    apply (rule upd.matches_ptrs_some[where ts = "[]" and r' = "{}" and w' = "{}", simplified])
     apply (rule upd.u_t_struct; simp?)
     apply (rule upd.u_t_r_cons1[where r = "{}" and w = "{}", simplified])
       apply (clarsimp simp: wa_abs_typing_u_def)
       apply (erule_tac x = frm in allE; clarsimp)+
       apply (rule upd.u_t_prim'; clarsimp)
      apply (rule upd.u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
       apply (rule upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
        apply (rule upd.u_t_r_empty)
       apply (drule_tac v = obsv in upd.type_repr_uval_repr(1); simp)
      apply (drule_tac v = acc in upd.type_repr_uval_repr(1); simp)
     apply (clarsimp simp: wa_abs_typing_u_def)
     apply (erule_tac x = frm in allE; clarsimp)+
    apply (rule upd.matches_ptrs_empty[where \<tau>s = "[]", simplified])
   apply blast
  apply (clarsimp simp: wa_abs_typing_u_def)
  apply (case_tac t; clarsimp)
  apply (case_tac x5; clarsimp)
  apply (drule upd_wa_foldnb_bod_back_step; simp?)
    apply (metis (no_types, hide_lams) word_le_less_eq word_zero_le)
   apply (metis (full_types) add.commute inc_le word_le_less_eq word_not_le)
  apply clarsimp
  apply (drule_tac x = \<sigma>'' in meta_spec)
  apply (drule_tac x = r'' in meta_spec)
  apply clarsimp
  apply (erule_tac x = to in allE; clarsimp)+
  apply (erule impE)
   apply (cut_tac x = to in word_overflow)
   apply (erule disjE; clarsimp simp: add.commute)
   apply auto[1]
  apply clarsimp
  apply (drule_tac ?\<Gamma> = "[option.Some (TRecord [(b0, TPrim (Num x1), Present), (b1, u, Present),
    (b2, v, Present)] Unboxed)]" and r = "r' \<union> rc" and  w = w' and \<tau> = u in upd.preservation_mono(1); simp?)
   apply (rule upd.matches_ptrs_some[where ts = "[]" and r' = "{}" and w' = "{}", simplified])
    apply (rule upd.u_t_struct; simp?)
    apply (rule upd.u_t_r_cons1[where r = "{}" and w = "{}", simplified])
      apply (rule upd.u_t_prim'; clarsimp)
     apply (rule upd.u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
       apply (rule upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
         apply (rule upd.uval_typing_frame(1); simp?)
         apply (rule disjointI)
         apply (clarsimp simp: frame_def)
         apply (erule_tac x = y in allE; clarsimp)
         apply (drule_tac x = y in orthD1; simp)
        apply (rule upd.u_t_r_empty)
       apply (drule_tac v = obsv in upd.type_repr_uval_repr(1); simp)
      apply (rule disjointI)
      apply (thin_tac "frame _ _ _ _")
      apply (clarsimp simp: frame_def)
      apply (erule_tac x = y in allE; clarsimp)+
      apply (drule_tac x = y in orthD2; simp)
      apply (drule_tac u = obsv and p = y in upd.uval_typing_valid(1)[rotated 1]; simp)
     apply (drule_tac v = r'' in upd.type_repr_uval_repr(1); simp)
    apply clarsimp
   apply (rule upd.matches_ptrs_empty[where \<tau>s = "[]", simplified])
  apply clarsimp
  apply (thin_tac "frame _ _ _ _")
  apply (rule_tac x = r'a in exI)
  apply (rule_tac x = w'a in exI)
  apply clarsimp
  apply (rule conjI, blast)
  apply (rule upd.frame_trans; simp)
  done

lemma upd_wa_foldnb_0_preservation:
  "\<And>K a b \<sigma> \<sigma>' \<tau>s v v' r w.
   \<lbrakk>list_all2 (kinding []) \<tau>s K; wordarray_fold_no_break_0_type = (K, a, b);
    upd.uval_typing \<Xi> \<sigma> v (instantiate \<tau>s a) r w; upd_wa_foldnb_0 (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi> \<sigma>' v' (instantiate \<tau>s b) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: wordarray_fold_no_break_0_type_def upd_wa_foldnb_0_def)
  apply (erule upd.u_t_recE; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym; clarsimp)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym; clarsimp)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym; clarsimp)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym; clarsimp)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply clarsimp
  apply (erule upd.u_t_r_emptyE; clarsimp)
  apply (erule upd.u_t_p_absE; clarsimp)
  apply (erule upd.u_t_primE)+
  apply (drule_tac t = "lit_type _" in sym)+
  apply clarsimp
  apply (erule upd.u_t_unitE; clarsimp)
  apply (case_tac xa; clarsimp simp: abbreviatedType1_def)
  apply (erule upd.u_t_functionE; clarsimp)
   apply (drule_tac ra = rg in upd_wa_foldnb_bod_preservation[OF proc_ctx_wellformed_\<Xi> 
        upd_proc_env_matches_ptrs_\<xi>0_\<Xi>, where rb = "{}" and rc = "{}" and 
        ptrl = undefined and wa = "{}" and wb = "{}", simplified]; simp?; clarsimp?)
     apply (rule upd.u_t_prim'; clarsimp)
    apply (rule upd.u_t_unit)
   apply blast
  apply (erule upd.u_t_afunE; clarsimp)
  apply (drule_tac ra = rg in upd_wa_foldnb_bod_preservation[OF proc_ctx_wellformed_\<Xi> 
        upd_proc_env_matches_ptrs_\<xi>0_\<Xi>, where rb = "{}" and rc = "{}" and 
        ptrl = undefined and wa = "{}" and wb = "{}", simplified]; simp?; clarsimp?)
    apply (rule upd.u_t_prim'; clarsimp)
   apply (rule upd.u_t_unit)
  apply blast
  done

inductive_cases v_t_prim_tE : "val.vval_typing \<Xi>' v (TPrim l)"

lemma lit_type_ex:
  "lit_type l = Bool \<Longrightarrow> \<exists>v. l = LBool v"
  "lit_type l = Num U8 \<Longrightarrow> \<exists>v. l = LU8 v"
  "lit_type l = Num U16 \<Longrightarrow> \<exists>v. l = LU16 v"
  "lit_type l = Num U32 \<Longrightarrow> \<exists>v. l = LU32 v"
  "lit_type l = Num U64 \<Longrightarrow> \<exists>v. l = LU64 v"
  apply (induct l; clarsimp)+
  done

lemma 
  "\<lbrakk>val.proc_env_matches \<xi>\<^sub>m \<Xi>'; proc_ctx_wellformed \<Xi>'; 
    val_wa_foldnb_bod \<xi>\<^sub>m xs frm to (Fun (val.rename_expr rename' (val.monoexpr (specialise ts f))) [])
         acc obsv res;
\<forall>i<length xs. \<exists>v. xs ! i = VPrim (LU32 v);
    \<Xi>, [], [option.Some Generated_TypeProof.abbreviatedType1] \<turnstile> App (Fun (val.rename_expr rename 
      (val.monoexpr (specialise ts f))) []) (Var 0) : TPrim (Num U32)
    \<rbrakk>
       \<Longrightarrow> val_wa_foldnb_bod \<xi>\<^sub>p xs frm to (Fun f ts) acc obsv (VPrim (LU32 r))"
  oops

lemma val_wa_foldnb_0_mono_helper1:
  "\<lbrakk>val.proc_env_matches \<xi>m1 \<Xi>; proc_ctx_wellformed \<Xi>; \<forall>i<length xs. \<exists>v. xs ! i = VPrim (LU32 v);
    \<Xi>, [], [option.Some Generated_TypeProof.abbreviatedType1] \<turnstile> App (Fun (val.rename_expr rename 
      (val.monoexpr (specialise ts f))) []) (Var 0) : TPrim (Num U32);
    val_wa_foldnb_bod \<xi>m xs frm to (Fun (val.rename_expr rename (val.monoexpr (specialise ts f))) [])
         (VPrim (LU32 acc)) VUnit (VPrim (LU32 r))\<rbrakk>
       \<Longrightarrow> val_wa_foldnb_bod \<xi>p xs frm to (Fun f ts) (VPrim (LU32 acc)) VUnit (VPrim (LU32 r))"
  apply (induct to arbitrary: r)
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
   apply (subst val_wa_foldnb_bod.simps; clarsimp)
  apply clarsimp
  apply (case_tac "length xs < Suc to")
   apply (erule_tac x = r in meta_allE)
   apply (drule val_wa_foldnb_bod_back_step'; simp)
   apply (drule val_wa_foldnb_bod_to_geq_lenD)
    apply linarith
   apply (rule val_wa_foldnb_bod_to_geq_len; simp)
  apply (clarsimp simp: not_less)
  apply (case_tac "frm \<ge> to")
   apply (erule val_wa_foldnb_bod.elims; clarsimp split: if_splits)
    apply (erule val_wa_foldnb_bod.elims; clarsimp)
    apply (subst val_wa_foldnb_bod.simps; clarsimp)
    apply (subst val_wa_foldnb_bod.simps; clarsimp)
    apply (drule_tac \<gamma> = "[VRecord [xs ! frm, VPrim (LU32 acc), VUnit]]" and
      \<Gamma> = "[option.Some abbreviatedType1]" and
      e = "App (Fun f ts) (Var 0)" and
      v' = "VPrim (LU32 r)" and
      \<tau>  = "TPrim (Num U32)" in val.rename_monoexpr_correct(1)
      [OF _ val_proc_env_matches_\<xi>m_\<Xi> value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p]; clarsimp?)
      apply (clarsimp simp: abbreviatedType1_def)
      apply (clarsimp simp: val.matches_Cons[where xs = "[]" and ys = "[]", simplified])
      apply (clarsimp simp: val.matches_def)
      apply (rule val.v_t_record; simp?)
      apply (rule val.v_t_r_cons1; clarsimp?)
       apply (erule_tac x = frm in allE; clarsimp)
       apply (rule val.v_t_prim'; clarsimp)
      apply (rule val.v_t_r_cons1; clarsimp?)
       apply (rule val.v_t_prim'; clarsimp)
      apply (rule val.v_t_r_cons1; clarsimp?)
       apply (rule val.v_t_unit)
      apply (rule val.v_t_r_empty)
     apply (erule_tac x = frm in allE; clarsimp)
    apply (case_tac v; clarsimp)
   apply (subst val_wa_foldnb_bod.simps; clarsimp)
  apply (clarsimp simp: not_le)
  apply (frule_tac x = to in spec)
  apply (erule impE, simp)
  apply (erule exE)
  apply (drule val_wa_foldnb_bod_back_step; simp?)
  apply clarsimp
  apply (subgoal_tac "\<exists>y. r' = VPrim (LU32 y)", clarsimp)
   apply (erule_tac x = y in meta_allE)
   apply clarsimp
   apply (drule_tac \<gamma> = "[VRecord [VPrim (LU32 v), VPrim (LU32 y), VUnit]]" and
      \<Gamma> = "[option.Some abbreviatedType1]" and
      e = "App (Fun f ts) (Var 0)" and
      v' = "VPrim (LU32 r)" and
      \<tau>  = "TPrim (Num U32)" in val.rename_monoexpr_correct(1)
      [OF _ val_proc_env_matches_\<xi>m_\<Xi> value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p]; clarsimp?)
    apply (clarsimp simp: abbreviatedType1_def)
    apply (clarsimp simp: val.matches_Cons[where xs = "[]" and ys = "[]", simplified])
    apply (clarsimp simp: val.matches_def)
    apply (rule val.v_t_record; simp?)
    apply (rule val.v_t_r_cons1; clarsimp?)
     apply (rule val.v_t_prim'; clarsimp)
    apply (rule val.v_t_r_cons1; clarsimp?)
     apply (rule val.v_t_prim'; clarsimp)
    apply (rule val.v_t_r_cons1; clarsimp?)
     apply (rule val.v_t_unit)
    apply (rule val.v_t_r_empty)
   apply (case_tac va; clarsimp)
   apply (drule_tac r' = "VPrim (LU32 r)" in val_wa_foldnb_bod_step; simp)
  apply (insert val_proc_env_matches_\<xi>m_\<Xi>)
  apply (clarsimp simp: abbreviatedType1_def)
  apply (drule val_wa_foldnb_bod_preservation; simp?)
     apply (clarsimp simp: wa_abs_typing_v_def)
     apply (erule_tac x = i in allE; clarsimp)
     apply (rule val.v_t_prim'; clarsimp)
    apply (rule val.v_t_unit)
   apply clarsimp
  apply (erule v_t_prim_tE)
  apply (drule lit_type_ex[OF sym])
  apply clarsimp
  done

lemma val_wa_foldnb_0_mono_helper2:
  "\<lbrakk>val.proc_env_matches \<xi>m1 \<Xi>; proc_ctx_wellformed \<Xi>; \<forall>i<length xs. \<exists>v. xs ! i = VPrim (LU32 v);
    \<Xi>, [], [option.Some Generated_TypeProof.abbreviatedType1] \<turnstile> App (AFun (rename (f, ts)) []) 
      (Var 0) : TPrim (Num U32);
    val_wa_foldnb_bod \<xi>m xs frm to (AFun (rename (f, ts)) [])
         (VPrim (LU32 acc)) VUnit (VPrim (LU32 r))\<rbrakk>
       \<Longrightarrow> val_wa_foldnb_bod \<xi>p xs frm to (AFun f ts) (VPrim (LU32 acc)) VUnit (VPrim (LU32 r))"
  apply (induct to arbitrary: r)
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
   apply (subst val_wa_foldnb_bod.simps; clarsimp)
  apply clarsimp
  apply (case_tac "length xs < Suc to")
   apply (erule_tac x = r in meta_allE)
   apply (drule val_wa_foldnb_bod_back_step'; simp)
   apply (drule val_wa_foldnb_bod_to_geq_lenD)
    apply linarith
   apply (rule val_wa_foldnb_bod_to_geq_len; simp)
  apply (clarsimp simp: not_less)
  apply (case_tac "frm \<ge> to")
   apply (erule val_wa_foldnb_bod.elims; clarsimp split: if_splits)
    apply (erule val_wa_foldnb_bod.elims; clarsimp)
    apply (subst val_wa_foldnb_bod.simps; clarsimp)
    apply (subst val_wa_foldnb_bod.simps; clarsimp)
    apply (drule_tac \<gamma> = "[VRecord [xs ! frm, VPrim (LU32 acc), VUnit]]" and
      \<Gamma> = "[option.Some abbreviatedType1]" and
      e = "App (AFun f ts) (Var 0)" and
      v' = "VPrim (LU32 r)" and
      \<tau>  = "TPrim (Num U32)" in val.rename_monoexpr_correct(1)
      [OF _ val_proc_env_matches_\<xi>m_\<Xi> value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p]; clarsimp?)
      apply (clarsimp simp: abbreviatedType1_def)
      apply (clarsimp simp: val.matches_Cons[where xs = "[]" and ys = "[]", simplified])
      apply (clarsimp simp: val.matches_def)
      apply (rule val.v_t_record; simp?)
      apply (rule val.v_t_r_cons1; clarsimp?)
       apply (erule_tac x = frm in allE; clarsimp)
       apply (rule val.v_t_prim'; clarsimp)
      apply (rule val.v_t_r_cons1; clarsimp?)
       apply (rule val.v_t_prim'; clarsimp)
      apply (rule val.v_t_r_cons1; clarsimp?)
       apply (rule val.v_t_unit)
      apply (rule val.v_t_r_empty)
     apply (erule_tac x = frm in allE; clarsimp)
    apply (case_tac v; clarsimp)
   apply (subst val_wa_foldnb_bod.simps; clarsimp)
  apply (clarsimp simp: not_le)
  apply (frule_tac x = to in spec)
  apply (erule impE, simp)
  apply (erule exE)
  apply (drule val_wa_foldnb_bod_back_step; simp?)
  apply clarsimp
  apply (subgoal_tac "\<exists>y. r' = VPrim (LU32 y)", clarsimp)
   apply (erule_tac x = y in meta_allE)
   apply clarsimp
   apply (drule_tac \<gamma> = "[VRecord [VPrim (LU32 v), VPrim (LU32 y), VUnit]]" and
      \<Gamma> = "[option.Some abbreviatedType1]" and
      e = "App (AFun f ts) (Var 0)" and
      v' = "VPrim (LU32 r)" and
      \<tau>  = "TPrim (Num U32)" in val.rename_monoexpr_correct(1)
      [OF _ val_proc_env_matches_\<xi>m_\<Xi> value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p]; clarsimp?)
    apply (clarsimp simp: abbreviatedType1_def)
    apply (clarsimp simp: val.matches_Cons[where xs = "[]" and ys = "[]", simplified])
    apply (clarsimp simp: val.matches_def)
    apply (rule val.v_t_record; simp?)
    apply (rule val.v_t_r_cons1; clarsimp?)
     apply (rule val.v_t_prim'; clarsimp)
    apply (rule val.v_t_r_cons1; clarsimp?)
     apply (rule val.v_t_prim'; clarsimp)
    apply (rule val.v_t_r_cons1; clarsimp?)
     apply (rule val.v_t_unit)
    apply (rule val.v_t_r_empty)
   apply (case_tac va; clarsimp)
   apply (drule_tac r' = "VPrim (LU32 r)" in val_wa_foldnb_bod_step; simp)
  apply (insert val_proc_env_matches_\<xi>m_\<Xi>)
  apply (clarsimp simp: abbreviatedType1_def)
  apply (drule val_wa_foldnb_bod_preservation; simp?)
     apply (clarsimp simp: wa_abs_typing_v_def)
     apply (erule_tac x = i in allE; clarsimp)
     apply (rule val.v_t_prim'; clarsimp)
    apply (rule val.v_t_unit)
   apply clarsimp
  apply (erule v_t_prim_tE)
  apply (drule lit_type_ex[OF sym])
  apply clarsimp
  done

lemma value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m1_\<xi>p1: 
  "value_sem.rename_mono_prog wa_abs_typing_v rename \<Xi> \<xi>m1 \<xi>p1"
  apply (clarsimp simp: val.rename_mono_prog_def)
  apply (rule conjI; clarsimp)
   apply (rule_tac x = v' in exI)
   apply (subst (asm) rename_def)
   apply (subst (asm) assoc_lookup.simps)+
   apply (clarsimp split: if_split_asm)
  apply (clarsimp simp: val_wa_length_rename_monoexpr_correct)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x = v' in exI)
   apply (subst (asm) rename_def)
   apply (subst (asm) assoc_lookup.simps)+
   apply (clarsimp split: if_split_asm)
  apply (clarsimp simp: val_wa_get_rename_monoexpr_correct)
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (rule_tac x = v' in exI)
   apply (subst (asm) rename_def)
   apply (subst (asm) assoc_lookup.simps)+
   apply (clarsimp split: if_split_asm)
   apply (clarsimp simp: val_wa_put2_rename_monoexpr_correct)
  apply (subst (asm) rename_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm simp: val_wa_foldnb_0_def val_wa_foldnb_0p_def)
  apply (case_tac v; clarsimp)
  apply (case_tac z; clarsimp)
  apply (case_tac za; clarsimp)
  apply (case_tac zb; clarsimp)
  apply (case_tac zd; clarsimp)
  apply (case_tac ze; clarsimp)
  apply (rule_tac x = "VPrim (LU32 r)" in exI)
  apply clarsimp
  apply (case_tac zc; clarsimp)
   apply (clarsimp simp: val_wa_foldnb_0_mono_helper1)
  apply (clarsimp simp: val_wa_foldnb_0_mono_helper2)
  done


lemma val_proc_env_matches_\<xi>m1_\<Xi>:
  "val.proc_env_matches \<xi>m1 \<Xi>"
 apply (clarsimp simp: val.proc_env_matches_def)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
    apply (clarsimp simp: wordarray_get_0_type_def abbreviatedType3_def)
    apply (drule val_wa_get_preservation; simp?)
   apply (clarsimp simp: wordarray_length_0_type_def)
  apply (drule val_wa_length_preservation; simp?)
  apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType2_def)
  apply (drule val_wa_put2_preservation; simp?)
  apply (clarsimp simp: wordarray_fold_no_break_0_type_def val_wa_foldnb_0_def) thm val_wa_foldnb_bod_preservation
  apply (erule val.v_t_recordE)
  apply (erule val.v_t_r_consE; clarsimp)+
  apply (erule val.v_t_abstractE; clarsimp)
  apply (clarsimp simp: abbreviatedType1_def)
  apply (drule val_wa_foldnb_bod_preservation[OF proc_ctx_wellformed_\<Xi> val_proc_env_matches_\<xi>m_\<Xi>]; simp?)
  apply clarsimp
  done

lemma upd_wa_foldnb_bod_pres_obsv:
  "\<lbrakk>upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv (ra \<union> s) (\<sigma>', res); upd_val_rel \<Xi>' \<sigma> obsv obsv' t s {};
    \<sigma> p = option.Some (UAbstract (UWA (TPrim (Num n)) len arr)); 
    \<forall>i < len. \<exists>x. \<sigma> (arr + size_of_num_type n * i) = option.Some x\<rbrakk> 
    \<Longrightarrow> upd_val_rel \<Xi>' \<sigma>' obsv obsv' t s {}"
  apply (induct to arbitrary: \<sigma>' res)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
  apply (case_tac "len < 1 + to")
   apply (drule upd_wa_foldnb_bod_back_step'; simp?)
  apply (case_tac "frm < to")
   apply (frule_tac x = to in spec)
   apply (erule impE)
    apply (drule unatSuc; clarsimp simp: word_less_nat_alt)
   apply clarsimp
   apply (drule upd_wa_foldnb_bod_back_step; simp?)
    apply (drule unatSuc; clarsimp simp: word_less_nat_alt)
   apply clarsimp
   apply (drule_tac x = \<sigma>'' in meta_spec)
   apply (drule_tac x = r'' in meta_spec)
   apply clarsimp
   apply (drule_tac upd_val_rel_frame(1); simp?)
   apply blast
  apply (case_tac "\<not> frm < 1 + to")
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
  apply (clarsimp simp: not_le not_less)
  apply (subgoal_tac "to = frm")
  apply (erule upd_wa_foldnb_bod.elims; clarsimp split: if_splits)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp simp: add.commute)
   apply (drule_tac upd_val_rel_frame(1); simp?)
   apply blast
  by (metis add.commute inc_le not_less word_le_less_eq)

lemma upd_val_wa_foldnb_bod_corres:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; proc_env_u_v_matches \<xi>\<^sub>u \<xi>\<^sub>v \<Xi>'; 
    upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv (ra \<union> s) (\<sigma>', res); 
    val_wa_foldnb_bod \<xi>\<^sub>v xs (unat frm) (unat to) f acc' obsv' res';
    \<sigma> p = option.Some (UAbstract (UWA v len arr));
    wa_abs_upd_val (UWA v len arr) (VWA v xs) ''WordArray'' [v] (Boxed ReadOnly undefined) r w \<sigma>;
    upd_val_rel \<Xi>' \<sigma> acc acc' u ra wa; upd_val_rel \<Xi>' \<sigma> obsv obsv' t s {}; wa \<inter> s = {};
    \<tau> = TRecord [(''elem'', (v, Present)), (''acc'', (u, Present)), (''obsv'', (t, Present))] Unboxed;
     \<Xi>', [], [option.Some \<tau>] \<turnstile> App f (Var 0) : u\<rbrakk>
    \<Longrightarrow> \<exists>ra' wa'.  upd_val_rel \<Xi>' \<sigma>' res res' u ra' wa' \<and> ra' \<subseteq> ({p} \<union> ra \<union> s \<union> r)\<and> frame \<sigma> wa \<sigma>' wa'"
  apply (induct to arbitrary: res res' \<sigma>')
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = wa in exI)
   apply (clarsimp simp: frame_def)
  apply (case_tac "len < 1 + to")
   apply (drule upd_wa_foldnb_bod_back_step'; simp?)
   apply (drule unatSuc; clarsimp)
   apply (drule val_wa_foldnb_bod_back_step'; clarsimp simp: wa_abs_upd_val_def word_less_nat_alt)
   apply (case_tac v; clarsimp)
   apply (case_tac x5; clarsimp)
  apply (case_tac "1 + to \<le> frm")
   apply (frule_tac y = "1 + to" and x = frm in leD)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = wa in exI)
   apply (clarsimp simp: frame_def)
  apply (case_tac "frm = to")
   apply (clarsimp simp: not_le not_less)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp split: if_split_asm)
   apply (erule disjE; clarsimp)
    apply (erule upd_wa_foldnb_bod.elims; clarsimp simp: add.commute)
    apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt wa_abs_upd_val_def)
    apply (case_tac v; clarsimp)
    apply (erule val_wa_foldnb_bod.elims; clarsimp)
    apply (erule val_wa_foldnb_bod.elims; clarsimp)
    apply (erule_tac x = frm in allE; clarsimp)
    apply (frule_tac \<gamma> = "[URecord [(va, upd.uval_repr va), (acc, upd.uval_repr acc),
      (obsv, upd.uval_repr obsv)]]" and 
      \<gamma>' = "[VRecord [xs ! unat frm, acc', obsv']]" and
      r = "ra \<union> s" and w = wa in mono_correspondence(1); simp?)
     apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
      apply (rule u_v_struct; simp?)
      apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
        apply (clarsimp simp: wa_abs_typing_v_def)
        apply (erule_tac x = frm in allE; clarsimp)+
        apply (erule_tac x = "unat frm" in allE; clarsimp)
        apply (rule u_v_prim'; clarsimp)
       apply (rule u_v_r_cons1[where r = ra and w' = "{}", simplified]; simp?)
        apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
         apply (rule u_v_r_empty)
        apply (drule_tac u = obsv in upd_val_rel_to_uval_typing(1))
        apply (drule upd.type_repr_uval_repr(1); simp)
       apply (drule upd_val_rel_to_uval_typing(1))
       apply (drule upd.type_repr_uval_repr(1); simp)
      apply (erule_tac x = frm in allE; clarsimp)+
     apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
    apply clarsimp
    apply (rule_tac x = r' in exI)
    apply (rule_tac x = w' in exI; simp)
    apply blast
   apply (erule impE)
    apply auto[1]
   apply clarsimp
   apply (erule upd_wa_foldnb_bod.elims; clarsimp simp: add.commute)
    apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt wa_abs_upd_val_def)
   apply (erule val_wa_foldnb_bod.elims; clarsimp)+
   apply (frule_tac \<gamma> = "[URecord [(va, upd.uval_repr va), (acc, upd.uval_repr acc),
      (obsv, upd.uval_repr obsv)]]" and 
      \<gamma>' = "[VRecord [xs ! unat frm, acc', obsv']]" and
      r = "ra \<union> s" and w = wa in mono_correspondence(1); simp?)
    apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
      apply (rule u_v_struct; simp?)
     apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
       apply (clarsimp simp: wa_abs_typing_v_def)
       apply (erule_tac x = frm in allE; clarsimp)+
       apply (erule_tac x = "unat frm" in allE; clarsimp)
       apply (rule u_v_prim'; clarsimp)
      apply (rule u_v_r_cons1[where r = ra and w' = "{}", simplified]; simp?)
       apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
        apply (rule u_v_r_empty)
       apply (drule_tac u = obsv in upd_val_rel_to_uval_typing(1))
       apply (drule upd.type_repr_uval_repr(1); simp)
      apply (drule upd_val_rel_to_uval_typing(1))
      apply (drule upd.type_repr_uval_repr(1); simp)
     apply (erule_tac x = frm in allE; clarsimp)+
    apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
   apply clarsimp
   apply (rule_tac x = r' in exI)
   apply (rule_tac x = w' in exI)
   apply clarsimp
   apply blast
  apply (clarsimp simp: wa_abs_upd_val_def)
  apply (case_tac v; clarsimp)
  apply (case_tac x5; clarsimp)
  apply (drule upd_wa_foldnb_bod_back_step; simp?)
    apply (drule unatSuc; clarsimp simp: word_less_nat_alt)
   apply (metis add.commute inc_le not_less_iff_gr_or_eq)
  apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
  apply (drule_tac val_wa_foldnb_bod_back_step; simp?)
   apply (meson Suc_leI not_less_iff_gr_or_eq word_less_nat_alt)
  apply clarsimp
  apply (drule_tac x = r'' in meta_spec)
  apply (drule_tac x = r' in meta_spec)
  apply (drule_tac x = \<sigma>'' in meta_spec)
  apply clarsimp
  apply (frule_tac \<gamma> = "[URecord [(va, upd.uval_repr va), (r'', upd.uval_repr r''),
      (obsv, upd.uval_repr obsv)]]" and 
      \<gamma>' = "[VRecord [xs ! unat to, r', obsv']]" and
      r = "ra' \<union> s" and w = wa' in mono_correspondence(1); simp?)
   apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
    apply (rule u_v_struct; simp?)
    apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
      apply (erule_tac x = to in allE)
      apply (clarsimp simp: not_less word_less_nat_alt)
      apply (rule u_v_prim'; clarsimp)
     apply (rule u_v_r_cons1[where r' = s and w' = "{}", simplified]; simp?)
       apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
         apply (rule upd_val_rel_frame(1); simp?) 
         apply (rule disjointI)
         apply (thin_tac "frame _ _ _ _")
         apply (clarsimp simp: frame_def)
         apply (erule_tac x = y in allE)
         apply (drule_tac x = y in orthD2; simp)
        apply (rule u_v_r_empty)
       apply (drule_tac u = obsv in upd_val_rel_to_uval_typing(1))
       apply (drule upd.type_repr_uval_repr(1); simp)
      apply (drule upd_val_rel_to_uval_typing(1))
      apply (thin_tac "frame _ _ _ _")
      apply (rule disjointI)
      apply (clarsimp simp: frame_def)
      apply (erule_tac x = y in allE)+
      apply clarsimp
      apply (drule_tac x = y in orthD2; simp)
      apply (drule_tac p = y and u = obsv in upd_val_rel_valid(1)[rotated 1]; simp?)
     apply (drule_tac u = r'' in upd_val_rel_to_uval_typing(1))
     apply (drule upd.type_repr_uval_repr(1); simp)
    apply (erule_tac x = to in allE; clarsimp)
   apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
  apply clarsimp
  apply (rule_tac x = r'a in exI)
  apply (rule_tac x = w' in exI)
  apply clarsimp
  apply (rule conjI)
   apply blast
  apply (rule upd.frame_trans; simp)
  done



lemma val_executes_from_upd_wa_foldnb_bod:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; proc_env_u_v_matches \<xi>\<^sub>u \<xi>\<^sub>v \<Xi>';
    upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv (ra \<union> s) (\<sigma>', res);
    \<sigma> p = option.Some (UAbstract (UWA v len arr));
    wa_abs_upd_val (UWA v len arr) (VWA v xs) ''WordArray'' [v] (Boxed ReadOnly undefined) r w \<sigma>;
    upd_val_rel \<Xi>' \<sigma> acc acc' u ra wa; upd_val_rel \<Xi>' \<sigma> obsv obsv' t s {}; wa \<inter> s = {};
    \<tau> = TRecord [(''elem'', (v, Present)), (''acc'', (u, Present)), (''obsv'', (t, Present))] Unboxed;
     \<Xi>', [], [option.Some \<tau>] \<turnstile> App f (Var 0) : u\<rbrakk>
    \<Longrightarrow> \<exists>res' r w. val_wa_foldnb_bod \<xi>\<^sub>v xs (unat frm) (unat to) f acc' obsv' res' \<and> upd_val_rel \<Xi>' \<sigma>' res res' u r w"
  apply (induct arbitrary: \<sigma>' res rule: word_induct[where m = "to"])
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
   apply (rule_tac x = acc' in exI)
   apply (subst val_wa_foldnb_bod.simps; clarsimp)
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = wa in exI)
   apply clarsimp
  apply (case_tac "1 + n \<le> 0"; clarsimp)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
   apply (rule_tac x = acc' in exI)
   apply (subst val_wa_foldnb_bod.simps; clarsimp)
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = wa in exI)
   apply clarsimp
  apply (case_tac "len < 1 + n")
   apply (drule upd_wa_foldnb_bod_back_step'; simp?)
   apply (erule_tac x = \<sigma>' in meta_allE)
   apply (erule_tac x = res in meta_allE)
   apply clarsimp
   apply (rule_tac x = res' in exI)
   apply (drule val_wa_foldnb_bod_to_geq_lenD)
    apply (clarsimp simp: wa_abs_upd_val_def)
    apply (case_tac v; clarsimp)
    apply (case_tac x5; clarsimp)
    apply (simp add: unatSuc word_less_nat_alt)
   apply (drule unatSuc; clarsimp)
   apply (rule conjI)
    apply (rule val_wa_foldnb_bod_to_geq_len; simp?)
    apply (clarsimp simp: wa_abs_upd_val_def)
    apply (case_tac v; clarsimp)
    apply (case_tac x5; clarsimp simp: word_less_nat_alt)
   apply (rule_tac x = rb in exI)
   apply (rule_tac x = x in exI)
   apply clarsimp
  apply (case_tac "1 + n \<le> frm")
   apply (rule_tac x = acc' in exI)
  apply (frule_tac y = "1 + n" and x = frm in leD)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
   apply (subst val_wa_foldnb_bod.simps; clarsimp)
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = wa in exI)
   apply clarsimp
  apply (case_tac "frm = n")
   apply (clarsimp simp: not_le not_less)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp split: if_split_asm)
   apply (erule disjE; clarsimp)
    apply (erule upd_wa_foldnb_bod.elims; clarsimp simp: add.commute)
    apply (frule_tac \<gamma> = "[URecord [(va, upd.uval_repr va), (acc, upd.uval_repr acc), 
      (obsv, upd.uval_repr obsv)]]" and 
      \<gamma>' = "[VRecord [xs ! unat frm, acc', obsv']]" and
      r = "ra \<union> s" and w = wa in val_executes_from_upd_executes(1); simp?)
     apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
      apply (rule u_v_struct; simp?)
      apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
        apply (clarsimp simp: wa_abs_upd_val_def)
        apply (erule_tac x = frm in allE; clarsimp)+
        apply (rule u_v_prim'; clarsimp)
       apply (rule u_v_r_cons1[where r' = s and w' = "{}", simplified]; simp?)
        apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
         apply (rule u_v_r_empty)
        apply (drule_tac u = obsv in upd_val_rel_to_uval_typing(1))
        apply (drule upd.type_repr_uval_repr(1); simp)
       apply (drule upd_val_rel_to_uval_typing(1))
       apply (drule upd.type_repr_uval_repr(1); simp)
      apply (clarsimp simp: wa_abs_upd_val_def)
      apply (erule_tac x = frm in allE; clarsimp)+
     apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
    apply clarsimp
    apply (rule_tac x = v' in exI)
    apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
    apply (rule conjI)
     apply (subst val_wa_foldnb_bod.simps; clarsimp)
     apply (subst val_wa_foldnb_bod.simps; clarsimp)
     apply (rule FalseE)
     apply (clarsimp simp: wa_abs_upd_val_def)
    apply (frule_tac \<gamma> = "[URecord [(va, upd.uval_repr va), (acc, upd.uval_repr acc),
      (obsv, upd.uval_repr obsv)]]" and 
      \<gamma>' = "[VRecord [xs ! unat frm, acc', obsv']]" and
      r = "ra \<union> s" and w = wa in mono_correspondence(1); simp?)
     apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
      apply (rule u_v_struct; simp?)
      apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
        apply (clarsimp simp: wa_abs_upd_val_def)
        apply (erule_tac x = frm in allE; clarsimp simp: word_less_nat_alt)+
        apply (rule u_v_prim'; clarsimp)
       apply (rule u_v_r_cons1[where r' = s and w' = "{}", simplified]; simp?)
        apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
         apply (rule u_v_r_empty)
        apply (drule_tac u = obsv in upd_val_rel_to_uval_typing(1))
        apply (drule upd.type_repr_uval_repr(1); simp)
       apply (drule upd_val_rel_to_uval_typing(1))
       apply (drule upd.type_repr_uval_repr(1); simp)
      apply (clarsimp simp: wa_abs_upd_val_def)
      apply (erule_tac x = frm in allE; clarsimp simp: word_less_nat_alt)+
     apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
    apply clarsimp
    apply (rule_tac x = r' in exI)
    apply (rule_tac x = w' in exI)
    apply clarsimp
   apply (erule impE)
    apply simp
   apply clarsimp
   apply (erule upd_wa_foldnb_bod.elims; clarsimp simp: add.commute)
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
   apply (frule_tac \<gamma> = "[URecord [(va, upd.uval_repr va), (acc, upd.uval_repr acc), 
      (obsv, upd.uval_repr obsv)]]" and
      \<gamma>' = "[VRecord [xs ! unat frm, acc', obsv']]" and
      r = "ra \<union> s" and w = wa in val_executes_from_upd_executes(1); simp?)
    apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
  apply (rule u_v_struct; simp?)
     apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
       apply (clarsimp simp: wa_abs_upd_val_def)
       apply (erule_tac x = frm in allE; clarsimp simp: word_less_nat_alt)+
       apply (rule u_v_prim'; clarsimp)
      apply (rule u_v_r_cons1[where r' = s and w' = "{}", simplified]; simp?)
       apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
        apply (rule u_v_r_empty)
       apply (drule_tac u = obsv in upd_val_rel_to_uval_typing(1))
       apply (drule upd.type_repr_uval_repr(1); simp)
      apply (drule upd_val_rel_to_uval_typing(1))
      apply (drule upd.type_repr_uval_repr(1); simp)
     apply (clarsimp simp: wa_abs_upd_val_def)
     apply (erule_tac x = frm in allE; clarsimp simp: word_less_nat_alt)+
    apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
   apply clarsimp
   apply (frule_tac \<gamma> = "[URecord [(va, upd.uval_repr va), (acc, upd.uval_repr acc),
      (obsv, upd.uval_repr obsv)]]" and 
      \<gamma>' = "[VRecord [xs ! unat frm, acc', obsv']]" and
      r = "ra \<union> s" and w = wa in mono_correspondence(1); simp?)
    apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
     apply (rule u_v_struct; simp?)
     apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
       apply (clarsimp simp: wa_abs_upd_val_def)
       apply (erule_tac x = frm in allE; clarsimp simp: word_less_nat_alt)+
       apply (rule u_v_prim'; clarsimp)
      apply (rule u_v_r_cons1[where r' = s and w' = "{}", simplified]; simp?)
       apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
        apply (rule u_v_r_empty)
       apply (drule_tac u = obsv in upd_val_rel_to_uval_typing(1))
       apply (drule upd.type_repr_uval_repr(1); simp)
      apply (drule upd_val_rel_to_uval_typing(1))
      apply (drule upd.type_repr_uval_repr(1); simp)
     apply (clarsimp simp: wa_abs_upd_val_def)
     apply (erule_tac x = frm in allE; clarsimp simp: word_less_nat_alt)+
    apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
   apply clarsimp
   apply (clarsimp simp: wa_abs_upd_val_def)
   apply (rule_tac x = v' in exI)
   apply (subst val_wa_foldnb_bod.simps; clarsimp)+
   apply (rule_tac x = r' in exI)
   apply (rule_tac x = w' in exI)
   apply clarsimp
  apply (clarsimp simp: wa_abs_upd_val_def)
  apply (case_tac v; clarsimp)
  apply (case_tac x5; clarsimp)
  apply (drule_tac upd_wa_foldnb_bod_back_step; simp?)
    apply (metis word_le_less_eq word_zero_le)
   apply (metis add.commute plus_one_helper word_le_less_eq word_not_le)
   apply clarsimp
   apply (drule_tac x = \<sigma>'' in meta_spec)
   apply (drule_tac x = r'' in meta_spec)
   apply clarsimp
  apply (frule_tac r = r and w = w in upd_val_wa_foldnb_bod_corres; simp?)
   apply (clarsimp simp: wa_abs_upd_val_def)
  apply clarsimp
  apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
  apply (frule_tac \<gamma> = "[URecord [(va, upd.uval_repr va), (r'', upd.uval_repr r''), 
      (obsv, upd.uval_repr obsv)]]" and
      \<gamma>' = "[VRecord [xs ! unat n, res', obsv']]" and
      r = "ra' \<union> s" and w = wa' in val_executes_from_upd_executes(1); simp?)
   apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
    apply (rule u_v_struct; simp?)
    apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
      apply (erule_tac x = n in allE; clarsimp)+
      apply (rule u_v_prim'; clarsimp)
     apply (rule u_v_r_cons1[where r' = s and w' = "{}", simplified]; simp?)
       apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
         apply (rule upd_val_rel_frame(1); simp?)
         apply (rule disjointI)
         apply (thin_tac "frame _ _ _ _")
         apply (clarsimp simp: frame_def)
         apply (erule_tac x = y in allE)
         apply (drule_tac x = y in orthD2; simp)
        apply (rule u_v_r_empty)
       apply (drule_tac u = obsv in  upd_val_rel_to_uval_typing(1))
       apply (drule upd.type_repr_uval_repr(1); simp)
      apply (rule disjointI)
      apply (thin_tac "frame _ _ _ _")
      apply (clarsimp simp: frame_def)
      apply (erule_tac x = y in allE; clarsimp)+
      apply (drule_tac x = y in orthD2; simp)
      apply (drule_tac u = obsv and p = y in upd_val_rel_valid(1)[rotated 1]; simp?)
     apply (drule_tac u = r'' in  upd_val_rel_to_uval_typing(1))
     apply (drule upd.type_repr_uval_repr(1); simp)
    apply (erule_tac x = n in allE; clarsimp)+
   apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
  apply clarsimp
  apply (drule_tac r' = v' in  val_wa_foldnb_bod_step; simp?)
  apply (rule_tac x = v' in exI)
  apply clarsimp
  apply (frule_tac \<gamma> = "[URecord [(va, upd.uval_repr va), (r'', upd.uval_repr r''), 
      (obsv, upd.uval_repr obsv)]]" and 
      \<gamma>' = "[VRecord [xs ! unat n, res', obsv']]" and
      r = "ra' \<union> s" and w = wa' in mono_correspondence(1); simp?)
   apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
    apply (rule u_v_struct; simp?)
    apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
      apply (erule_tac x = n in allE; clarsimp)
      apply (rule u_v_prim'; clarsimp)
     apply (rule u_v_r_cons1[where r' = s and w' = "{}", simplified]; simp?)
       apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
         apply (rule upd_val_rel_frame(1); simp?) 
         apply (rule disjointI)
         apply (thin_tac "frame _ _ _ _")
         apply (clarsimp simp: frame_def)
         apply (erule_tac x = y in allE)
         apply (drule_tac x = y in orthD2; simp)
        apply (rule u_v_r_empty)
       apply (drule_tac u = obsv in  upd_val_rel_to_uval_typing(1))
       apply (drule upd.type_repr_uval_repr(1); simp)
      apply (rule disjointI)
      apply (thin_tac "frame _ _ _ _")
      apply (clarsimp simp: frame_def)
      apply (erule_tac x = y in allE; clarsimp)+
      apply (drule_tac x = y in orthD2; simp)
      apply (drule_tac u = obsv and p = y in upd_val_rel_valid(1)[rotated 1]; simp?)
     apply (drule_tac u = r'' in  upd_val_rel_to_uval_typing(1))
     apply (drule upd.type_repr_uval_repr(1); simp)
    apply (erule_tac x = n in allE; clarsimp)
   apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
  apply clarsimp
  apply (rule_tac x = r' in exI)
  apply (rule_tac x = w' in exI)
  apply simp
  done

lemma wordarray_fold_no_break_upd_val:
  "\<And>K a b \<sigma> \<sigma>' \<tau>s aa a' v v' r w.
   \<lbrakk>list_all2 (kinding []) \<tau>s K; wordarray_fold_no_break_0_type = (K, a, b); 
    upd_val_rel \<Xi> \<sigma> aa a' (instantiate \<tau>s a) r w; upd_wa_foldnb_0 (\<sigma>, aa) (\<sigma>', v)\<rbrakk>
    \<Longrightarrow> (val_wa_foldnb_0 a' v' \<longrightarrow> (\<exists>r' w'. upd_val_rel \<Xi> \<sigma>' v v' (instantiate \<tau>s b) r' w' \<and> r' \<subseteq> r \<and>
          frame \<sigma> w \<sigma>' w')) \<and> Ex (val_wa_foldnb_0 a')"
  apply (clarsimp simp: wordarray_fold_no_break_0_type_def upd_wa_foldnb_0_def)
  apply (erule u_v_recE'; clarsimp)
  apply (erule u_v_r_consE'; clarsimp)
  apply (erule u_v_p_absE'; clarsimp)
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)
  apply clarsimp
  apply (erule u_v_primE')
  apply (drule_tac t = "lit_type _" in sym)
  apply clarsimp
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)
  apply clarsimp
  apply (erule u_v_primE')
  apply (drule_tac t = "lit_type _" in sym)
  apply clarsimp
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)
  apply clarsimp
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)
  apply clarsimp
  apply (erule u_v_primE')
  apply (drule_tac t = "lit_type _" in sym)
  apply clarsimp
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply clarsimp
  apply (erule u_v_r_emptyE'; clarsimp)
  apply (subst (asm) upd_val_rel.simps[of _ _ "UUnit", simplified])
  apply clarsimp
  apply (erule disjE; clarsimp?)
  apply (erule disjE; clarsimp?)
  apply (case_tac a'; clarsimp simp: wa_abs_upd_val_def val_wa_foldnb_0_def)
  apply (case_tac x11; clarsimp)
  apply (case_tac x5; clarsimp)
  apply (rule conjI; clarsimp)
   apply (drule_tac xs = x12 and r = r and w = "{}" and acc' = "VPrim (LU32 acc)" and 
      wa = "{}" and obsv' = "VUnit" and t = "TUnit" and res' = "(VPrim (LU32 rc))"
      in upd_val_wa_foldnb_bod_corres[OF proc_ctx_wellformed_\<Xi> proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>,
        where ra = "{}" and s = "{}", simplified]; simp?)
        apply (case_tac xa; clarsimp)
         apply (subst (asm) upd_val_rel.simps[of _ _ "UFunction _ _", simplified])
         apply clarsimp
         apply (erule disjE; clarsimp?)
         apply (erule disjE; clarsimp?)
        apply (subst (asm) upd_val_rel.simps[of _ _ "UAFunction _ _", simplified])
        apply clarsimp
        apply (erule disjE; clarsimp?)
        apply (erule disjE; clarsimp?)
       apply (clarsimp simp: wa_abs_upd_val_def)
      apply (rule u_v_prim'; clarsimp)
     apply (rule u_v_unit)
    apply (clarsimp simp: abbreviatedType1_def)
   apply clarsimp
   apply (case_tac xa; clarsimp)
    apply (subst (asm) upd_val_rel.simps[of _ _ "UFunction _ _", simplified])
    apply clarsimp
    apply (erule disjE; clarsimp?)
    apply (erule disjE; clarsimp?)
    apply blast
   apply (subst (asm) upd_val_rel.simps[of _ _ "UAFunction _ _", simplified])
   apply clarsimp
   apply (erule disjE; clarsimp?)
   apply (erule disjE; clarsimp?)
   apply blast
  apply (drule_tac xs = x12 and r = r and w = "{}" and acc' = "VPrim (LU32 acc)" and
      wa = "{}" and obsv' = "VUnit" and t = "TUnit" 
      in val_executes_from_upd_wa_foldnb_bod[OF proc_ctx_wellformed_\<Xi> proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>,
        where ra = "{}" and s = "{}", simplified]; simp?)
      apply (clarsimp simp: wa_abs_upd_val_def)
     apply (rule u_v_prim'; clarsimp)
    apply (rule u_v_unit)
   apply (clarsimp simp: abbreviatedType1_def)
  apply clarsimp
  apply (rule_tac x = res' in exI)
  apply (clarsimp simp: val_wa_foldnb_0_def)
  apply (rule conjI)
  apply (clarsimp simp: abbreviatedType1_def)
  apply (drule val_wa_foldnb_bod_preservation[OF proc_ctx_wellformed_\<Xi> val_proc_env_matches_\<xi>m_\<Xi>]; simp?)
      apply (clarsimp simp: wa_abs_typing_v_def)
      apply (rule val.v_t_prim'; simp)
     apply (rule val.v_t_unit)
    apply clarsimp
   apply (erule v_t_prim_tE; clarsimp) 
   apply (drule lit_type_ex[OF sym]; simp)
  apply (rule conjI, clarsimp simp: wa_abs_typing_v_def)
   apply (erule_tac x = i in allE; clarsimp)
   apply (drule lit_type_ex; simp)
  apply (case_tac xa; clarsimp)
   apply (subst (asm) upd_val_rel.simps[of _ _ "UFunction _ _", simplified])
   apply clarsimp
   apply (erule disjE; clarsimp?)
   apply (erule disjE; clarsimp?)
  apply (subst (asm) upd_val_rel.simps[of _ _ "UAFunction _ _", simplified])
  apply clarsimp
  apply (erule disjE; clarsimp?)
  apply (erule disjE; clarsimp?)
  done

lemma upd_proc_env_matches_ptrs_\<xi>1_\<Xi>:
  "upd.proc_env_matches_ptrs \<xi>1 \<Xi>"
  apply (unfold upd.proc_env_matches_ptrs_def)
  apply clarsimp
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
     apply (clarsimp simp: wordarray_get_0_type_def abbreviatedType3_def)
     apply (drule upd_wa_get_preservation; simp?)
    apply (clarsimp simp: wordarray_length_0_type_def)
    apply (drule upd_wa_length_preservation; simp)
   apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType2_def)
   apply (drule upd_wa_put2_preservation; simp)
  apply (clarsimp simp: upd_wa_foldnb_0_preservation)
  done

lemma proc_env_u_v_matches_\<xi>1_\<xi>m1_\<Xi>:
  "proc_env_u_v_matches \<xi>1 \<xi>m1 \<Xi>"
  apply (clarsimp simp: proc_env_u_v_matches_def)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
     apply (clarsimp simp: wordarray_get_0_type_def abbreviatedType3_def)
     apply (drule wa_get_upd_val; simp)
    apply (clarsimp simp: wordarray_length_0_type_def)
    apply (drule wa_length_upd_val; simp)
   apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType2_def)
   apply (drule wa_put2_upd_val; simp)
  apply (clarsimp simp: wordarray_fold_no_break_upd_val)
  done

(*


lemma 
  "\<lbrakk>val_wa_foldnb_bod xs frm (Suc to) f acc obsv r; frm < Suc to\<rbrakk>
    \<Longrightarrow> \<exists>acc'. val_wa_foldnb_bod xs to (Suc to) f acc' obsv r"
  apply (induct rule: val_wa_foldnb_bod.induct[where ?a0.0 = xs and
                                                       ?a1.0 = frm and
                                                       ?a2.0 = to and
                                                       ?a3.0 = f and
                                                       ?a4.0 = acc and
                                                       ?a5.0 = obsv and
                                                       ?a6.0 = r]; clarsimp)
  apply (case_tac "frm < length xs")
   apply (case_tac "frm < to")
    apply (erule val_wa_foldnb_bod.elims; clarsimp)
   apply clarsimp
   apply (rule_tac x = acc in exI)
   apply (erule val_wa_foldnb_bod.elims; clarsimp)+
   apply (subst val_wa_foldnb_bod.simps; clarsimp)+
   apply (rule_tac x = v in exI)
   apply clarsimp
   apply (subgoal_tac "frma = to")
    apply clarsimp
   apply linarith
  apply (rule_tac x = res in exI)
  apply (subst val_wa_foldnb_bod.simps; clarsimp)
  done
lemma 
  "\<lbrakk>val_wa_foldnb_bod xs frm to f (VPrim (LU32 acc)) VUnit r; 
    \<forall>i<length xs. \<exists>v. xs ! i = VPrim (LU32 v);
    \<Xi>, [], [option.Some abbreviatedType1] \<turnstile> App f (Var 0) : TPrim (Num U32)\<rbrakk>
    \<Longrightarrow> \<exists>x. r = VPrim (LU32 x)"
  apply (induct to arbitrary: r)
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
  apply (case_tac "length xs < Suc to")
   apply (drule val_wa_foldnb_bod_back_step'; simp)
  apply (case_tac "to \<le> frm")
   apply (erule val_wa_foldnb_bod.elims; clarsimp split: if_splits)
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
   apply (insert proc_ctx_wellformed_\<Xi> val_proc_env_matches_\<xi>m_\<Xi>)
   apply (drule val.preservation(1)[of "[]" "[]" _ _ _  \<xi>m, simplified]; simp?)
    apply (clarsimp simp: abbreviatedType1_def)
    apply (clarsimp simp: val.matches_Cons[where xs = "[]" and ys = "[]", simplified])
    apply (clarsimp simp: val.matches_def)
    apply (rule val.v_t_record; simp?)
    apply (rule val.v_t_r_cons1; clarsimp?)
     apply (rule val.v_t_prim'; clarsimp)
    apply (rule val.v_t_r_cons1; clarsimp?)
     apply (rule val.v_t_prim'; clarsimp)
    apply (rule val.v_t_r_cons1; clarsimp?)
     apply (rule val.v_t_unit)
    apply (rule val.v_t_r_empty)
   apply (erule v_t_prim_tE; clarsimp simp: lit_type_ex)
  apply (clarsimp simp: not_less not_le)
  apply (erule_tac x = to in allE; clarsimp)
  apply (drule val_wa_foldnb_bod_back_step; simp?)
  apply clarsimp
  apply (drule_tac x = r' in meta_spec)
  apply clarsimp
  apply (insert proc_ctx_wellformed_\<Xi> val_proc_env_matches_\<xi>m_\<Xi>)
  apply (drule val.preservation(1)[of "[]" "[]" _ _ _  \<xi>m, simplified]; simp?)
   apply (clarsimp simp: abbreviatedType1_def)
   apply (clarsimp simp: val.matches_Cons[where xs = "[]" and ys = "[]", simplified])
   apply (clarsimp simp: val.matches_def)
   apply (rule val.v_t_record; simp?)
   apply (rule val.v_t_r_cons1; clarsimp?)
    apply (rule val.v_t_prim'; clarsimp)
   apply (rule val.v_t_r_cons1; clarsimp?)
    apply (rule val.v_t_prim'; clarsimp)
   apply (rule val.v_t_r_cons1; clarsimp?)
    apply (rule val.v_t_unit)
   apply (rule val.v_t_r_empty)
  apply (erule v_t_prim_tE; clarsimp simp: lit_type_ex)
  done

*)

end (* of context *)

end
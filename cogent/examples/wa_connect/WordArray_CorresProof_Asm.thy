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
  apply (clarsimp split: vatyp.splits type.splits prim_type.splits)
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
  apply (clarsimp split: vatyp.splits type.splits prim_type.splits)
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
    apply (rule_tac a = "UWA (TPrim (Num ta)) len arr" and ptrl = ptrl
      in u_v_p_abs_w[where ts = "[TPrim _]", simplified]; simp?)
     apply (clarsimp simp: wa_abs_upd_val_def)
     apply (rule conjI)
      apply (clarsimp simp: wa_abs_typing_u_def split: if_split_asm)
     apply (rule conjI)
      apply (clarsimp simp: wa_abs_typing_v_def)
      apply (erule_tac x = i in allE; clarsimp)+
      apply (case_tac "i = unat idx"; clarsimp)
     apply (clarsimp split: if_splits)
     apply (rule conjI; clarsimp)
      apply (drule distinct_indices)
      apply (erule_tac x = i in allE)+
      apply clarsimp
      apply (erule_tac x = idx in allE)
      apply (clarsimp simp: word_less_nat_alt)
     apply (erule_tac x = i in allE)
     apply clarsimp
     apply (case_tac "unat i = unat idx"; clarsimp simp: wa_abs_typing_u_def)
    apply (clarsimp split: if_splits)
    apply (clarsimp simp: wa_abs_upd_val_def)
    apply (erule_tac x = idx in allE)
    apply clarsimp
   apply (clarsimp simp: frame_def wa_abs_upd_val_def wa_abs_typing_u_def split: if_splits)
   apply (rule conjI; clarsimp)
    apply (rule conjI)
     apply clarsimp
    apply (rule conjI; clarsimp)
    apply (rule conjI; clarsimp)
   apply (rule conjI; clarsimp)
  apply clarsimp
  apply (frule wa_abs_upd_val_elims(2))
  apply (drule wa_abs_typing_v_elims(1))
  apply clarsimp
  apply (rule_tac x = "VAbstract (VWA t (xs[unat idx := VPrim l]))" in exI)
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
  apply (drule_tac t = "lit_type _" in sym; clarsimp)
   apply (rule_tac ptrl = ptrl and a = "UWA (TPrim (Num ta)) len arr" 
      in upd.u_t_p_abs_w[where ts = "[TPrim _]", simplified]; simp?)
    apply (clarsimp simp: wa_abs_typing_u_def split: prim_type.splits if_splits)
   apply (frule wa_abs_typing_u_elims(3); clarsimp split: if_splits)
  apply (clarsimp split: if_splits simp: upd.frame_id)
  apply (drule_tac t = "lit_type _" in sym; clarsimp)
  apply (frule wa_abs_typing_u_elims(3); clarsimp)
  apply (clarsimp simp: frame_def)
  apply (rule conjI; clarsimp)
   apply (rule conjI, clarsimp)
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
    \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi>' \<sigma>' res u r' w' \<and> r' \<subseteq> ({p} \<union> ra \<union> rb \<union> rc) \<and> frame \<sigma> wb \<sigma>' w'"
  apply (induct to arbitrary: \<sigma>' res)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
   apply (rule_tac x = rb in exI)
   apply (rule_tac x = wb in exI)
   apply (clarsimp simp: upd.frame_id)
  apply (case_tac "len < 1 + to")
   apply (drule upd_wa_foldnb_bod_back_step'; simp?)
  apply (case_tac "1 + to \<le> frm")
   apply (frule_tac y = "1 + to" and x = frm in leD)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
   apply (rule_tac x = rb in exI)
   apply (rule_tac x = wb in exI)
   apply (clarsimp simp: upd.frame_id)
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (drule upd_wa_foldnb_bod_back_step; simp?)
  apply clarsimp
  apply (drule_tac x = \<sigma>'' in meta_spec)
  apply (drule_tac x = r'' in meta_spec)
  apply clarsimp
  apply (frule wa_abs_typing_u_elims(5))
  apply (erule_tac x = to in allE; clarsimp)+
  apply (erule impE)
   apply (cut_tac x = to in word_overflow)
   apply (erule disjE; clarsimp simp: add.commute)
   apply auto[1]
  apply clarsimp
  apply (drule_tac ?\<Gamma> = "[option.Some (TRecord [(b0, TPrim (Num ta), Present), (b1, u, Present),
    (b2, v, Present)] Unboxed)]" and r = "r' \<union> rc" and  w = w' and \<tau> = u in upd.preservation_mono(1); simp?)
   apply (rule upd.matches_ptrs_some[where ts = "[]" and r' = "{}" and w' = "{}", simplified])
    apply (rule upd.u_t_struct; simp?)
    apply (rule upd.u_t_r_cons1[where r = "{}" and w = "{}", simplified])
      apply (rule upd.u_t_prim'; clarsimp)
     apply (rule upd.u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
       apply (rule upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
         apply (rule upd.uval_typing_frame(1); simp?)
         apply blast
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

lemma readonly_not_in_frame:
  "\<lbrakk>frame \<sigma> w \<sigma>' w'; \<sigma> p = option.Some v; p \<notin> w\<rbrakk> \<Longrightarrow> p \<notin> w'"
  apply (frule_tac p = p in valid_ptr_not_in_frame_same; simp?)
  by (clarsimp simp: frame_def)

lemma frame_expand:
  "\<lbrakk>frame \<sigma> w \<sigma>' w'; \<sigma> p \<noteq> option.None\<rbrakk> \<Longrightarrow> frame \<sigma> (insert p w) \<sigma>' (insert p w')"
  "\<lbrakk>frame \<sigma> w \<sigma>' w'; \<forall>p\<in>s. \<sigma> p \<noteq> option.None\<rbrakk> \<Longrightarrow> frame \<sigma> (s \<union> w) \<sigma>' (s \<union> w')"
   apply (clarsimp simp: frame_def)
   apply (rule conjI; clarsimp)
  apply (clarsimp simp: frame_def)
  apply (rule conjI; clarsimp)
  done

lemma upd_wa_mapAccumnb_bod_preservation:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; upd.proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>'; (wa \<union> wb) \<inter> rc = {}; 
    wa \<inter> wb = {}; wa \<inter> rb = {}; p \<notin> wa \<union> rb \<union> wb \<union> rc; \<sigma> p = option.Some (UAbstract (UWA t len arr));
    upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv (rb \<union> rc) (\<sigma>', res); 
    wa_abs_typing_u (UWA t len arr) ''WordArray'' [t] (Boxed Writable ptrl) ra wa \<sigma>;
    upd.uval_typing \<Xi>' \<sigma> acc u rb wb; upd.uval_typing \<Xi>' \<sigma> obsv v rc {};
    \<Xi>', [], [option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)] 
      \<turnstile> (App f (Var 0)) : TRecord [(b0, t, Present), (b1, u, Present)] Unboxed;
    distinct [a0, a1, a2]; distinct [b0, b1]\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. 
      upd.uval_typing \<Xi>' \<sigma>' res (TRecord [(b0, (TCon ''WordArray'' [t] (Boxed Writable ptrl), Present)),
        (b1, (u, Present))] Unboxed) r' (insert p w') \<and> 
      r' \<subseteq> (ra \<union> rb \<union> rc) \<and> frame \<sigma> (wa \<union> wb) \<sigma>' w'"
  apply (induct to arbitrary: \<sigma>' res)
   apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp)
   apply (rule_tac x = "ra \<union> rb" in exI)
   apply (rule_tac x = "wa \<union> wb" in exI)
   apply (clarsimp simp: upd.frame_id)
   apply (rule upd.u_t_struct; simp?)
   apply (subst Set.Un_insert_left[symmetric])
   apply (rule upd.u_t_r_cons1[where r' = rb and w' = wb, simplified]; simp?)
     apply (rule_tac ptrl = ptrl and
      a = "UWA (TPrim (Num ta)) len arr"
      in upd.u_t_p_abs_w[where ts = "[TPrim _]", simplified]; simp?)
     apply (drule_tac wa_abs_typing_u_elims(3); simp)
    apply (rule upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
     apply (rule upd.u_t_r_empty)
    apply (drule upd.type_repr_uval_repr(1); simp)
   apply (drule_tac wa_abs_typing_u_elims(3); simp)
  apply (case_tac "len < 1 + to")
   apply (drule upd_wa_mapAccumnb_bod_back_step'; simp?)
  apply (case_tac "1 + to \<le> frm")
   apply (frule_tac y = "1 + to" and x = frm in leD)
   apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp)
   apply (rule_tac x = "ra \<union> rb" in exI)
   apply (rule_tac x = "wa \<union> wb" in exI)
   apply (clarsimp simp: upd.frame_id)
   apply (rule upd.u_t_struct; simp?)
   apply (subst Set.Un_insert_left[symmetric])
   apply (rule upd.u_t_r_cons1[where r' = rb and w' = wb, simplified]; simp?)
     apply (rule_tac ptrl = ptrl and
      a = "UWA (TPrim (Num ta)) len arr"
      in upd.u_t_p_abs_w[where ts = "[TPrim _]", simplified]; simp?)
     apply (drule_tac wa_abs_typing_u_elims(3); simp)
    apply (rule upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
     apply (rule upd.u_t_r_empty)
    apply (drule upd.type_repr_uval_repr(1); simp)
   apply (drule_tac wa_abs_typing_u_elims(3); simp)
  apply (subgoal_tac "to < len")
   apply (frule_tac wa_abs_typing_u_elims(1); clarsimp)
   apply (frule upd_wa_mapAccumnb_bod_preservation'; simp?)
   apply clarsimp
   apply (drule upd_wa_mapAccumnb_bod_back_step; simp?)
    apply (drule wa_abs_typing_u_elims(6); simp)
   apply clarsimp
   apply (drule_tac x = \<sigma>'' in meta_spec)
   apply (drule_tac x = "URecord [
    (UPtr p (RCon ''WordArray'' [RPrim (Num ta)]), RPtr (RCon ''WordArray'' [RPrim (Num ta)])),
    (r'', upd.uval_repr r'')]" in meta_spec)
   apply clarsimp
   apply (erule upd.u_t_recE; clarsimp)
   apply (erule upd.u_t_r_consE; simp?)
  apply (erule conjE)+
   apply (drule_tac t = "type_repr _" in sym)+
   apply clarsimp
   apply (erule upd.u_t_r_consE; simp?)
  apply (erule conjE)+
   apply (drule_tac t = "type_repr _" in sym)+
   apply clarsimp
   apply (erule upd.u_t_r_emptyE; clarsimp)
   apply (drule_tac r = "raa \<union> rc" and 
      w = waa and
      ?\<Gamma> = "[option.Some (TRecord [(a0, TPrim (Num ta), Present), (a1, u, Present), (a2, v, Present)] Unboxed)]" and
      \<tau> = "TRecord [(b0, TPrim (Num ta), Present), (b1, u, Present)] Unboxed" 
      in upd.preservation_mono(1); simp?)
    apply (rule upd.matches_ptrs_some[where ts = "[]" and r' = "{}" and w' = "{}", simplified])
     apply (rule upd.u_t_struct; simp?)
     apply (rule upd.u_t_r_cons1[where r = "{}" and w = "{}", simplified])
       apply (drule wa_abs_typing_u_elims(5))
       apply (erule_tac x = to in allE)
       apply clarsimp
       apply (rule upd.u_t_prim'; clarsimp)
      apply (rule upd.u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
       apply (rule upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
         apply (rule upd.uval_typing_frame(1); simp?)
         apply blast
        apply (rule upd.u_t_r_empty)
       apply (drule_tac v = obsv in upd.type_repr_uval_repr(1); simp)
      apply (rule disjointI)
      apply (frule_tac p = y and u = obsv in upd.uval_typing_valid(1)[rotated 1]; simp)
      apply clarsimp
      apply (drule_tac x = y in orthD2; simp)
      apply clarsimp
      apply (drule_tac p = y and  \<sigma> = \<sigma> in readonly_not_in_frame; simp?)
      apply (subgoal_tac "y \<notin> w \<union> waa")
       apply blast
      apply (drule_tac t = "w \<union> waa" in sym)
      apply simp
      apply blast
     apply (frule wa_abs_typing_u_elims(5))
     apply (erule_tac x = to in allE)
     apply clarsimp
    apply (rule upd.matches_ptrs_empty[where \<tau>s = "[]", simplified])
   apply clarsimp
   apply (thin_tac "frame _ _ _ _")
   apply (cut_tac v = v' and l = "arr + size_of_num_type ta * to" and \<sigma> = \<sigma>''' in frame_single_update)
   apply (rule_tac x = r' in exI)
   apply (rule_tac x = "{arr + size_of_num_type ta * i |i. i < len} \<union> w'a" in exI)
   apply clarsimp
   apply (erule upd.u_t_recE; clarsimp)
   apply (erule upd.u_t_r_consE; simp?)
   apply (erule conjE)+
   apply (drule_tac t = "type_repr _" in sym)+
   apply clarsimp
   apply (erule upd.u_t_r_consE; simp?)
   apply (erule conjE)+
   apply clarsimp
   apply (erule upd.u_t_r_emptyE; clarsimp)
   apply (erule upd_u_t_prim_tE; clarsimp)
   apply (erule upd.u_t_p_absE[where s = "Boxed Writable _", simplified])
   apply (drule_tac s = "RCon _ _" in sym)
   apply (drule_tac t = "lit_type _" in sym; clarsimp)
   apply (frule_tac p = p and \<sigma> = \<sigma> in valid_ptr_not_in_frame_same; simp?)
   apply clarsimp
   apply (rule conjI)
    apply (rule upd.u_t_struct; simp?)
    apply (rule_tac upd.u_t_r_cons1[where r = "{}" and w = "insert _ _", simplified]; simp?)
       apply (rule_tac ptrl = ptrl and
      a = "UWA (TPrim (Num ta)) len arr"
      in upd.u_t_p_abs_w[where ts = "[TPrim _]", simplified]; simp?)
         apply (frule_tac \<sigma> = \<sigma>'' in wa_abs_typing_u_elims(3); clarsimp)
         apply (drule_tac \<sigma> = \<sigma>'' and \<sigma>' = \<sigma>''' in upd.abs_typing_frame; simp?)
         apply (rule wa_abs_typing_u_update; simp?)
        apply (rule conjI; clarsimp)
         apply (frule wa_abs_typing_u_elims(5))
         apply (erule_tac x = to in allE)
         apply clarsimp
        apply (drule_tac p = p and \<sigma> = \<sigma>'' in valid_ptr_not_in_frame_same; simp?)
       apply (drule wa_abs_typing_u_elims(3); clarsimp)
      apply (rule upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
       apply (drule_tac u = xb and r = rca and w = wc and \<sigma> = \<sigma>''' in upd.uval_typing_frame(1); simp?)
        apply (frule_tac p = "arr + size_of_num_type ta * to" in upd.abs_typing_valid; simp?)
         apply (drule wa_abs_typing_u_elims(3); clarsimp)
         apply (rule_tac x = to in exI; simp)
        apply clarsimp
        apply (frule_tac w = wba in wa_abs_typing_u_elims(5))
        apply (erule_tac x = to in allE; clarsimp)
        apply (drule_tac p = "arr + size_of_num_type ta * to" and \<sigma> = \<sigma>'' in readonly_not_in_frame; simp?)
        apply (drule_tac x = "arr + size_of_num_type ta * to" and S = wba in orthD1; simp?)
        apply (drule_tac w = wba in wa_abs_typing_u_elims(3); clarsimp)
        apply (rule_tac x = to in exI; simp)
       apply (drule_tac x = "arr + size_of_num_type ta * to" and S = wba and S' = raa in orthD1; simp?)
        apply (drule_tac w = wba in wa_abs_typing_u_elims(3); clarsimp)
        apply (rule_tac x = to in exI; simp)
       apply (drule_tac x = "arr + size_of_num_type ta * to" and S' = rc in orthD1; simp?)
        apply (rule disjI1)
        apply (drule wa_abs_typing_u_elims(3); clarsimp)
        apply (rule_tac x = to in exI; clarsimp)
       apply clarsimp
       apply (drule_tac A = rca and B = "raa \<union> rc" and x = "arr + size_of_num_type ta * to" in in_mono)
       apply blast
      apply (rule upd.u_t_r_empty)
     apply (frule_tac p = p  and \<sigma> = \<sigma>'' in readonly_not_in_frame; simp?)
     apply (rule disjointI)
     apply (frule_tac p = "xa" in upd.abs_typing_valid; simp?)
      apply clarsimp
      apply (drule wa_abs_typing_u_elims(3); clarsimp)
     apply clarsimp
     apply (frule_tac \<sigma> = \<sigma>'' in wa_abs_typing_u_elims(5))
     apply (erule_tac x = i in allE; clarsimp)
     apply (drule_tac p = "arr + size_of_num_type ta * i" and \<sigma> = \<sigma>'' in readonly_not_in_frame; simp?)
     apply (drule_tac x = "arr + size_of_num_type ta * i" and S = wba in orthD1; simp?)
     apply (drule_tac w = wba in wa_abs_typing_u_elims(3); clarsimp)
     apply (rule_tac x = i in exI; simp)
    apply (rule conjI)
     apply (drule_tac A = rca and B = "raa \<union> rc" and x = p in in_mono; clarsimp)
    apply (rule disjointI)
    apply (drule_tac A = rca and B = "raa \<union> rc" and x = xa in in_mono; clarsimp)
    apply (erule disjE)
     apply (drule_tac x = "arr + size_of_num_type ta * i" and S' = raa in orthD1; simp?)
     apply (drule_tac w = wba in wa_abs_typing_u_elims(3); clarsimp)
     apply (rule_tac x = i in exI; simp)
    apply (drule_tac x = "arr + size_of_num_type ta * i" and S' = rc in orthD1; simp?)
    apply (drule wa_abs_typing_u_elims(3); clarsimp)
    apply (rule_tac x = i in exI; simp)
   apply (rule conjI)
    apply (drule_tac A = rca and B = "raa \<union> rc" and C = "ra \<union> rb \<union> rc" in subset_trans; simp?)
   apply (frule_tac p = p  and \<sigma> = \<sigma> in readonly_not_in_frame; simp?)
   apply (frule_tac A = "w'" and x = p and B = "wba \<union> waa" in insert_ident; simp?)
   apply (drule_tac \<sigma> = \<sigma>'' and s = wba in frame_expand(2))
    apply (frule_tac w = wba in wa_abs_typing_u_elims(5); clarsimp)
    apply (drule_tac w = wba in wa_abs_typing_u_elims(3); clarsimp)
    apply (thin_tac "\<forall>i. p = arr + size_of_num_type ta * i \<longrightarrow> \<not> i < len")
    apply (erule_tac x = i in allE; clarsimp)
   apply (drule_tac \<sigma> = \<sigma> and \<sigma>' = \<sigma>'' and \<sigma>'' = \<sigma>''' in upd.frame_trans; simp?)
   apply (drule_tac \<sigma> = \<sigma> in upd.frame_app; simp?)
   apply clarsimp
   apply (subst (asm) insert_absorb[where A = "_ \<union> wb"])
    apply clarsimp
    apply (drule wa_abs_typing_u_elims(3); clarsimp)
    apply (rule_tac x = to in exI; simp)
   apply (subst (asm) insert_absorb[where A = "_ \<union> _"])
    apply (drule_tac w = wba in wa_abs_typing_u_elims(3); clarsimp)
    apply (rule_tac x = to in exI; simp)
   apply (drule_tac w = wba in wa_abs_typing_u_elims(3); clarsimp)
  apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
  done

lemma upd_wa_foldnb_0_preservation:
  "\<And>K a b \<sigma> \<sigma>' \<tau>s v v' r w.
   \<lbrakk>list_all2 (kinding []) \<tau>s K; wordarray_fold_no_break_0_type = (K, a, b);
    upd.uval_typing \<Xi> \<sigma> v (instantiate \<tau>s a) r w; upd_wa_foldnb_0 \<Xi> \<xi>0 abbreviatedType1 (\<sigma>, v) (\<sigma>', v')\<rbrakk>
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
  apply (subst (asm) abbreviatedType1_def; clarsimp)
  apply (frule_tac r = rb and r' = rg in upd.uval_typing_unique_ptrs(1); simp?)
  apply clarsimp
  apply (frule_tac r = ra and r' = rf in upd.uval_typing_unique_ptrs(1); simp?)
  apply clarsimp
  apply (erule upd.u_t_primE)+
  apply (drule_tac t = "lit_type _" in sym)+
  apply clarsimp
  apply (clarsimp simp: abbreviatedType1_def)
  apply (drule_tac ra = rh and rb = rf and rc = rg and wb = wd in 
      upd_wa_foldnb_bod_preservation[OF proc_ctx_wellformed_\<Xi> upd_proc_env_matches_ptrs_\<xi>0_\<Xi>, 
        where ptrl = undefined and wa = "{}", simplified]; simp?; clarsimp?)
  apply (rule_tac x = r' in exI)
  apply (rule_tac x = w' in exI)
  apply (case_tac xa; clarsimp)
   apply (erule upd.u_t_functionE; clarsimp)
   apply blast
  apply (erule upd.u_t_afunE; clarsimp)
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

lemma val_wa_foldnb_bod_rename_monoexpr_correct:
  "\<lbrakk>val.proc_env_matches \<xi>\<^sub>m \<Xi>'; proc_ctx_wellformed \<Xi>'; 
    value_sem.rename_mono_prog wa_abs_typing_v rename' \<Xi>' \<xi>\<^sub>m \<xi>\<^sub>p;
    val_wa_foldnb_bod \<xi>\<^sub>m t xs frm to (vvalfun_to_exprfun (val.rename_val rename' (val.monoval f))) 
      (val.rename_val rename' (val.monoval acc )) (val.rename_val rename' (val.monoval obsv)) r;
    is_vval_fun (val.rename_val rename' (val.monoval f)); wa_abs_typing_v (VWA t xs) ''WordArray'' [t]; 
    val.vval_typing \<Xi>' (val.rename_val rename' (val.monoval acc )) u;
    val.vval_typing \<Xi>' (val.rename_val rename' (val.monoval obsv)) v;
    \<Xi>', [], [option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)] \<turnstile>
      App (vvalfun_to_exprfun (val.rename_val rename' (val.monoval f))) (Var 0) : u; 
    distinct [a0, a1, a2]\<rbrakk>
       \<Longrightarrow> is_vval_fun f \<and> (\<exists>r'. r = val.rename_val rename' (val.monoval r') \<and>
         val_wa_foldnb_bod \<xi>\<^sub>p t xs frm to (vvalfun_to_exprfun f) acc obsv r')"
  apply (rule conjI)
   apply (case_tac f; clarsimp)
  apply (induct to arbitrary: r)
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
   apply (subst val_wa_foldnb_bod.simps; clarsimp)
  apply (case_tac "length xs < Suc to")
   apply (drule val_wa_foldnb_bod_back_step'; simp)
   apply (drule val_wa_foldnb_bod_to_geq_lenD)
    apply linarith
   apply (drule_tac x = r in meta_spec)
   apply clarsimp
   apply (erule meta_impE)
    apply (rule val_wa_foldnb_bod_to_geq_len; simp?)
   apply clarsimp
   apply (rule_tac x = r' in exI; clarsimp)
   apply (rule val_wa_foldnb_bod_to_geq_len; simp?)
   apply (drule_tac to = to in val_wa_foldnb_bod_to_geq_lenD; simp?)
  apply (case_tac "frm \<ge> Suc to")
   apply (clarsimp simp: not_less not_le)
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
   apply (subst val_wa_foldnb_bod.simps; clarsimp)
  apply (drule val_wa_foldnb_bod_back_step; simp?)
  apply clarsimp
  apply (drule_tac x = r' in meta_spec)
  apply clarsimp
  apply (frule_tac \<gamma> = "[VRecord [xs ! to, r'a, obsv]]" and
      ?\<Gamma> = "[option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)]" and
      e = "App (vvalfun_to_exprfun f) (Var 0)" and
      v' = r and
      \<tau> = u in val.rename_monoexpr_correct(1); simp?)
     apply (clarsimp simp: val.matches_Cons[where xs = "[]" and ys = "[]", simplified])
     apply (clarsimp simp: val.matches_def)
     apply (rule val.v_t_record; simp?)
     apply (rule val.v_t_r_cons1; clarsimp?)
      apply (frule wa_abs_typing_v_elims(1); clarsimp)
      apply (drule wa_abs_typing_v_elims(2))
      apply (erule_tac x = to in allE; clarsimp)
      apply (rule val.v_t_prim'; clarsimp)
     apply (rule val.v_t_r_cons1; clarsimp?)
      apply (drule val_wa_foldnb_bod_preservation; simp?)
     apply (rule val.v_t_r_cons1; clarsimp?)
     apply (rule val.v_t_r_empty)
    apply (frule wa_abs_typing_v_elims(1); clarsimp)
    apply (drule wa_abs_typing_v_elims(2))
    apply (erule_tac x = to in allE; clarsimp)
    apply (case_tac f; clarsimp)
   apply (case_tac f; clarsimp)
  apply clarsimp
  apply (drule_tac \<xi>\<^sub>v = \<xi>\<^sub>p in val_wa_foldnb_bod_step; simp?)
  apply (rule_tac x = va in exI)
  apply clarsimp
  done

lemma val_wa_mapAccumnb_bod_rename_monoexpr_correct:
  "\<lbrakk>val.proc_env_matches \<xi>\<^sub>m \<Xi>'; proc_ctx_wellformed \<Xi>'; 
    value_sem.rename_mono_prog wa_abs_typing_v rename' \<Xi>' \<xi>\<^sub>m \<xi>\<^sub>p;
    val_wa_mapAccumnb_bod \<xi>\<^sub>m t xs frm to (vvalfun_to_exprfun (val.rename_val rename' (val.monoval f))) 
      (val.rename_val rename' (val.monoval acc )) (val.rename_val rename' (val.monoval obsv)) r;
    is_vval_fun (val.rename_val rename' (val.monoval f)); wa_abs_typing_v (VWA t xs) ''WordArray'' [t]; 
    val.vval_typing \<Xi>' (val.rename_val rename' (val.monoval acc )) u;
    val.vval_typing \<Xi>' (val.rename_val rename' (val.monoval obsv)) v;
    \<Xi>', [], [option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)] \<turnstile>
      App (vvalfun_to_exprfun (val.rename_val rename' (val.monoval f))) (Var 0) :
      TRecord [(b0, t, Present), (b1, u, Present)] Unboxed; distinct [a0, a1, a2]; distinct [b0, b1]\<rbrakk>
       \<Longrightarrow> is_vval_fun f \<and> (\<exists>r'. r = val.rename_val rename' (val.monoval r') \<and>
         val_wa_mapAccumnb_bod \<xi>\<^sub>p t xs frm to (vvalfun_to_exprfun f) acc obsv r')"
  apply (rule conjI)
   apply (case_tac f; clarsimp)
  apply (induct to arbitrary: r)
   apply (erule val_wa_mapAccumnb_bod.elims; clarsimp)
   apply (subst val_wa_mapAccumnb_bod.simps; clarsimp)
  apply (case_tac "length xs < Suc to")
   apply (drule val_wa_mapAccumnb_bod_back_step'; simp)
   apply (drule val_wa_mapAccumnb_bod_to_geq_lenD)
    apply linarith
   apply (drule_tac x = r in meta_spec)
   apply clarsimp
   apply (erule meta_impE)
    apply (rule val_wa_mapAccumnb_bod_to_geq_len; simp?)
   apply clarsimp
   apply (rule_tac x = r' in exI; clarsimp)
   apply (rule val_wa_mapAccumnb_bod_to_geq_len; simp?)
   apply (drule_tac to = to in val_wa_mapAccumnb_bod_to_geq_lenD; simp?)
  apply (case_tac "frm \<ge> Suc to")
  apply (clarsimp simp: not_less not_le)
   apply (erule val_wa_mapAccumnb_bod.elims; clarsimp)
   apply (subst val_wa_mapAccumnb_bod.simps; clarsimp)
  apply (frule val_wa_mapAccumnb_bod_preservation'; clarsimp)
  apply (drule val_wa_mapAccumnb_bod_back_step; simp?)
  apply clarsimp
  apply (drule_tac x = "VRecord [VAbstract (VWA t (rxs[to := xs ! to])), racc']" in meta_spec)
  apply clarsimp
  apply (case_tac r'; clarsimp)
  apply (case_tac z; clarsimp)
  apply (frule_tac \<gamma> = "[VRecord [xs ! to, za, obsv]]" and
      ?\<Gamma> = "[option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)]" and
      e = "App (vvalfun_to_exprfun f) (Var 0)" and
      v' = "VRecord [rxs ! to, racc]" and
      \<tau> = "TRecord [(b0, t, Present), (b1, u, Present)] Unboxed" 
      in val.rename_monoexpr_correct(1); simp?)
     apply (clarsimp simp: val.matches_Cons[where xs = "[]" and ys = "[]", simplified])
     apply (clarsimp simp: val.matches_def)
     apply (rule val.v_t_record; simp?)
     apply (rule val.v_t_r_cons1; clarsimp?)
      apply (frule wa_abs_typing_v_elims(1); clarsimp)
      apply (drule wa_abs_typing_v_elims(2))
      apply (erule_tac x = to in allE; clarsimp)
      apply (rule val.v_t_prim'; clarsimp)
     apply (rule val.v_t_r_cons1; clarsimp?)
      apply (drule val_wa_mapAccumnb_bod_preservation; simp?)
      apply (erule val.v_t_recordE; clarsimp)
      apply (erule val.v_t_r_consE; clarsimp)+
     apply (rule val.v_t_r_cons1; clarsimp?)
     apply (rule val.v_t_r_empty)
    apply (frule wa_abs_typing_v_elims(1); clarsimp)
    apply (drule wa_abs_typing_v_elims(2))
    apply (erule_tac x = to in allE; clarsimp)
    apply (case_tac f; clarsimp)
   apply (case_tac f; clarsimp)
  apply clarsimp
  apply (case_tac va; clarsimp)
  apply (drule_tac \<xi>\<^sub>v = \<xi>\<^sub>p in val_wa_mapAccumnb_bod_step; simp?)
  apply (rule_tac x = "VRecord [VAbstract (VWA t (rxs[to := z])), zb]" in exI)
  apply clarsimp
   apply (frule_tac e = "App (vvalfun_to_exprfun (val.rename_val rename' (val.monoval f))) (Var 0)" and
      v = "VRecord [val.rename_val rename' (val.monoval z), val.rename_val rename' (val.monoval zb)]" and
      \<gamma> = "[VRecord [xs ! to, val.rename_val rename' (val.monoval za), val.rename_val rename' (val.monoval obsv)]]" and
      \<tau> = "TRecord [(b0, t, Present), (b1, u, Present)] Unboxed" and
      \<Gamma> = "[option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)]" 
      in val.preservation(1)[of "[]" "[]" _ _ _  \<xi>\<^sub>m, simplified]; simp?)
  apply (clarsimp simp: val.matches_def)
  apply (rule val.v_t_record; simp?)
   apply (rule val.v_t_r_cons1)
    apply (frule wa_abs_typing_v_elims(1); clarsimp)
    apply (drule wa_abs_typing_v_elims(2))
    apply (erule_tac x = to in allE; clarsimp)
    apply (rule val.v_t_prim'; clarsimp)
   apply (rule val.v_t_r_cons1; simp?)
    apply (drule val_wa_mapAccumnb_bod_preservation; simp?)
    apply (erule val.v_t_recordE; clarsimp)
    apply (erule val.v_t_r_consE; clarsimp)+
   apply (rule val.v_t_r_cons1; simp?)
   apply (rule val.v_t_r_empty)
  apply (erule val.v_t_recordE; clarsimp)
   apply (erule val.v_t_r_consE; clarsimp)+
  apply (erule val.v_t_r_emptyE; simp)
  apply (drule wa_abs_typing_v_elims(1); clarsimp)
  apply (clarsimp simp: val.vval_typing.simps[of _ _ "TPrim _", simplified])
  apply (case_tac z; clarsimp)
  by (simp add: upd.list_helper)
  

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
  apply (clarsimp split: if_split_asm simp: val_wa_foldnb_0_def val_wa_foldnbp_def)
  apply (case_tac v; clarsimp)
  apply (clarsimp simp: abbreviatedType1_def)
  thm val_wa_foldnb_bod_rename_monoexpr_correct
  apply (drule_tac xs = xs and frm = "unat frm" and to = "unat to" and acc = zd and obsv = ze and
      r = v' and \<xi>\<^sub>p = \<xi>p in 
      val_wa_foldnb_bod_rename_monoexpr_correct[OF val_proc_env_matches_\<xi>m_\<Xi>] ; simp?)
    apply (rule value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p)
   apply clarsimp
  apply clarsimp
  apply (rule_tac x = r' in exI; clarsimp)
  apply (case_tac z; clarsimp)
  apply (case_tac za; clarsimp)
  apply(case_tac zb; clarsimp)
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
  apply (clarsimp simp: wordarray_fold_no_break_0_type_def val_wa_foldnb_0_def)
  apply (erule val.v_t_recordE)
  apply (erule val.v_t_r_consE; clarsimp)+
  apply (erule val.v_t_abstractE; clarsimp)
  apply (clarsimp simp: abbreviatedType1_def)
  apply (drule val_wa_foldnb_bod_preservation[OF proc_ctx_wellformed_\<Xi> val_proc_env_matches_\<xi>m_\<Xi>]; simp?)
  apply clarsimp
  done

lemma upd_val_wa_foldnb_bod_corres:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; proc_env_u_v_matches \<xi>\<^sub>u \<xi>\<^sub>v \<Xi>'; 
    upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv (ra \<union> s) (\<sigma>', res); 
    val_wa_foldnb_bod \<xi>\<^sub>v v xs (unat frm) (unat to) f acc' obsv' res';
    \<sigma> p = option.Some (UAbstract (UWA v len arr));
    wa_abs_upd_val (UWA v len arr) (VWA v xs) ''WordArray'' [v] (Boxed ReadOnly ptrl) r w \<sigma>;
    upd_val_rel \<Xi>' \<sigma> acc acc' u ra wa; upd_val_rel \<Xi>' \<sigma> obsv obsv' t s {}; wa \<inter> s = {};
    \<tau> = TRecord [(a0, (v, Present)), (a1, (u, Present)), (a2, (t, Present))] Unboxed;
     \<Xi>', [], [option.Some \<tau>] \<turnstile> App f (Var 0) : u; distinct [a0, a1, a2]\<rbrakk>
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
  apply (clarsimp simp: wa_abs_upd_val_def)
  apply (case_tac v; clarsimp)
  apply (case_tac x5; clarsimp)
  apply (drule upd_wa_foldnb_bod_back_step; simp?)
  apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
  apply (drule_tac val_wa_foldnb_bod_back_step; simp?)
  apply clarsimp
  apply (drule_tac x = r'' in meta_spec)
  apply (drule_tac x = r' in meta_spec)
  apply (drule_tac x = \<sigma>'' in meta_spec)
  apply clarsimp
  apply (frule_tac \<gamma> = "[URecord [(va, upd.uval_repr va), (r'', upd.uval_repr r''),
      (obsv, upd.uval_repr obsv)]]" and 
      \<gamma>' = "[VRecord [xs ! unat to, r', obsv']]" and
      r = "ra' \<union> s" and w = wa' in mono_correspondence(1); simp?; clarsimp?)
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
    wa_abs_upd_val (UWA v len arr) (VWA v xs) ''WordArray'' [v] (Boxed ReadOnly ptrl) r w \<sigma>;
    upd_val_rel \<Xi>' \<sigma> acc acc' u ra wa; upd_val_rel \<Xi>' \<sigma> obsv obsv' t s {}; wa \<inter> s = {};
    \<tau> = TRecord [(a0, (v, Present)), (a1, (u, Present)), (a2, (t, Present))] Unboxed;
     \<Xi>', [], [option.Some \<tau>] \<turnstile> App f (Var 0) : u; distinct [a0, a1, a2]\<rbrakk>
    \<Longrightarrow> \<exists>res'. val_wa_foldnb_bod \<xi>\<^sub>v v xs (unat frm) (unat to) f acc' obsv' res'"
  apply (induct to arbitrary: \<sigma>' res)
   apply (rule_tac x = acc' in exI)
   apply (subst val_wa_foldnb_bod.simps; clarsimp)
   apply clarsimp
  apply (case_tac "len < 1 + to")
   apply (drule upd_wa_foldnb_bod_back_step'; simp?)
   apply (erule_tac x = \<sigma>' in meta_allE)
   apply (erule_tac x = res in meta_allE)
   apply clarsimp
   apply (rule_tac x = x in exI)
   apply (drule val_wa_foldnb_bod_to_geq_lenD)
    apply (drule wa_abs_upd_val_elims(3); clarsimp simp: unatSuc word_less_nat_alt)
   apply (drule unatSuc; clarsimp)
   apply (rule val_wa_foldnb_bod_to_geq_len; simp?)
   apply (drule wa_abs_upd_val_elims(3); clarsimp simp: unatSuc word_less_nat_alt)
  apply (case_tac "1 + to \<le> frm")
   apply (rule_tac x = acc' in exI)
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
   apply (subst val_wa_foldnb_bod.simps; clarsimp)
  apply (frule wa_abs_upd_val_elims(2))
  apply (drule wa_abs_typing_v_elims(1); clarsimp)
  apply (drule_tac upd_wa_foldnb_bod_back_step; simp?)
  apply clarsimp
  apply (drule_tac x = \<sigma>'' in meta_spec)
  apply (drule_tac x = r'' in meta_spec)
  apply clarsimp
  apply (frule_tac r = r and w = w and ptrl = ptrl in upd_val_wa_foldnb_bod_corres; simp?)
  apply clarsimp
  apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
  apply (frule_tac \<gamma> = "[URecord [(va, upd.uval_repr va), (r'', upd.uval_repr r''), 
      (obsv, upd.uval_repr obsv)]]" and
      \<gamma>' = "[VRecord [xs ! unat to, x, obsv']]" and
      r = "ra' \<union> s" and w = wa' in val_executes_from_upd_executes(1); simp?; clarsimp?)
   apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
    apply (rule u_v_struct; simp?)
    apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
      apply (drule wa_abs_upd_val_elims(4))
      apply (erule_tac x = to in allE; clarsimp simp: word_less_nat_alt)+
      apply (rule u_v_prim'; clarsimp)
     apply (rule u_v_r_cons1[where r' = s and w' = "{}", simplified]; simp?)
       apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
         apply (rule upd_val_rel_frame(1); simp add: Int_commute)
        apply (rule u_v_r_empty)
       apply (drule_tac u = obsv in  upd_val_rel_to_uval_typing(1))
       apply (drule upd.type_repr_uval_repr(1); simp)
      apply (rule disjointI)
      apply (drule_tac u = obsv and p = y in upd_val_rel_valid(1)[rotated 1]; simp?)
      apply clarsimp
      apply (drule_tac p = y and \<sigma> = \<sigma> in readonly_not_in_frame; simp?)
      apply blast
     apply (drule_tac u = r'' in  upd_val_rel_to_uval_typing(1))
     apply (drule upd.type_repr_uval_repr(1); simp)
    apply (drule wa_abs_upd_val_elims(4))
    apply (erule_tac x = to in allE; clarsimp simp: word_less_nat_alt)+
   apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
  apply (drule_tac r' = v' in  val_wa_foldnb_bod_step; simp?)
   apply (drule wa_abs_upd_val_elims(3); simp)
  apply (rule_tac x = v' in exI)
  apply clarsimp
  done


lemma upd_val_wa_mapAccumnb_bod_corres:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; proc_env_u_v_matches \<xi>\<^sub>u \<xi>\<^sub>v \<Xi>'; 
    upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv (rb \<union> rc) (\<sigma>', res); 
    val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs (unat frm) (unat to) f acc' obsv' res';
    \<sigma> p = option.Some (UAbstract (UWA t len arr));
    wa_abs_upd_val (UWA t len arr) (VWA t xs) ''WordArray'' [t] (Boxed Writable ptrl) ra wa \<sigma>;
    upd_val_rel \<Xi>' \<sigma> acc acc' u rb wb; upd_val_rel \<Xi>' \<sigma> obsv obsv' v rc {};
    (wa \<union> wb) \<inter> rc = {}; wa \<inter> wb = {}; wa \<inter> rb = {}; p \<notin> wa \<union> rb \<union> wb \<union> rc;
    \<Xi>', [], [option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)] 
      \<turnstile> (App f (Var 0)) : TRecord [(b0, t, Present), (b1, u, Present)] Unboxed;
    distinct [a0, a1, a2]; distinct [b0, b1]\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. upd_val_rel \<Xi>' \<sigma>' res res' (TRecord [
        (b0, TCon ''WordArray'' [t] (Boxed Writable ptrl), Present),
        (b1, u, Present)] Unboxed) r'(insert p w') \<and> 
      r' \<subseteq> (ra \<union> rb \<union> rc)\<and> frame \<sigma> (wa \<union> wb) \<sigma>' w'"
  apply (induct to arbitrary:  \<sigma>' res' res)
   apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp)
   apply (erule val_wa_mapAccumnb_bod.elims; clarsimp)
   apply (rule_tac x = "ra \<union> rb" in exI)
   apply (rule_tac x = "wa \<union> wb" in exI)
   apply (clarsimp simp: upd.frame_id)
   apply (rule u_v_struct; simp?)
   apply (subst Set.Un_insert_left[symmetric])
   apply (rule u_v_r_cons1; simp?)
     apply (rule_tac ptrl = ptrl in u_v_p_abs_w[where ts = "[TPrim _]", simplified]; simp?)
     apply (drule wa_abs_upd_val_elims(1))
     apply (drule wa_abs_typing_u_elims(3); clarsimp)
    apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
     apply (rule u_v_r_empty)
    apply (drule upd_val_rel_to_uval_typing)
    apply (drule upd.type_repr_uval_repr(1); simp)
   apply (drule wa_abs_upd_val_elims(1))
   apply (drule wa_abs_typing_u_elims(3); clarsimp)
  apply (case_tac "len < 1 + to")
   apply (drule upd_wa_mapAccumnb_bod_back_step'; simp?)
   apply (drule unatSuc; clarsimp)
   apply (drule val_wa_mapAccumnb_bod_back_step'; simp?)
   apply (drule wa_abs_upd_val_elims(3); clarsimp simp: word_less_nat_alt)
  apply (case_tac "1 + to \<le> frm")
   apply (frule_tac y = "1 + to" and x = frm in leD)
   apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp)
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
   apply (erule val_wa_mapAccumnb_bod.elims; clarsimp)
   apply (rule_tac x = "ra \<union> rb" in exI)
   apply (rule_tac x = "wa \<union> wb" in exI)
   apply (clarsimp simp: upd.frame_id)
   apply (rule u_v_struct; simp?)
   apply (subst Set.Un_insert_left[symmetric])
   apply (rule u_v_r_cons1; simp?)
     apply (rule_tac ptrl = ptrl in u_v_p_abs_w[where ts = "[TPrim _]", simplified]; simp?)
     apply (drule wa_abs_upd_val_elims(1))
     apply (drule wa_abs_typing_u_elims(3); clarsimp)
    apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
     apply (rule u_v_r_empty)
    apply (drule upd_val_rel_to_uval_typing)
    apply (drule upd.type_repr_uval_repr(1); simp)
   apply (drule wa_abs_upd_val_elims(1))
   apply (drule wa_abs_typing_u_elims(3); clarsimp)
  apply (frule wa_abs_upd_val_elims(2))
  apply (drule wa_abs_typing_v_elims(1); clarsimp)
  apply (frule upd_wa_mapAccumnb_bod_preservation'; simp?; clarsimp)
  apply (drule upd_wa_mapAccumnb_bod_back_step; simp?)
   apply (drule wa_abs_upd_val_elims(1))
   apply (drule wa_abs_typing_u_elims(6); clarsimp)
  apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
  apply (frule val_wa_mapAccumnb_bod_preservation'; clarsimp)
  apply (drule val_wa_mapAccumnb_bod_back_step; simp?)
   apply (drule wa_abs_upd_val_elims(3); clarsimp)
  apply clarsimp
  apply (drule_tac x = \<sigma>'' in meta_spec)
  apply (erule meta_allE; erule meta_allE; erule meta_impE; simp?; erule meta_impE; simp?)
  apply clarsimp
  apply (erule u_v_recE; clarsimp)
  apply (erule u_v_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)
  apply clarsimp
  apply (erule u_v_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)
  apply clarsimp
  apply (erule u_v_r_emptyE; clarsimp)
  apply (frule_tac \<gamma> = "[URecord [(va, upd.uval_repr va), (x, upd.uval_repr x),
      (obsv, upd.uval_repr obsv)]]" and 
      \<gamma>' = "[VRecord [xs ! unat to, racc', obsv']]" and
      r = "raa \<union> rc" and w = waa in mono_correspondence(1); simp?; clarsimp?)
   apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
    apply (rule u_v_struct; simp?)
    apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
      apply (drule wa_abs_upd_val_elims(4))
      apply (erule_tac x = to in allE; clarsimp simp: word_less_nat_alt)
      apply (rule u_v_prim'; clarsimp)
     apply (rule u_v_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
      apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
        apply (rule upd_val_rel_frame; simp?; simp add: Int_commute)
       apply (rule u_v_r_empty)
      apply (drule_tac u = obsv in upd_val_rel_to_uval_typing(1))
      apply (drule_tac v = obsv in upd.type_repr_uval_repr(1); simp)
     apply (rule disjointI)
     apply (drule_tac u = obsv in upd_val_rel_to_uval_typing(1))
     apply (frule_tac p = y and u = obsv in upd.uval_typing_valid(1)[rotated 1]; simp)
     apply clarsimp
     apply (drule_tac x = y in orthD2; simp)
     apply clarsimp
     apply (drule_tac p = y and  \<sigma> = \<sigma> in readonly_not_in_frame; simp?)
     apply (subgoal_tac "y \<notin> w \<union> waa")
      apply blast
     apply (drule_tac t = "w \<union> waa" in sym)
     apply simp
     apply blast
    apply (drule wa_abs_upd_val_elims(4))
    apply (erule_tac x = to in allE; clarsimp simp: word_less_nat_alt)
   apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
  apply (erule u_v_recE; clarsimp)
  apply (erule u_v_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)
  apply clarsimp
  apply (erule u_v_r_consE; simp)
  apply (erule conjE)+
  apply clarsimp
  apply (erule u_v_r_emptyE; clarsimp)
  apply (erule u_v_t_prim_tE)
  apply clarsimp
  apply (drule_tac t = "lit_type _" in sym)+
  apply clarsimp
  apply (thin_tac "frame _ _ _ _")
  apply (erule u_v_p_absE[where s = "Boxed Writable _" and ts = "[_]", simplified])
  apply (drule_tac t = "RCon _ _" in sym; clarsimp)
  apply (frule_tac p = p in valid_ptr_not_in_frame_same; simp?)
  apply clarsimp
  apply (frule_tac \<sigma> = \<sigma>'' in wa_abs_upd_val_elims(4))
  apply (erule_tac x = to in allE; clarsimp simp: word_less_nat_alt)
  apply (frule_tac \<sigma> = \<sigma>'' in wa_abs_upd_val_elims(3))
  apply (subst (asm) nth_list_update_eq; simp)
  apply (frule_tac \<sigma> = \<sigma>'' and p = "arr + size_of_num_type ta * to" in readonly_not_in_frame; simp?)
   apply (drule_tac w = wba in wa_abs_upd_val_elims(1))
   apply (drule wa_abs_typing_u_elims(3); clarsimp simp: word_less_nat_alt not_le not_less)
   apply (drule Suc_le_lessD)
   apply (drule_tac x = "arr + size_of_num_type ta * to" and S' = waa in orthD1; simp?)
   apply (rule_tac x = to in exI; simp)
  apply (frule_tac r = r in wa_abs_upd_val_elims(1))
  apply (drule_tac r = r in abs_upd_val_frame; simp?)
   apply (drule_tac wa_abs_typing_u_elims(3); simp)
  apply (cut_tac \<sigma> = \<sigma>''' and l = "arr + size_of_num_type ta * to" and v = "UPrim l" in frame_single_update)
  apply (drule_tac r = rca in upd_val_rel_frame(1)[rotated 3]; simp?)
    apply clarsimp
   apply (drule_tac x = "arr + size_of_num_type ta * to" and S = wba and S' = raa in orthD1; simp?)
    apply (drule_tac w = wba in wa_abs_upd_val_elims(1))
    apply (drule_tac w = wba in wa_abs_typing_u_elims(3); clarsimp)
    apply (rule_tac x = to in exI; simp add: word_less_nat_alt)
   apply (drule_tac x = "arr + size_of_num_type ta * to" and S' = rc in orthD1; simp?)
    apply (rule disjI1)
    apply (drule wa_abs_upd_val_elims(1))
    apply (drule_tac \<sigma> = \<sigma> in wa_abs_typing_u_elims(3); clarsimp)
    apply (rule_tac x = to in exI; clarsimp simp: word_less_nat_alt)
   apply clarsimp
   apply (drule_tac A = rca and B = "raa \<union> rc" and x = "arr + size_of_num_type ta * to" in in_mono)
   apply blast
  apply (rule_tac x = "r \<union> rca" in exI)
  apply (rule_tac x = "wba \<union> wc" in exI)
  apply (rule conjI)
   apply (rule u_v_struct; simp?)
   apply (subst Set.Un_insert_left[symmetric])
   apply (rule u_v_r_cons1; simp?)
       apply (rule_tac a = "UWA (TPrim (Num ta)) len arr" and 
      ptrl = ptrl in u_v_p_abs_w[where ts = "[TPrim _]", simplified]; simp?)
        apply (drule_tac \<sigma> = \<sigma>''' and  i = to in wa_abs_upd_val_update; simp?)
         apply (clarsimp simp: word_less_nat_alt)
        apply (drule_tac s = "rxs ! unat to" in sym; clarsimp)
       apply (drule wa_abs_upd_val_elims(1))
       apply (drule_tac \<sigma> = \<sigma> in wa_abs_typing_u_elims(3); clarsimp)
       apply (rule conjI; clarsimp)
       apply (drule_tac p = p and \<sigma> = \<sigma>'' in valid_ptr_not_in_frame_same; simp?)
      apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (rule u_v_r_empty)
     apply (frule_tac p = p and \<sigma>= \<sigma>'' in readonly_not_in_frame; simp?)
     apply (rule disjointI)
     apply (drule wa_abs_typing_u_elims(5))
     apply (drule_tac w = wba in wa_abs_upd_val_elims(1))
     apply (drule wa_abs_typing_u_elims(3); clarsimp)
     apply (erule_tac x = i in allE; clarsimp)+
     apply (drule_tac p = "arr + size_of_num_type ta * i" and \<sigma> = \<sigma>'' in readonly_not_in_frame; simp?)
     apply clarsimp
     apply (drule_tac x = "arr + size_of_num_type ta * i" and S' = waa in orthD1; simp?)
     apply (rule_tac x = i in exI; simp)
    apply (frule_tac A = rca and B = "raa \<union> rc" and x = p in in_mono; clarsimp)
    apply (rule disjointI; clarsimp)
    apply (drule_tac x = y and S' = raa in orthD1; simp?)
    apply (drule_tac x = y and S' = rc in orthD1; simp?)
     apply (rule disjI1)
     apply (drule wa_abs_upd_val_elims(1))
     apply (drule_tac w = wa in wa_abs_typing_u_elims(3); clarsimp)
     apply (drule wa_abs_typing_u_elims(3); clarsimp)
    apply (drule_tac A = rca and B = "raa \<union> rc" and x = y in in_mono; clarsimp)
   apply (drule wa_abs_typing_u_elims(3); clarsimp)
  apply clarsimp
  apply (rule conjI)
   apply (rule_tac B = "raa \<union> rc" in subset_trans; simp?)
  apply (subst (asm) insert_ident; simp?)
   apply (drule_tac p = p and \<sigma> = \<sigma> in readonly_not_in_frame; simp?)
  apply (drule_tac s = wba and \<sigma> = \<sigma>'' in frame_expand(2); simp?)
   apply (frule wa_abs_typing_u_elims(5))
   apply (drule wa_abs_typing_u_elims(3); clarsimp)
   apply (erule_tac x = i in allE; clarsimp)+
  apply (drule wa_abs_typing_u_elims(3); clarsimp)
  apply (drule wa_abs_upd_val_elims(1))
  apply (drule wa_abs_typing_u_elims(3); clarsimp)
  apply (drule_tac \<sigma> = \<sigma>'' and \<sigma>' = \<sigma>''' in upd.frame_app; simp?)
  apply (rule upd.frame_trans; simp?)
  apply (subst (asm) insert_absorb[where A = "_ \<union> _", simplified]; simp?)
   apply (rule disjI1)
   apply (rule_tac x = to in exI; simp add: word_less_nat_alt)
  apply (subst (asm) insert_absorb[where A = "_ \<union> _", simplified]; simp?)
  apply (rule_tac x = to in exI; simp add: word_less_nat_alt)
  done

lemma val_executes_fron_upd_wa_mapAccumnb_bod:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; proc_env_u_v_matches \<xi>\<^sub>u \<xi>\<^sub>v \<Xi>'; 
    upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv (rb \<union> rc) (\<sigma>', res); 
    \<sigma> p = option.Some (UAbstract (UWA t len arr));
    wa_abs_upd_val (UWA t len arr) (VWA t xs) ''WordArray'' [t] (Boxed Writable ptrl) ra wa \<sigma>;
    upd_val_rel \<Xi>' \<sigma> acc acc' u rb wb; upd_val_rel \<Xi>' \<sigma> obsv obsv' v rc {};
    (wa \<union> wb) \<inter> rc = {}; wa \<inter> wb = {}; wa \<inter> rb = {}; p \<notin> wa \<union> rb \<union> wb \<union> rc;
    \<Xi>', [], [option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)] 
      \<turnstile> (App f (Var 0)) : TRecord [(b0, t, Present), (b1, u, Present)] Unboxed;
    distinct [a0, a1, a2]; distinct [b0, b1]\<rbrakk>
    \<Longrightarrow> Ex (val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs (unat frm) (unat to) f acc' obsv')"
  apply (induct to arbitrary: \<sigma>' res)
   apply (rule_tac x = "VRecord [VAbstract (VWA t xs), acc']" in exI)
   apply (subst val_wa_mapAccumnb_bod.simps; clarsimp)
  apply (case_tac "len < 1 + to")
   apply (drule upd_wa_mapAccumnb_bod_back_step'; simp?)
   apply (erule meta_allE, erule meta_allE, erule meta_impE, simp?)
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt not_less)
   apply (rule_tac x = x in exI)
   apply (clarsimp simp: less_Suc_eq_le)
   apply (drule wa_abs_upd_val_elims(3))
   apply (drule val_wa_mapAccumnb_bod_to_geq_lenD; simp?)
   apply (rule val_wa_mapAccumnb_bod_to_geq_len; simp)
  apply (case_tac "1 + to \<le> frm")
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt not_less word_le_nat_alt)
   apply (rule_tac x = "VRecord [VAbstract (VWA t xs), acc']" in exI)
   apply (subst val_wa_mapAccumnb_bod.simps; clarsimp)
  apply (frule upd_wa_mapAccumnb_bod_preservation'; simp?)
  apply clarsimp
  apply (frule wa_abs_upd_val_elims(2))
  apply (drule wa_abs_typing_v_elims(1); clarsimp)
  apply (drule upd_wa_mapAccumnb_bod_back_step; simp?)
   apply (drule wa_abs_upd_val_elims(1))
   apply (drule wa_abs_typing_u_elims(6); simp)
  apply clarsimp
  apply (erule meta_allE; erule meta_allE; erule meta_impE; simp?)
  apply clarsimp
  apply (frule_tac rb = rb and wb = wb and rc = rc in upd_val_wa_mapAccumnb_bod_corres; simp?)
  apply clarsimp
  apply (frule val_wa_mapAccumnb_bod_preservation'; simp?)
  apply clarsimp
  apply (erule u_v_recE; clarsimp)
  apply (erule u_v_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym; clarsimp)
  apply (erule u_v_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym; clarsimp)
  apply (erule u_v_r_emptyE; clarsimp)
  apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
  apply (subgoal_tac "u_v_matches \<Xi>' \<sigma>'' 
    [URecord [(va, upd.uval_repr va), (x, upd.uval_repr x), (obsv, upd.uval_repr obsv)]]
    [VRecord [xs ! unat to, racca, obsv']]
    [option.Some (TRecord [(a0, TPrim (Num ta), Present), (a1, u, Present), (a2, v, Present)] Unboxed)]
    (raa \<union> rc) waa")
   apply (frule_tac \<gamma> = "[URecord [(va, upd.uval_repr va), (x, upd.uval_repr x),
      (obsv, upd.uval_repr obsv)]]" and
      \<gamma>' = "[VRecord [xs ! unat to, racca, obsv']]" and
      r = "raa \<union> rc" and w = waa in val_executes_from_upd_executes(1); simp?; clarsimp?)
  apply (frule_tac \<gamma> = "[URecord [(va, upd.uval_repr va), (x, upd.uval_repr x), 
      (obsv, upd.uval_repr obsv)]]" and
      \<gamma>' = "[VRecord [xs ! unat to, racca, obsv']]" and
      r = "raa \<union> rc" and w = waa in mono_correspondence(1); simp?; clarsimp?)
   apply (erule u_v_recE'; clarsimp)
   apply (erule u_v_r_consE'; simp?)
   apply (erule conjE)+
   apply (drule_tac t = "type_repr _" in sym; clarsimp)
   apply (erule u_v_r_consE'; simp?)
   apply (erule conjE)+
   apply clarsimp
   apply (erule u_v_r_emptyE'; clarsimp)
   apply (drule val_wa_mapAccumnb_bod_step; simp?)
    apply (drule wa_abs_upd_val_elims(3); simp)
   apply (rule exI; simp?)
  apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
   apply (rule u_v_struct; simp?)
   apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
     apply (frule wa_abs_upd_val_elims(4))
     apply (drule wa_abs_upd_val_elims(3))
     apply (erule_tac x = to in allE; clarsimp simp: word_less_nat_alt)
     apply (rule u_v_prim'; clarsimp)
    apply (rule u_v_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
     apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
       apply (rule upd_val_rel_frame(1); simp add: Int_commute)
      apply (rule u_v_r_empty)
     apply (drule_tac u = obsv in upd_val_rel_to_uval_typing(1))
     apply (drule upd.type_repr_uval_repr; simp?)
    apply (drule_tac u = obsv in upd_val_rel_to_uval_typing(1))
    apply (rule disjointI)
    apply (drule_tac p = y in upd.uval_typing_valid(1)[rotated 1]; simp?)
    apply clarsimp
    apply (drule_tac p = y and \<sigma> = \<sigma> in readonly_not_in_frame; simp?)
     apply (drule_tac x = y and S' = rc in orthD2; simp?)
    apply (drule equalityD2[where A = "insert _ _", simplified])
    apply clarsimp
    apply (drule_tac x = y and A = waa and B = "insert p w'" in  in_mono; simp?)
   apply (drule wa_abs_upd_val_elims(4))
   apply (erule_tac x = to in allE; clarsimp simp: word_less_nat_alt)
  apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
  done


inductive_cases u_v_t_funE: "upd_val_rel \<Xi>' \<sigma> (UFunction f ts) v t r w"
inductive_cases u_v_t_afunE: "upd_val_rel \<Xi>' \<sigma> (UAFunction f ts) v t r w"

lemma wordarray_fold_no_break_upd_val:
  "\<And>K a b \<sigma> \<sigma>' \<tau>s aa a' v v' r w.
   \<lbrakk>list_all2 (kinding []) \<tau>s K; wordarray_fold_no_break_0_type = (K, a, b); 
    upd_val_rel \<Xi> \<sigma> aa a' (instantiate \<tau>s a) r w; upd_wa_foldnb_0 \<Xi> \<xi>0 abbreviatedType1 (\<sigma>, aa) (\<sigma>', v)\<rbrakk>
    \<Longrightarrow> (val_wa_foldnb_0 \<Xi> \<xi>m abbreviatedType1 a' v' \<longrightarrow> (\<exists>r' w'. upd_val_rel \<Xi> \<sigma>' v v' (instantiate \<tau>s b) r' w' \<and> r' \<subseteq> r \<and>
          frame \<sigma> w \<sigma>' w')) \<and> Ex (val_wa_foldnb_0 \<Xi> \<xi>m abbreviatedType1 a')"
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
  apply (subst (asm) abbreviatedType1_def; clarsimp)
  apply (frule_tac u = xb in upd_val_rel_to_uval_typing(1))
  apply (drule_tac x = xb in upd.uval_typing_unique_ptrs(1); simp?)
  apply clarsimp
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply clarsimp
  apply (erule u_v_r_emptyE'; clarsimp)
  apply (frule_tac u = x in upd_val_rel_to_uval_typing(1))
  apply (drule_tac x = x in upd.uval_typing_unique_ptrs(1); simp?)
  apply clarsimp
  apply (case_tac a'; clarsimp simp: wa_abs_upd_val_def val_wa_foldnb_0_def)
  apply (case_tac x11; clarsimp)
  apply (case_tac x5; clarsimp)
  apply (rule conjI; clarsimp)
  apply (clarsimp simp: abbreviatedType1_def)
   apply (drule_tac xs = x12 and r = r and w = "{}" and acc' = x'a and 
      obsv' = x'b and t = "TUnit" and res' = v' and ra = rd and wa = wa and ptrl = undefined
      in upd_val_wa_foldnb_bod_corres[OF proc_ctx_wellformed_\<Xi> proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>]; simp?)
      apply (case_tac xa; clarsimp; elim u_v_t_funE u_v_t_afunE; clarsimp)
     apply (clarsimp simp: wa_abs_upd_val_def)
    apply clarsimp
   apply (case_tac xa; clarsimp; elim u_v_t_funE u_v_t_afunE; clarsimp; blast)
  apply (clarsimp simp: abbreviatedType1_def)
   apply (drule_tac xs = x12 and r = r and w = "{}" and acc' = x'a and 
      obsv' = x'b and t = "TUnit" and ra = rd and wa = wa and ptrl = undefined
      in val_executes_from_upd_wa_foldnb_bod[OF proc_ctx_wellformed_\<Xi> proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>]; simp?)
    apply (clarsimp simp: wa_abs_upd_val_def)
   apply clarsimp
  apply clarsimp
  apply (rule_tac x = xc in exI)
  apply (clarsimp simp: val_wa_foldnb_0_def)
  apply (drule_tac v = x'a in upd_val_rel_to_vval_typing(1)) 
  apply (drule_tac v = x'b in upd_val_rel_to_vval_typing(1)) 
  apply (case_tac xa; clarsimp; elim u_v_t_funE u_v_t_afunE; clarsimp)
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

end (* of context *)

end
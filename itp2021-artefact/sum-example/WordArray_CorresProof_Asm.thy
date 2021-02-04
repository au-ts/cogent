(*
  This file contains the provable assumptions which are required when proving correspondence of
  word array functions.
*)
theory WordArray_CorresProof_Asm
  imports WordArray_UAbsFun WordArray_VAbsFun
begin

context WordArray begin

section "Type Assumptions"

lemma proc_ctx_wellformed_\<Xi>:
  "proc_ctx_wellformed \<Xi>"
  apply (clarsimp simp: proc_ctx_wellformed_def \<Xi>_def)
  apply (clarsimp split: if_splits
                  simp: assoc_lookup.simps abbreviated_type_defs
                        wordarray_get_0_type_def wordarray_get_u32_type_def
                        wordarray_length_0_type_def wordarray_length_u32_type_def
                        wordarray_put2_0_type_def wordarray_put2_u32_type_def
                        wordarray_fold_no_break_0_type_def
                        wordarray_map_no_break_0_type_def
                        add_type_def sum_arr_type_def
                        mul_type_def mul_arr_type_def
                        inc_type_def inc_arr_type_def
                        dec_type_def dec_arr_type_def)
  done

section "First Order Abstract Function Assumptions"

subsection "Monomorphisation"

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

subsection "Type preservation in the Value semantics"

lemma val_proc_env_matches_\<xi>m_\<Xi>:
  "val.proc_env_matches \<xi>m \<Xi>"
  apply (clarsimp simp: val.proc_env_matches_def)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
    apply (clarsimp simp: wordarray_get_0_type_def abbreviated_type_defs)
    apply (drule val_wa_get_preservation; simp?)
   apply (clarsimp simp: wordarray_length_0_type_def)
  apply (drule val_wa_length_preservation; simp?)
  apply (clarsimp simp: wordarray_put2_0_type_def abbreviated_type_defs)
  apply (drule val_wa_put2_preservation; simp?)
  done

subsection "Correspondence and upward propagation from Update to the Value semantics"

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
  apply (erule u_v_t_primtE)
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
    apply (clarsimp simp: wordarray_get_0_type_def abbreviated_type_defs)
    apply (drule wa_get_upd_val; simp)
   apply (clarsimp simp: wordarray_length_0_type_def)
   apply (drule wa_length_upd_val; simp)
  apply (clarsimp simp: wordarray_put2_0_type_def abbreviated_type_defs)
  apply (drule wa_put2_upd_val; simp)
  done

subsection "Type preservation and frame constraint satisfaction in the Update semantics"

lemma upd_proc_env_matches_ptrs_\<xi>0_\<Xi>:
  "upd.proc_env_matches_ptrs \<xi>0 \<Xi>"
  apply (unfold upd.proc_env_matches_ptrs_def)
  apply clarsimp
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
    apply (clarsimp simp: wordarray_get_0_type_def abbreviated_type_defs)
    apply (drule upd_wa_get_preservation; simp?)
   apply (clarsimp simp: wordarray_length_0_type_def)
  apply (drule upd_wa_length_preservation; simp)
  apply (clarsimp simp: wordarray_put2_0_type_def abbreviated_type_defs)
  apply (drule upd_wa_put2_preservation; simp)
  done

section "Second Order Abstract Function Assumptions"

lemma lit_type_ex:
  "lit_type l = Bool \<Longrightarrow> \<exists>v. l = LBool v"
  "lit_type l = Num U8 \<Longrightarrow> \<exists>v. l = LU8 v"
  "lit_type l = Num U16 \<Longrightarrow> \<exists>v. l = LU16 v"
  "lit_type l = Num U32 \<Longrightarrow> \<exists>v. l = LU32 v"
  "lit_type l = Num U64 \<Longrightarrow> \<exists>v. l = LU64 v"
  apply (induct l; clarsimp)+
  done

subsection "Monomorphisation"

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
  apply (subst (asm) rename_def)+
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
    apply (rule conjI; clarsimp; subst (asm) rename_def; clarsimp)
    apply (clarsimp simp: val_wa_foldnb_def val_wa_foldnbp_def)
    apply (case_tac v; clarsimp)
    apply (case_tac z; clarsimp)
    apply (case_tac za; clarsimp)
    apply (case_tac zb; clarsimp)
    apply (rotate_tac 4)
    apply (subst (asm) \<Xi>_def; clarsimp simp: wordarray_fold_no_break_0_type_def abbreviated_type_defs)
    apply (drule_tac xs = xs and frm = "unat frm" and to = "unat to" and acc = zd and obsv = ze and
      r = v' and \<xi>\<^sub>p = \<xi>p in 
      val_wa_foldnb_bod_rename_monoexpr_correct[OF val_proc_env_matches_\<xi>m_\<Xi>] ; simp?; clarsimp?)
    apply (rule value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p)
   apply (rule conjI; clarsimp; subst (asm) rename_def; clarsimp)
   apply (clarsimp simp: val_wa_mapAccumnb_def val_wa_mapAccumnbp_def)
   apply (case_tac v; clarsimp)
   apply (case_tac z; clarsimp)
   apply (case_tac za; clarsimp)
   apply (case_tac zb; clarsimp)
   apply (rotate_tac 4)
   apply (subst (asm) \<Xi>_def; clarsimp simp: wordarray_map_no_break_0_type_def abbreviated_type_defs)
   apply (subst (asm) \<Xi>_def; clarsimp simp: wordarray_map_no_break_0_type_def abbreviated_type_defs)
    apply (drule_tac xs = xs and frm = "unat frm" and to = "unat to" and acc = zd and obsv = ze and
      r = v' and \<xi>\<^sub>p = \<xi>p in 
      val_wa_mapAccumnb_bod_rename_monoexpr_correct[OF val_proc_env_matches_\<xi>m_\<Xi>] ; simp?; clarsimp?)
   apply (rule value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p)
  apply (rule conjI; clarsimp; subst (asm) rename_def; clarsimp)
  done

subsection "Type preservation in the Value semantics"

lemma val_proc_env_matches_\<xi>m1_\<Xi>:
  "val.proc_env_matches \<xi>m1 \<Xi>"
 apply (clarsimp simp: val.proc_env_matches_def)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
      apply (clarsimp simp: wordarray_get_0_type_def abbreviated_type_defs)
      apply (drule val_wa_get_preservation; simp?)
     apply (clarsimp simp: wordarray_length_0_type_def)
     apply (drule val_wa_length_preservation; simp?)
    apply (clarsimp simp: wordarray_put2_0_type_def abbreviated_type_defs)
    apply (drule val_wa_put2_preservation; simp?)
   apply (clarsimp simp: wordarray_fold_no_break_0_type_def val_wa_foldnb_def)
   apply (erule val.v_t_recordE)
   apply (erule val.v_t_r_consE; clarsimp)+
   apply (erule val.v_t_abstractE; clarsimp)
   apply (subst (asm) \<Xi>_def; clarsimp simp: wordarray_fold_no_break_0_type_def abbreviated_type_defs)
   apply (drule val_wa_foldnb_bod_preservation[OF proc_ctx_wellformed_\<Xi> val_proc_env_matches_\<xi>m_\<Xi>]; simp?; clarsimp)
  apply (clarsimp simp: wordarray_map_no_break_0_type_def val_wa_mapAccumnb_def)
  apply (erule val.v_t_recordE)
  apply (erule val.v_t_r_consE; clarsimp)+
  apply (erule val.v_t_abstractE; clarsimp)
  apply (subst (asm) \<Xi>_def; clarsimp simp: wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (subst (asm) \<Xi>_def; clarsimp simp: wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (drule_tac ptrl = undefined in val_wa_mapAccumnb_bod_preservation[OF proc_ctx_wellformed_\<Xi> val_proc_env_matches_\<xi>m_\<Xi>]; simp?)
  apply clarsimp+
  done

subsection "Type preservation and frame constraint satisfaction in the Update semantics"

lemma upd_wa_foldnb_preservation:
  "\<And>K a b \<sigma> \<sigma>' \<tau>s v v' r w.
   \<lbrakk>list_all2 (kinding []) \<tau>s K; wordarray_fold_no_break_0_type = (K, a, b);
    upd.uval_typing \<Xi> \<sigma> v (instantiate \<tau>s a) r w;
    upd_wa_foldnb \<Xi> \<xi>0 (foldmap_funarg_type ''wordarray_fold_no_break_0'') (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi> \<sigma>' v' (instantiate \<tau>s b) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: wordarray_fold_no_break_0_type_def upd_wa_foldnb_def)
  apply (rename_tac rb wb rc)
  apply (erule upd.u_t_recE; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym; clarsimp)+
  apply (erule upd.u_t_r_consE; clarsimp)+
  apply (erule upd.u_t_r_emptyE; clarsimp)
  apply (erule upd.u_t_p_absE; clarsimp)
  apply (rotate_tac 4)
  apply (subst (asm) \<Xi>_def; clarsimp simp: wordarray_fold_no_break_0_type_def abbreviated_type_defs)
  apply (erule upd.u_t_primE)+
  apply (drule_tac t = "lit_type _" in sym)+
  apply clarsimp
  apply (frule upd.tfun_no_pointers(1))
  apply (frule upd.tfun_no_pointers(2))
  apply clarsimp
  apply (rename_tac f acc r_a w_a obsv r_o w_o ra)
  apply (drule_tac x = acc in upd.uval_typing_unique_ptrs(1); simp?)
  apply (drule_tac x = obsv in upd.uval_typing_unique_ptrs(1); simp?)
  apply clarsimp
  apply (drule_tac ra = ra and rb = rb and rc = rc and wb = wb in 
      upd_wa_foldnb_bod_preservation[OF proc_ctx_wellformed_\<Xi> upd_proc_env_matches_ptrs_\<xi>0_\<Xi>, 
        where ptrl = undefined and wa = "{}", simplified]; simp?; clarsimp?)
  apply (case_tac f; clarsimp)
  apply (elim upd.u_t_functionE upd.u_t_afunE; clarsimp; blast)+
  done

lemma upd_wa_mapAccumnb_preservation:
  "\<And>K a b \<sigma> \<sigma>' \<tau>s v v' r w.
       \<lbrakk>list_all2 (kinding []) \<tau>s K; wordarray_map_no_break_0_type = (K, a, b); upd.uval_typing \<Xi> \<sigma> v (instantiate \<tau>s a) r w;
        upd_wa_mapAccumnb \<Xi> \<xi>0
         (funarg_type (present_type (rec_type_list (prod.fst (prod.snd (\<Xi> ''wordarray_map_no_break_0''))) ! 3)))
         (funret_type (present_type (rec_type_list (prod.fst (prod.snd (\<Xi> ''wordarray_map_no_break_0''))) ! 3))) (\<sigma>, v) (\<sigma>', v')\<rbrakk>
       \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi> \<sigma>' v' (instantiate \<tau>s b) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: wordarray_map_no_break_0_type_def upd_wa_mapAccumnb_def)
  apply (rotate_tac 6)
  apply (subst (asm) \<Xi>_def; clarsimp simp: wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (subst (asm) \<Xi>_def; clarsimp simp: wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (rename_tac rb wb rc)
  apply (erule upd.u_t_recE; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym; clarsimp)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (frule upd.tfun_no_pointers(1))
  apply (frule upd.tfun_no_pointers(2))
  apply clarsimp
  apply (rename_tac f r' w')
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (rename_tac acc r_a w_a r' w')
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_r_emptyE; clarsimp)
  apply (rename_tac obsv r_o w_o) 
  apply (erule upd.u_t_primE)+
  apply (drule_tac t = "lit_type _" in sym)+
  apply clarsimp
  apply (drule upd.uval_typing_unique_ptrs(1); simp?)
  apply (drule upd.uval_typing_unique_ptrs(1); simp?)
  apply (erule upd.u_t_p_absE; clarsimp)
  apply (rename_tac wa)
  apply (cut_tac ra = ra and rb = r_a and rc = r_o  and wa = wa and wb = w_a in 
      upd_wa_mapAccumnb_bod_preservation[OF proc_ctx_wellformed_\<Xi> upd_proc_env_matches_ptrs_\<xi>0_\<Xi>, 
        where ptrl = undefined, simplified]; simp?; clarsimp?)
    apply (subst Int_Un_distrib2; clarsimp)
    apply (cut_tac A = wa and B = r_a and C = r_o in Int_Un_distrib; simp?)
   apply (cut_tac A = wa and B = r_a and C = r_o in Int_Un_distrib; simp?)
  apply (erule_tac x = r' in allE)
  apply (clarsimp simp: Un_assoc)
  apply (erule_tac x = "insert p w'" in allE)
  apply clarsimp
  apply (drule_tac p = p in frame_expand(1); simp?)
  done

lemma upd_proc_env_matches_ptrs_\<xi>1_\<Xi>:
  "upd.proc_env_matches_ptrs \<xi>1 \<Xi>"
  apply (unfold upd.proc_env_matches_ptrs_def)
  apply clarsimp
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
     apply (clarsimp simp: wordarray_get_0_type_def abbreviated_type_defs)
     apply (drule upd_wa_get_preservation; simp?)
    apply (clarsimp simp: wordarray_length_0_type_def)
    apply (drule upd_wa_length_preservation; simp)
   apply (clarsimp simp: wordarray_put2_0_type_def abbreviated_type_defs)
   apply (drule upd_wa_put2_preservation; simp)
  apply (clarsimp simp: upd_wa_foldnb_preservation)
  apply (clarsimp simp: upd_wa_mapAccumnb_preservation)
  done

subsection "Correspondence and upward propagation from Update to the Value semantics"

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
  apply (drule_tac x = \<sigma>a in meta_spec)
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
  apply (erule u_v_t_primtE)
  apply clarsimp
  apply (drule_tac t = "lit_type _" in sym)+
  apply clarsimp
  apply (thin_tac "frame _ _ _ _")
  apply (erule u_v_p_absE[where s = "Boxed Writable _" and ts = "[_]", simplified])
  apply (drule_tac t = "RCon _ _" in sym; clarsimp)
  apply (frule_tac p = p in valid_ptr_not_in_frame_same; simp?)
  apply clarsimp
  apply (frule_tac \<sigma> = \<sigma>a in wa_abs_upd_val_elims(4))
  apply (erule_tac x = to in allE; clarsimp simp: word_less_nat_alt)
  apply (frule_tac \<sigma> = \<sigma>a in wa_abs_upd_val_elims(3))
  apply (subst (asm) nth_list_update_eq; simp)
  apply (frule_tac \<sigma> = \<sigma>a and p = "arr + size_of_num_type ta * to" in readonly_not_in_frame; simp?)
   apply (drule_tac w = wba in wa_abs_upd_val_elims(1))
   apply (drule wa_abs_typing_u_elims(3); clarsimp simp: word_less_nat_alt not_le not_less)
   apply (drule Suc_le_lessD)
   apply (drule_tac x = "arr + size_of_num_type ta * to" and S' = waa in orthD1; simp?)
   apply (rule_tac x = to in exI; simp)
  apply (frule_tac r = r in wa_abs_upd_val_elims(1))
  apply (drule_tac r = r in abs_upd_val_frame; simp?)
   apply (drule_tac wa_abs_typing_u_elims(3); simp)
  apply (cut_tac \<sigma> = \<sigma>b and l = "arr + size_of_num_type ta * to" and v = "UPrim l" in upd.frame_single_update)
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
        apply (drule_tac \<sigma> = \<sigma>b and  i = to in wa_abs_upd_val_update; simp?)
         apply (clarsimp simp: word_less_nat_alt)
        apply (drule_tac s = "rxs ! unat to" in sym; clarsimp)
       apply (drule wa_abs_upd_val_elims(1))
       apply (drule_tac \<sigma> = \<sigma> in wa_abs_typing_u_elims(3); clarsimp)
       apply (rule conjI; clarsimp)
       apply (drule_tac p = p and \<sigma> = \<sigma>a in valid_ptr_not_in_frame_same; simp?)
      apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (rule u_v_r_empty)
     apply (frule_tac p = p and \<sigma> = \<sigma>a in readonly_not_in_frame; simp?)
     apply (rule disjointI)
     apply (drule wa_abs_typing_u_elims(5))
     apply (drule_tac w = wba in wa_abs_upd_val_elims(1))
     apply (drule wa_abs_typing_u_elims(3); clarsimp)
     apply (erule_tac x = i in allE; clarsimp)+
     apply (drule_tac p = "arr + size_of_num_type ta * i" and \<sigma> = \<sigma>a in readonly_not_in_frame; simp?)
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
  apply (drule_tac s = wba and \<sigma> = \<sigma>a in frame_expand(2); simp?)
   apply (frule wa_abs_typing_u_elims(5))
   apply (drule wa_abs_typing_u_elims(3); clarsimp)
   apply (erule_tac x = i in allE; clarsimp)+
  apply (drule wa_abs_typing_u_elims(3); clarsimp)
  apply (drule wa_abs_upd_val_elims(1))
  apply (drule wa_abs_typing_u_elims(3); clarsimp)
  apply (drule_tac \<sigma> = \<sigma>a and \<sigma>' = \<sigma>b in upd.frame_app; simp?)
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
  apply (subgoal_tac "u_v_matches \<Xi>' \<sigma>a 
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




lemma wordarray_fold_no_break_upd_val:
  "\<And>K a b \<sigma> \<sigma>' \<tau>s aa a' v v' r w.
   \<lbrakk>list_all2 (kinding []) \<tau>s K; wordarray_fold_no_break_0_type = (K, a, b); 
    upd_val_rel \<Xi> \<sigma> aa a' (instantiate \<tau>s a) r w; 
    upd_wa_foldnb \<Xi> \<xi>0 (foldmap_funarg_type ''wordarray_fold_no_break_0'') (\<sigma>, aa) (\<sigma>', v)\<rbrakk>
    \<Longrightarrow> (val_wa_foldnb \<Xi> \<xi>m (foldmap_funarg_type ''wordarray_fold_no_break_0'') a' v' 
          \<longrightarrow> (\<exists>r' w'. upd_val_rel \<Xi> \<sigma>' v v' (instantiate \<tau>s b) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w')) \<and> 
        Ex (val_wa_foldnb \<Xi> \<xi>m (foldmap_funarg_type ''wordarray_fold_no_break_0'') a')"
  apply (clarsimp simp: wordarray_fold_no_break_0_type_def upd_wa_foldnb_def)
  apply (rotate_tac 6)
  apply (subst (asm) \<Xi>_def; clarsimp simp: wordarray_fold_no_break_0_type_def abbreviated_type_defs)
  apply (rename_tac rb wb rc)
  apply (erule u_v_recE'; clarsimp)
  apply (erule u_v_r_consE'; clarsimp)
  apply (erule u_v_p_absE'; clarsimp)
  apply (frule wa_abs_upd_val_elims(2), drule wa_abs_typing_v_elims(1); clarsimp)
  apply (erule u_v_r_consE'; simp)
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)
  apply clarsimp
  apply (erule u_v_primE')+
  apply (drule_tac t = "lit_type _" in sym)+
  apply clarsimp
  apply (erule u_v_r_consE'; clarsimp)
  apply (rename_tac f f' r_f w_f xs' r' w')
  apply (frule_tac u = f in upd_val_rel_to_uval_typing(1))
  apply (frule upd.tfun_no_pointers(1))
  apply (drule upd.tfun_no_pointers(2))
  apply clarsimp
  apply (erule u_v_r_consE'; clarsimp)
  apply (rename_tac acc acc' r_a w_a xs' r' w')
  apply (erule u_v_r_consE'; clarsimp)
  apply (erule u_v_r_emptyE'; clarsimp)
  apply (rename_tac obsv obsv' r_o w_o)
  apply (frule_tac u = acc in upd_val_rel_to_uval_typing(1))
  apply (drule_tac x = acc in upd.uval_typing_unique_ptrs(1); simp?)
  apply clarsimp
  apply (frule_tac u = obsv in upd_val_rel_to_uval_typing(1))
  apply (drule_tac x = obsv in upd.uval_typing_unique_ptrs(1); simp?)
  apply clarsimp
  apply (clarsimp simp: val_wa_foldnb_def)
  apply (erule impE; simp?)+
   apply (case_tac f; clarsimp; elim u_v_t_funE u_v_t_afunE; clarsimp)
  apply (erule impE, rule upd_val_rel_to_vval_typing(1); simp?)+
  apply (erule impE; simp?)+
   apply (case_tac f; clarsimp; elim u_v_t_funE u_v_t_afunE; clarsimp)
  apply (erule impE, erule wa_abs_upd_val_elims(2); simp?)
  apply (erule disjE; simp?)
  apply clarsimp
   apply (drule_tac xs = xs and r = r and w = "{}" and acc' = acc' and 
      obsv' = obsv' and t = "TUnit" and res' = v' and ra = r_a and wa = w_a and ptrl = undefined
      in upd_val_wa_foldnb_bod_corres[OF proc_ctx_wellformed_\<Xi> proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>]; simp?)
     apply (case_tac f; clarsimp; elim u_v_t_funE u_v_t_afunE; clarsimp)
    apply clarsimp
   apply clarsimp
   apply (case_tac f; clarsimp; elim u_v_t_funE u_v_t_afunE; clarsimp; blast)
  apply (drule_tac xs = xs and r = r and w = "{}" and acc' = acc' and 
      obsv' = obsv' and t = "TUnit" and ra = r_a and wa = w_a and ptrl = undefined
      in val_executes_from_upd_wa_foldnb_bod[OF proc_ctx_wellformed_\<Xi> proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>]; simp?)
   apply clarsimp
  apply clarsimp
  apply (rename_tac res)
  apply (erule_tac x = res in allE)
  apply (case_tac f; clarsimp; elim u_v_t_funE u_v_t_afunE; clarsimp)
  done


lemma wordarray_mapAccumnb_abs_upd_val:
  "\<And>K a b \<sigma> \<sigma>' \<tau>s aa a' v v' r w.
       \<lbrakk>list_all2 (kinding []) \<tau>s K; wordarray_map_no_break_0_type = (K, a, b); upd_val_rel \<Xi> \<sigma> aa a' (instantiate \<tau>s a) r w;
        upd_wa_mapAccumnb \<Xi> \<xi>0
         (funarg_type (present_type (rec_type_list (prod.fst (prod.snd (\<Xi> ''wordarray_map_no_break_0''))) ! 3)))
         (funret_type (present_type (rec_type_list (prod.fst (prod.snd (\<Xi> ''wordarray_map_no_break_0''))) ! 3))) (\<sigma>, aa) (\<sigma>', v)\<rbrakk>
       \<Longrightarrow> (val_wa_mapAccumnb \<Xi> \<xi>m
             (funarg_type (present_type (rec_type_list (prod.fst (prod.snd (\<Xi> ''wordarray_map_no_break_0''))) ! 3)))
             (funret_type (present_type (rec_type_list (prod.fst (prod.snd (\<Xi> ''wordarray_map_no_break_0''))) ! 3))) a' v' \<longrightarrow>
            (\<exists>r' w'. upd_val_rel \<Xi> \<sigma>' v v' (instantiate \<tau>s b) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w')) \<and>
           Ex (val_wa_mapAccumnb \<Xi> \<xi>m
                (funarg_type (present_type (rec_type_list (prod.fst (prod.snd (\<Xi> ''wordarray_map_no_break_0''))) ! 3)))
                (funret_type (present_type (rec_type_list (prod.fst (prod.snd (\<Xi> ''wordarray_map_no_break_0''))) ! 3))) a')"
  apply (clarsimp simp: wordarray_map_no_break_0_type_def upd_wa_mapAccumnb_def)
  apply (rename_tac rb wb rc)
  apply (rotate_tac 6)
  apply (subst (asm) \<Xi>_def; clarsimp simp: wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (subst (asm) \<Xi>_def; clarsimp simp: wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (erule u_v_recE'; clarsimp)
  apply (erule u_v_r_consE'; clarsimp)
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)
  apply clarsimp
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)
  apply clarsimp
  apply (erule u_v_r_consE'; clarsimp)
  apply (rename_tac f f' r_f w_f xs r' w')
  apply (erule u_v_r_consE'; clarsimp)
  apply (rename_tac acc acc' r_a w_a xs r' w')
  apply (erule u_v_r_consE'; clarsimp)
  apply (rename_tac obsv obsv' r_o w_o xs r' w')
  apply (erule u_v_r_emptyE'; clarsimp)
  apply (erule u_v_primE')+
  apply (drule_tac t = "lit_type _" in sym)+
  apply clarsimp
  apply (erule u_v_p_absE'; clarsimp)
  apply (rename_tac wa)
  apply (frule wa_abs_upd_val_elims(2))
  apply (drule wa_abs_typing_v_elims(1); clarsimp)
  apply (frule_tac u = acc in upd_val_rel_to_uval_typing(1))
  apply (drule upd.uval_typing_unique_ptrs(1); simp?)
  apply clarsimp
  apply (frule_tac u = obsv in upd_val_rel_to_uval_typing(1))
  apply (drule upd.uval_typing_unique_ptrs(1); simp?)
  apply (frule_tac u = f in upd_val_rel_to_uval_typing(1))
  apply (frule_tac v= f in upd.tfun_no_pointers(1))
  apply (drule_tac v= f in upd.tfun_no_pointers(2))
  apply (clarsimp simp: val_wa_mapAccumnb_def)
  apply (erule impE; simp?)
   apply (case_tac f; simp; elim u_v_t_funE u_v_t_afunE; simp)
  apply (erule impE, rule upd_val_rel_to_vval_typing(1), simp?)+
  apply (erule impE; simp?)
   apply (case_tac f; simp; elim u_v_t_funE u_v_t_afunE; simp)
  apply (erule impE, erule wa_abs_upd_val_elims(2), simp?)
  apply (erule disjE)
   apply (drule_tac xs = xs and ra = ra and wa = wa and acc' = acc' and 
      obsv' = obsv' and  ptrl = undefined and res' = v' and rb = r_a and wb = w_a and rc = r_o
      in upd_val_wa_mapAccumnb_bod_corres[OF proc_ctx_wellformed_\<Xi> proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>]; simp?; clarsimp?)
      apply (case_tac f; clarsimp; elim u_v_t_funE u_v_t_afunE; clarsimp)
     apply (subst Int_Un_distrib2; clarsimp)
     apply (cut_tac A = wa and B = r_a and C = r_o in Int_Un_distrib; simp?; clarsimp)
    apply (cut_tac A = wa and B = r_a and C = r_o in Int_Un_distrib; simp?; clarsimp)
   apply (erule_tac x = r' in allE)
   apply (clarsimp simp: Un_assoc)
   apply (erule_tac x = "insert p w'" in allE)
   apply clarsimp
   apply (drule_tac p = p in frame_expand(1); simp?)
  apply (drule_tac xs = xs and ra = ra and wa = wa  and  ptrl = undefined and rb = r_a and wb = w_a and rc = r_o
      in val_executes_fron_upd_wa_mapAccumnb_bod[OF proc_ctx_wellformed_\<Xi> proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>]; simp?; clarsimp?)
     apply (subst Int_Un_distrib2; clarsimp)
    apply (cut_tac A = wa and B = r_a and C = r_o in Int_Un_distrib; simp?; clarsimp)
   apply (cut_tac A = wa and B = r_a and C = r_o in Int_Un_distrib; simp?; clarsimp)
  apply (erule_tac x = x in allE)
  apply (case_tac f; simp; elim u_v_t_funE u_v_t_afunE; simp)
  done

lemma proc_env_u_v_matches_\<xi>1_\<xi>m1_\<Xi>:
  "proc_env_u_v_matches \<xi>1 \<xi>m1 \<Xi>"
  apply (clarsimp simp: proc_env_u_v_matches_def)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
      apply (clarsimp simp: wordarray_get_0_type_def abbreviated_type_defs)
      apply (drule wa_get_upd_val; simp)
     apply (clarsimp simp: wordarray_length_0_type_def)
     apply (drule wa_length_upd_val; simp)
    apply (clarsimp simp: wordarray_put2_0_type_def abbreviated_type_defs)
    apply (drule wa_put2_upd_val; simp)
   apply (drule wordarray_fold_no_break_upd_val; simp?)
  apply (clarsimp simp: wordarray_mapAccumnb_abs_upd_val)
  done

end (* of context *)

end
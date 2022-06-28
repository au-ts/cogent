(*
  This file contains the provable assumptions which are required when proving correspondence of
  word array functions.
*)
theory WordArray_CorresProof_Asm
  imports WordArray_UAbsFun WordArray_VAbsFun Generated_AllRefine
begin

context WordArray begin

lemmas abbreviated_type_defs = abbreviated_type_defs Generated_TypeProof.abbreviated_type_defs

section "Level 0 Assumptions"

lemma value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p: 
  "value_sem.rename_mono_prog wa_abs_typing_v rename \<Xi> \<xi>m \<xi>p"
  apply (clarsimp simp: rename_mono_prog_def)
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

lemma val_proc_env_matches_\<xi>m_\<Xi>:
  "proc_env_matches \<xi>m \<Xi>"
  apply (clarsimp simp: proc_env_matches_def)
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

inductive_cases u_v_recE': "upd_val_rel \<Xi>' \<sigma> (URecord fs ls) v \<tau> r w"
inductive_cases u_v_ptrE': "upd_val_rel \<Xi>' \<sigma> (UPtr p rp) v \<tau> r w"
inductive_cases u_v_r_emptyE': "upd_val_rel_record \<Xi>' \<sigma>  [] vs \<tau>s r w"
inductive_cases u_v_primE': "upd_val_rel \<Xi>' \<sigma> (UPrim l) v \<tau> r w"

lemma wa_get_upd_val:
  "\<lbrakk>upd_val_rel \<Xi>' \<sigma> au av (TRecord [(a, TCon ''WordArray'' [t] (Boxed ReadOnly ptrl), Present),
      (b, TPrim (Num U32), Present)] Unboxed) r w; upd_wa_get_0 (\<sigma>, au) (\<sigma>', v)\<rbrakk>
    \<Longrightarrow> (val_wa_get av v' \<longrightarrow> (\<exists>r' w'. upd_val_rel \<Xi>' \<sigma>' v v' t r' w' \<and> r' \<subseteq> r \<and> 
      frame \<sigma> w \<sigma>' w')) \<and> Ex (val_wa_get av)"
 apply (clarsimp simp: upd_wa_get_0_def) 
  apply (erule u_v_recE'; clarsimp)
  apply (erule u_v_r_consE'; clarsimp)
  apply (erule u_v_ptrE'; clarsimp)
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
  apply (erule u_v_ptrE'; clarsimp)
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
  apply (erule u_v_ptrE'; clarsimp)
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

lemma upd_proc_env_matches_ptrs_\<xi>0_\<Xi>:
  "proc_env_matches_ptrs \<xi>0 \<Xi>"
  apply (unfold proc_env_matches_ptrs_def)
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

lemma proc_ctx_wellformed_\<Xi>:
  "proc_ctx_wellformed \<Xi>"
  apply (clarsimp simp: proc_ctx_wellformed_def \<Xi>_def)
  apply (clarsimp split: if_splits
                  simp: assoc_lookup.simps abbreviated_type_defs
                        wordarray_get_0_type_def Generated_TypeProof.wordarray_get_u32_type_def
                        wordarray_length_0_type_def Generated_TypeProof.wordarray_length_u32_type_def
                        wordarray_put2_0_type_def Generated_TypeProof.wordarray_put2_u32_type_def
                        wordarray_fold_no_break_0_type_def
                        wordarray_map_no_break_0_type_def
                        Generated_TypeProof.add_type_def Generated_TypeProof.sum_arr_type_def
                        Generated_TypeProof.mul_type_def Generated_TypeProof.mul_arr_type_def
                        Generated_TypeProof.inc_type_def Generated_TypeProof.inc_arr_type_def
                        Generated_TypeProof.dec_type_def Generated_TypeProof.dec_arr_type_def)
  done

section "Level 1 Assumptions"

lemma upd_wa_foldnb_preservation:
  "\<And>L K C a b \<sigma> \<sigma>' ls \<tau>s v v' r w.
   \<lbrakk>list_all2 (kinding 0 [] {}) \<tau>s K; wordarray_fold_no_break_0_type = (L, K, C, a, b);
    uval_typing \<Xi> \<sigma> v (instantiate ls \<tau>s a) r w;
    upd_wa_foldnb \<Xi> \<xi>0 (foldmap_funarg_type ''wordarray_fold_no_break_0'') (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. uval_typing \<Xi> \<sigma>' v' (instantiate ls \<tau>s b) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: wordarray_fold_no_break_0_type_def upd_wa_foldnb_def)
  apply (rename_tac rb wb rc)
  apply (erule u_t_recE; clarsimp)
  apply (erule u_t_r_consE; clarsimp)
  apply (erule u_t_r_consE; simp)
  apply (erule u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym; clarsimp)+
  apply (erule u_t_r_consE; clarsimp)+
  apply (erule u_t_r_emptyE; clarsimp)
  apply (erule u_t_ptrE; simp)
  apply (drule_tac t = "map type_repr _" in sym; clarsimp) 
  apply (erule u_t_primE)+
  apply (drule_tac t = "lit_type _" in sym)+
  apply clarsimp
  apply (rename_tac \<sigma> \<sigma>' v' p frm to \<tau>a \<tau>b len arr a0 a1 a2 f rf wf acc rb wb obsv rc wc ra)
  apply (subst (asm) \<Xi>_def; simp add: wordarray_fold_no_break_0_type_def abbreviated_type_defs)
  apply (frule_tac v = obsv and K' = "[]" and k = "kinding_fn [] \<tau>b" in discardable_or_shareable_not_writable(1)[rotated 1]; simp?)
    apply (rule kindingI; clarsimp)
  apply (frule tfun_no_pointers(1))
  apply (frule tfun_no_pointers(2))
  apply clarsimp
  apply (drule_tac ra = ra and rb = rb and rc = rc and wb = wb in 
      upd_wa_foldnb_bod_preservation[OF proc_ctx_wellformed_\<Xi> upd_proc_env_matches_ptrs_\<xi>0_\<Xi>, 
        where ptrl = None and wa = "{}", simplified]; simp?; clarsimp?)
    apply blast
   apply blast
  apply (case_tac f; clarsimp)
  apply (elim u_t_functionE u_t_afunE; clarsimp; blast)+
  done

lemma lit_type_ex:
  "lit_type l = Bool \<Longrightarrow> \<exists>v. l = LBool v"
  "lit_type l = Num U8 \<Longrightarrow> \<exists>v. l = LU8 v"
  "lit_type l = Num U16 \<Longrightarrow> \<exists>v. l = LU16 v"
  "lit_type l = Num U32 \<Longrightarrow> \<exists>v. l = LU32 v"
  "lit_type l = Num U64 \<Longrightarrow> \<exists>v. l = LU64 v"
  apply (induct l; clarsimp)+
  done

lemma value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m1_\<xi>p1: 
  "value_sem.rename_mono_prog wa_abs_typing_v rename \<Xi> \<xi>m1 \<xi>p1"
  apply (clarsimp simp: rename_mono_prog_def)
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

lemma val_proc_env_matches_\<xi>m1_\<Xi>:
  "proc_env_matches \<xi>m1 \<Xi>"
 apply (clarsimp simp: proc_env_matches_def)
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
   apply (erule v_t_recordE)
   apply (erule v_t_r_consE; clarsimp)+
   apply (erule v_t_abstractE; clarsimp)
   apply (rotate_tac 2)
   apply (subst (asm) \<Xi>_def; clarsimp simp: wordarray_fold_no_break_0_type_def abbreviated_type_defs)
   apply (drule val_wa_foldnb_bod_preservation[OF proc_ctx_wellformed_\<Xi> val_proc_env_matches_\<xi>m_\<Xi>]; simp?; clarsimp)
  apply (clarsimp simp: wordarray_map_no_break_0_type_def val_wa_mapAccumnb_def)
  apply (erule v_t_recordE)
  apply (erule v_t_r_consE; clarsimp)+
  apply (erule v_t_abstractE; clarsimp)
  apply (rotate_tac 2)
  apply (subst (asm) \<Xi>_def; clarsimp simp: wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (subst (asm) \<Xi>_def; clarsimp simp: wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (drule_tac ptrl = None in val_wa_mapAccumnb_bod_preservation[OF proc_ctx_wellformed_\<Xi> val_proc_env_matches_\<xi>m_\<Xi>]; simp?)
  apply clarsimp+
  done

lemma upd_val_wa_foldnb_bod_corres:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; proc_env_u_v_matches \<xi>\<^sub>u \<xi>\<^sub>v \<Xi>'; proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
    upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f u acc t obsv (\<sigma>', res); 
    val_wa_foldnb_bod \<xi>\<^sub>v v xs (unat frm) (unat to) f acc' obsv' res';
    \<sigma> p = option.Some (UAbstract (UWA v len arr));
    wa_abs_upd_val \<Xi>' (UWA v len arr) (VWA v xs) ''WordArray'' [v] (Boxed ReadOnly ptrl) r w \<sigma>;
    upd_val_rel \<Xi>' \<sigma> acc acc' u ra wa; upd_val_rel \<Xi>' \<sigma> obsv obsv' t s {};
     p \<notin> w; p \<notin> wa;
     r \<inter> wa = {}; 
     ra \<inter> w = {}; 
     s \<inter> w = {}; s \<inter> wa = {};
     w \<inter> wa = {};
    \<tau> = TRecord [(a0, (v, Present)), (a1, (u, Present)), (a2, (t, Present))] Unboxed;
     \<Xi>', 0, [], {}, [option.Some \<tau>] \<turnstile> App f (Var 0) : u; distinct [a0, a1, a2]\<rbrakk>
    \<Longrightarrow> \<exists>ra' wa'.  upd_val_rel \<Xi>' \<sigma>' res res' u ra' wa' \<and> ra' \<subseteq> ({p} \<union> ra \<union> s \<union> r)\<and> frame \<sigma> wa \<sigma>' wa'"
  apply (induct to arbitrary: res res' \<sigma>')
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = wa in exI)
   apply (clarsimp simp: frame_def)
  apply (case_tac "len < 1 + to")
   apply (drule_tac ptrl = ptrl and ra = r and wa = w and rb = ra and wb = wa and rc = s 
      in upd_wa_foldnb_bod_back_step'[OF _ _ _ abs_upd_val_to_uval_typing
        upd_val_rel_to_uval_typing(1) upd_val_rel_to_uval_typing(1), rotated -2]; simp?)
   apply (drule unatSuc; clarsimp)
   apply (drule val_wa_foldnb_bod_back_step'; simp?)
    apply (drule wa_abs_upd_val_elims(3); clarsimp simp: word_less_nat_alt)
  apply (case_tac "1 + to \<le> frm")
   apply (frule_tac y = "1 + to" and x = frm in leD)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = wa in exI)
   apply (clarsimp simp: frame_def)
  apply (frule wa_abs_upd_val_elims(1)[THEN wa_abs_typing_u_elims(1)]; clarsimp)
  apply (rename_tac ta)
  apply (drule_tac ta = ta and ptrl = ptrl and ra = r and wa = w and rb = ra and wb = wa and rc = s
      in upd_wa_foldnb_bod_back_step[OF _ _ _ abs_upd_val_to_uval_typing
        upd_val_rel_to_uval_typing(1) upd_val_rel_to_uval_typing(1), rotated -3]; simp?)
  apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
  apply (drule_tac val_wa_foldnb_bod_back_step; simp?)
   apply (drule wa_abs_upd_val_elims(3); clarsimp)
  apply clarsimp
  apply (elim meta_allE meta_impE, assumption, assumption)
  apply clarsimp
  apply (rename_tac \<sigma>' ta \<sigma>'' resa va r' ra' wa')
  apply (frule_tac \<gamma> = "[URecord [(va, RPrim (Num ta)), (resa, type_repr u), 
       (obsv, type_repr t)] None]" and
      \<gamma>' = "[VRecord [xs ! unat to, r', obsv']]" and
      r = "ra' \<union> s" and w = wa' in mono_correspondence(1); simp?; clarsimp?)
   apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
    apply (rule u_v_struct; simp?)
    apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
     apply (drule abs_upd_val_frame[rotated 1]; simp?)
     apply (drule wa_abs_upd_val_elims(4))
     apply (erule_tac x = to in allE)
     apply (clarsimp simp: not_less word_less_nat_alt)
     apply (rule u_v_prim'; clarsimp)
    apply (rule u_v_r_cons1[where r' = s and w' = "{}", simplified]; simp?)
     apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (rule_tac ?w1.0 = wa in upd_val_rel_frame(1); simp?) 
     apply (rule u_v_r_empty)
    apply (rule disjointI)
    apply (rename_tac x y)
    apply (drule_tac p = y and u = obsv in upd_val_rel_valid(1)[rotated -1]; simp?)
    apply clarsimp
    apply (drule_tac p = y in readonly_not_in_frame; simp?)
    apply (drule_tac x = y and S = s and S' = wa in orthD1; simp)
   apply (rule u_v_matches_empty[where \<tau>s = "[]" and \<epsilon>="[]", simplified])
  apply (intro exI conjI, assumption; simp?)
  apply clarsimp
   apply blast
  apply (rule frame_trans; simp)
  done

lemma val_executes_from_upd_wa_foldnb_bod:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; proc_env_u_v_matches \<xi>\<^sub>u \<xi>\<^sub>v \<Xi>'; proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
    upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f u acc t obsv (\<sigma>', res);
    \<sigma> p = option.Some (UAbstract (UWA v len arr));
    wa_abs_upd_val \<Xi>' (UWA v len arr) (VWA v xs) ''WordArray'' [v] (Boxed ReadOnly ptrl) r w \<sigma>;
    upd_val_rel \<Xi>' \<sigma> acc acc' u ra wa; upd_val_rel \<Xi>' \<sigma> obsv obsv' t s {};
    p \<notin> w; p \<notin> wa;
    r \<inter> wa = {}; 
    ra \<inter> w = {}; 
    s \<inter> w = {}; s \<inter> wa = {};
    w \<inter> wa = {};
    \<tau> = TRecord [(a0, (v, Present)), (a1, (u, Present)), (a2, (t, Present))] Unboxed;
     \<Xi>', 0, [], {}, [option.Some \<tau>] \<turnstile> App f (Var 0) : u; distinct [a0, a1, a2]\<rbrakk>
    \<Longrightarrow> \<exists>res'. val_wa_foldnb_bod \<xi>\<^sub>v v xs (unat frm) (unat to) f acc' obsv' res'"
  apply (induct to arbitrary: \<sigma>' res)
   apply (rule_tac x = acc' in exI)
   apply (subst val_wa_foldnb_bod.simps; clarsimp)
   apply clarsimp
  apply (case_tac "len < 1 + to")
   apply (drule_tac ptrl = ptrl and ra = r and wa = w and rb = ra and wb = wa and rc = s
      in upd_wa_foldnb_bod_back_step'[OF _ _ _ abs_upd_val_to_uval_typing
        upd_val_rel_to_uval_typing(1) upd_val_rel_to_uval_typing(1), rotated -2]; simp?)
   apply (drule unatSuc; clarsimp)
   apply (elim meta_allE meta_impE; simp?)
   apply clarsimp
   apply (drule val_wa_foldnb_bod_to_geq_lenD)
    apply (drule wa_abs_upd_val_elims(3); clarsimp simp: unatSuc word_less_nat_alt)
   apply (intro exI, rule val_wa_foldnb_bod_to_geq_len; simp?)
   apply (drule wa_abs_upd_val_elims(3); clarsimp simp: unatSuc word_less_nat_alt)
  apply (case_tac "1 + to \<le> frm")
   apply (rule_tac x = acc' in exI)
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
   apply (subst val_wa_foldnb_bod.simps; clarsimp)
  apply (frule wa_abs_upd_val_elims(2)[THEN wa_abs_typing_v_elims(1)]; clarsimp)
  apply (rename_tac ta)
  apply (drule_tac ptrl = ptrl and ta = ta and ra = r and wa = w and rb= ra and wb = wa and rc = s
      in upd_wa_foldnb_bod_back_step[OF _ _ _ abs_upd_val_to_uval_typing
        upd_val_rel_to_uval_typing(1) upd_val_rel_to_uval_typing(1), rotated -3]; simp?)
  apply clarsimp
  apply (elim meta_allE meta_impE, assumption)
  apply clarsimp
  apply (frule_tac r = r and w = w and ra = ra and wa = wa and s = s and ptrl = ptrl
      in upd_val_wa_foldnb_bod_corres; simp?)
  apply clarsimp
  apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
  apply (rename_tac \<sigma>'' resa va x ra' wa')
  apply (frule_tac \<gamma> = "[URecord [(va, RPrim (Num ta)), (resa, type_repr u), 
       (obsv, type_repr t)] None]" and
      \<gamma>' = "[VRecord [xs ! unat to, x, obsv']]" and
      r = "ra' \<union> s" and w = wa' in val_executes_from_upd_executes(1); simp?; clarsimp?)
   apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
    apply (rule u_v_struct; simp?)
    apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
     apply (drule abs_upd_val_frame[rotated 1]; simp?)
     apply (drule wa_abs_upd_val_elims(4))
     apply (erule_tac x = to in allE; clarsimp simp: word_less_nat_alt)+
     apply (rule u_v_prim'; clarsimp)
    apply (rule u_v_r_cons1[where r' = s and w' = "{}", simplified]; simp?)
     apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (rule upd_val_rel_frame(1); simp add: Int_commute)
     apply (rule u_v_r_empty)
    apply (rule disjointI)
    apply (rename_tac xa y)
    apply (drule_tac u = obsv and p = y in upd_val_rel_valid(1)[rotated 1]; simp?)
    apply clarsimp
    apply (drule_tac p = y and \<sigma> = \<sigma> in readonly_not_in_frame; simp?)
    apply blast  
   apply (rule u_v_matches_empty[where \<tau>s = "[]" and \<epsilon> = "[]", simplified])
  apply (drule_tac r' = v' in  val_wa_foldnb_bod_step; simp?)
   apply (drule wa_abs_upd_val_elims(3); simp)
  apply (rule_tac x = v' in exI)
  apply clarsimp
  done

lemma word_set_compr_helper4:
  "{arr + size_of_num_type ta * i |i. i < len \<and> frm \<le> i \<and> i < to} \<subseteq> {arr + size_of_num_type ta * i |i. i < len}"
  apply blast
  done

lemma val_exec_from_upd_and_corres:
assumes "proc_ctx_wellformed \<Xi>'"
and     "u_v_matches \<Xi>' \<sigma> \<gamma> \<gamma>' \<Gamma>' r w"
and     "proc_env_u_v_matches \<xi>\<^sub>u \<xi>\<^sub>v \<Xi>'"
shows   "\<lbrakk> \<xi>\<^sub>u , \<gamma>  \<turnstile> (\<sigma>, e) \<Down>! (\<sigma>', v)
         ; \<Xi>', 0, [], {}, \<Gamma>' \<turnstile> e : \<tau>
         \<rbrakk> \<Longrightarrow> \<exists>v' r' w'. (\<xi>\<^sub>v, \<gamma>' \<turnstile> e \<Down> v') \<and> upd_val_rel \<Xi>' \<sigma>' v v' \<tau> r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
and     "\<lbrakk> \<xi>\<^sub>u , \<gamma>  \<turnstile>* (\<sigma>, es) \<Down>! (\<sigma>', vs)
         ; \<Xi>', 0, [], {}, \<Gamma>' \<turnstile>* es : \<tau>s'
         \<rbrakk> \<Longrightarrow> \<exists>vs' r' w'. (\<xi>\<^sub>v, \<gamma>' \<turnstile>* es \<Down> vs') \<and> upd_val_rel_all \<Xi>' \<sigma>' vs vs' \<tau>s' r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  using assms
  apply -
   apply (frule val_executes_from_upd_executes(1); simp?)
  apply clarsimp
   apply (rule exI, rule conjI, simp)
   apply (frule mono_correspondence(1); simp?)
   apply (frule val_executes_from_upd_executes(2); simp?)
  apply clarsimp
   apply (rule exI, rule conjI, simp)
   apply (frule mono_correspondence(2); simp?)
  done

lemma upd_val_wa_mapAccumnb_bod_corres:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; proc_env_u_v_matches \<xi>\<^sub>u \<xi>\<^sub>v \<Xi>'; proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
    upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv (\<sigma>', res); 
    val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs (unat frm) (unat to) f acc' obsv' res';
    \<sigma> p = option.Some (UAbstract (UWA t len arr));
    wa_abs_upd_val \<Xi>' (UWA t len arr) (VWA t xs) ''WordArray'' \<tau>s (Boxed Writable ptrl) ra wa \<sigma>;
    upd_val_rel \<Xi>' \<sigma> acc acc' u rb wb; upd_val_rel \<Xi>' \<sigma> obsv obsv' v rc {};
    p \<notin> wa; p \<notin> wb; p \<notin> rb; p \<notin> rc;
    ra \<inter> wb = {}; 
    rb \<inter> wa = {}; 
    rc \<inter> wa = {}; rc \<inter> wb = {};
    wa \<inter> wb = {};
    \<Xi>', 0, [], {}, [option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)] 
      \<turnstile> (App f (Var 0)) : TRecord [(b0, t, Present), (b1, u, Present)] Unboxed;
    distinct [a0, a1, a2]; distinct [b0, b1]\<rbrakk>
    \<Longrightarrow>  \<exists>rp ta uacc r' w' xs' vacc. 
      res = URecord [(rp, uval_repr rp), (uacc, type_repr u)] None
    \<and> res' = VRecord[VAbstract (VWA t xs'), vacc]
    \<and> rp = UPtr p (RCon ''WordArray'' [type_repr t])
    \<and> t = TPrim (Num ta)
    \<and> wa_abs_upd_val \<Xi>' (UWA t len arr) (VWA t xs') ''WordArray'' \<tau>s (Boxed Writable ptrl) ra wa \<sigma>'
    \<and> upd_val_rel  \<Xi>' \<sigma>' uacc vacc u r' w'
    \<and> r' \<subseteq> rb \<union> rc
    \<and> (insert p wa) \<inter> r' = {}
    \<and> (insert p wa) \<inter> w' = {}
    \<and> ra \<inter> w' = {}
    \<and> frame \<sigma> ({arr + size_of_num_type ta * i | i. i < len \<and> frm \<le> i \<and> i < to } \<union> wb) \<sigma>' 
        ({arr + size_of_num_type ta * i | i. i < len \<and> frm \<le> i \<and> i < to } \<union> w')"
  apply (induct to arbitrary:  \<sigma>' res' res)
   apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp)
   apply (erule val_wa_mapAccumnb_bod.elims; clarsimp)
   apply (rule_tac x = "rb" in exI)
   apply (rule_tac x = "wb" in exI)
   apply (clarsimp simp: frame_id Int_commute)
  apply (frule abs_upd_val_to_uval_typing[THEN wa_abs_typing_u_elims(1)]; clarsimp)
  apply (rename_tac ta)
  apply (case_tac "len < 1 + to")
   apply (drule_tac ptrl = ptrl and ra = ra and wa = wa and rb = rb and wb = wb and rc = rc
      in upd_wa_mapAccumnb_bod_back_step'[OF _ _ _ abs_upd_val_to_uval_typing
        upd_val_rel_to_uval_typing(1) upd_val_rel_to_uval_typing(1), rotated -2]; simp?)
   apply (drule unatSuc; clarsimp)
   apply (drule val_wa_mapAccumnb_bod_back_step'; simp?)
    apply (drule wa_abs_upd_val_elims(3); clarsimp simp: word_less_nat_alt)
   apply (elim meta_allE meta_impE, assumption, assumption)
   apply clarsimp
   apply (intro exI conjI, assumption; simp?)
   apply (clarsimp simp: word_set_compr_helper)
  apply (case_tac "1 + to \<le> frm")
   apply (frule_tac y = "1 + to" and x = frm in leD)
   apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp)
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
   apply (erule val_wa_mapAccumnb_bod.elims; clarsimp)
   apply (rule_tac x = "rb" in exI)
   apply (rule_tac x = "wb" in exI)
   apply (clarsimp simp: frame_id Int_commute)
  apply (drule_tac ptrl = ptrl and ta = ta and ra = ra and wa = wa and rb = rb and wb = wb and
      rc = rc in upd_wa_mapAccumnb_bod_back_step[OF _ _ _ abs_upd_val_to_uval_typing
        upd_val_rel_to_uval_typing(1) upd_val_rel_to_uval_typing(1), rotated -3]; simp?)
  apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
  apply (frule val_wa_mapAccumnb_bod_preservation'; clarsimp)
  apply (drule val_wa_mapAccumnb_bod_back_step; simp?)
   apply (drule wa_abs_upd_val_elims(3); clarsimp)
  apply clarsimp
  apply (elim meta_allE meta_impE, assumption, assumption)
  apply clarsimp
  apply (rename_tac \<sigma>'' \<sigma>''' uacc uacc' x x' xs' vacc' vacc r' w')
  apply (frule_tac \<gamma> = "[URecord [(x, RPrim (Num ta)), (uacc, type_repr u),
      (obsv, type_repr v)] None]" and 
      \<gamma>' = "[VRecord [xs ! unat to, vacc, obsv']]" and
      r = "r' \<union> rc" and w = w' in mono_correspondence(1); simp?; clarsimp?)
   apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
    apply (rule u_v_struct; simp?)
    apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
     apply (drule_tac \<sigma> = \<sigma>'' in wa_abs_upd_val_elims(4))
     apply (erule_tac x = to in allE; clarsimp simp: word_less_nat_alt)
     apply (subst (asm) nth_list_update_eq)
      apply (drule wa_abs_upd_val_elims(3); clarsimp)
     apply clarsimp
     apply (rule u_v_prim'; clarsimp)
    apply (rule u_v_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
     apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (erule upd_val_rel_frame; simp?; simp add: Int_commute)
      apply (drule wa_abs_upd_val_elims(1)[THEN wa_abs_typing_u_elims(3)]; clarsimp)
      apply (clarsimp simp: Int_Un_distrib)
      apply (rule subset_helper[OF _ subset_refl
        word_set_compr_helper4[simplified word_le_nat_alt word_less_nat_alt]])
      apply (clarsimp simp: word_less_nat_alt word_le_nat_alt)
     apply (rule u_v_r_empty)
    apply (rule disjointI)
    apply (rename_tac y)
    apply (drule_tac p = y and u = obsv in upd_val_rel_valid(1)[rotated 1]; simp)
    apply clarsimp
    apply (drule_tac x = y and S = rc and S' = wb in orthD1; simp?)
    apply (drule_tac x = y and S = rc and S' = wa in orthD1; simp?)
    apply (drule wa_abs_upd_val_elims(1)[THEN wa_abs_typing_u_elims(3)];
      clarsimp simp: word_less_nat_alt word_le_nat_alt)
    apply (drule_tac p = y and  \<sigma> = \<sigma> in readonly_not_in_frame; simp?)
    apply blast
   apply (rule u_v_matches_empty[where \<tau>s = "[]" and \<epsilon> = "[]", simplified])
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
  apply (rename_tac uacc' r'' w'' l)
  apply (rule conjI)
   apply (drule_tac \<sigma> = \<sigma>'' and l = w' in  abs_upd_val_frame[rotated 1]; simp?)
   apply (drule_tac \<sigma> = \<sigma>''' and i = to  in wa_abs_upd_val_update; simp?)
    apply (clarsimp simp: word_less_nat_alt word_le_nat_alt)
   apply (drule_tac t = "VPrim l" in sym; clarsimp)
    apply (cut_tac \<sigma> = \<sigma>''' and
                 l = "arr + size_of_num_type ta * to" and
                 v = "UPrim l" 
                 in frame_single_update)
  apply (rule_tac x = r'' in exI)
  apply (rule_tac x = w'' in exI)
  apply (rule conjI)
   apply (drule_tac u = uacc' in upd_val_rel_frame(1)[rotated 3]; simp?)
    apply (drule_tac p = "arr + size_of_num_type ta * to" and \<sigma> = \<sigma>'' in readonly_not_in_frame; simp?)
    apply (rule_tac S = wa in orthD1; simp?)
    apply (drule wa_abs_upd_val_elims(1)[THEN wa_abs_typing_u_elims(3)]; clarsimp)
    apply (intro exI conjI, simp)
    apply (clarsimp simp: word_less_nat_alt word_le_nat_alt)
   apply simp
   apply (rule contra_subsetD; simp?)
   apply simp
   apply (drule wa_abs_upd_val_elims(1)[THEN wa_abs_typing_u_elims(3)]; clarsimp)
   apply (rule conjI)
    apply (rule_tac S = wa in orthD1; simp?)
    apply (intro exI conjI, simp)
    apply (clarsimp simp: word_less_nat_alt word_le_nat_alt)
   apply (rule_tac S' = wa in orthD2; simp?)
   apply (intro exI conjI, simp)
   apply (clarsimp simp: word_less_nat_alt word_le_nat_alt)
  apply (intro conjI)
        apply clarsimp
        apply (rename_tac x)
        apply (drule_tac A = r'' and B = "r' \<union> rc" and c = x in subsetD; simp)
        apply (drule_tac A = r' and B = "rb \<union> rc" and c = x in subsetD; simp)
       apply clarsimp
       apply (drule_tac A = r'' and B = "r' \<union> rc" and c = p in subsetD; simp)
      apply (rule disjointI)
      apply (rename_tac x y)
      apply (drule_tac A = r'' and B = "r' \<union> rc" and c = y in subsetD; simp)
      apply (rule disjE; blast)
     apply (drule wa_abs_upd_val_elims(1)[THEN wa_abs_typing_u_elims(3)]; clarsimp)
     apply (drule_tac p = p and \<sigma> = \<sigma> in valid_ptr_not_in_frame_same; simp?)
      apply (clarsimp simp: word_less_nat_alt word_le_nat_alt)
     apply (drule_tac p = p and w = w' in readonly_not_in_frame; simp?)
    apply (rule disjointI)
    apply (rename_tac x y)
    apply (drule_tac \<sigma> = \<sigma>'' in wa_abs_upd_val_elims(1))
    apply (frule wa_abs_typing_u_elims(5))
    apply (drule wa_abs_typing_u_elims(3); clarsimp)
    apply (rename_tac i)
    apply (erule_tac x = i in allE; clarsimp)+
    apply (drule_tac p = "arr + size_of_num_type ta * i" and \<sigma> = \<sigma>'' in readonly_not_in_frame; simp?)
     apply (drule_tac x = "arr + size_of_num_type ta * i" and S' = w' in orthD1; simp?)
      apply (intro exI conjI; simp)
   apply (drule wa_abs_upd_val_elims(1)[THEN wa_abs_typing_u_elims(3)]; clarsimp)
  apply (drule_tac s = "{arr + size_of_num_type ta * i |i. i < len \<and> frm \<le> i \<and> i < 1 + to}" and
      \<sigma> = \<sigma>''' in frame_expand(2); simp?)
   apply (drule_tac l = w' and l' = w'' and \<sigma> = \<sigma>'' in abs_upd_val_frame[rotated 1]; simp?)
   apply (drule_tac \<sigma> = \<sigma>''' in wa_abs_upd_val_elims(4); clarsimp)
   apply (rename_tac i)
   apply (erule_tac x = i in allE; clarsimp)+
  apply (drule_tac s = "{arr + size_of_num_type ta * i |i. i < len \<and> frm \<le> i \<and> i < 1 + to}" and 
      \<sigma> = \<sigma>'' in frame_expand(2); simp?)
   apply (drule_tac \<sigma> = \<sigma>'' in wa_abs_upd_val_elims(4); clarsimp)
   apply (rename_tac i)
   apply (erule_tac x = i in allE; clarsimp)+
  apply (drule_tac p = "arr + size_of_num_type ta * to" and \<sigma> = \<sigma> in frame_expand(1))
   apply (drule wa_abs_upd_val_elims(4); clarsimp)
   apply (erule_tac x = to in allE)
   apply (clarsimp simp: word_less_nat_alt word_le_nat_alt)  
  apply (subst (asm) Un_insert_left[symmetric])
  apply (subst (asm) word_set_compr_helper3[simplified word_less_nat_alt word_le_nat_alt]; simp?)
    apply auto[1]
   apply (drule distinct_indices[OF abs_upd_val_to_uval_typing]; simp?)
   apply (clarsimp simp: word_less_nat_alt)
  apply (subst (asm) Un_insert_left[symmetric])
  apply (subst (asm) word_set_compr_helper3[simplified word_less_nat_alt word_le_nat_alt]; simp?)
    apply auto[1]
   apply (drule distinct_indices[OF abs_upd_val_to_uval_typing]; simp?)
   apply (clarsimp simp: word_less_nat_alt)
  apply (subst (asm) insert_absorb, clarsimp)
   apply (intro exI conjI; simp?; unat_arith?; simp?)
  apply (subst (asm) insert_absorb, clarsimp)
   apply (intro exI conjI; simp?; unat_arith?; simp?)
  apply (clarsimp simp: word_less_nat_alt word_le_nat_alt)
  apply (drule_tac \<sigma> = \<sigma> and \<sigma>' = \<sigma>'' and \<sigma>'' = \<sigma>''' in frame_trans; simp?)
   apply (drule_tac s = w'' in frame_expand(2); simp?)
   apply clarsimp
   apply (rename_tac pa)
   apply (drule_tac p = pa and u = uacc' in upd_val_rel_valid(1)[rotated 1]; simp?)
  apply (erule frame_trans; simp?)
  apply (clarsimp simp: Un_commute)
  done

lemma val_executes_fron_upd_wa_mapAccumnb_bod:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; proc_env_u_v_matches \<xi>\<^sub>u \<xi>\<^sub>v \<Xi>'; proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
    upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv (\<sigma>', res); 
    \<sigma> p = option.Some (UAbstract (UWA t len arr));
    wa_abs_upd_val \<Xi>' (UWA t len arr) (VWA t xs) ''WordArray'' [t] (Boxed Writable ptrl) ra wa \<sigma>;
    upd_val_rel \<Xi>' \<sigma> acc acc' u rb wb; upd_val_rel \<Xi>' \<sigma> obsv obsv' v rc {};
    p \<notin> wa; p \<notin> wb; p \<notin> rb; p \<notin> rc;
    ra \<inter> wb = {}; 
    rb \<inter> wa = {}; 
    rc \<inter> wa = {}; rc \<inter> wb = {};
    wa \<inter> wb = {};
    \<Xi>', 0, [], {}, [option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)] 
      \<turnstile> (App f (Var 0)) : TRecord [(b0, t, Present), (b1, u, Present)] Unboxed;
    distinct [a0, a1, a2]; distinct [b0, b1]\<rbrakk>
    \<Longrightarrow> Ex (val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs (unat frm) (unat to) f acc' obsv')"
  apply (induct to arbitrary: \<sigma>' res)
   apply (rule_tac x = "VRecord [VAbstract (VWA t xs), acc']" in exI)
   apply (subst val_wa_mapAccumnb_bod.simps; clarsimp)
  apply (case_tac "len < 1 + to")
   apply (drule_tac ptrl = ptrl and ra = ra and wa = wa and rb = rb and wb = wb and rc = rc
      in upd_wa_mapAccumnb_bod_back_step'[OF _ _ _ abs_upd_val_to_uval_typing
        upd_val_rel_to_uval_typing(1) upd_val_rel_to_uval_typing(1), rotated -2]; simp?)
   apply (elim  meta_allE meta_impE, assumption)
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt not_less)
   apply (rename_tac x)
   apply (rule_tac x = x in exI)
   apply (clarsimp simp: less_Suc_eq_le)
   apply (drule wa_abs_upd_val_elims(3))
   apply (drule val_wa_mapAccumnb_bod_to_geq_lenD; simp?)
   apply (rule val_wa_mapAccumnb_bod_to_geq_len; simp)
  apply (case_tac "1 + to \<le> frm")
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt not_less word_le_nat_alt)
   apply (rule_tac x = "VRecord [VAbstract (VWA t xs), acc']" in exI)
   apply (subst val_wa_mapAccumnb_bod.simps; clarsimp)
  apply (frule wa_abs_upd_val_elims(2))
  apply (drule wa_abs_typing_v_elims(1); clarsimp) 
  apply (drule_tac ptrl = ptrl and ra = ra and wa = wa and rb = rb and wb = wb and rc = rc
      in upd_wa_mapAccumnb_bod_back_step[OF _ _ _ abs_upd_val_to_uval_typing
        upd_val_rel_to_uval_typing(1) upd_val_rel_to_uval_typing(1), rotated -3]; simp?)
  apply clarsimp
  apply (elim meta_allE meta_impE, assumption)
  apply clarsimp
  apply (frule_tac ptrl = ptrl and \<tau>s = "[t]" and ra = ra and wa = wa and rb = rb and wb = wb and
      rc = rc in upd_val_wa_mapAccumnb_bod_corres; simp?)
  apply clarsimp
  apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
  apply (rename_tac \<sigma>'' \<sigma>''' uacc uacc' x x' r' w' xs' vacc)
  apply (frule wa_abs_upd_val_elims(4))
  apply (erule_tac x = to in allE)
  apply (erule impE; clarsimp simp: word_less_nat_alt word_le_nat_alt)
  apply (frule_tac p = "arr + size_of_num_type ta * to" in valid_ptr_not_in_frame_same; simp?)
   apply (drule wa_abs_upd_val_elims(1)[THEN wa_abs_typing_u_elims(3)]; clarsimp)
   apply (intro conjI allI impI)
    apply (clarsimp simp: word_less_nat_alt word_le_nat_alt)
    apply (drule distinct_indices[OF wa_abs_upd_val_elims(1)])
    apply (rename_tac i)
    apply (erule_tac x = i in allE)+
    apply (clarsimp simp: word_less_nat_alt)
    apply (erule_tac x = to in allE)
    apply (erule impE; fastforce)
   apply (rule_tac S = wa in orthD1; simp)
   apply (intro exI conjI, simp, fastforce simp: word_less_nat_alt word_le_nat_alt)
  apply (frule_tac 
      \<gamma> = "[URecord [(x, RPrim (Num ta)), (uacc, type_repr u), (obsv, type_repr v)] None]" and
      \<gamma>' = "[VRecord [xs ! unat to, vacc, obsv']]" and
      r = "r' \<union> rc" and w = w' in val_exec_from_upd_and_corres(1); simp?; clarsimp?)
    apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
     apply (rule u_v_struct; simp?)
     apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
      apply (rule u_v_prim'; clarsimp)
     apply (rule u_v_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
      apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
       apply (erule upd_val_rel_frame(1); simp add: Int_commute)
       apply (clarsimp simp: Int_Un_distrib)
       apply (rule subset_helper[OF _ subset_refl
        word_set_compr_helper4[simplified word_le_nat_alt word_less_nat_alt]])
       apply (drule wa_abs_upd_val_elims(1)[THEN wa_abs_typing_u_elims(3)])
       apply (clarsimp simp: word_less_nat_alt word_le_nat_alt)
      apply (rule u_v_r_empty)
    apply (rule disjointI)
    apply (drule_tac p = y and u = obsv in upd_val_rel_valid(1)[rotated 1]; simp?)
    apply clarsimp
     apply (drule_tac p = y and \<sigma> = \<sigma> in readonly_not_in_frame; simp?)
     apply (drule wa_abs_upd_val_elims(1)[THEN wa_abs_typing_u_elims(3)])
     apply (clarsimp simp: word_less_nat_alt word_le_nat_alt)
     apply blast
   apply (rule u_v_matches_empty[where \<tau>s = "[]" and \<epsilon> = "[]", simplified])
  apply (erule u_v_recE'; clarsimp)
  apply (erule u_v_r_consE'; simp?)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym; clarsimp)
  apply (erule u_v_r_consE'; clarsimp)
  apply (erule u_v_r_emptyE'; clarsimp)
  apply (drule val_wa_mapAccumnb_bod_step; simp?)
   apply (drule wa_abs_upd_val_elims(3); clarsimp)
  apply (intro exI, assumption)
  done

lemma wordarray_fold_no_break_upd_val:
  "\<And>K a b \<sigma> \<sigma>' ls \<tau>s aa a' v v' r w.
   \<lbrakk>list_all2 (kinding 0 [] {}) \<tau>s K; wordarray_fold_no_break_0_type = (0, K,{}, a, b); 
    upd_val_rel \<Xi> \<sigma> aa a' (instantiate ls \<tau>s a) r w; 
    upd_wa_foldnb \<Xi> \<xi>0 (foldmap_funarg_type ''wordarray_fold_no_break_0'') (\<sigma>, aa) (\<sigma>', v)\<rbrakk>
    \<Longrightarrow> (val_wa_foldnb \<Xi> \<xi>m (foldmap_funarg_type ''wordarray_fold_no_break_0'') a' v' 
          \<longrightarrow> (\<exists>r' w'. upd_val_rel \<Xi> \<sigma>' v v' (instantiate ls \<tau>s b) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w')) \<and> 
        Ex (val_wa_foldnb \<Xi> \<xi>m (foldmap_funarg_type ''wordarray_fold_no_break_0'') a')"
  apply (clarsimp simp: wordarray_fold_no_break_0_type_def upd_wa_foldnb_def)
  apply (erule u_v_recE'; clarsimp)
  apply (erule u_v_r_consE'; clarsimp)
  apply (erule u_v_ptrE'; simp)
  apply (drule_tac t = "map type_repr _" in sym; clarsimp)
  apply (frule wa_abs_upd_val_elims(2), drule wa_abs_typing_v_elims(1); clarsimp)
  apply (erule u_v_r_consE'; simp)
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)
  apply clarsimp

  apply (erule u_v_primE')+
  apply (drule_tac t = "TPrim _" in sym)
  apply (drule_tac t = "TPrim _" in sym)
  apply clarsimp
  apply (erule u_v_r_consE'; clarsimp)
  apply (frule tfun_no_pointers(1)[OF upd_val_rel_to_uval_typing(1)]; clarsimp)
  apply (frule tfun_no_pointers(2)[OF upd_val_rel_to_uval_typing(1)]; clarsimp)
  apply (erule u_v_r_consE'; clarsimp)+
  apply (erule u_v_r_emptyE'; clarsimp)
  apply (rename_tac \<sigma> \<sigma>' v v' p frm to \<tau>a \<tau>o len arr a0 a1 a2 r xs f f' uacc vacc rb wb uobsv vobsv rc wa)
  apply (subst (asm) \<Xi>_def; simp add: wordarray_fold_no_break_0_type_def abbreviated_type_defs)
  apply (frule_tac v = uobsv and K' = "[]" and k = "kinding_fn [] \<tau>o" 
      in discardable_or_shareable_not_writable(1)[rotated 1, OF upd_val_rel_to_uval_typing(1)]; simp?)
    apply (rule kindingI; clarsimp)
  apply (clarsimp simp: val_wa_foldnb_def)
  apply (erule impE; simp?)+
   apply (case_tac f; clarsimp; elim u_v_t_funE u_v_t_afunE; clarsimp)
  apply (erule impE, rule upd_val_rel_to_vval_typing(1); simp?)+
  apply (erule impE; simp?)+
   apply (case_tac f; clarsimp; elim u_v_t_funE u_v_t_afunE; clarsimp)
  apply (erule impE, erule wa_abs_upd_val_elims(2); simp?)
  apply (erule disjE; simp?)
   apply clarsimp
   apply (drule_tac xs = xs and acc' = vacc and obsv' = vobsv and res' = v' and
      ptrl = None and r = r and w = "{}" and ra = rb and wa = wb
      in upd_val_wa_foldnb_bod_corres[OF proc_ctx_wellformed_\<Xi> proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>
        upd_proc_env_matches_ptrs_\<xi>0_\<Xi>]; (simp add: Int_commute)?; clarsimp?)
    apply (case_tac f; clarsimp; elim u_v_t_funE u_v_t_afunE; clarsimp)
   apply (rename_tac r' w')
   apply (erule_tac x = r' in allE)
   apply (erule impE, blast)
   apply (erule_tac x = w' in allE; clarsimp)
   apply (drule_tac xs = xs and acc' = vacc and obsv' = vobsv and
      ptrl = None and r = r and w = "{}" and ra = rb and wa = wb
      in val_executes_from_upd_wa_foldnb_bod[OF proc_ctx_wellformed_\<Xi> proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>
        upd_proc_env_matches_ptrs_\<xi>0_\<Xi>]; (simp add: Int_commute)?; clarsimp?)
  apply (rename_tac res)
  apply (erule_tac x = res in allE)
  apply (case_tac f; clarsimp; elim u_v_t_funE u_v_t_afunE; clarsimp)
  done


lemma frame_expand2:
  "\<lbrakk>frame \<sigma> (w \<union> u) \<sigma>' (w \<union> u'); w \<subseteq> w'\<rbrakk> \<Longrightarrow> frame \<sigma> (w' \<union> u) \<sigma>' (w' \<union> u')"
  apply (clarsimp simp: frame_def)
  apply blast
  done

lemma upd_wa_mapAccumnb_preservation:
  "\<And>K a b \<sigma> \<sigma>' ls \<tau>s v v' r w.
       \<lbrakk>list_all2 (kinding 0 [] {}) \<tau>s K; 
        wordarray_map_no_break_0_type = (0, K,{}, a, b); 
        uval_typing \<Xi> \<sigma> v (instantiate ls \<tau>s a) r w;
        upd_wa_mapAccumnb \<Xi> \<xi>0
         (funarg_type (present_type (rec_type_list (prod.fst (prod.snd(prod.snd(prod.snd(\<Xi> ''wordarray_map_no_break_0''))))) ! 3)))
         (funret_type (present_type (rec_type_list (prod.fst (prod.snd(prod.snd(prod.snd(\<Xi> ''wordarray_map_no_break_0''))))) ! 3))) (\<sigma>, v) (\<sigma>', v')\<rbrakk>
       \<Longrightarrow> \<exists>r' w'. uval_typing \<Xi> \<sigma>' v' (instantiate ls \<tau>s b) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: wordarray_map_no_break_0_type_def upd_wa_mapAccumnb_def)
  apply (rename_tac \<sigma> \<sigma>' v' r w p frm to func acc obsv t \<tau>a \<tau>o len arr a0 a1 a2 b0 b1)
  apply (erule u_t_recE; clarsimp)
  apply (erule u_t_r_consE; clarsimp)
  apply (erule u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym; clarsimp)
  apply (erule u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym; clarsimp)
  apply (erule u_t_r_consE; clarsimp)
  apply (frule tfun_no_pointers(1))
  apply (frule tfun_no_pointers(2))
  apply clarsimp
  apply (rename_tac f r' w')
  apply (erule u_t_r_consE; clarsimp)
  apply (rename_tac acc r_a w_a r' w')
  apply (erule u_t_r_consE; clarsimp)
  apply (erule u_t_r_emptyE; clarsimp)
  apply (rename_tac obsv r_o w_o) 
  apply (erule u_t_primE)+
  apply (drule_tac t = "lit_type _" in sym)+
  apply clarsimp
  apply (erule u_t_ptrE; clarsimp)
  apply (rename_tac wa)
  apply (subst (asm) \<Xi>_def; simp add: wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (subst (asm) \<Xi>_def; simp add: wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (frule_tac v = obsv and K' = "[]" and k = "kinding_fn [] \<tau>o" in discardable_or_shareable_not_writable(1)[rotated 1]; simp?)
   apply (rule kindingI; clarsimp)
  apply clarsimp
  apply (cut_tac ra = ra and rb = r_a and rc = r_o  and wa = wa and wb = w_a in 
      upd_wa_mapAccumnb_bod_preservation[OF proc_ctx_wellformed_\<Xi> upd_proc_env_matches_ptrs_\<xi>0_\<Xi>, 
        where ptrl = None, simplified]; simp?; clarsimp?)
      apply blast
     apply blast
    apply blast
   apply blast
  apply (rename_tac r' w')
  apply (erule_tac x = "ra \<union> r'" in allE)
  apply (erule impE, blast)
  apply (erule_tac x = "(insert p wa) \<union> w'" in allE)
  apply (erule impE)
   apply (rule u_t_struct)
    apply (rule u_t_r_cons1; simp?)
      apply (rule u_t_p_abs_w[where ts = "[TPrim (Num _)]", simplified]; simp?)
      apply (drule wa_abs_typing_u_elims(3))
      apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp?)
      apply clarsimp
     apply (rule u_t_r_cons1[where r' = "{}" and w' = "{}" and xs = "[]" and ts = "[]", simplified]; simp?)
     apply (rule u_t_r_empty)
    apply (drule wa_abs_typing_u_elims(3); blast)
   apply clarsimp
  apply (rotate_tac -1)
  apply (erule notE)
  apply (drule_tac w' = wa in frame_expand2)
   apply (drule wa_abs_typing_u_elims(3); clarsimp simp: word_set_compr_helper4)
   apply blast
  apply clarsimp
  apply (drule_tac p = p in frame_expand(1); simp?)
  done

lemma upd_proc_env_matches_ptrs_\<xi>1_\<Xi>:
  "proc_env_matches_ptrs \<xi>1 \<Xi>"
  apply (unfold proc_env_matches_ptrs_def)
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
   apply (clarsimp simp: upd_wa_foldnb_preservation subst_wellformed_def) 
  apply (fastforce intro!: upd_wa_mapAccumnb_preservation 
                   simp add: subst_wellformed_def wordarray_map_no_break_0_type_def)
  done

lemma wordarray_mapAccumnb_abs_upd_val:
  "\<And>K a b \<sigma> \<sigma>' ls \<tau>s aa a' v v' r w.
       \<lbrakk>list_all2 (kinding 0 [] {}) \<tau>s K; 
        wordarray_map_no_break_0_type = (0, K,{}, a, b); 
        upd_val_rel \<Xi> \<sigma> aa a' (instantiate ls \<tau>s a) r w;
        upd_wa_mapAccumnb \<Xi> \<xi>0
         (funarg_type (present_type (rec_type_list (prod.fst (prod.snd (prod.snd (prod.snd (\<Xi> ''wordarray_map_no_break_0''))))) ! 3)))
         (funret_type (present_type (rec_type_list (prod.fst (prod.snd (prod.snd (prod.snd (\<Xi> ''wordarray_map_no_break_0''))))) ! 3))) (\<sigma>, aa) (\<sigma>', v)\<rbrakk>
       \<Longrightarrow> (val_wa_mapAccumnb \<Xi> \<xi>m
             (funarg_type (present_type (rec_type_list (prod.fst (prod.snd (prod.snd (prod.snd (\<Xi> ''wordarray_map_no_break_0''))))) ! 3)))
             (funret_type (present_type (rec_type_list (prod.fst (prod.snd (prod.snd (prod.snd (\<Xi> ''wordarray_map_no_break_0''))))) ! 3))) a' v' \<longrightarrow>
            (\<exists>r' w'. upd_val_rel \<Xi> \<sigma>' v v' (instantiate ls \<tau>s b) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w')) \<and>
           Ex (val_wa_mapAccumnb \<Xi> \<xi>m
                (funarg_type (present_type (rec_type_list (prod.fst (prod.snd (prod.snd (prod.snd (\<Xi> ''wordarray_map_no_break_0''))))) ! 3)))
                (funret_type (present_type (rec_type_list (prod.fst (prod.snd (prod.snd (prod.snd (\<Xi> ''wordarray_map_no_break_0''))))) ! 3))) a')"
  apply (clarsimp simp: wordarray_map_no_break_0_type_def upd_wa_mapAccumnb_def)
  apply (rename_tac \<sigma> \<sigma>' a' v v' r w p frm to func acc obsv t \<tau>a \<tau>o len arr a0 a1 a2 b0 b1)
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
  apply (erule u_v_r_consE'; clarsimp)
  apply (erule u_v_r_consE'; clarsimp)
  apply (erule u_v_r_emptyE'; clarsimp)
  apply (erule u_v_primE')+
  apply (drule_tac t ="TPrim _" in sym)
  apply (drule_tac t ="TPrim _" in sym)
  apply clarsimp
  apply (erule u_v_ptrE'; clarsimp)
  apply (frule tfun_no_pointers(1)[OF upd_val_rel_to_uval_typing(1)]; simp)
  apply (frule tfun_no_pointers(2)[OF upd_val_rel_to_uval_typing(1)]; simp)
  apply clarsimp
  apply (rename_tac ra f f' acc acc' rb wb obsv obsv' rc wc a' wa)
  apply (subst (asm) \<Xi>_def; simp add: wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (frule_tac v = obsv and K' = "[]" and k = "kinding_fn [] \<tau>o"
      in discardable_or_shareable_not_writable(1)[rotated 1, OF upd_val_rel_to_uval_typing(1)];
      simp?)
   apply (rule kindingI; clarsimp)
  apply (subst (asm) \<Xi>_def; simp add: wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (clarsimp simp: val_wa_mapAccumnb_def)
  apply (erule impE; simp?)
   apply (case_tac f; simp; elim u_v_t_funE u_v_t_afunE; simp)
  apply (erule impE, rule upd_val_rel_to_vval_typing(1), simp?)+
  apply (erule impE; simp?)
   apply (case_tac f; simp; elim u_v_t_funE u_v_t_afunE; simp)
  apply (frule wa_abs_upd_val_elims(2)[THEN wa_abs_typing_v_elims(1)]; clarsimp)
  apply (rename_tac xs)
  apply (erule impE, drule wa_abs_upd_val_elims(2), assumption)
  apply (erule disjE; clarsimp)
   apply (drule_tac xs = xs and acc' = acc' and obsv' = obsv' and res' = v' and
      ptrl = None and ra = ra and wa = wa and rb = rb and wb = wb
      in upd_val_wa_mapAccumnb_bod_corres[OF proc_ctx_wellformed_\<Xi> proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>
        upd_proc_env_matches_ptrs_\<xi>0_\<Xi>]; (simp add: Int_commute)?; clarsimp?)
      apply (case_tac f; clarsimp; elim u_v_t_funE u_v_t_afunE; clarsimp)
     apply blast
    apply blast
   apply (rename_tac uacc r' w' xs' vacc)
   apply (erule_tac x = "ra \<union> r'" in allE)
   apply (erule impE, blast)
   apply (erule_tac x = "(insert p wa) \<union> w'" in allE)
   apply (erule impE)
    apply (rule u_v_struct)
     apply (rule u_v_r_cons1; simp?)
       apply (rule u_v_p_abs_w[where ts = "[TPrim (Num _)]", simplified]; simp?)
       apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp?)
       apply (drule wa_abs_upd_val_elims(1)[THEN wa_abs_typing_u_elims(3)]; clarsimp)
      apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (rule u_v_r_empty)
     apply (drule wa_abs_upd_val_elims(1)[THEN wa_abs_typing_u_elims(3)]; blast)
    apply clarsimp
   apply (rotate_tac -1)
   apply (erule notE)
   apply (drule_tac w' = wa in frame_expand2)
    apply (drule wa_abs_upd_val_elims(1)[THEN wa_abs_typing_u_elims(3)]; clarsimp simp: word_set_compr_helper4)
    apply blast
   apply clarsimp
   apply (drule_tac p = p in frame_expand(1); simp?)
  apply (drule_tac xs = xs and acc' = acc' and obsv' = obsv' and
      ptrl = None and ra = ra and wa = wa and rb = rb and wb = wb
      in val_executes_fron_upd_wa_mapAccumnb_bod[OF proc_ctx_wellformed_\<Xi> proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>
        upd_proc_env_matches_ptrs_\<xi>0_\<Xi>]; (simp add: Int_commute)?; clarsimp?)
    apply blast
   apply blast
  apply (rename_tac x)
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
   apply (clarsimp simp: subst_wellformed_def)
   apply (fastforce dest!: wordarray_fold_no_break_upd_val 
                    simp: wordarray_fold_no_break_0_type_def)
  apply (clarsimp simp: subst_wellformed_def)
  apply (fastforce dest!: wordarray_mapAccumnb_abs_upd_val simp: wordarray_map_no_break_0_type_def )
  done

end (* of context *)

end
(*
  This file contains the provable assumptions which are required when proving correspondence of
  word array functions.
*)
theory WordArray_CorresProof_Asm
  imports WordArray_Abstractions
begin

context WordArray begin

section "Level 0 Assumptions"

lemma value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p: 
  "value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m \<xi>p"
  apply (clarsimp simp: val.rename_mono_prog_def)
  apply (rule conjI; clarsimp)
   apply (rule_tac x = v' in exI)
   apply (subst (asm) rename_def)
   apply (subst (asm) assoc_lookup.simps)+
   apply (clarsimp split: if_split_asm simp: val_wa_length_0_def)
   apply (case_tac v; clarsimp)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x = v' in exI)
   apply (subst (asm) rename_def)
   apply (subst (asm) assoc_lookup.simps)+
   apply (clarsimp split: if_split_asm simp: val_wa_get_0_def)
   apply (case_tac v; clarsimp)
   apply (case_tac z; clarsimp)
   apply (case_tac za; clarsimp)
  apply clarsimp
  apply (rule_tac x = v' in exI)
  apply (subst (asm) rename_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm simp: val_wa_put2_0_def)
  apply (case_tac v; clarsimp)
  apply (case_tac z; clarsimp)
  apply (case_tac za; clarsimp)
  apply (case_tac zb; clarsimp)
  done

lemma val_proc_env_matches_\<xi>m_\<Xi>:
  "val.proc_env_matches \<xi>m \<Xi>"
  apply (clarsimp simp: val.proc_env_matches_def)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
    apply (clarsimp simp: wordarray_get_0_type_def abbreviatedType3_def val_wa_get_0_def)
    apply (rule val.v_t_prim[where l = "(LU32 _)", simplified])
   apply (clarsimp simp: wordarray_length_0_type_def val_wa_length_0_def)
   apply (rule val.v_t_prim[where l = "(LU32 _)", simplified])
  apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType2_def val_wa_put2_0_def)
  apply (erule val.v_t_recordE)
  apply (erule val.v_t_r_consE; clarsimp)
  apply (erule val.v_t_abstractE)
  apply (rule val.v_t_abstract; clarsimp)
   apply (clarsimp simp: abs_typing_v_def)
   apply (erule_tac x = i in allE; clarsimp)
   apply (case_tac "i = unat idx")
    apply (rule_tac x = val in exI; simp)
   apply (rule_tac x = x in exI; simp)
  done

lemma wordarray_get_upd_val:
  "\<And>K a b \<sigma> \<sigma>' \<tau>s aa a' v v' r w.
   \<lbrakk>list_all2 (kinding []) \<tau>s K; wordarray_get_0_type = (K, a, b);
    upd_val_rel \<Xi> \<sigma> aa a' (instantiate \<tau>s a) r w; upd_wa_get_0 (\<sigma>, aa) (\<sigma>', v)\<rbrakk>
    \<Longrightarrow> (val_wa_get_0 a' v' \<longrightarrow> (\<exists>r' w'. upd_val_rel \<Xi> \<sigma>' v v' (instantiate \<tau>s b) r' w' \<and> r' \<subseteq> r \<and> 
          frame \<sigma> w \<sigma>' w')) \<and> Ex (val_wa_get_0 a')"
  apply (clarsimp simp: upd_wa_get_0_def wordarray_get_0_type_def abbreviatedType3_def)
  apply (erule u_v_recE'; clarsimp)
  apply (erule u_v_r_consE'; clarsimp)
  apply (erule u_v_p_absE'; clarsimp)
  apply (erule u_v_r_consE'; clarsimp)
  apply (erule u_v_r_emptyE')
  apply (erule u_v_primE')+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: val_wa_get_0_def)
   apply (rule_tac x = "{}" in exI)+
   apply (clarsimp simp: abs_upd_val'_def frame_def word_less_nat_alt)
   apply (erule_tac x = idx in allE)
   apply clarsimp
   apply (case_tac "unat idx < length xs"; clarsimp intro!: u_v_prim[where l = "(LU32 _)", simplified])
  apply (clarsimp simp: word_less_nat_alt abs_upd_val'_def)
  apply (case_tac a'; clarsimp simp: word_less_nat_alt)
  apply (erule_tac x = idx in allE)
  apply (case_tac "unat idx < length x1"; clarsimp)
   apply (rule_tac x = "VPrim (LU32 x)" in exI)
   apply (clarsimp simp: val_wa_get_0_def)
  apply (rule_tac x = "VPrim (LU32 0)" in exI)
  apply (clarsimp simp: val_wa_get_0_def)
  done

lemma wordarray_length_upd_val:
  "\<And>K a b \<sigma> \<sigma>' \<tau>s aa a' v v' r w.
   \<lbrakk>list_all2 (kinding []) \<tau>s K; wordarray_length_0_type = (K, a, b);
    upd_val_rel \<Xi> \<sigma> aa a' (instantiate \<tau>s a) r w; upd_wa_length_0 (\<sigma>, aa) (\<sigma>', v)\<rbrakk>
    \<Longrightarrow> (val_wa_length_0 a' v' \<longrightarrow> (\<exists>r' w'. upd_val_rel \<Xi> \<sigma>' v v' (instantiate \<tau>s b) r' w' \<and> r' \<subseteq> r \<and> 
          frame \<sigma> w \<sigma>' w')) \<and> Ex (val_wa_length_0 a')"
  apply (clarsimp simp: upd_wa_length_0_def wordarray_length_0_type_def)
  apply (erule u_v_p_absE'; clarsimp)
  apply (clarsimp simp: abs_upd_val'_def)
  apply (case_tac a'a; clarsimp)
  apply (rule conjI)
   apply (clarsimp simp: val_wa_length_0_def)
   apply (rule_tac x = "{}" in exI)+
   apply (clarsimp simp: frame_def intro!: u_v_prim[where l = "(LU32 _)", simplified])
  apply (clarsimp simp: abs_upd_val'_def)
  apply (rule_tac x = "VPrim (LU32 len)" in exI)
  apply (clarsimp simp: val_wa_length_0_def)
  done

lemma wordarray_put2_upd_val:
  "\<And>K a b \<sigma> \<sigma>' \<tau>s aa a' v v' r w.
   \<lbrakk>list_all2 (kinding []) \<tau>s K; wordarray_put2_0_type = (K, a, b); 
    upd_val_rel \<Xi> \<sigma> aa a' (instantiate \<tau>s a) r w; upd_wa_put2_0 (\<sigma>, aa) (\<sigma>', v)\<rbrakk>
    \<Longrightarrow> (val_wa_put2_0 a' v' \<longrightarrow> (\<exists>r' w'. upd_val_rel \<Xi> \<sigma>' v v' (instantiate \<tau>s b) r' w' \<and> r' \<subseteq> r \<and>
          frame \<sigma> w \<sigma>' w')) \<and> Ex (val_wa_put2_0 a')"
  apply (clarsimp simp: upd_wa_put2_0_def wordarray_put2_0_type_def abbreviatedType2_def)
  apply (erule u_v_recE'; clarsimp)
  apply (erule u_v_r_consE'; clarsimp)
  apply (erule u_v_p_absE'; clarsimp)
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (subst (asm) type_repr.simps[symmetric])+
  apply clarsimp
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (subst (asm) type_repr.simps[symmetric])+
  apply clarsimp
  apply (erule u_v_r_emptyE')
  apply (erule u_v_primE')+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: val_wa_put2_0_def)
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = "insert p w" in exI)
   apply clarsimp
   apply (rule conjI)
    apply (rule_tac a = a and  ptrl = undefined in u_v_p_abs_w[where ts = "[TPrim (Num U32)]", simplified])
       apply simp
      apply (clarsimp simp: abs_upd_val'_def)
      apply (case_tac a; clarsimp)
      apply (rule conjI)
       apply (clarsimp simp: abs_typing_u_def)
      apply (rule conjI)
       apply (clarsimp simp: abs_typing_v_def word_less_nat_alt)
       apply (erule_tac x = i in allE)
       apply (case_tac "i = unat idx"; clarsimp)
      apply (clarsimp simp: word_less_nat_alt)
      apply (rule conjI)
       apply (drule distinct_indices)
       apply (clarsimp simp: word_less_nat_alt)
       apply (erule_tac x = i in allE)+
       apply clarsimp
       apply (erule_tac x = idx in allE)
       apply clarsimp
      apply clarsimp
      apply (erule_tac x = i in allE)
      apply clarsimp
      apply (case_tac "unat i = unat idx"; clarsimp)
     apply (clarsimp simp: abs_upd_val'_def)
     apply (erule_tac x = idx in allE)
     apply clarsimp
    apply simp
   apply (clarsimp simp: frame_def abs_upd_val'_def abs_typing_u_def)
  apply (case_tac a; clarsimp)
   apply (rule conjI; clarsimp)
    apply (rule conjI)
     apply clarsimp
    apply (rule conjI; clarsimp)
   apply (rule conjI; clarsimp)
  apply (clarsimp simp: abs_upd_val'_def)
  apply (case_tac a; clarsimp simp: abs_typing_u_def)
  apply (case_tac a'; clarsimp)
  apply (rule_tac x = "VAbstract (VWA (x1[unat idx := VPrim (LU32 val)]))" in exI)
  apply (clarsimp simp: val_wa_put2_0_def)
  done

lemma proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>:
  "proc_env_u_v_matches \<xi>0 \<xi>m \<Xi>"
  apply (clarsimp simp: proc_env_u_v_matches_def)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
    apply (clarsimp simp: wordarray_get_upd_val)
   apply (clarsimp simp: wordarray_length_upd_val)
  apply (clarsimp simp: wordarray_put2_upd_val)
  done

lemma wordarray_get_uval_typing_frame:
  "\<And>K a b \<sigma> \<sigma>' \<tau>s v v' r w.
   \<lbrakk>list_all2 (kinding []) \<tau>s K; wordarray_get_0_type = (K, a, b);
    upd.uval_typing \<Xi> \<sigma> v (instantiate \<tau>s a) r w; upd_wa_get_0 (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi> \<sigma>' v' (instantiate \<tau>s b) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: wordarray_get_0_type_def abbreviatedType3_def upd_wa_get_0_def)
  apply (erule upd.u_t_recE; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_p_absE; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_r_emptyE; clarsimp)
  apply (erule upd.u_t_primE; subst (asm) lit_type.simps; clarsimp)+
  apply (rule_tac x = "{}" in exI)+
  apply (clarsimp simp: frame_def abs_typing_u_def)
  apply (erule_tac x = idx in allE)
  apply (case_tac "idx < len"; clarsimp intro!: upd.u_t_prim[where l = "(LU32 _)", simplified])
  done

lemma wordarray_length_uval_typing_frame:
  "\<And>K a b \<sigma> \<sigma>' \<tau>s v v' r w.
   \<lbrakk>list_all2 (kinding []) \<tau>s K; wordarray_length_0_type = (K, a, b); 
    upd.uval_typing \<Xi> \<sigma> v (instantiate \<tau>s a) r w; upd_wa_length_0 (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi> \<sigma>' v' (instantiate \<tau>s b) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: wordarray_length_0_type_def upd_wa_length_0_def)
  apply (erule upd.u_t_p_absE; clarsimp)
  apply (rule_tac x = "{}" in exI)+
  apply (clarsimp simp: frame_def intro!: upd.u_t_prim[where l = "(LU32 _)", simplified])
  done

lemma wordarray_put2_uval_typing_frame:
  "\<And>K a b \<sigma> \<sigma>' \<tau>s v v' r w.
   \<lbrakk>list_all2 (kinding []) \<tau>s K; wordarray_put2_0_type = (K, a, b);
    upd.uval_typing \<Xi> \<sigma> v (instantiate \<tau>s a) r w; upd_wa_put2_0 (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi> \<sigma>' v' (instantiate \<tau>s b) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType2_def upd_wa_put2_0_def)
  apply (erule upd.u_t_recE; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_p_absE; clarsimp)
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
  apply (case_tac a; clarsimp)
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = "insert p w" in exI)
   apply (rule conjI)
    apply (rename_tac len arr)
    apply (rule_tac ptrl = undefined and a = "WAU32 len arr" in upd.u_t_p_abs_w[where ts = "[TPrim (Num U32)]", simplified])
       apply simp
      apply (clarsimp simp: abs_typing_u_def)
     apply (clarsimp simp: abs_typing_u_def)
    apply clarsimp
   apply (clarsimp simp: frame_def abs_typing_u_def)
   apply (rule conjI; clarsimp)
    apply (rule conjI)
     apply clarsimp
    apply (rule conjI; clarsimp)
   apply (rule conjI; clarsimp)
  apply (clarsimp simp: abs_typing_u_def)
  done

lemma upd_proc_env_matches_ptrs_\<xi>0_\<Xi>:
  "upd.proc_env_matches_ptrs \<xi>0 \<Xi>"
  apply (unfold upd.proc_env_matches_ptrs_def)
  apply clarsimp
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
    apply (clarsimp simp: wordarray_get_uval_typing_frame)
   apply (clarsimp simp: wordarray_length_uval_typing_frame)
  apply (clarsimp simp: wordarray_put2_uval_typing_frame)
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

lemma wordarray_fold_no_break_uval_typing_frame:
  "\<And>K a b \<sigma> \<sigma>' \<tau>s v v' r w.
   \<lbrakk>list_all2 (kinding []) \<tau>s K; wordarray_fold_no_break_0_type = (K, a, b);
    upd.uval_typing \<Xi> \<sigma> v (instantiate \<tau>s a) r w; upd_wa_foldnb_0 (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi> \<sigma>' v' (instantiate \<tau>s b) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: wordarray_fold_no_break_0_type_def upd_wa_foldnb_0_def)
  apply (rule_tac x = "{}" in exI)
  apply (rule_tac x = w in exI)
  apply (clarsimp simp: frame_def)
  apply (erule upd.u_t_recE; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_p_absE; clarsimp)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (subst (asm) type_repr.simps[symmetric])+
  apply clarsimp
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (subst (asm) type_repr.simps[symmetric])+
  apply clarsimp
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (subst (asm) type_repr.simps[symmetric])+
  apply clarsimp
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (subst (asm) type_repr.simps[symmetric])+
  apply clarsimp
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply clarsimp
  apply (erule upd.u_t_r_emptyE)
  apply (erule upd.u_t_primE)+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (erule upd.u_t_unitE)
  apply clarsimp
  apply (case_tac xa; clarsimp)
   apply (erule upd.u_t_funE'; clarsimp)
   apply (rule upd.u_t_prim[where l = "LU32 _", simplified])
  apply (erule upd.u_t_afunE; clarsimp)
  apply (rule upd.u_t_prim[where l = "LU32 _", simplified])
  done

inductive_cases v_t_prim_tE : "val.vval_typing \<Xi>' v (TPrim (Num U32))"

lemma lit_type_ex_32:
  "lit_type l = Num U32 \<Longrightarrow> \<exists>v. l = LU32 v"
  apply (induct l; clarsimp)
  done

lemma val_wa_foldnb_0_mono_helper1:
  "\<lbrakk>val.proc_env_matches \<xi>m1 \<Xi>; proc_ctx_wellformed \<Xi>; \<forall>i<length xs. \<exists>v. xs ! i = VPrim (LU32 v);
    \<Xi>, [], [option.Some Generated_TypeProof.abbreviatedType1] \<turnstile> App (Fun (val.rename_expr rename 
      (val.monoexpr (specialise ts f))) []) (Var 0) : TPrim (Num U32);
    val_wa_foldnb_bod_0 xs frm to (Fun (val.rename_expr rename (val.monoexpr (specialise ts f))) [])
         (VPrim (LU32 acc)) VUnit (VPrim (LU32 r))\<rbrakk>
       \<Longrightarrow> val_wa_foldnb_bod_0p xs frm to (Fun f ts) (VPrim (LU32 acc)) VUnit (VPrim (LU32 r))"
  apply (induct to arbitrary: r)
   apply (erule val_wa_foldnb_bod_0.elims; clarsimp)
   apply (subst val_wa_foldnb_bod_0p.simps; clarsimp)
  apply clarsimp
  apply (case_tac "length xs < Suc to")
   apply (erule_tac x = r in meta_allE)
   apply (drule val_wa_foldnb_bod_0_back_step'; simp)
   apply (drule val_wa_foldnb_bod_0p_to_geq_lenD)
    apply linarith
   apply (rule val_wa_foldnb_bod_0p_to_geq_len; simp)
  apply (clarsimp simp: not_less)
  apply (case_tac "frm \<ge> to")
   apply (erule val_wa_foldnb_bod_0.elims; clarsimp split: if_splits)
    apply (erule val_wa_foldnb_bod_0.elims; clarsimp)
    apply (subst val_wa_foldnb_bod_0p.simps; clarsimp)
    apply (subst val_wa_foldnb_bod_0p.simps; clarsimp)
    apply (drule_tac \<gamma> = "[VRecord [VPrim (LU32 v), VPrim (LU32 acc), VUnit]]" and
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
   apply (subst val_wa_foldnb_bod_0p.simps; clarsimp)
  apply (clarsimp simp: not_le)
  apply (frule_tac x = to in spec)
  apply (erule impE, simp)
  apply (erule exE)
  apply (drule val_wa_foldnb_bod_0_back_step; simp?)
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
   apply (drule_tac v = v and r' = "VPrim (LU32 r)" in val_wa_foldnb_bod_0p_step; simp)
  apply (insert val_proc_env_matches_\<xi>m_\<Xi>)
  apply (clarsimp simp: abbreviatedType1_def)
  apply (drule val_wa_foldnb_bod_0_preservation; simp?)
    apply (rule val.v_t_prim[where l = "LU32 _", simplified])
   apply (rule val.v_t_unit)
  apply (erule v_t_prim_tE)
  apply (drule lit_type_ex_32[OF sym])
  apply clarsimp
  done

lemma val_wa_foldnb_0_mono_helper2:
  "\<lbrakk>val.proc_env_matches \<xi>m1 \<Xi>; proc_ctx_wellformed \<Xi>; \<forall>i<length xs. \<exists>v. xs ! i = VPrim (LU32 v);
    \<Xi>, [], [option.Some Generated_TypeProof.abbreviatedType1] \<turnstile> App (AFun (rename (f, ts)) []) 
      (Var 0) : TPrim (Num U32);
    val_wa_foldnb_bod_0 xs frm to (AFun (rename (f, ts)) [])
         (VPrim (LU32 acc)) VUnit (VPrim (LU32 r))\<rbrakk>
       \<Longrightarrow> val_wa_foldnb_bod_0p xs frm to (AFun f ts) (VPrim (LU32 acc)) VUnit (VPrim (LU32 r))"
  apply (induct to arbitrary: r)
   apply (erule val_wa_foldnb_bod_0.elims; clarsimp)
   apply (subst val_wa_foldnb_bod_0p.simps; clarsimp)
  apply clarsimp
  apply (case_tac "length xs < Suc to")
   apply (erule_tac x = r in meta_allE)
   apply (drule val_wa_foldnb_bod_0_back_step'; simp)
   apply (drule val_wa_foldnb_bod_0p_to_geq_lenD)
    apply linarith
   apply (rule val_wa_foldnb_bod_0p_to_geq_len; simp)
  apply (clarsimp simp: not_less)
  apply (case_tac "frm \<ge> to")
   apply (erule val_wa_foldnb_bod_0.elims; clarsimp split: if_splits)
    apply (erule val_wa_foldnb_bod_0.elims; clarsimp)
    apply (subst val_wa_foldnb_bod_0p.simps; clarsimp)
    apply (subst val_wa_foldnb_bod_0p.simps; clarsimp)
    apply (drule_tac \<gamma> = "[VRecord [VPrim (LU32 v), VPrim (LU32 acc), VUnit]]" and
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
   apply (subst val_wa_foldnb_bod_0p.simps; clarsimp)
  apply (clarsimp simp: not_le)
  apply (frule_tac x = to in spec)
  apply (erule impE, simp)
  apply (erule exE)
  apply (drule val_wa_foldnb_bod_0_back_step; simp?)
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
   apply (drule_tac v = v and r' = "VPrim (LU32 r)" in val_wa_foldnb_bod_0p_step; simp)
  apply (insert val_proc_env_matches_\<xi>m_\<Xi>)
  apply (clarsimp simp: abbreviatedType1_def)
  apply (drule val_wa_foldnb_bod_0_preservation; simp?)
    apply (rule val.v_t_prim[where l = "LU32 _", simplified])
   apply (rule val.v_t_unit)
  apply (erule v_t_prim_tE)
  apply (drule lit_type_ex_32[OF sym])
  apply clarsimp
  done

lemma value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m1_\<xi>p1: 
  "value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m1 \<xi>p1"
  apply (clarsimp simp: val.rename_mono_prog_def)
  apply (rule conjI; clarsimp)
   apply (rule_tac x = v' in exI)
   apply (subst (asm) rename_def)
   apply (subst (asm) assoc_lookup.simps)+
   apply (clarsimp split: if_split_asm simp: val_wa_length_0_def)
   apply (case_tac v; clarsimp)
  apply (rule conjI; clarsimp)
   apply (rule_tac x = v' in exI)
   apply (subst (asm) rename_def)
   apply (subst (asm) assoc_lookup.simps)+
   apply (clarsimp split: if_split_asm simp: val_wa_get_0_def)
   apply (case_tac v; clarsimp)
   apply (case_tac z; clarsimp)
   apply (case_tac za; clarsimp)
  apply (rule conjI; clarsimp)
   apply (rule_tac x = v' in exI)
   apply (subst (asm) rename_def)
   apply (subst (asm) assoc_lookup.simps)+
   apply (clarsimp split: if_split_asm simp: val_wa_put2_0_def)
   apply (case_tac v; clarsimp)
   apply (case_tac z; clarsimp)
   apply (case_tac za; clarsimp)
   apply (case_tac zb; clarsimp)
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
    apply (clarsimp simp: wordarray_get_0_type_def abbreviatedType3_def val_wa_get_0_def)
    apply (rule val.v_t_prim[where l = "(LU32 _)", simplified])
   apply (clarsimp simp: wordarray_length_0_type_def val_wa_length_0_def)
   apply (rule val.v_t_prim[where l = "(LU32 _)", simplified])
  apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType2_def val_wa_put2_0_def)
  apply (erule val.v_t_recordE)
  apply (erule val.v_t_r_consE; clarsimp)
  apply (erule val.v_t_abstractE)
  apply (rule val.v_t_abstract; clarsimp)
   apply (clarsimp simp: abs_typing_v_def)
   apply (erule_tac x = i in allE; clarsimp)
   apply (case_tac "i = unat idx")
    apply (rule_tac x = val in exI; simp)
   apply (rule_tac x = x in exI; simp)
  apply (clarsimp simp: wordarray_fold_no_break_0_type_def val_wa_foldnb_0_def)
  apply (erule val.v_t_recordE)
  apply (erule val.v_t_r_consE; clarsimp)+
  apply (rule val.v_t_prim'; simp)
  done

lemma upd_wa_foldnb_bod_0_pres_obsv:
  "\<lbrakk>upd_wa_foldnb_bod_0 \<sigma> p frm to f acc (obsv, s) (\<sigma>', res); upd_val_rel \<Xi> \<sigma> obsv obsv' t s {};
    \<sigma> p = option.Some (UAbstract (WAU32 len arr)); \<forall>i < len. \<exists>x. \<sigma> (arr + 4 * i) = option.Some (UPrim (LU32 x))\<rbrakk> 
    \<Longrightarrow> upd_val_rel \<Xi> \<sigma>' obsv obsv' t s {}"
  apply (induct to arbitrary: \<sigma>' res)
   apply (erule upd_wa_foldnb_bod_0.elims; clarsimp)
  apply (case_tac "len < 1 + to")
   apply (drule upd_wa_foldnb_bod_0_back_step'; simp?)
  apply (case_tac "frm < to")
   apply (frule_tac x = to in spec)
   apply (erule impE)
    apply (drule unatSuc; clarsimp simp: word_less_nat_alt)
   apply clarsimp
   apply (drule upd_wa_foldnb_bod_0_back_step; simp?)
    apply (drule unatSuc; clarsimp simp: word_less_nat_alt)
   apply clarsimp
   apply (drule_tac x = \<sigma>'' in meta_spec)
   apply (drule_tac x = r'' in meta_spec)
   apply clarsimp thm upd_val_rel_frame
   apply (drule_tac upd_val_rel_frame(1); simp?)
   apply blast
  apply (case_tac "\<not> frm < 1 + to")
   apply (erule upd_wa_foldnb_bod_0.elims; clarsimp)
  apply (clarsimp simp: not_le not_less)
  apply (subgoal_tac "to = frm")
  apply (erule upd_wa_foldnb_bod_0.elims; clarsimp split: if_splits)
   apply (erule upd_wa_foldnb_bod_0.elims; clarsimp simp: add.commute)
   apply (drule_tac upd_val_rel_frame(1); simp?)
   apply blast
  by (metis add.commute inc_le not_less word_le_less_eq)

lemma upd_val_wa_foldnb_bod_0_corres:
  "\<lbrakk>upd_wa_foldnb_bod_0 \<sigma> p frm to f acc (obsv, s) (\<sigma>', res); 
    val_wa_foldnb_bod_0 xs (unat frm) (unat to) f acc' obsv' res';
    \<sigma> p = option.Some (UAbstract (WAU32 len arr));
    abs_upd_val' (WAU32 len arr) (VWA xs) ''WordArray'' [TPrim (Num U32)] (Boxed ReadOnly undefined) r w \<sigma>;
    upd_val_rel \<Xi> \<sigma> acc acc' u ra wa; upd_val_rel \<Xi> \<sigma> obsv obsv' t s {}; wa \<inter> s = {}; proc_ctx_wellformed \<Xi>;
    \<tau> = TRecord [(''elem'', (TPrim (Num U32), Present)), (''acc'', (u, Present)), (''obsv'', (t, Present))] Unboxed;
    proc_env_u_v_matches \<xi>0 \<xi>m \<Xi>;  \<Xi>, [], [option.Some \<tau>] \<turnstile> App f (Var 0) : u\<rbrakk>
    \<Longrightarrow> \<exists>ra' wa'.  upd_val_rel \<Xi> \<sigma>' res res' u ra' wa' \<and> ra' \<subseteq> ({p} \<union> ra \<union> s \<union> r)\<and> frame \<sigma> wa \<sigma>' wa'"
  apply (induct to arbitrary: res res' \<sigma>')
   apply (erule upd_wa_foldnb_bod_0.elims; clarsimp)
   apply (erule val_wa_foldnb_bod_0.elims; clarsimp)
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = wa in exI)
   apply (clarsimp simp: frame_def)
  apply (case_tac "len < 1 + to")
   apply (drule upd_wa_foldnb_bod_0_back_step'; simp?)
   apply (drule unatSuc; clarsimp)
   apply (drule val_wa_foldnb_bod_0_back_step'; clarsimp simp: abs_upd_val'_def word_less_nat_alt)
  apply (case_tac "1 + to \<le> frm")
   apply (frule_tac y = "1 + to" and x = frm in leD)
   apply (erule upd_wa_foldnb_bod_0.elims; clarsimp)
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
   apply (erule val_wa_foldnb_bod_0.elims; clarsimp)
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = wa in exI)
   apply (clarsimp simp: frame_def)
  apply (case_tac "frm = to")
   apply (clarsimp simp: not_le not_less)
   apply (erule upd_wa_foldnb_bod_0.elims; clarsimp split: if_split_asm)
    apply (erule upd_wa_foldnb_bod_0.elims; clarsimp simp: add.commute)
    apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt abs_upd_val'_def)
    apply (erule val_wa_foldnb_bod_0.elims; clarsimp)
    apply (erule val_wa_foldnb_bod_0.elims; clarsimp)
    apply (erule_tac x = frm in allE; clarsimp)
    apply (frule_tac \<gamma> = "[URecord [(UPrim (LU32 v), RPrim (Num U32)), (acc, upd.uval_repr acc),
      (obsv, upd.uval_repr obsv)]]" and 
      \<gamma>' = "[VRecord [VPrim (LU32 v), acc', obsv']]" and
      r = "ra \<union> s" and w = wa in mono_correspondence(1); simp?)
     apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
      apply (rule u_v_struct; simp?)
      apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
       apply (rule u_v_prim[where l = "LU32 _", simplified])
      apply (rule u_v_r_cons1[where r = ra and w' = "{}", simplified]; simp?)
       apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
        apply (rule u_v_r_empty)
       apply (drule_tac u = obsv in upd_val_rel_to_uval_typing(1))
       apply (drule upd.type_repr_uval_repr(1); simp)
      apply (drule  upd_val_rel_to_uval_typing(1))
      apply (drule upd.type_repr_uval_repr(1); simp)
     apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
    apply clarsimp
    apply (rule_tac x = r' in exI)
    apply (rule_tac x = w' in exI; simp)
    apply blast
   apply (rule FalseE)
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
  apply clarsimp
  apply (subgoal_tac "\<exists>v. \<sigma> (arr + 4 * to) = option.Some (UPrim (LU32 v))")
   apply clarsimp
   apply (drule upd_wa_foldnb_bod_0_back_step; simp?)
     apply (drule unatSuc; clarsimp simp: word_less_nat_alt)
    apply (metis add.commute inc_le not_less_iff_gr_or_eq)
   apply clarsimp
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
   apply (drule_tac v = v in val_wa_foldnb_bod_0_back_step; simp?)
      apply (clarsimp simp: abs_upd_val'_def)
     apply (meson Suc_leI not_less_iff_gr_or_eq word_less_nat_alt)
    apply (clarsimp simp: abs_upd_val'_def)
    apply (erule_tac x = to in allE; clarsimp)
    apply (clarsimp simp: not_less word_less_nat_alt)
   apply clarsimp
   apply (drule_tac x = r'' in meta_spec)
   apply (drule_tac x = r' in meta_spec)
   apply (drule_tac x = \<sigma>'' in meta_spec)
   apply clarsimp
   apply (frule_tac \<gamma> = "[URecord [(UPrim (LU32 v), RPrim (Num U32)), (r'', upd.uval_repr r''), 
      (obsv, upd.uval_repr obsv)]]" and 
      \<gamma>' = "[VRecord [VPrim (LU32 v), r', obsv']]" and
      r = "ra' \<union> s" and w = wa' in mono_correspondence(1); simp?)
    apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
     apply (rule u_v_struct; simp?)
     apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
      apply (rule u_v_prim[where l = "LU32 _", simplified])
     apply (rule u_v_r_cons1[where r' = s and w' = "{}", simplified]; simp?)
       apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
         apply (drule upd_wa_foldnb_bod_0_pres_obsv; simp?)
         apply (clarsimp simp: abs_upd_val'_def abs_typing_u_def)
        apply (rule u_v_r_empty)
       apply (drule_tac u = obsv in upd_val_rel_to_uval_typing(1))
       apply (drule upd.type_repr_uval_repr(1); simp)
      apply (drule upd_val_rel_to_uval_typing(1))
      apply (thin_tac "frame _ _ _ _")
      apply (case_tac "\<exists>e. e \<in> wa' \<inter> s"; simp)
       apply (clarsimp simp: frame_def)
       apply (erule_tac x = e in allE)
       apply clarsimp
       apply (erule impE)
        apply (drule_tac x = e in orthD2; simp)
       apply (drule upd_val_rel_to_uval_typing(1))
       apply (drule_tac p = e and u = obsv in upd.uval_typing_valid(1)[rotated 1]; simp?)
      apply blast
     apply (drule_tac u = r'' in upd_val_rel_to_uval_typing(1))
     apply (drule upd.type_repr_uval_repr(1); simp)
    apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
   apply clarsimp
   apply (rule_tac x = r'a in exI)
   apply (rule_tac x = w' in exI)
   apply clarsimp
   apply (rule conjI)
    apply blast
   apply (rule upd.frame_trans; simp)
  apply (clarsimp simp: abs_upd_val'_def)
  apply (erule_tac x = to in allE)
  apply (erule impE)
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt)
  apply clarsimp
  done

lemma val_executes_from_upd_wa_foldnb_bod_0:
  "\<lbrakk>upd_wa_foldnb_bod_0 \<sigma> p frm to f acc (obsv, s) (\<sigma>', res); \<sigma> p = option.Some (UAbstract (WAU32 len arr));
    abs_upd_val' (WAU32 len arr) (VWA xs) ''WordArray'' [TPrim (Num U32)] (Boxed ReadOnly undefined) r w \<sigma>;
    upd_val_rel \<Xi> \<sigma> acc acc' u ra wa; upd_val_rel \<Xi> \<sigma> obsv obsv' t s {}; wa \<inter> s = {}; proc_ctx_wellformed \<Xi>;
    \<tau> = TRecord [(''elem'', (TPrim (Num U32), Present)), (''acc'', (u, Present)), (''obsv'', (t, Present))] Unboxed;
    proc_env_u_v_matches \<xi>0 \<xi>m \<Xi>;  \<Xi>, [], [option.Some \<tau>] \<turnstile> App f (Var 0) : u\<rbrakk>
    \<Longrightarrow> \<exists>res' r w. val_wa_foldnb_bod_0 xs (unat frm) (unat to) f acc' obsv' res' \<and> upd_val_rel \<Xi> \<sigma>' res res' u r w"
  apply (induct arbitrary: \<sigma>' res rule: word_induct[where m = "to"])
   apply (erule upd_wa_foldnb_bod_0.elims; clarsimp)
   apply (rule_tac x = acc' in exI)
   apply (subst val_wa_foldnb_bod_0.simps; clarsimp)
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = wa in exI)
   apply clarsimp
  apply (case_tac "1 + n \<le> 0"; clarsimp)
   apply (erule upd_wa_foldnb_bod_0.elims; clarsimp)
   apply (rule_tac x = acc' in exI)
   apply (subst val_wa_foldnb_bod_0.simps; clarsimp)
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = wa in exI)
   apply clarsimp
  apply (case_tac "len < 1 + n")
   apply (drule upd_wa_foldnb_bod_0_back_step'; simp?)
   apply (erule_tac x = \<sigma>' in meta_allE)
   apply (erule_tac x = res in meta_allE)
   apply clarsimp
   apply (rule_tac x = res' in exI)
   apply (drule val_wa_foldnb_bod_0_to_geq_lenD)
    apply (clarsimp simp: abs_upd_val'_def)
    apply (simp add: unatSuc word_less_nat_alt)
   apply (drule unatSuc; clarsimp)
   apply (rule conjI)
    apply (rule val_wa_foldnb_bod_0_to_geq_len; simp?)
    apply (clarsimp simp: abs_upd_val'_def word_less_nat_alt)
   apply (rule_tac x = rb in exI)
   apply (rule_tac x = x in exI)
   apply clarsimp
  apply (case_tac "1 + n \<le> frm")
   apply (rule_tac x = acc' in exI)
  apply (frule_tac y = "1 + n" and x = frm in leD)
   apply (erule upd_wa_foldnb_bod_0.elims; clarsimp)
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
   apply (subst val_wa_foldnb_bod_0.simps; clarsimp)
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = wa in exI)
   apply clarsimp
  apply (case_tac "frm = n")
   apply (clarsimp simp: not_le not_less)
   apply (erule upd_wa_foldnb_bod_0.elims; clarsimp split: if_split_asm)
    apply (erule upd_wa_foldnb_bod_0.elims; clarsimp simp: add.commute)
    apply (frule_tac \<gamma> = "[URecord [(UPrim (LU32 v), RPrim (Num U32)), (acc, upd.uval_repr acc), 
      (obsv, upd.uval_repr obsv)]]" and 
      \<gamma>' = "[VRecord [VPrim (LU32 v), acc', obsv']]" and
      r = "ra \<union> s" and w = wa in val_executes_from_upd_executes(1); simp?)
     apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
      apply (rule u_v_struct; simp?)
      apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
       apply (rule u_v_prim[where l = "LU32 _", simplified])
      apply (rule u_v_r_cons1[where r' = s and w' = "{}", simplified]; simp?)
       apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
        apply (rule u_v_r_empty)
       apply (drule_tac u = obsv in  upd_val_rel_to_uval_typing(1))
       apply (drule upd.type_repr_uval_repr(1); simp)
      apply (drule upd_val_rel_to_uval_typing(1))
      apply (drule upd.type_repr_uval_repr(1); simp)
     apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
    apply clarsimp
    apply (rule_tac x = v' in exI)
    apply (rule conjI)
     apply (clarsimp simp: abs_upd_val'_def)
     apply (erule_tac x = frm in allE; clarsimp)
     apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
     apply (subst val_wa_foldnb_bod_0.simps; clarsimp)
     apply (subst val_wa_foldnb_bod_0.simps; clarsimp)
    apply (frule_tac \<gamma> = "[URecord [(UPrim (LU32 v), RPrim (Num U32)), (acc, upd.uval_repr acc),
      (obsv, upd.uval_repr obsv)]]" and 
      \<gamma>' = "[VRecord [VPrim (LU32 v), acc', obsv']]" and
      r = "ra \<union> s" and w = wa in mono_correspondence(1); simp?)
     apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
      apply (rule u_v_struct; simp?)
      apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
       apply (rule u_v_prim[where l = "LU32 _", simplified])
      apply (rule u_v_r_cons1[where r' = s and w' = "{}", simplified]; simp?)
       apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
        apply (rule u_v_r_empty)
       apply (drule_tac u = obsv in  upd_val_rel_to_uval_typing(1))
       apply (drule upd.type_repr_uval_repr(1); simp)
      apply (drule upd_val_rel_to_uval_typing(1))
      apply (drule upd.type_repr_uval_repr(1); simp)
     apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
    apply clarsimp
    apply (rule_tac x = r' in exI)
    apply (rule_tac x = w' in exI)
    apply clarsimp
   apply (rule FalseE)
   apply simp
  apply (subgoal_tac "\<exists>v. \<sigma> (arr + 4 * n) = option.Some (UPrim (LU32 v))")
   apply clarsimp
   apply (drule_tac v = v in upd_wa_foldnb_bod_0_back_step; simp?)
     apply (metis word_le_less_eq word_zero_le)
    apply (metis add.commute plus_one_helper word_le_less_eq word_not_le)
   apply clarsimp
   apply (drule_tac x = \<sigma>'' in meta_spec)
   apply (drule_tac x = r'' in meta_spec)
   apply clarsimp
   apply (frule upd_val_wa_foldnb_bod_0_corres; simp?)
  apply clarsimp
   apply (subgoal_tac "wa' \<inter> s = {}")
    apply (frule_tac \<gamma> = "[URecord [(UPrim (LU32 v), RPrim (Num U32)), (r'', upd.uval_repr r''), 
      (obsv, upd.uval_repr obsv)]]" and 
      \<gamma>' = "[VRecord [VPrim (LU32 v), res', obsv']]" and
      r = "ra' \<union> s" and w = wa' in val_executes_from_upd_executes(1); simp?)
     apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
      apply (rule u_v_struct; simp?)
      apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
       apply (rule u_v_prim[where l = "LU32 _", simplified])
      apply (rule u_v_r_cons1[where r' = s and w' = "{}", simplified]; simp?)
       apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
         apply (drule upd_wa_foldnb_bod_0_pres_obsv; simp?)
         apply (clarsimp simp: abs_upd_val'_def abs_typing_u_def)
        apply (rule u_v_r_empty)
       apply (drule_tac u = obsv in  upd_val_rel_to_uval_typing(1))
       apply (drule upd.type_repr_uval_repr(1); simp)
      apply (drule_tac u = r'' in  upd_val_rel_to_uval_typing(1))
      apply (drule upd.type_repr_uval_repr(1); simp)
     apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
    apply clarsimp
    apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
    apply (drule_tac val_wa_foldnb_bod_0_step; simp?)
      apply (clarsimp simp: abs_upd_val'_def)
     apply (clarsimp simp: abs_upd_val'_def word_less_nat_alt)
     apply (erule_tac x = n in allE)
     apply clarsimp
    apply (rule_tac x = v' in exI)
    apply clarsimp
    apply (frule_tac \<gamma> = "[URecord [(UPrim (LU32 v), RPrim (Num U32)), (r'', upd.uval_repr r''), 
      (obsv, upd.uval_repr obsv)]]" and 
      \<gamma>' = "[VRecord [VPrim (LU32 v), res', obsv']]" and
      r = "ra' \<union> s" and w = wa' in mono_correspondence(1); simp?)
     apply (rule u_v_matches_some[where r' = "{}" and w' = "{}", simplified])
      apply (rule u_v_struct; simp?)
      apply (rule u_v_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
       apply (rule u_v_prim[where l = "LU32 _", simplified])
      apply (rule u_v_r_cons1[where r' = s and w' = "{}", simplified]; simp?)
       apply (rule u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
         apply (drule upd_wa_foldnb_bod_0_pres_obsv; simp?)
         apply (clarsimp simp: abs_upd_val'_def abs_typing_u_def)
        apply (rule u_v_r_empty)
       apply (drule_tac u = obsv in  upd_val_rel_to_uval_typing(1))
       apply (drule upd.type_repr_uval_repr(1); simp)
      apply (drule_tac u = r'' in  upd_val_rel_to_uval_typing(1))
      apply (drule upd.type_repr_uval_repr(1); simp)
     apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
    apply clarsimp
    apply (rule_tac x = r' in exI)
    apply (rule_tac x = w' in exI)
    apply simp
   apply (case_tac "\<exists>e. e \<in> wa' \<inter> s"; simp)
    apply (thin_tac "frame _ _ _ _")
    apply (thin_tac "upd_val_rel _ _ r'' _ _ _ _")
    apply (clarsimp simp: frame_def)
    apply (erule_tac x = e in allE)
    apply clarsimp
    apply (erule impE)
     apply blast
    apply (drule_tac u = obsv in upd_val_rel_to_uval_typing(1))
    apply (drule_tac p = e in upd.uval_typing_valid(1)[rotated 1]; simp?)
   apply blast
  apply (clarsimp simp: abs_upd_val'_def)
  apply (erule_tac x = n in allE)
  apply (erule impE)
   apply (metis add.commute plus_one_helper2 word_not_le)
  apply clarsimp
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
  apply (drule_tac t = ts in sym)
  apply (drule_tac t = t in sym)
  apply (drule_tac t = "type_repr t" in sym)
  apply (drule_tac t = xa in sym)
  apply (drule_tac t = n in sym)
  apply clarsimp
  apply (erule u_v_primE')
  apply (drule_tac s = "Num U32" in sym)
  apply clarsimp
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (drule_tac t = ts in sym)
  apply (drule_tac t = t in sym)
  apply (drule_tac t = "type_repr t" in sym)
  apply (drule_tac t = xa in sym)
  apply (drule_tac t = n in sym)
  apply clarsimp
  apply (erule u_v_primE')
  apply (drule_tac s = "Num U32" in sym)
  apply clarsimp
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (drule_tac t = ts in sym)
  apply (drule_tac t = t in sym)
  apply (drule_tac t = "type_repr t" in sym)
  apply (drule_tac t = xa in sym)
  apply (drule_tac t = n in sym)
  apply clarsimp
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (drule_tac t = ts in sym)
  apply (drule_tac t = t in sym)
  apply (drule_tac t = "type_repr t" in sym)
  apply (drule_tac t = xa in sym)
  apply (drule_tac t = n in sym)
  apply clarsimp
  apply (erule u_v_primE')
  apply (drule_tac s = "Num U32" in sym)
  apply clarsimp
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (drule_tac t = ts in sym)
  apply (drule_tac t = t in sym)
  apply (drule_tac t = xa in sym)
  apply (drule_tac t = n in sym)
  apply clarsimp
  apply (erule u_v_r_emptyE'; clarsimp)
  apply (subst (asm) upd_val_rel.simps[of _ _ "UUnit", simplified])
  apply clarsimp
  apply (erule disjE; clarsimp?)
  apply (erule disjE; clarsimp?)
  apply (case_tac a'; clarsimp simp: abs_upd_val'_def val_wa_foldnb_0_def)
  apply (case_tac x; clarsimp)
   apply (subst (asm) upd_val_rel.simps[of _ _ "UFunction _ _", simplified])
   apply clarsimp
   apply (erule disjE; clarsimp?)
   apply (erule disjE; clarsimp?)
   apply (rule conjI; clarsimp)
    apply (drule_tac xs = x1 and r = r and w = "{}" and acc' = "VPrim (LU32 acc)" and
      ra = "{}" and wa = "{}" and obsv' = "VUnit" and t = "TUnit" 
      in upd_val_wa_foldnb_bod_0_corres; simp?)
         apply (clarsimp simp: abs_upd_val'_def)
        apply (rule u_v_prim'; clarsimp)
       apply (rule u_v_unit)
      apply (rule proc_ctx_wellformed_\<Xi>)
     apply (clarsimp simp: abbreviatedType1_def)
    apply (rule proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>)
   apply (clarsimp simp: abs_typing_v_def)
   apply (drule_tac xs = x1 and r = r and w = "{}" and acc' = "VPrim (LU32 acc)" and
      ra = "{}" and wa = "{}" and obsv' = "VUnit" and t = "TUnit" 
      in val_executes_from_upd_wa_foldnb_bod_0; simp?)
         apply (clarsimp simp: abs_upd_val'_def abs_typing_v_def)
        apply (rule u_v_prim'; clarsimp)
       apply (rule u_v_unit)
      apply (rule proc_ctx_wellformed_\<Xi>)
     apply (clarsimp simp: abbreviatedType1_def)
    apply (rule proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>)
   apply clarsimp
   apply (rule_tac x = res' in exI)
   apply (clarsimp simp: val_wa_foldnb_0_def)
   apply (clarsimp simp: abbreviatedType1_def)
   apply (drule val_wa_foldnb_bod_0_preservation[OF proc_ctx_wellformed_\<Xi> val_proc_env_matches_\<xi>m_\<Xi>]; simp?)
     apply (rule val.v_t_prim'; simp)
    apply (rule val.v_t_unit)
   apply (erule v_t_prim_tE; clarsimp)
   apply (drule lit_type_ex_32[OF sym]; simp)
  apply (subst (asm) upd_val_rel.simps[of _ _ "UAFunction _ _", simplified])
  apply clarsimp
  apply (erule disjE; clarsimp?)
  apply (erule disjE; clarsimp?)
  apply (rule conjI; clarsimp)
   apply (drule_tac xs = x1 and r = r and w = "{}" and acc' = "VPrim (LU32 acc)" and
      ra = "{}" and wa = "{}" and obsv' = "VUnit" and t = "TUnit" 
      in upd_val_wa_foldnb_bod_0_corres; simp?)
        apply (clarsimp simp: abs_upd_val'_def)
       apply (rule u_v_prim'; clarsimp)
      apply (rule u_v_unit)
     apply (rule proc_ctx_wellformed_\<Xi>)
    apply (clarsimp simp: abbreviatedType1_def)
   apply (rule proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>)
  apply (drule_tac xs = x1 and r = r and w = "{}" and acc' = "VPrim (LU32 acc)" and
      ra = "{}" and wa = "{}" and obsv' = "VUnit" and t = "TUnit" 
      in val_executes_from_upd_wa_foldnb_bod_0; simp?)
        apply (clarsimp simp: abs_upd_val'_def)
       apply (rule u_v_prim'; clarsimp)
      apply (rule u_v_unit)
     apply (rule proc_ctx_wellformed_\<Xi>)
    apply (clarsimp simp: abbreviatedType1_def)
   apply (rule proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>)
  apply clarsimp
  apply (rule_tac x = res' in exI)
  apply (clarsimp simp: val_wa_foldnb_0_def abs_typing_v_def)
  apply (clarsimp simp: abbreviatedType1_def)
  apply (drule val_wa_foldnb_bod_0_preservation[OF proc_ctx_wellformed_\<Xi> val_proc_env_matches_\<xi>m_\<Xi>]; simp?)
    apply (rule val.v_t_prim'; simp)
   apply (rule val.v_t_unit)
  apply (erule v_t_prim_tE; clarsimp)
  apply (drule lit_type_ex_32[OF sym]; simp)
  done


lemma upd_proc_env_matches_ptrs_\<xi>1_\<Xi>:
  "upd.proc_env_matches_ptrs \<xi>1 \<Xi>"
  apply (unfold upd.proc_env_matches_ptrs_def)
  apply clarsimp
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
     apply (clarsimp simp: wordarray_get_uval_typing_frame)
    apply (clarsimp simp: wordarray_length_uval_typing_frame)
   apply (clarsimp simp: wordarray_put2_uval_typing_frame)
  apply (clarsimp simp: wordarray_fold_no_break_uval_typing_frame)
  done

lemma proc_env_u_v_matches_\<xi>1_\<xi>m1_\<Xi>:
  "proc_env_u_v_matches \<xi>1 \<xi>m1 \<Xi>"
  apply (clarsimp simp: proc_env_u_v_matches_def)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
     apply (clarsimp simp: wordarray_get_upd_val)
    apply (clarsimp simp: wordarray_length_upd_val)
   apply (clarsimp simp: wordarray_put2_upd_val)
  apply (clarsimp simp: wordarray_fold_no_break_upd_val)
  done

(*


lemma 
  "\<lbrakk>val_wa_foldnb_bod_0 xs frm (Suc to) f acc obsv r; frm < Suc to\<rbrakk>
    \<Longrightarrow> \<exists>acc'. val_wa_foldnb_bod_0 xs to (Suc to) f acc' obsv r"
  apply (induct rule: val_wa_foldnb_bod_0.induct[where ?a0.0 = xs and
                                                       ?a1.0 = frm and
                                                       ?a2.0 = to and
                                                       ?a3.0 = f and
                                                       ?a4.0 = acc and
                                                       ?a5.0 = obsv and
                                                       ?a6.0 = r]; clarsimp)
  apply (case_tac "frm < length xs")
   apply (case_tac "frm < to")
    apply (erule val_wa_foldnb_bod_0.elims; clarsimp)
   apply clarsimp
   apply (rule_tac x = acc in exI)
   apply (erule val_wa_foldnb_bod_0.elims; clarsimp)+
   apply (subst val_wa_foldnb_bod_0.simps; clarsimp)+
   apply (rule_tac x = v in exI)
   apply clarsimp
   apply (subgoal_tac "frma = to")
    apply clarsimp
   apply linarith
  apply (rule_tac x = res in exI)
  apply (subst val_wa_foldnb_bod_0.simps; clarsimp)
  done
lemma 
  "\<lbrakk>val_wa_foldnb_bod_0 xs frm to f (VPrim (LU32 acc)) VUnit r; 
    \<forall>i<length xs. \<exists>v. xs ! i = VPrim (LU32 v);
    \<Xi>, [], [option.Some abbreviatedType1] \<turnstile> App f (Var 0) : TPrim (Num U32)\<rbrakk>
    \<Longrightarrow> \<exists>x. r = VPrim (LU32 x)"
  apply (induct to arbitrary: r)
   apply (erule val_wa_foldnb_bod_0.elims; clarsimp)
  apply (case_tac "length xs < Suc to")
   apply (drule val_wa_foldnb_bod_0_back_step'; simp)
  apply (case_tac "to \<le> frm")
   apply (erule val_wa_foldnb_bod_0.elims; clarsimp split: if_splits)
   apply (erule val_wa_foldnb_bod_0.elims; clarsimp)
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
   apply (erule v_t_prim_tE; clarsimp simp: lit_type_ex_32)
  apply (clarsimp simp: not_less not_le)
  apply (erule_tac x = to in allE; clarsimp)
  apply (drule val_wa_foldnb_bod_0_back_step; simp?)
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
  apply (erule v_t_prim_tE; clarsimp simp: lit_type_ex_32)
  done


  term fold
function extract_ptr :: "(funtyp, abstyp, ptrtyp) uval \<Rightarrow> (funtyp, abstyp, ptrtyp) store \<Rightarrow> ptrtyp set \<Rightarrow> ptrtyp set"
  where
"extract_ptr (UPrim _) _ ps = ps" |
"extract_ptr UUnit _ ps = ps" |
"extract_ptr (UFunction _ _) _ ps = ps" |
"extract_ptr (UAFunction _ _) _ ps = ps" |
"extract_ptr (UAbstract _) _  ps = ps" |
"extract_ptr (UProduct a b) \<sigma> ps = fold (\<lambda>x ps. extract_ptr x \<sigma> ps) [a, b] ps" |
"extract_ptr (USum _ a _) \<sigma> ps = extract_ptr a \<sigma> ps" | 
"extract_ptr (URecord fs) \<sigma> ps = fold (\<lambda>x ps. extract_ptr x \<sigma> ps) (map prod.fst fs) ps" |
"extract_ptr (UPtr p _) \<sigma> ps = 
  (if p \<in> ps \<or> p > max_word then ps 
  else (case \<sigma> p of option.Some x \<Rightarrow> extract_ptr x \<sigma> (insert p ps)
                    | _ \<Rightarrow> ps))"
  by pat_completeness auto
termination
  oops
*)


end (* of context *)

end
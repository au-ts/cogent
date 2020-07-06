(*
  This file contains the provable assumptions which are required when proving correspondence of
  word array functions.
*)
theory WordArray_CorresProof_Asm
  imports WordArray_Abstractions
begin

context WordArray begin

section "Monomorphising Functions Assumption"

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
    apply (clarsimp simp: wordarray_get_0_type_def abbreviatedType6_def val_wa_get_0_def)
    apply (rule val.v_t_prim[where l = "(LU32 _)", simplified])
   apply (clarsimp simp: wordarray_length_0_type_def val_wa_length_0_def)
   apply (rule val.v_t_prim[where l = "(LU32 _)", simplified])
  apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType5_def val_wa_put2_0_def)
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

lemma proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>:
  "proc_env_u_v_matches \<xi>0 \<xi>m \<Xi>"
  apply (clarsimp simp: proc_env_u_v_matches_def)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
    apply (clarsimp simp: upd_wa_get_0_def wordarray_get_0_type_def abbreviatedType6_def)
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
  apply (clarsimp simp: upd_wa_put2_0_def wordarray_put2_0_type_def abbreviatedType5_def)
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
   apply (clarsimp simp: frame_def)
   apply (rule conjI; clarsimp)
    apply (rule conjI)
     apply (clarsimp simp: abs_upd_val'_def abs_typing_u_def)
    apply (rule conjI; clarsimp)
    apply (clarsimp simp: abs_upd_val'_def abs_typing_u_def)
   apply (rule conjI; clarsimp)
  apply (clarsimp simp: abs_upd_val'_def)
  apply (case_tac a; clarsimp simp: abs_typing_u_def)
  apply (case_tac a'; clarsimp)
  apply (rule_tac x = "VAbstract (VWA (x1[unat idx := VPrim (LU32 val)]))" in exI)
  apply (clarsimp simp: val_wa_put2_0_def)
  done

lemma upd_proc_env_matches_ptrs_\<xi>0_\<Xi>:
  "upd.proc_env_matches_ptrs \<xi>0 \<Xi>"
  apply (unfold upd.proc_env_matches_ptrs_def)
  apply clarsimp
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
    apply (clarsimp simp: wordarray_get_0_type_def abbreviatedType6_def upd_wa_get_0_def)
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
   apply (clarsimp simp: wordarray_length_0_type_def upd_wa_length_0_def)
   apply (erule upd.u_t_p_absE; clarsimp)
   apply (rule_tac x = "{}" in exI)+
   apply (clarsimp simp: frame_def intro!: upd.u_t_prim[where l = "(LU32 _)", simplified])
  apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType5_def upd_wa_put2_0_def)
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
     apply (rule disjI2)
     apply (rule disjI2)
     apply (rule_tac x = idx in exI; simp)
    apply (rule conjI; clarsimp)
   apply (rule conjI; clarsimp)
  apply (clarsimp simp: abs_typing_u_def)
  done

lemma proc_ctx_wellformed_\<Xi>:
  "proc_ctx_wellformed \<Xi>"
  apply (clarsimp simp: proc_ctx_wellformed_def \<Xi>_def)
  apply (clarsimp split: if_splits
                  simp: assoc_lookup.simps
                        wordarray_get_0_type_def abbreviatedType6_def wordarray_get_u32_type_def
                        wordarray_length_0_type_def wordarray_length_u32_type_def
                        wordarray_put2_0_type_def abbreviatedType5_def wordarray_put2_u32_type_def
                        wordarray_fold_no_break_0_type_def abbreviatedType1_def
                        wordarray_map_no_break_0_type_def abbreviatedType4_def abbreviatedType3_def abbreviatedType2_def
                        dec_type_def dec_arr_type_def
                        inc_type_def inc_arr_type_def
                        sum_type_def sum_arr_type_def
                        mul_type_def mul_arr_type_def)
  done

end (* of context *)

end
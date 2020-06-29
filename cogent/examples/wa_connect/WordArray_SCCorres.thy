(*
  This file contains all the Isabelle shallow embedding to C correspondence theorems for word
  array functions.
*)
theory WordArray_SCCorres
  imports WordArray_Abstractions
begin

context WordArray begin
section "Correspondence From Isabelle Shallow Embedding to C"

theorem shallow_C_wordarray_put2_corres:
"\<lbrakk>\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_put2_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_put2_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_put2_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st;
 value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m \<xi>p;
 vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
 value_sem.proc_env_matches abs_typing_v \<xi>m \<Xi>;
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.wordarray_put2_u32 vv\<^sub>s) Generated_TypeProof.wordarray_put2_u32
     (main_pp_inferred.wordarray_put2_u32' uv\<^sub>C) \<xi>0 \<xi>m \<xi>p [uv\<^sub>m] [vv\<^sub>m] \<Xi>
     [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))] \<sigma> s"
  apply clarsimp
  apply (frule val_rel_shallow_C_elim(1))
  apply (clarsimp simp: valRel_WordArrayPutP valRel_WordArrayU32)
  apply (drule_tac x = 0 in meta_spec)
  apply (drule_tac x = "[uv\<^sub>m]" in meta_spec)
  apply (drule_tac x = uv\<^sub>C in meta_spec)
  apply (drule_tac x = "[option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]" in meta_spec)
  apply (drule_tac x = \<sigma> in meta_spec)
  apply (drule_tac x = s in meta_spec)
  apply (clarsimp simp: corres_shallow_C_def)
  apply (monad_eq simp: wordarray_put2_u32'_def)
  apply (drule meta_mp)
   apply (drule val_rel_shallow_C_elim(3); simp)
  apply (drule meta_mp)
   apply (subst \<Xi>_def; subst wordarray_put2_u32_type_def; subst wordarray_put2_0_type_def; clarsimp)
  apply (clarsimp simp: corres_def)
  apply (erule impE)
   apply (rule_tac x = r in exI)
   apply (rule_tac x = x in exI)
   apply (frule u_v_matches_to_matches_ptrs)
   apply (clarsimp simp: \<Xi>_def wordarray_put2_u32_type_def wordarray_put2_0_type_def)
  apply clarsimp
  apply (erule_tac x = r' in allE)
  apply (erule_tac x = s' in allE)
  apply clarsimp
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = ra in exI)
  apply (clarsimp simp: Generated_TypeProof.wordarray_put2_u32_def)
  apply (rule conjI)
   apply (rule_tac \<sigma>' = \<sigma> and a' = uv\<^sub>m in u_sem_let)
    apply (rule u_sem_var[where i = 0 and \<gamma> = "[_]", simplified])
   apply (rule u_sem_abs_app)
     apply (rule u_sem_afun)
    apply (rule u_sem_var)
   apply (erule u_sem_appE; clarsimp)
    apply (erule u_sem_afunE; clarsimp)
    apply (erule u_sem_varE; clarsimp)
   apply (erule u_sem_afunE; clarsimp)
  apply (rule_tac x = "VAbstract (VWA (xs[unat (WordArrayPutP.idx\<^sub>f vv\<^sub>s) := VPrim (LU32 (WordArrayPutP.val\<^sub>f vv\<^sub>s))]))" in exI)
  apply clarsimp
  apply (rule conjI)
   apply (rule v_sem_let)
    apply (rule v_sem_var)
   apply (rule v_sem_abs_app)
     apply (rule v_sem_afun)
    apply (rule v_sem_var)
   apply (clarsimp simp: val_wa_put2_0_def)
  apply (clarsimp simp: Generated_Shallow_Desugar.wordarray_put2_u32_def wordarray_put2')
  apply (subst val_rel_shallow_C_def)
  apply (clarsimp simp: valRel_WordArrayPutP valRel_WordArrayU32)
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x = i in allE)
   apply clarsimp
   apply (case_tac "i = unat (WordArrayPutP.idx\<^sub>f vv\<^sub>s)"; clarsimp)
  apply (frule_tac i = 0 and 
                   \<tau> = "(prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))" 
                       in u_v_matches_proj_single'; simp)
  apply clarsimp
  apply (frule val_rel_shallow_C_elim(3); clarsimp simp: val_rel_simp)
  apply (erule u_v_recE)
  apply (erule u_v_r_consE; clarsimp simp: Generated_TypeProof.wordarray_put2_u32_type_def abbreviatedType5_def)
  apply (erule u_v_r_consE; clarsimp)+
  apply (erule u_v_r_emptyE; clarsimp)
  apply (erule u_v_primE)+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (erule u_v_p_absE; clarsimp)
  apply (erule u_sem_appE; erule u_sem_afunE; clarsimp)
  apply (erule u_sem_varE; clarsimp)
  apply (rule_tac x = "TCon ''WordArray'' [TPrim (Num U32)] (Boxed Writable undefined)" in exI)
  apply (rule_tac x = ra in exI)
  apply (rule_tac x = "insert (ptr_val (t2_C.arr_C uv\<^sub>C)) wa" in exI)
  apply (clarsimp simp: upd_wa_put2_0_def)
  apply (rule_tac ptrl = undefined and a = a in u_v_p_abs_w[where ts = "[TPrim (Num U32)]", simplified])
     apply simp
    apply (clarsimp simp: abs_upd_val'_def)
    apply (case_tac a; clarsimp)
    apply (rule conjI)
     apply (clarsimp simp: abs_typing_u_def)
    apply (rule conjI)
     apply (clarsimp simp: abs_typing_v_def)
     apply (erule_tac x = i in allE)
     apply clarsimp
     apply (case_tac "i = unat (t2_C.idx_C uv\<^sub>C)"; clarsimp)
    apply clarsimp
    apply (rule conjI; clarsimp)
     apply (drule distinct_indices)
     apply (erule_tac x = i in allE)+
     apply clarsimp
     apply (erule_tac x = "t2_C.idx_C uv\<^sub>C" in allE)
     apply (clarsimp simp: word_less_nat_alt)
    apply (erule_tac x = i in allE)
    apply clarsimp
    apply (case_tac "unat i = unat (t2_C.idx_C uv\<^sub>C)"; clarsimp)
   apply (clarsimp simp: abs_upd_val'_def)
   apply (erule_tac x = " idx_C uv\<^sub>C" in allE)
   apply clarsimp
  apply clarsimp
  done



theorem shallow_C_wordarray_length_corres:
"\<lbrakk>\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_length_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_length_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st;
 value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m \<xi>p;
 vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
 value_sem.proc_env_matches abs_typing_v \<xi>m \<Xi>;
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_length_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.wordarray_length_u32 vv\<^sub>s) Generated_TypeProof.wordarray_length_u32
     (main_pp_inferred.wordarray_length_u32' uv\<^sub>C) \<xi>0 \<xi>m \<xi>p [uv\<^sub>m] [vv\<^sub>m] \<Xi>
     [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_length_u32_type))] \<sigma> s"
  apply clarsimp
  apply (drule_tac x = 0 in meta_spec)
  apply (drule_tac x = "[uv\<^sub>m]" in meta_spec)
  apply (drule_tac x = uv\<^sub>C in meta_spec)
  apply (drule_tac x = "[option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_length_u32_type))]" in meta_spec)
  apply (drule_tac x = \<sigma> in meta_spec)
  apply (drule_tac x = s in meta_spec)
  apply (clarsimp simp:  corres_shallow_C_def)
  apply (monad_eq simp: wordarray_length_u32'_def)
  apply (drule meta_mp)
   apply (drule val_rel_shallow_C_elim(3); simp)
  apply (drule meta_mp)
   apply (subst \<Xi>_def; subst wordarray_length_u32_type_def; subst wordarray_length_0_type_def; simp)
  apply (clarsimp simp: corres_def)
  apply (erule impE)
   apply (rule_tac x = r in exI)
   apply (rule_tac x = x in exI)
   apply (frule u_v_matches_to_matches_ptrs)
   apply (clarsimp simp: \<Xi>_def wordarray_length_u32_type_def wordarray_length_0_type_def)
  apply clarsimp
  apply (erule_tac x = r' in allE)
  apply (erule_tac x = s' in allE)
  apply clarsimp
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = ra in exI)
  apply (clarsimp simp: Generated_TypeProof.wordarray_length_u32_def)
  apply (rule conjI)
   apply (rule_tac \<sigma>' = \<sigma> and a' = uv\<^sub>m in u_sem_let)
    apply (rule u_sem_var[where i = 0 and \<gamma> = "[_]", simplified])
   apply (rule u_sem_abs_app)
     apply (rule u_sem_afun)
    apply (rule u_sem_var)
   apply (erule u_sem_appE; clarsimp)
    apply (erule u_sem_afunE; clarsimp)
    apply (erule u_sem_varE; clarsimp)
   apply (erule u_sem_afunE; clarsimp)
  apply (monad_eq simp: wordarray_length_0'_def val_rel_simp)
  apply (rule_tac x = "VPrim (LU32 (SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C s uv\<^sub>C))))" in exI)
  apply (frule_tac i = 0 and 
                   \<tau> = "(prod.fst (prod.snd Generated_TypeProof.wordarray_length_u32_type))" 
                       in u_v_matches_proj_single'; simp)
  apply (clarsimp simp: Generated_TypeProof.wordarray_length_u32_type_def)
  apply (frule val_rel_shallow_C_elim(1); clarsimp simp: valRel_WordArrayU32)
  apply (frule val_rel_shallow_C_elim(3); clarsimp simp: val_rel_simp)
  apply (erule u_v_p_absE; clarsimp)
  apply (clarsimp simp: abs_upd_val'_def)
  apply (case_tac a; clarsimp)
  apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta)
  apply (drule_tac p =  uv\<^sub>C and 
                  uv = "UAbstract (WAU32 x11 x12)" in all_heap_rel_ptrD; 
         clarsimp simp: is_valid_simp heap_simp abs_repr_u_def type_rel_simp val_rel_simp)
  apply (rule conjI)
   apply (rule v_sem_let)
    apply (rule v_sem_var)
   apply (rule v_sem_abs_app)
     apply (rule v_sem_afun)
    apply (rule v_sem_var)
   apply (clarsimp simp: val_wa_length_0_def)
  apply (subst val_rel_shallow_C_def)
  apply (rule_tac x = "TPrim (Num U32)" in exI)
  apply (rule_tac x = "{}" in exI)+
  apply (clarsimp simp: Generated_Shallow_Desugar.wordarray_length_u32_def wordarray_length')
  apply (rule conjI)
   apply (metis word_unat.Rep_inverse)
  apply (rule conjI)
   apply (rule u_v_prim[where l = "LU32 _", simplified])
  apply (clarsimp simp: val_rel_simp)
  done


theorem shallow_C_wordarray_get_corres:
"\<lbrakk>\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_get_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_get_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_get_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st;
 value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m \<xi>p; vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
 value_sem.proc_env_matches abs_typing_v \<xi>m \<Xi>;
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_get_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.wordarray_get_u32 vv\<^sub>s) Generated_TypeProof.wordarray_get_u32
     (main_pp_inferred.wordarray_get_u32' uv\<^sub>C) \<xi>0 \<xi>m \<xi>p [uv\<^sub>m] [vv\<^sub>m] \<Xi>
     [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_get_u32_type))] \<sigma> s"
  apply clarsimp
  apply (frule val_rel_shallow_C_elim(1))
  apply (clarsimp simp: valRel_RR valRel_WordArrayU32)
  apply (drule_tac x = 0 in meta_spec)
  apply (drule_tac x = "[uv\<^sub>m]" in meta_spec)
  apply (drule_tac x = uv\<^sub>C in meta_spec)
  apply (drule_tac x = "[option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_get_u32_type))]" in meta_spec)
  apply (drule_tac x = \<sigma> in meta_spec)
  apply (drule_tac x = s in meta_spec)
  apply (clarsimp simp:  corres_shallow_C_def)
  apply (monad_eq simp: wordarray_get_u32'_def)
  apply (drule meta_mp)
   apply (drule val_rel_shallow_C_elim(3); simp)
  apply (drule meta_mp)
   apply (subst \<Xi>_def; subst wordarray_get_u32_type_def; subst wordarray_get_0_type_def; clarsimp)
  apply (clarsimp simp: corres_def)
  apply (erule impE)
   apply (rule_tac x = r in exI)
   apply (rule_tac x = x in exI)
   apply (frule u_v_matches_to_matches_ptrs)
   apply (clarsimp simp: \<Xi>_def wordarray_get_u32_type_def wordarray_get_0_type_def)
  apply clarsimp
  apply (erule_tac x = r' in allE)
  apply (erule_tac x = s' in allE)
  apply clarsimp
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = ra in exI)
  apply (clarsimp simp: Generated_TypeProof.wordarray_get_u32_def)
  apply (rule conjI)
   apply (rule_tac \<sigma>' = \<sigma> and a' = uv\<^sub>m in u_sem_let)
    apply (rule u_sem_var[where i = 0 and \<gamma> = "[_]", simplified])
   apply (rule u_sem_abs_app)
     apply (rule u_sem_afun)
    apply (rule u_sem_var)
   apply (erule u_sem_appE; clarsimp)
    apply (erule u_sem_afunE; clarsimp)
    apply (erule u_sem_varE; clarsimp)
   apply (erule u_sem_afunE; clarsimp)
  apply (rule_tac x = "VPrim (LU32 r')" in exI)
  apply (frule_tac i = 0 and 
                   \<tau> = "(prod.fst (prod.snd Generated_TypeProof.wordarray_get_u32_type))" 
                       in u_v_matches_proj_single'; simp)
  apply clarsimp
  apply (frule val_rel_shallow_C_elim(3))
  apply (clarsimp simp: val_rel_simp wordarray_get_u32_type_def abbreviatedType6_def)
  apply (erule u_v_recE)
  apply (erule u_v_r_consE; clarsimp)+
  apply (erule u_v_r_emptyE)
  apply (erule u_v_primE)
  apply (subst (asm) lit_type.simps; simp)
  apply (erule u_v_p_absE; clarsimp)
  apply (erule u_sem_appE; erule u_sem_afunE; clarsimp)
  apply (erule u_sem_varE; clarsimp simp: upd_wa_get_0_def)
  apply (simp add: word_less_nat_alt)
  apply (rule conjI)
   apply (rule v_sem_let)
    apply (rule v_sem_var)
   apply (rule v_sem_abs_app)
     apply (rule v_sem_afun)
    apply (rule v_sem_var)
   apply (clarsimp simp: val_wa_get_0_def abs_upd_val'_def)
  apply (erule_tac x = "t1_C.p2_C uv\<^sub>C" in allE; clarsimp simp: word_less_nat_alt)
  apply (subst val_rel_shallow_C_def)
  apply (rule_tac x = "TPrim (Num U32)" in exI)
  apply (rule_tac x = "{}" in exI)+
  apply (clarsimp simp: Generated_Shallow_Desugar.wordarray_get_u32_def wordarray_get' abs_upd_val'_def word_less_nat_alt)
  apply (erule_tac x = "unat (t1_C.p2_C uv\<^sub>C)" in allE)
  apply (force simp: val_rel_simp intro!: u_v_prim[where l = "LU32 _", simplified])
  done

theorem
"\<lbrakk>\<And>i \<gamma> v' \<Gamma>' \<sigma>' st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_length_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_length_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi>  \<Gamma>' \<sigma>' st;
 \<And>v' i \<gamma> \<Gamma> \<sigma> s.
    \<lbrakk>t5_C.f_C v' = FUN_ENUM_sum; i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma> ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_fold_no_break_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u)
         (App (AFun ''wordarray_fold_no_break_0'' []) (Var i)) (do x <- main_pp_inferred.wordarray_fold_no_break_0' v';
gets (\<lambda>s. x)
                                                                od)
         \<xi>0 \<gamma> \<Xi>  \<Gamma> \<sigma> s;
 value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m \<xi>p;
 vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
 value_sem.proc_env_matches abs_typing_v \<xi>m \<Xi>;
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.sum_arr_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.sum_arr vv\<^sub>s) Generated_TypeProof.sum_arr (main_pp_inferred.sum_arr' uv\<^sub>C) \<xi>0 \<xi>m \<xi>p
     [uv\<^sub>m] [vv\<^sub>m] \<Xi> [option.Some (prod.fst (prod.snd Generated_TypeProof.sum_arr_type))] \<sigma> s"
  apply (monad_eq simp: sum_arr'_def  corres_shallow_C_def)
  apply (frule val_rel_shallow_C_elim(1))
  
  oops
end (* of context *)
end
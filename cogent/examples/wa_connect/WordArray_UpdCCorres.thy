(*
  This file contains the update semantics to C correspondence lemmas for word array functions
*)
theory WordArray_UpdCCorres
  imports WordArray_Abstractions
begin

context WordArray begin
(*
abbreviation "w_val h w \<equiv> values_C (h w)"
abbreviation "w_len h w \<equiv> SCAST(32 signed \<rightarrow> 32) (len_C (h w))"

abbreviation "w_p s w \<equiv> w_val (heap_WordArray_u32_C s) w"
abbreviation "w_l s w \<equiv> w_len (heap_WordArray_u32_C s) w"

section "Helper Lemma for Word Array Existence and Validity"
 
definition valid_c_wordarray
  where
  "valid_c_wordarray s w \<equiv> is_valid_WordArray_u32_C s w \<and> 
                            (\<forall>i < w_l s w. is_valid_w32 s ((w_p s w) +\<^sub>p uint i)) "

definition valid_cogent_wordarray
  where
  "valid_cogent_wordarray \<sigma> s w \<equiv> (\<exists>len arr. len = w_l s w \<and> arr = ptr_val (w_p s w) \<and> 
                                    \<sigma> (ptr_val w) = option.Some (UAbstract (WAU32 len arr)) \<and> 
                                   (\<forall>i < len. \<sigma> (arr + 4 * i) = option.Some (UPrim (LU32 (heap_w32 s ((w_p s w) +\<^sub>p uint i))))))"

definition valid_wordarray
  where
  "valid_wordarray \<sigma> s w \<equiv> valid_c_wordarray s w \<and> valid_cogent_wordarray \<sigma> s w"


lemma well_typed_related_wordarray: "\<And>\<sigma> st x x' a ts s r w.
       \<lbrakk>(\<sigma>, st) \<in> state_rel; val_rel x (x':: WordArray_u32_C ptr); abs_typing_u a ts\<rbrakk>
       \<Longrightarrow> valid_wordarray \<sigma> st x'"
  apply (unfold valid_wordarray_def valid_c_wordarray_def valid_cogent_wordarray_def)
  apply (clarsimp simp: val_rel_simp)
  apply (erule u_t_recE)
  apply (erule u_t_r_consE; clarsimp simp: \<Xi>_def wordarray_put2_0_type_def abbreviatedType1_def)
  apply (erule u_t_p_absE; clarsimp)
  apply (clarsimp simp: abs_typing'_def)
  apply (case_tac a; clarsimp)
  apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta heap_rel_ptr_w32_meta)
  apply (drule_tac p = "arr_C x'" and uv = "UAbstract (WAU32 x11 x12)" in all_heap_rel_ptrD; 
         clarsimp simp: type_rel_simp abs_repr'_def val_rel_simp is_valid_simp heap_simp)
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x = i in allE)
   apply (erule_tac x = i in allE)
   apply clarsimp
   apply (drule_tac uv = "UPrim (LU32 x)" and 
                     p = "values_C (heap_WordArray_u32_C st (arr_C x')) +\<^sub>p uint i"
                     in all_heap_rel_ptrD;
          clarsimp simp: ptr_add_def mult.commute type_rel_simp)
  apply clarsimp
  apply (erule_tac x = i in allE)
  apply (erule_tac x = i in allE)
  apply clarsimp
  apply (drule_tac uv = "UPrim (LU32 x)" and 
                    p = "values_C (heap_WordArray_u32_C st (arr_C x')) +\<^sub>p uint i"
                    in all_heap_rel_ptrD;
         clarsimp simp: ptr_add_def mult.commute type_rel_simp val_rel_simp)
  done
*)
section "Correspondence Lemmas Between Update Semantics and C"

lemma upd_C_wordarray_put2_corres:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_put2_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_put2_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_put2_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (rule afun_corres; simp)
  apply (thin_tac "i < length \<gamma>")
  apply (thin_tac "val_rel (\<gamma> ! i) v'")
  apply (thin_tac "\<Gamma>' ! i = _")
  apply (clarsimp simp: abs_rel_def; rename_tac r w)
  apply (clarsimp simp: val_rel_simp \<Xi>_def wordarray_put2_0_type_def abbreviatedType5_def)
  apply (erule upd.u_t_recE)
  apply (erule upd.u_t_r_consE; clarsimp)+
  apply (erule upd.u_t_primE)+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (erule upd.u_t_r_emptyE)
  apply (erule upd.u_t_p_absE; clarsimp simp: abs_typing_u_def)
  apply (case_tac a; clarsimp)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_put2_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def)
   apply (erule_tac x = "t2_C.arr_C x'" in allE)
   apply (erule_tac x = "values_C (heap_WordArray_u32_C st (t2_C.arr_C x')) +\<^sub>p uint (t2_C.idx_C x')" in allE)
   apply (clarsimp simp: heap_rel_ptr_def heap_rel_ptr_w32_def abs_repr_u_def is_valid_simp type_rel_simp)
   apply (erule_tac x = "t2_C.idx_C x'" in allE)+
   apply (clarsimp simp: val_rel_simp heap_simp type_rel_simp)
  apply clarsimp
  apply (rule_tac x = "\<lambda>l. (if \<exists>len arr. (\<sigma> \<circ> ptr_val \<circ> t2_C.arr_C) x' = option.Some (UAbstract (WAU32 len arr)) \<and> 
                                l = arr + 4 * t2_C.idx_C x' \<and> t2_C.idx_C x' < len 
                            then option.Some (UPrim (LU32 (t2_C.val_C x'))) 
                            else \<sigma> l)" in exI)
  apply (rule_tac x = "UPtr (ptr_val y') (RCon ''WordArray'' [RPrim (Num U32)])" in exI)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_put2_0'_def upd_wa_put2_0_def)
  apply (rule conjI)
   apply (rule_tac x = "RCon ''WordArray'' [RPrim (Num U32)]" in exI, simp)
  apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta heap_rel_ptr_w32_meta)
  apply (rule conjI)
   apply (clarsimp simp: heap_rel_meta_def)
   apply (rule conjI; clarsimp)
    apply (clarsimp simp: type_rel_simp)
   apply (monad_eq simp: wordarray_put2_0'_def)
   apply (case_tac "idx_C x' < SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C st (t2_C.arr_C x')))"; 
          drule_tac p = x and uv = uv in all_heap_rel_ptrD; clarsimp simp: is_valid_simp heap_simp)
  apply (erule_tac x = "t2_C.arr_C x'" in allE)
  apply (clarsimp simp: heap_rel_meta_def abs_repr_u_def type_rel_simp val_rel_simp)
  apply (monad_eq simp: wordarray_put2_0'_def heap_simp is_valid_simp)
  apply (rule conjI; clarsimp)
   apply (drule_tac p = "values_C (heap_WordArray_u32_C st (t2_C.arr_C x')) +\<^sub>p uint (t2_C.idx_C x')" and 
                   uv = uv in all_heap_rel_ptrD; clarsimp simp: type_rel_simp val_rel_simp)
  apply (rule conjI)
   apply (clarsimp simp: ptr_add_def)
   apply (metis Ptr_ptr_val mult.commute)
  apply clarsimp
  apply (case_tac "idx_C x' < SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C st (t2_C.arr_C x')))";
         drule_tac p = x and uv = uv in all_heap_rel_ptrD; clarsimp simp: type_rel_simp val_rel_simp)
  done


lemma upd_C_wordarray_length_corres:
"\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_length_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_length_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (rule afun_corres; simp)
  apply (clarsimp simp: abs_rel_def; rename_tac r w)
  apply (thin_tac "i < length \<gamma>")
  apply (thin_tac "val_rel (\<gamma> ! i) v'")
  apply (thin_tac "\<Gamma>' ! i = _")
  apply (clarsimp simp: val_rel_simp \<Xi>_def wordarray_length_0_type_def)
  apply (erule upd.u_t_p_absE; clarsimp simp: abs_typing_u_def)
  apply (case_tac a; clarsimp)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_length_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def)
   apply (erule_tac x = x' in allE)
   apply (clarsimp simp: heap_rel_ptr_def type_rel_simp abs_repr_u_def is_valid_simp)
  apply clarsimp
  apply (rule_tac x = \<sigma> in exI)
  apply (rule conjI)
   apply (clarsimp simp: upd_wa_length_0_def)
   apply (monad_eq simp: wordarray_length_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def)
   apply (erule_tac x = x' in allE)
   apply (clarsimp simp: heap_rel_ptr_def type_rel_simp abs_repr_u_def heap_simp val_rel_simp)
  apply (monad_eq simp: wordarray_length_0'_def)
  done


lemma upd_C_wordarray_get_corres:
"\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_get_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_get_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_get_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (rule afun_corres; simp)
  apply (clarsimp simp: abs_rel_def; rename_tac r w)
  apply (thin_tac "i < length \<gamma>")
  apply (thin_tac "val_rel (\<gamma> ! i) v'")
  apply (thin_tac "\<Gamma>' ! i = _")
  apply (clarsimp simp: val_rel_simp \<Xi>_def wordarray_get_0_type_def abbreviatedType6_def)
  apply (erule upd.u_t_recE)
  apply (erule upd.u_t_r_consE; clarsimp)+
  apply (erule upd.u_t_r_emptyE)
  apply (erule upd.u_t_primE; subst (asm) lit_type.simps; clarsimp)
  apply (erule upd.u_t_p_absE; clarsimp simp: abs_typing_u_def)
  apply (case_tac a; clarsimp)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_get_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta heap_rel_ptr_w32_meta)
   apply (drule_tac p = "t1_C.p1_C x'" and uv = "UAbstract (WAU32 x11 x12)" in all_heap_rel_ptrD; 
          clarsimp simp: type_rel_simp abs_repr_u_def val_rel_simp is_valid_simp heap_simp)
   apply (drule not_le_imp_less)
   apply (erule_tac x = "t1_C.p2_C x'" in allE; clarsimp)
   apply (drule_tac p = "values_C (heap_WordArray_u32_C st (t1_C.p1_C x')) +\<^sub>p uint (t1_C.p2_C x')" and
                   uv = "UPrim (LU32 x)" in all_heap_rel_ptrD; simp add: type_rel_simp)
  apply clarsimp
  apply (rule_tac x = \<sigma> in exI)
  apply (rule conjI)
   apply (clarsimp simp: upd_wa_get_0_def)
   apply (erule_tac x = "t1_C.p2_C x'" in allE)
   apply (monad_eq simp: wordarray_get_0'_def word_less_nat_alt word_le_nat_alt)
   apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta heap_rel_ptr_w32_meta)
   apply (drule_tac p = "t1_C.p1_C x'" and uv = "UAbstract (WAU32 x11 x12)" in all_heap_rel_ptrD; 
          clarsimp simp: type_rel_simp abs_repr_u_def val_rel_simp is_valid_simp heap_simp)
   apply (drule_tac p = "values_C (heap_WordArray_u32_C st (t1_C.p1_C x')) +\<^sub>p uint (t1_C.p2_C x')" and
                   uv = "UPrim (LU32 x)" in all_heap_rel_ptrD;
          clarsimp simp: type_rel_simp val_rel_simp)
  apply (monad_eq simp: wordarray_get_0'_def)
  apply blast
  done

lemma
" \<And>v' i \<gamma> \<Gamma>' \<sigma> s.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_map_no_break_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u)
         (App (AFun ''wordarray_map_no_break_0'' []) (Var i)) (do x <- main_pp_inferred.wordarray_map_no_break_0' v';
gets (\<lambda>s. x)
                                                                od)
         \<xi>1 \<gamma> \<Xi>  \<Gamma>' \<sigma> s"
  apply (rule afun_corres; clarsimp)
  apply (clarsimp simp: abs_rel_def)
  apply (thin_tac "i < length \<gamma>")
  apply (thin_tac "val_rel (\<gamma> ! i) v'")
  apply (thin_tac "\<Gamma>' ! i = _")
  apply clarsimp
  apply (clarsimp simp: val_rel_simp)
  oops


lemma
" \<And>v' i \<gamma> \<Gamma>' \<sigma> s.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_fold_no_break_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u)
         (App (AFun ''wordarray_fold_no_break_0'' []) (Var i)) (do x <- main_pp_inferred.wordarray_fold_no_break_0' v';
gets (\<lambda>s. x)
                                                                od)
         \<xi>1 \<gamma> \<Xi>  \<Gamma>' \<sigma> s"
  apply (rule afun_corres; clarsimp)
  apply (clarsimp simp: abs_rel_def')
  apply (thin_tac "i < length \<gamma>")
  apply (thin_tac "val_rel (\<gamma> ! i) v'")
  apply (thin_tac "\<Gamma>' ! i = _")
  apply clarsimp
  apply (clarsimp simp: val_rel_simp)
  apply (erule upd.u_t_recE)
  apply (clarsimp simp: \<Xi>_def wordarray_fold_no_break_0_type_def abbreviatedType1_def)
  apply (erule upd.u_t_r_consE; clarsimp)+
  apply (erule upd.u_t_primE; subst (asm) lit_type.simps; clarsimp)+
  apply (erule upd.u_t_r_emptyE)
  apply (erule upd.u_t_unitE)
  apply (case_tac "sint (t5_C.f_C x') \<noteq> sint FUN_ENUM_mul \<and> sint (t5_C.f_C x') \<noteq> sint FUN_ENUM_sum")
   apply (clarsimp simp: cogent_function_val_rel
                         FUN_ENUM_sum_def
                         FUN_ENUM_dec_def
                         FUN_ENUM_inc_def
                         FUN_ENUM_mul_def
                         FUN_ENUM_dec_arr_def
                         FUN_ENUM_inc_arr_def
                         FUN_ENUM_mul_arr_def
                         FUN_ENUM_sum_arr_def
                         FUN_ENUM_wordarray_get_0_def
                         FUN_ENUM_wordarray_length_0_def
                         FUN_ENUM_wordarray_put2_0_def
                         FUN_ENUM_wordarray_fold_no_break_0_def
                         FUN_ENUM_wordarray_map_no_break_0_def
                         FUN_ENUM_wordarray_get_u32_def
                         FUN_ENUM_wordarray_length_u32_def
                         FUN_ENUM_wordarray_put2_u32_def)
   apply (rule FalseE) 
   apply (thin_tac "_ \<in> state_rel")
   apply (thin_tac "sint (t5_C.f_C x') \<noteq> 4")
   apply (thin_tac "sint (t5_C.f_C x') \<noteq> 6")
   apply (thin_tac "upd.uval_typing _ _ (UPtr _ _) _ _ _")
   apply (thin_tac "_ = _")+
   apply clarsimp
   apply (erule disjE)
    apply clarsimp
    apply (erule upd.u_t_funE')
    apply (clarsimp simp: dec_def)
    apply (clarsimp simp: subtyping_simps(4) 
                          subtyping.simps[of _ _ "TPrim (Num U32)", simplified]
                          subtyping.simps[of _ "TRecord _ _ ", simplified]
                          subtyping.simps[of _ "TPrim (Num U32)", simplified]
                          subtyping.simps[of _ "TUnit", simplified]
                          kinding_simps(5, 9))
    apply (erule typing_takeE)+
    apply (erule typing_letE)+
    apply (erule typing_structE)
    apply clarsimp
   apply (erule disjE)
    apply clarsimp
    apply (erule upd.u_t_funE')
    apply (clarsimp simp: inc_def)
    apply (clarsimp simp: subtyping_simps(4) 
                          subtyping.simps[of _ _ "TPrim (Num U32)", simplified]
                          subtyping.simps[of _ "TRecord _ _ ", simplified]
                          subtyping.simps[of _ "TPrim (Num U32)", simplified]
                          subtyping.simps[of _ "TUnit", simplified]
                          kinding_simps(5, 9))
    apply (erule typing_takeE)+
    apply (erule typing_letE)+
    apply (erule typing_structE)
    apply clarsimp
   apply (erule disjE)
    apply clarsimp
    apply (erule upd.u_t_funE')     
    apply (clarsimp simp: dec_arr_def)
    apply (clarsimp simp: subtyping_simps(4) 
                          subtyping.simps[of _ _ "TPrim (Num U32)", simplified]
                          subtyping.simps[of _ "TRecord _ _ ", simplified]
                          subtyping.simps[of _ "TPrim (Num U32)", simplified]
                          subtyping.simps[of _ "TUnit", simplified]
                          kinding_simps(5, 9))     
    apply (erule typing_letE)
    apply (erule typing_letbE)
    apply (erule typing_letE)+
    apply (erule typing_appE)+
    apply (erule typing_afunE)+
    apply (thin_tac "_, _, _ \<turnstile> _ : _")+
    apply (clarsimp simp: wordarray_map_no_break_0_type_def abbreviatedType2_def)
   apply (erule disjE)
    apply clarsimp
    apply (erule upd.u_t_funE')
    apply (clarsimp simp: inc_arr_def)
    apply (clarsimp simp: subtyping_simps(4) 
                          subtyping.simps[of _ _ "TPrim (Num U32)", simplified]
                          subtyping.simps[of _ "TRecord _ _ ", simplified]
                          subtyping.simps[of _ "TPrim (Num U32)", simplified]
                          subtyping.simps[of _ "TUnit", simplified]
                          kinding_simps(5, 9)) 
    apply (erule typing_letE)
    apply (erule typing_letbE)
    apply (erule typing_letE)+
    apply (erule typing_appE)+
    apply (erule typing_afunE)+
    apply (thin_tac "_, _, _ \<turnstile> _ : _")+
    apply (clarsimp simp: wordarray_map_no_break_0_type_def abbreviatedType2_def)
   apply (erule disjE)
    prefer 2
    apply (erule disjE)
     prefer 2
     apply (erule disjE)
      apply clarsimp
      apply (erule upd.u_t_afunE; clarsimp)
      apply (clarsimp simp: subtyping_simps(4) 
                            subtyping.simps[of _ _ "TPrim (Num U32)", simplified]
                            wordarray_get_0_type_def abbreviatedType6_def
                            subtyping_simps(6))
     apply (erule disjE)
      apply clarsimp
      apply (erule upd.u_t_afunE; clarsimp)
      apply (clarsimp simp: subtyping_simps(4) 
                            subtyping.simps[of _ _ "TPrim (Num U32)", simplified]
                            wordarray_put2_0_type_def)
     apply (erule disjE)
      apply clarsimp
      apply (erule upd.u_t_funE'; clarsimp)
      apply (clarsimp simp: subtyping_simps(4)
                            subtyping.simps[of _ "TRecord _ _ ", simplified]
                            subtyping.simps[of _ _ "TPrim (Num U32)", simplified]
                            subtyping.simps[of _ "TPrim (Num U32)", simplified]
                            subtyping.simps[of _ "TUnit", simplified]
                            kinding_simps(5, 9))
      apply (clarsimp simp: wordarray_get_u32_def)
      apply (erule typing_letE)
      apply (erule typing_appE)
      apply (erule typing_afunE)
      apply (clarsimp simp: wordarray_get_0_type_def abbreviatedType6_def)
      apply (erule typing_varE)+
      apply (clarsimp simp: split_conv_all_nth weakening_conv_all_nth empty_def)
      apply (erule_tac x = 0 in allE)+
      apply (clarsimp simp: weakening_comp.simps split_comp.simps)
      apply (erule disjE; clarsimp)
     apply (erule disjE)
      apply clarsimp
      apply (erule upd.u_t_afunE; clarsimp)
      apply (clarsimp simp: subtyping_simps(4) 
                            subtyping.simps[of _ _ "TPrim (Num U32)", simplified]
                            subtyping.simps[of _ "TRecord _ _ ", simplified]
                            wordarray_length_0_type_def)
     apply (erule disjE)
      apply clarsimp
      apply (erule upd.u_t_funE'; clarsimp)
      apply (clarsimp simp: subtyping_simps(4)
                            subtyping.simps[of _ "TRecord _ _ ", simplified]
                            subtyping.simps[of _ _ "TPrim (Num U32)", simplified]
                            subtyping.simps[of _ "TPrim (Num U32)", simplified]
                            subtyping.simps[of _ "TUnit", simplified]
                            kinding_simps(5, 9))
      apply (clarsimp simp: wordarray_put2_u32_def)
      apply (erule typing_letE)
      apply (erule typing_appE)
      apply (erule typing_afunE)
      apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType5_def)
     apply (erule disjE)
      apply clarsimp
      apply (erule upd.u_t_funE'; clarsimp)
      apply (clarsimp simp: subtyping_simps(4)
                            subtyping.simps[of _ "TRecord _ _ ", simplified]
                            subtyping.simps[of _ _ "TPrim (Num U32)", simplified]
                            subtyping.simps[of _ "TPrim (Num U32)", simplified]
                            subtyping.simps[of _ "TUnit", simplified]
                            kinding_simps(5, 9))
      apply (clarsimp simp: wordarray_length_u32_def)
      apply (erule typing_letE)
      apply (erule typing_appE)
      apply (erule typing_afunE)
      apply (clarsimp simp: wordarray_length_0_type_def)
      apply (erule typing_varE)+
      apply (clarsimp simp: split_conv_all_nth weakening_conv_all_nth empty_def)
      apply (erule_tac x = 0 in allE)+
      apply (clarsimp simp: weakening_comp.simps split_comp.simps)
      apply (erule disjE; clarsimp)
     apply (erule disjE)
      apply clarsimp
      apply (erule upd.u_t_afunE; clarsimp)
      apply (clarsimp simp: subtyping_simps(4) 
                            subtyping.simps[of _ _ "TPrim (Num U32)", simplified]
                            subtyping.simps[of _ "TRecord _ _ ", simplified]
                            wordarray_map_no_break_0_type_def)
     apply clarsimp
     apply (erule upd.u_t_afunE; clarsimp)
     apply (clarsimp simp: subtyping_simps(4) 
                           subtyping.simps[of _ _ "TPrim (Num U32)", simplified]
                           subtyping.simps[of _ "TRecord _ _ ", simplified])
    apply clarsimp
    apply (erule upd.u_t_funE')
    apply (clarsimp simp: subtyping_simps(4) 
                          subtyping.simps[of _ _ "TPrim (Num U32)", simplified]
                          subtyping.simps[of _ "TRecord _ _ ", simplified]
                          subtyping.simps[of _ "TPrim (Num U32)", simplified]
                          subtyping.simps[of _ "TUnit", simplified]
                          kinding_simps(5, 9))
    apply (thin_tac "_ \<or> _")+
    apply (clarsimp simp: sum_arr_def)
    apply (erule typing_letE)
    apply (erule typing_letE)
    apply (erule typing_varE)
    apply (thin_tac "_, _, (_ #_) \<turnstile> _ : _")
    apply (erule typing_appE)
    apply (erule typing_afunE)
    apply (erule typing_varE)
    apply (clarsimp simp: split_conv_all_nth weakening_conv_all_nth empty_def wordarray_length_0_type_def)
    apply (erule_tac x= 0 in allE)+
    apply clarsimp
    apply (clarsimp simp: weakening_comp.simps split_comp.simps neq_Nil_lengthI)
    apply (erule disjE; clarsimp)+
   apply clarsimp
   apply (erule upd.u_t_funE')
   apply (clarsimp simp: subtyping_simps(4) 
                         subtyping.simps[of _ _ "TPrim (Num U32)", simplified]
                         subtyping.simps[of _ "TRecord _ _ ", simplified]
                         subtyping.simps[of _ "TPrim (Num U32)", simplified]
                         subtyping.simps[of _ "TUnit", simplified]
                         kinding_simps(5, 9))
   apply (thin_tac "_ \<or> _")+
   apply (clarsimp simp: mul_arr_def)
   apply (erule typing_letE)
   apply (erule typing_letE)
   apply (erule typing_varE)
   apply (thin_tac "_, _, (_ #_) \<turnstile> _ : _")
   apply (erule typing_appE)
   apply (erule typing_afunE)
   apply (erule typing_varE)
   apply (clarsimp simp: split_conv_all_nth weakening_conv_all_nth empty_def wordarray_length_0_type_def)
   apply (erule_tac x= 0 in allE)+
   apply clarsimp
   apply (clarsimp simp: weakening_comp.simps split_comp.simps neq_Nil_lengthI)
   apply (erule disjE; clarsimp)+
  apply clarsimp
  apply (erule upd.u_t_p_absE; clarsimp)
  apply (clarsimp simp: wordarray_fold_no_break_0'_def upd_wa_foldnb_0_def)
  apply (subst unknown_bind_ignore)+
  apply clarsimp
  apply wp 
      apply (clarsimp simp: split_def unknown_bind_ignore)
      apply (subst whileLoop_add_inv
              [where M = "\<lambda>((_, r), _). unat (t5_C.to_C x') - unat r" and 
                     I = "\<lambda>(a, b) s. 
                        (\<exists>func. cogent_function_val_rel x (sint (t5_C.f_C x')) \<and> func = x \<and>
                        (case func of
                            UFunction f ts \<Rightarrow> (\<Xi>, [], [option.Some abbreviatedType1] \<turnstile> 
                                               (App (Fun f ts) (Var 0)) : TPrim (Num U32)) \<and>
                                              upd_wa_foldnb_bod_0 \<sigma> (ptr_val (t5_C.arr_C x')) 
                                                (t5_C.frm_C x') b (Fun f ts) 
                                                (UPrim (LU32 (t5_C.acc_C x'))) 
                                                (UUnit) (\<sigma>, UPrim (LU32 (t3_C.acc_C a)))
                          | UAFunction f ts \<Rightarrow> (\<Xi>, [], [option.Some abbreviatedType1] \<turnstile> 
                                                (App (AFun f ts) (Var 0)) : TPrim (Num U32)) \<and>
                                               upd_wa_foldnb_bod_0 \<sigma> (ptr_val (t5_C.arr_C x')) 
                                                (t5_C.frm_C x') b (AFun f ts) 
                                                (UPrim (LU32 (t5_C.acc_C x'))) 
                                                (UUnit) (\<sigma>, UPrim (LU32 (t3_C.acc_C a)))
                          | _ \<Rightarrow> False)) \<and> 
                        (\<sigma>, s) \<in> state_rel \<and> t5_C.frm_C x' \<le> b \<and>
                        ret = min (t5_C.to_C x') ((SCAST(32 signed \<rightarrow> 32))(len_C (heap_WordArray_u32_C s (t5_C.arr_C x')))) \<and>
                        (t5_C.frm_C x' \<le> ret \<longrightarrow> b \<le> ret) \<and> (t5_C.frm_C x' \<ge> ret \<longrightarrow> b = t5_C.frm_C x')"])
      apply (wp; clarsimp simp: split_def unknown_bind_ignore)
           apply (clarsimp simp: split_def dispatch_t4'_def unknown_bind_ignore)
           apply wp
            apply (clarsimp simp: mul'_def unknown_bind_ignore)
            apply wp
           apply (clarsimp simp: sum'_def unknown_bind_ignore)
           apply wp
          apply wp
         apply wp
        apply wp
       apply (clarsimp simp: split_def cogent_function_val_rel
                             FUN_ENUM_sum_def
                             FUN_ENUM_dec_def
                             FUN_ENUM_inc_def
                             FUN_ENUM_mul_def
                             FUN_ENUM_dec_arr_def
                             FUN_ENUM_inc_arr_def
                             FUN_ENUM_mul_arr_def
                             FUN_ENUM_sum_arr_def
                             FUN_ENUM_wordarray_get_0_def
                             FUN_ENUM_wordarray_length_0_def
                             FUN_ENUM_wordarray_put2_0_def
                             FUN_ENUM_wordarray_fold_no_break_0_def
                             FUN_ENUM_wordarray_map_no_break_0_def
                             FUN_ENUM_wordarray_get_u32_def
                             FUN_ENUM_wordarray_length_u32_def
                             FUN_ENUM_wordarray_put2_u32_def)
       apply (thin_tac "upd.uval_typing _ _ _ _ _ _")
       apply (clarsimp simp: abs_typing_u_def)
       apply (case_tac a; clarsimp)
       apply (erule_tac x = b in allE)
       apply (thin_tac "_ \<in> state_rel")
       apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta heap_rel_ptr_w32_meta)
       apply (drule_tac p = "t5_C.arr_C x'" and uv = "UAbstract (WAU32 x11 x12)" in all_heap_rel_ptrD; 
              clarsimp simp: type_rel_simps is_valid_simp heap_simp abs_repr_u_def val_rel_simps) 
       apply (drule_tac p = "values_C (heap_WordArray_u32_C s (t5_C.arr_C x')) +\<^sub>p uint b" and 
                       uv = "UPrim (LU32 xa)" in all_heap_rel_ptrD; clarsimp simp: type_rel_simps)
       apply (rule conjI; clarsimp)
        apply (rule conjI)
         apply (rule_tac r = "UPrim (LU32 (t3_C.acc_C aa))" and 
                       len = "(SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C s (t5_C.arr_C x'))))" and
                       arr = "(ptr_val (values_C (heap_WordArray_u32_C s (t5_C.arr_C x'))))" and
                         v = xa and \<sigma> = \<sigma> and \<sigma>' = \<sigma> and \<sigma>'' = \<sigma> and ra = "{}" and ?w1.0 = "{}" and 
                         ?w2.0 = "{}" and t = "TUnit"
                       in upd_wa_foldnb_bod_0_step; simp?)
           apply (clarsimp simp: frame_def)
          apply (rule u_sem_app)
           apply (rule u_sem_fun)
          apply (rule u_sem_var)
         apply (subst mul_def; clarsimp)
         apply (rule u_sem_take_ub; simp?)
          apply (rule u_sem_var[where \<gamma> = "[_]" and i = 0, simplified])
         apply clarsimp
         apply (rule u_sem_take_ub; simp?)
          apply (rule u_sem_var[where \<gamma> = "[_, _, _]" and i = 1, simplified])
         apply clarsimp
         apply (rule u_sem_take_ub; simp?)
          apply (rule u_sem_var[where \<gamma> = "[_, _, _, _, _]" and i = 1, simplified])
         apply clarsimp
         apply (cut_tac \<xi> = \<xi>0 and 
                        \<gamma> = "[UUnit, 
                              URecord [(UPrim (LU32 xa), RPrim (Num U32)),
                                 (UPrim (LU32 (t3_C.acc_C aa)), RPrim (Num U32)), (UUnit, RUnit)],
                              UPrim (LU32 (t3_C.acc_C aa)),
                              URecord [(UPrim (LU32 xa), RPrim (Num U32)), 
                                 (UPrim (LU32 (t3_C.acc_C aa)), RPrim (Num U32)), (UUnit, RUnit)],
                              UPrim (LU32 xa),
                              URecord [(UPrim (LU32 xa), RPrim (Num U32)),
                                 (UPrim (LU32 (t3_C.acc_C aa)), RPrim (Num U32)), (UUnit, RUnit)],
                              URecord [(UPrim (LU32 xa), RPrim (Num U32)),
                                 (UPrim (LU32 (t3_C.acc_C aa)), RPrim (Num U32)),
                                 (UUnit, RUnit)]]" and
                        \<sigma> = \<sigma> and 
                       \<sigma>' = \<sigma> and
                        p = "Times U32" and
                       as = "[Var 4, Var 2]"  in u_sem_prim)
          apply (rule u_sem_all_cons)
           apply (rule u_sem_var)
          apply (rule u_sem_all_cons)
           apply (rule u_sem_var)
          apply (rule u_sem_all_empty)
          apply (clarsimp simp: eval_prim_u_def val_rel_simps)
         apply (rule upd.u_t_unit)
        apply (rule conjI)  
         apply (metis (no_types, hide_lams) max_word_max word_Suc_le word_le_less_eq word_not_le)
        apply (rule conjI)
         apply clarsimp
         apply (metis (no_types, hide_lams) max_word_max word_Suc_le word_not_le)
        apply (rule conjI)
         apply (meson min_less_iff_conj word_not_le)
        apply (metis (no_types, hide_lams) add.commute diff_less_mono2 max_word_max unat_mono word_Suc_le word_le_less_eq word_less_nat_alt word_not_le)
       apply (rule conjI)
        apply (rule_tac r = "UPrim (LU32 (t3_C.acc_C aa))" and 
                      len = "(SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C s (t5_C.arr_C x'))))" and
                      arr = "(ptr_val (values_C (heap_WordArray_u32_C s (t5_C.arr_C x'))))" and
                        v = xa and \<sigma> = \<sigma> and \<sigma>' = \<sigma> and \<sigma>'' = \<sigma> and ra = "{}" and ?w1.0 = "{}" and
                        ?w2.0 = "{}" and t = "TUnit"
                      in upd_wa_foldnb_bod_0_step; simp?)
          apply (clarsimp simp: frame_def)
         apply (rule u_sem_app)
           apply (rule u_sem_fun)
          apply (rule u_sem_var)
         apply (subst sum_def; clarsimp)
         apply (rule u_sem_take_ub; simp?)
          apply (rule u_sem_var[where \<gamma> = "[_]" and i = 0, simplified])
         apply clarsimp
         apply (rule u_sem_take_ub; simp?)
          apply (rule u_sem_var[where \<gamma> = "[_, _, _]" and i = 1, simplified])
         apply clarsimp
         apply (rule u_sem_take_ub; simp?)
          apply (rule u_sem_var[where \<gamma> = "[_, _, _, _, _]" and i = 1, simplified])
         apply clarsimp
         apply (cut_tac \<xi> = \<xi>0 and 
                        \<gamma> = "[UUnit, 
                             URecord [(UPrim (LU32 xa), RPrim (Num U32)),
                                (UPrim (LU32 (t3_C.acc_C aa)), RPrim (Num U32)), (UUnit, RUnit)],
                             UPrim (LU32 (t3_C.acc_C aa)),
                             URecord [(UPrim (LU32 xa), RPrim (Num U32)), 
                                (UPrim (LU32 (t3_C.acc_C aa)), RPrim (Num U32)), (UUnit, RUnit)],
                             UPrim (LU32 xa),
                             URecord [(UPrim (LU32 xa), RPrim (Num U32)),
                                (UPrim (LU32 (t3_C.acc_C aa)), RPrim (Num U32)), (UUnit, RUnit)],
                             URecord [(UPrim (LU32 xa), RPrim (Num U32)),
                                (UPrim (LU32 (t3_C.acc_C aa)), RPrim (Num U32)),
                                (UUnit, RUnit)]]" and
                       \<sigma> = \<sigma> and 
                      \<sigma>' = \<sigma> and
                       p = "Plus U32" and
                      as = "[Var 4, Var 2]"  in u_sem_prim)
          apply (rule u_sem_all_cons)
           apply (rule u_sem_var)
          apply (rule u_sem_all_cons)
           apply (rule u_sem_var)
          apply (rule u_sem_all_empty)
         apply (clarsimp simp: eval_prim_u_def val_rel_simps)  
        apply (rule upd.u_t_unit)
       apply (rule conjI)  
        apply (metis (no_types, hide_lams) max_word_max word_Suc_le word_le_less_eq word_not_le)
       apply (rule conjI)
        apply clarsimp
        apply (metis (no_types, hide_lams) max_word_max word_Suc_le word_not_le)
       apply (rule conjI)
        apply (meson min_less_iff_conj word_not_le)
       apply (metis (no_types, hide_lams) add.commute diff_less_mono2 max_word_max unat_mono word_Suc_le word_le_less_eq word_less_nat_alt word_not_le)
      apply (case_tac a; clarsimp simp: abs_typing_u_def)
      apply (thin_tac "_ \<in> state_rel")
      apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta heap_rel_ptr_w32_meta)
      apply (drule_tac p = "t5_C.arr_C x'" and uv = "UAbstract (WAU32 x11 x12)" in all_heap_rel_ptrD; 
             clarsimp simp: type_rel_simps is_valid_simp heap_simp abs_repr_u_def val_rel_simps) 
      apply (thin_tac "cogent_function_val_rel _ _")
      apply (thin_tac "upd.uval_typing _ _ _ _ _ _")
      apply clarsimp
      apply (case_tac "t5_C.to_C x' = b"; clarsimp?)
      apply (case_tac "b < t5_C.to_C x'"; clarsimp)
       apply (case_tac x; clarsimp)
        apply (drule_tac arr = "ptr_val (values_C (heap_WordArray_u32_C s (t5_C.arr_C x')))" and 
                         len = "SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C s (t5_C.arr_C x')))" 
                         in upd_wa_foldnb_bod_0_to_geq_lenD; simp?)
        apply (rule_tac arr = "ptr_val (values_C (heap_WordArray_u32_C s (t5_C.arr_C x')))" and 
                        len = "SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C s (t5_C.arr_C x')))" 
                        in upd_wa_foldnb_bod_0_to_geq_len; simp)
       apply (drule_tac arr = "ptr_val (values_C (heap_WordArray_u32_C s (t5_C.arr_C x')))" and 
                        len = "SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C s (t5_C.arr_C x')))" 
                        in upd_wa_foldnb_bod_0_to_geq_lenD; simp?)
       apply (rule_tac arr = "ptr_val (values_C (heap_WordArray_u32_C s (t5_C.arr_C x')))" and 
                       len = "SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C s (t5_C.arr_C x')))" 
                       in upd_wa_foldnb_bod_0_to_geq_len; simp)
      apply (case_tac "min (t5_C.to_C x') (SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C s (t5_C.arr_C x')))) \<le> t5_C.frm_C x'")
       apply clarsimp
       apply (case_tac x; clarsimp)
        apply (erule upd_wa_foldnb_bod_0.elims; clarsimp)
        apply (clarsimp simp: min_def split: if_splits)
         apply (subst upd_wa_foldnb_bod_0.simps; clarsimp)
        apply (subst upd_wa_foldnb_bod_0.simps; clarsimp)
       apply (erule upd_wa_foldnb_bod_0.elims; clarsimp)
       apply (clarsimp simp: min_def split: if_splits)
        apply (subst upd_wa_foldnb_bod_0.simps; clarsimp)
       apply (subst upd_wa_foldnb_bod_0.simps; clarsimp)
      apply clarsimp
      apply (rule FalseE)
      apply (meson min_less_iff_disj not_less word_le_less_eq)
     apply wp
    apply wp
   apply clarsimp
   apply (subst unknown_def[symmetric])
   apply (rule validNF_unknown)
  apply (clarsimp simp: cogent_function_val_rel
                        FUN_ENUM_sum_def
                        FUN_ENUM_dec_def
                        FUN_ENUM_inc_def
                        FUN_ENUM_mul_def
                        FUN_ENUM_dec_arr_def
                        FUN_ENUM_inc_arr_def
                        FUN_ENUM_mul_arr_def
                        FUN_ENUM_sum_arr_def
                        FUN_ENUM_wordarray_get_0_def
                        FUN_ENUM_wordarray_length_0_def
                        FUN_ENUM_wordarray_put2_0_def
                        FUN_ENUM_wordarray_fold_no_break_0_def
                        FUN_ENUM_wordarray_map_no_break_0_def
                        FUN_ENUM_wordarray_get_u32_def
                        FUN_ENUM_wordarray_length_u32_def
                        FUN_ENUM_wordarray_put2_u32_def)
  apply (case_tac x; clarsimp)
   apply (subst upd_wa_foldnb_bod_0.simps)
   apply clarsimp
   apply (subst upd_wa_foldnb_bod_0.simps)
   apply clarsimp
   apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta abs_typing_u_def)
   apply (case_tac a; clarsimp)
   apply (drule_tac p = "t5_C.arr_C x'" and uv = "UAbstract (WAU32 x11 x12)" in all_heap_rel_ptrD;
          clarsimp simp: abs_repr_u_def type_rel_simps is_valid_simp)
   apply (thin_tac "upd.uval_typing _ _ _ _ _ _")
   apply (thin_tac "is_valid_WordArray_u32_C _ _")
   apply (thin_tac "val_rel _ _")
   apply (erule disjE; clarsimp)
   apply (erule disjE; clarsimp)
    apply (rule conjI; clarsimp)
     apply (rule conjI)
      apply (rule_tac x = abbreviatedType1 and 
        ?\<Gamma>1.0 = "[option.Some abbreviatedType1]" and
        ?\<Gamma>2.0 = "[option.Some abbreviatedType1]" in typing_app)
        apply (clarsimp simp: split_Cons split_empty)
        apply (rule_tac k = "{D, S, E}" in share; simp?)
        apply (clarsimp simp: abbreviatedType1_def)
        apply (rule kindingI; clarsimp)
       apply (rule_tac K' = "[]" and t = "abbreviatedType1" and u = "TPrim (Num U32)" in typing_fun; clarsimp?)
         apply (cut_tac mul_typecorrect') 
         apply (clarsimp simp: mul_type_def)
        apply (clarsimp simp: Cogent.empty_def weakening_Cons weakening_nil)
        apply (rule_tac k = "{D, S, E}" in drop; simp?)
        apply (clarsimp simp: abbreviatedType1_def)
        apply (rule kindingI; clarsimp)
       apply (clarsimp simp: abbreviatedType1_def)
      apply (rule typing_var; clarsimp simp: weakening_Cons Cogent.empty_def weakening_nil)
      apply (rule keep; clarsimp simp: abbreviatedType1_def)
     apply (metis (no_types, hide_lams) min.strict_order_iff min_def_raw not_less_iff_gr_or_eq)
    apply (rule conjI)
     apply (rule_tac x = abbreviatedType1 and 
        ?\<Gamma>1.0 = "[option.Some abbreviatedType1]" and
        ?\<Gamma>2.0 = "[option.Some abbreviatedType1]" in typing_app)
       apply (clarsimp simp: split_Cons split_empty)
       apply (rule_tac k = "{D, S, E}" in share; simp?)
       apply (clarsimp simp: abbreviatedType1_def)
       apply (rule kindingI; clarsimp)
      apply (rule_tac K' = "[]" and t = "abbreviatedType1" and u = "TPrim (Num U32)" in typing_fun; clarsimp?)
        apply (cut_tac mul_typecorrect')
        apply (clarsimp simp: mul_type_def)
       apply (clarsimp simp: Cogent.empty_def weakening_Cons weakening_nil)
       apply (rule_tac k = "{D, S, E}" in drop; simp?)
       apply (clarsimp simp: abbreviatedType1_def)
       apply (rule kindingI; clarsimp)
      apply (clarsimp simp: abbreviatedType1_def)
     apply (rule typing_var; clarsimp simp: weakening_Cons Cogent.empty_def weakening_nil)
     apply (rule keep; clarsimp simp: abbreviatedType1_def)
    apply (metis (no_types, hide_lams) min.strict_order_iff min_def_raw not_less_iff_gr_or_eq)
   apply (rule conjI; clarsimp)
    apply (rule conjI)
     apply (rule_tac x = abbreviatedType1 and 
        ?\<Gamma>1.0 = "[option.Some abbreviatedType1]" and
        ?\<Gamma>2.0 = "[option.Some abbreviatedType1]" in typing_app)
       apply (clarsimp simp: split_Cons split_empty)
       apply (rule_tac k = "{D, S, E}" in share; simp?)
       apply (clarsimp simp: abbreviatedType1_def)
       apply (rule kindingI; clarsimp)
      apply (rule_tac K' = "[]" and t = "abbreviatedType1" and u = "TPrim (Num U32)" in typing_fun; clarsimp?)
        apply (cut_tac sum_typecorrect') 
        apply (clarsimp simp: sum_type_def)
       apply (clarsimp simp: Cogent.empty_def weakening_Cons weakening_nil)
       apply (rule_tac k = "{D, S, E}" in drop; simp?)
       apply (clarsimp simp: abbreviatedType1_def)
       apply (rule kindingI; clarsimp)
      apply (clarsimp simp: abbreviatedType1_def)
     apply (rule typing_var; clarsimp simp: weakening_Cons Cogent.empty_def weakening_nil)
     apply (rule keep; clarsimp simp: abbreviatedType1_def)
    apply (metis (no_types, hide_lams) min.strict_order_iff min_def_raw not_less_iff_gr_or_eq)
   apply (rule conjI)
    apply (rule_tac x = abbreviatedType1 and 
        ?\<Gamma>1.0 = "[option.Some abbreviatedType1]" and
        ?\<Gamma>2.0 = "[option.Some abbreviatedType1]" in typing_app)
      apply (clarsimp simp: split_Cons split_empty)
      apply (rule_tac k = "{D, S, E}" in share; simp?)
      apply (clarsimp simp: abbreviatedType1_def)
      apply (rule kindingI; clarsimp)
     apply (rule_tac K' = "[]" and t = "abbreviatedType1" and u = "TPrim (Num U32)" in typing_fun; clarsimp?)
       apply (cut_tac sum_typecorrect')
       apply (clarsimp simp: sum_type_def)
      apply (clarsimp simp: Cogent.empty_def weakening_Cons weakening_nil)
      apply (rule_tac k = "{D, S, E}" in drop; simp?)
      apply (clarsimp simp: abbreviatedType1_def)
      apply (rule kindingI; clarsimp)
     apply (clarsimp simp: abbreviatedType1_def)
    apply (rule typing_var; clarsimp simp: weakening_Cons Cogent.empty_def weakening_nil)
    apply (rule keep; clarsimp simp: abbreviatedType1_def)
   apply (metis (no_types, hide_lams) min.strict_order_iff min_def_raw not_less_iff_gr_or_eq)
  apply (erule disjE; clarsimp)
  done
end (* of context *)
end
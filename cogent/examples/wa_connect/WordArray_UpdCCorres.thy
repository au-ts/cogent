(*
  This file contains the update semantics to C correspondence lemmas for word array functions
*)
theory WordArray_UpdCCorres
  imports WordArray_Abstractions
begin

context WordArray begin
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
  apply (clarsimp simp: abs_rel_def; rename_tac r w)
  apply (thin_tac "i < length \<gamma>")
  apply (thin_tac "val_rel (\<gamma> ! i) v'")
  apply (thin_tac "\<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_put2_0'')))")
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
  apply (thin_tac "\<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))")
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
  apply (thin_tac "\<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_get_0'')))")
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
     \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_fold_no_break_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u)
         (App (AFun ''wordarray_fold_no_break_0'' []) (Var i)) (do x <- main_pp_inferred.wordarray_fold_no_break_0' v';
gets (\<lambda>s. x)
                                                                od)
         \<xi>0 \<gamma> \<Xi>  \<Gamma>' \<sigma> s"
  apply (rule afun_corres; simp)
  apply (clarsimp simp: abs_rel_def')
  apply (thin_tac "i < length \<gamma>")
  apply (thin_tac "val_rel (\<gamma> ! i) v'")
  apply (thin_tac "\<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_fold_no_break_0'')))")
  apply clarsimp
  apply (clarsimp simp: val_rel_simp)
(*
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
*)
  apply (erule upd.u_t_recE)
  apply (clarsimp simp: \<Xi>_def wordarray_fold_no_break_0_type_def abbreviatedType1_def)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_p_absE; clarsimp simp: abs_typing_u_def)
  apply (case_tac a; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_primE; subst (asm) lit_type.simps; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_primE; subst (asm) lit_type.simps; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_primE; subst (asm) lit_type.simps; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_r_emptyE)
  apply (erule upd.u_t_unitE)
  apply (case_tac "sint (t5_C.f_C x') \<noteq> sint FUN_ENUM_mul")
   apply (case_tac "sint (t5_C.f_C x') \<noteq> sint FUN_ENUM_sum")
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
    apply (erule disjE)
     apply (clarsimp simp: dec_def)
     apply (erule upd.u_t_functionE)
     apply (erule typing_takeE)+
     apply (erule typing_letE)+
     apply (erule typing_structE)
     apply (erule typing_all_consE)+
     apply (erule typing_varE)+
     apply (clarsimp simp: subtyping_simps(4) subtyping.simps[of _ _ "TPrim (Num U32)", simplified])
    apply (erule disjE)
     apply (clarsimp simp: inc_def)
     apply (erule upd.u_t_functionE)
     apply (erule typing_takeE)+
     apply (erule typing_letE)+
     apply (erule typing_structE)
     apply (erule typing_all_consE)+
     apply (erule typing_varE)+
     apply (clarsimp simp: subtyping_simps(4) subtyping.simps[of _ _ "TPrim (Num U32)", simplified])
    apply (erule disjE)
     apply (clarsimp simp: dec_arr_def)
     apply (erule upd.u_t_functionE; clarsimp)
     apply (erule typing_letE)
     apply (erule typing_letbE)
     apply (erule typing_letE)+
     apply (erule typing_appE)+
     apply (erule typing_afunE)+
     apply (clarsimp simp: wordarray_map_no_break_0_type_def abbreviatedType2_def)
     apply (clarsimp simp: subtyping_simps(4) subtyping.simps[of _ _ "TPrim (Num U32)", simplified])
    apply (erule disjE)
     apply (clarsimp simp: inc_arr_def)
     apply (erule upd.u_t_functionE; clarsimp)
     apply (erule typing_letE)
     apply (erule typing_letbE)
     apply (erule typing_letE)+
     apply (erule typing_appE)+
     apply (erule typing_afunE)+
     apply (clarsimp simp: wordarray_map_no_break_0_type_def abbreviatedType2_def)
     apply (clarsimp simp: subtyping_simps(4) subtyping.simps[of _ _ "TPrim (Num U32)", simplified])
    apply (erule disjE)
     apply (clarsimp simp: mul_arr_def)
     apply (erule upd.u_t_functionE; clarsimp)
     apply (clarsimp simp: subtyping_simps(4) subtyping.simps[of _ _ "TPrim (Num U32)", simplified])
     apply (erule subtyping.cases; clarsimp)
     apply (subst (asm) subtyping.simps[of _ "TPrim (Num U32)", simplified])+
     apply (clarsimp simp: subtyping.simps[of _ "TUnit", simplified] kinding_simps(5, 9))
     apply (erule typing_letE)+
     apply (erule typing_structE)
     apply (erule typing_all_consE)+
     apply (erule typing_all_emptyE)
     apply (erule typing_varE)+
     apply (erule typing_litE)+
     apply (erule typing_unitE)+
     apply clarsimp
     apply (erule typing_appE)+
     apply (erule typing_funE)+
     apply (clarsimp simp: wordarray_length_u32_def mul_def)
     apply (erule typing_letE)
     apply (erule typing_appE)
     apply (erule typing_afunE)+
     apply clarsimp
     apply (erule typing_takeE)+
     apply (erule typing_primE)
     apply (erule typing_all_consE)+
     apply (erule typing_all_emptyE)
     apply (erule typing_varE)+
     apply (clarsimp simp: wordarray_length_0_type_def)
     apply (subst (asm) split_conv_all_nth)
     apply clarsimp
     apply (erule split_comp.cases; clarsimp)
  apply (subst (asm) weakening_conv_all_nth)
(*
     apply (case_tac \<Gamma>1; clarsimp)
     apply (case_tac \<Gamma>2)
      apply clarsimp
  find_theorems "split_comp"
*)


(*
     apply (case_tac \<Gamma>1; clarsimp)

*)
(*
     apply (case_tac \<Gamma>2; clarsimp)
     
     apply (case_tac a; clarsimp)
*)

(*
     apply (clarsimp simp: split_conv_all_nth  weakening_conv_all_nth)
*)



  oops
end (* of context *)
end
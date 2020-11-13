(*
  This file contains the update semantics to C correspondence lemmas for word array functions
*)
theory WordArray_UpdCCorres
  imports WordArray_UAbsFun
begin

context WordArray begin

thm abbreviated_type_defs
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

declare \<xi>0.simps[simp del]
lemma upd_C_wordarray_put2_corres:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_put2_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr) (App (AFun ''wordarray_put2_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_put2_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (rule absfun_corres; simp?)
  apply (thin_tac "\<Gamma>' ! i = _")
  apply (clarsimp simp: abs_fun_rel_def; rename_tac r w)
  apply (rotate_tac -1)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) \<Xi>_def)
  apply (clarsimp simp: val_rel_simp wordarray_put2_0_type_def abbreviated_type_defs)
  apply (erule upd.u_t_recE)
  apply (erule upd.u_t_r_consE; clarsimp)+
  apply (erule upd.u_t_primE)+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (erule upd.u_t_r_emptyE)
  apply (erule upd.u_t_p_absE; simp)
  apply (frule wa_abs_typing_u_elims(1); clarsimp; rename_tac len arr)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_put2_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def)
   apply (erule_tac x = "t2_C.arr_C v'" in allE)
   apply (erule_tac x = "values_C (heap_WordArray_u32_C st (t2_C.arr_C v')) +\<^sub>p uint (t2_C.idx_C v')" in allE)
   apply (clarsimp simp: heap_rel_ptr_def heap_rel_ptr_w32_def wa_abs_repr_def is_valid_simp type_rel_simp)
   apply (frule wa_abs_typing_u_elims(5))
   apply (erule_tac x = "t2_C.idx_C v'" in allE)+
   apply (clarsimp simp: val_rel_simp heap_simp type_rel_simp)
  apply clarsimp
  apply (monad_eq simp: upd_wa_put2_0_def \<xi>0.simps)
  apply (case_tac "idx_C v' < len"; clarsimp)
  apply (rule conjI)
    apply (monad_eq simp: wordarray_put2_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta heap_rel_ptr_w32_meta)
   apply (monad_eq simp: wordarray_put2_0'_def)
   apply (frule_tac p = "t2_C.arr_C v'" in all_heap_rel_ptrD; simp?)
    apply (clarsimp simp: type_rel_simp wa_abs_repr_def)
   apply (clarsimp simp: val_rel_simp heap_simp is_valid_simp)
   apply (drule wa_abs_typing_u_elims(5))
   apply (erule_tac x = "t2_C.idx_C v'" in allE; clarsimp)
   apply (drule_tac upd_h = "(heap_w32_update 
      (\<lambda>x. x(values_C (heap_WordArray_u32_C st (t2_C.arr_C v')) +\<^sub>p uint (idx_C v') := val_C v')) st)" and
      x = "(values_C (heap_WordArray_u32_C st (t2_C.arr_C v'))) +\<^sub>p uint (idx_C v')" and
      uv' = "UPrim (LU32 (val_C v'))" and uv = "UPrim x"
      in all_heap_rel_updE; simp?; clarsimp?)
    apply (clarsimp simp: type_rel_simp)
   apply (drule_tac upd_h = "(heap_w32_update
      (\<lambda>x. x(values_C (heap_WordArray_u32_C st (t2_C.arr_C v')) +\<^sub>p uint (idx_C v') := val_C v')) st)" and
      x = "(values_C (heap_WordArray_u32_C st (t2_C.arr_C v'))) +\<^sub>p uint (idx_C v')" and
      uv' = "UPrim (LU32 (val_C v'))" and uv = "UPrim x"
      in all_heap_rel_updE; simp?; clarsimp?)
   apply (rule conjI, clarsimp simp: val_rel_simp)
   apply clarsimp
   apply (rule FalseE)
   apply (cut_tac p = p and q = "((values_C (heap_WordArray_u32_C st (t2_C.arr_C v'))) +\<^sub>p uint (idx_C v'))" in ptr_val_inj)
   apply (clarsimp simp: ptr_add_def)
  apply (monad_eq simp: wordarray_put2_0'_def)
  apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta)
  apply (frule_tac p = "t2_C.arr_C v'" in all_heap_rel_ptrD; simp?)
   apply (clarsimp simp: type_rel_simp wa_abs_repr_def)
  apply (clarsimp simp: val_rel_simp heap_simp is_valid_simp)
  done

lemma upd_C_wordarray_length_corres:
"\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr) (App (AFun ''wordarray_length_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_length_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (rule absfun_corres; simp?)
  apply (clarsimp simp: abs_fun_rel_def; rename_tac r w)
  apply (thin_tac "\<Gamma>' ! i = _")
  apply (rotate_tac -1)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) \<Xi>_def)
  apply (clarsimp simp: val_rel_simp wordarray_length_0_type_def)
  apply (erule upd.u_t_p_absE; simp)
  apply (frule wa_abs_typing_u_elims(1); clarsimp; rename_tac len arr)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_length_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def)
   apply (erule_tac x = v' in allE)
   apply (clarsimp simp: heap_rel_ptr_def type_rel_simp wa_abs_repr_def is_valid_simp)
  apply clarsimp
  apply (rule_tac x = \<sigma> in exI)
  apply (rule conjI)
   apply (clarsimp simp: upd_wa_length_0_def \<xi>0.simps)
   apply (monad_eq simp: wordarray_length_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def)
   apply (erule_tac x = v' in allE)
   apply (clarsimp simp: heap_rel_ptr_def type_rel_simp wa_abs_repr_def heap_simp val_rel_simp)
  apply (monad_eq simp: wordarray_length_0'_def)
  done


lemma upd_C_wordarray_get_corres:
"\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_get_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr) (App (AFun ''wordarray_get_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_get_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (rule absfun_corres; simp?)
  apply (clarsimp simp: abs_fun_rel_def; rename_tac r w)
  apply (thin_tac "\<Gamma>' ! i = _")
  apply (rotate_tac -1)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) \<Xi>_def)
  apply (clarsimp simp: val_rel_simp wordarray_get_0_type_def abbreviated_type_defs)
  apply (erule upd.u_t_recE)
  apply (erule upd.u_t_r_consE; clarsimp)+
  apply (erule upd.u_t_r_emptyE)
  apply (erule upd.u_t_primE; subst (asm) lit_type.simps; clarsimp)
  apply (erule upd.u_t_p_absE; simp)
  apply (frule wa_abs_typing_u_elims(1); clarsimp; rename_tac len arr)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_get_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta heap_rel_ptr_w32_meta)
   apply (drule_tac p = "t1_C.p1_C v'" and uv = "UAbstract (UWA (TPrim (Num U32)) len arr)" in all_heap_rel_ptrD; 
          clarsimp simp: type_rel_simp wa_abs_repr_def val_rel_simp is_valid_simp heap_simp)
   apply (drule not_le_imp_less)
   apply (frule wa_abs_typing_u_elims(5))
   apply (erule_tac x = "t1_C.p2_C v'" in allE; clarsimp)
   apply (drule_tac p = "values_C (heap_WordArray_u32_C st (t1_C.p1_C v')) +\<^sub>p uint (t1_C.p2_C v')" and
                   uv = "UPrim x" in all_heap_rel_ptrD; simp add: type_rel_simp)
  apply clarsimp
  apply (rule_tac x = \<sigma> in exI)
  apply (rule conjI)
   apply (clarsimp simp: upd_wa_get_0_def \<xi>0.simps)
   apply (frule wa_abs_typing_u_elims(5))
   apply (erule_tac x = "t1_C.p2_C v'" in allE)
   apply (monad_eq simp: wordarray_get_0'_def word_less_nat_alt word_le_nat_alt)
   apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta heap_rel_ptr_w32_meta)
   apply (drule_tac p = "t1_C.p1_C v'" and uv = "UAbstract (UWA (TPrim (Num U32)) len arr)" in all_heap_rel_ptrD; 
          clarsimp simp: type_rel_simp wa_abs_repr_def val_rel_simp is_valid_simp heap_simp)
   apply (drule_tac p = "values_C (heap_WordArray_u32_C st (t1_C.p1_C v')) +\<^sub>p uint (t1_C.p2_C v')" and
                   uv = "UPrim x" in all_heap_rel_ptrD;
          clarsimp simp: type_rel_simp val_rel_simp)
  apply (monad_eq simp: wordarray_get_0'_def)
  apply blast
  done
thm corres_sum corres_app_concrete
declare \<xi>1.simps [simp del]
(*
lemma upd_C_wordarray_fold_no_break_corres:
" \<And>v' i \<gamma> \<Gamma>' \<sigma> s.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_fold_no_break_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr)
         (App (AFun ''wordarray_fold_no_break_0'' []) (Var i)) (do x <- main_pp_inferred.wordarray_fold_no_break_0' v';
gets (\<lambda>s. x)
                                                                od)
         \<xi>1 \<gamma> \<Xi>  \<Gamma>' \<sigma> s"
  apply (rule absfun_corres; simp?)
  apply (clarsimp simp: abs_fun_rel_def')
  apply (thin_tac "\<Gamma>' ! i = _")
  apply clarsimp
  apply (clarsimp simp: val_rel_simp)
  apply (erule upd.u_t_recE)
  apply (rotate_tac -3)
  apply (subst (asm) \<Xi>_def)
  apply (clarsimp simp: wordarray_fold_no_break_0_type_def abbreviated_type_defs)
  apply (erule upd.u_t_r_consE; clarsimp)+
  apply (erule upd.u_t_primE; subst (asm) lit_type.simps; clarsimp)+
  apply (erule upd.u_t_r_emptyE)
  apply (erule upd.u_t_unitE)
  apply (case_tac "sint (t5_C.f_C v') \<noteq> sint FUN_ENUM_mul \<and> sint (t5_C.f_C v') \<noteq> sint FUN_ENUM_sum")
   apply (clarsimp simp: cogent_function_val_rel
                         FUN_ENUM_sum_def
                         FUN_ENUM_mul_def
                         FUN_ENUM_mul_arr_def
                         FUN_ENUM_sum_arr_def
                         FUN_ENUM_wordarray_get_0_def
                         FUN_ENUM_wordarray_length_0_def
                         FUN_ENUM_wordarray_put2_0_def
                         FUN_ENUM_wordarray_fold_no_break_0_def
                         FUN_ENUM_wordarray_get_u32_def
                         FUN_ENUM_wordarray_length_u32_def
                         FUN_ENUM_wordarray_put2_u32_def)
   apply (rule FalseE) 
   apply (thin_tac "_ \<in> state_rel")
   apply (thin_tac "t5_C.f_C v' \<noteq> 0")
   apply (thin_tac "sint (t5_C.f_C v') \<noteq> 2")
   apply (thin_tac "upd.uval_typing _ _ (UPtr _ _) _ _ _")
   apply (thin_tac "_ = _")+
   apply clarsimp
   apply (erule disjE)
    prefer 2
    apply (erule disjE)
     prefer 2
     apply (erule disjE)
      apply clarsimp
      apply (erule upd.u_t_afunE; clarsimp)
      apply (clarsimp simp: subtyping_simps(4) 
                            subtyping.simps[of _ _ "TPrim (Num U32)", simplified]
                            wordarray_get_0_type_def abbreviated_type_defs
                            subtyping_simps(6) \<Xi>_def)
     apply (erule disjE)
      apply clarsimp
      apply (erule upd.u_t_afunE; clarsimp)
      apply (clarsimp simp: subtyping_simps(4) 
                            subtyping.simps[of _ _ "TPrim (Num U32)", simplified]
                            wordarray_put2_0_type_def \<Xi>_def)
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
      apply (clarsimp simp: wordarray_get_0_type_def abbreviated_type_defs \<Xi>_def)
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
                            wordarray_length_0_type_def \<Xi>_def)
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
      apply (clarsimp simp: wordarray_put2_0_type_def abbreviated_type_defs \<Xi>_def)
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
      apply (clarsimp simp: wordarray_length_0_type_def \<Xi>_def)
      apply (erule typing_varE)+
      apply (clarsimp simp: split_conv_all_nth weakening_conv_all_nth empty_def)
      apply (erule_tac x = 0 in allE)+
      apply (clarsimp simp: weakening_comp.simps split_comp.simps)
      apply (erule disjE; clarsimp)
     apply clarsimp
     apply (erule upd.u_t_afunE; clarsimp)
     apply (clarsimp simp: subtyping_simps(4) 
                           subtyping.simps[of _ _ "TPrim (Num U32)", simplified]
                           subtyping.simps[of _ "TRecord _ _ ", simplified]
                           \<Xi>_def wordarray_fold_no_break_0_type_def)
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
    apply (clarsimp simp: wordarray_length_0_type_def \<Xi>_def)
    apply (frule split_length; simp)
    apply (drule same_type_as_weakened; simp?)
    apply (drule split_preservation_some_left; simp?)
    apply clarsimp
    apply (drule same_type_as_weakened; simp?)
    apply (drule_tac ?\<Gamma>2.0 = \<Gamma>2b in split_preservation_some_right; simp?)
    apply (drule split_preservation_some_left; simp?)
    apply clarsimp
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
   apply (clarsimp simp: wordarray_length_0_type_def \<Xi>_def)
   apply (frule split_length; simp)
   apply (drule same_type_as_weakened; simp?)
   apply (drule split_preservation_some_left; simp?)
   apply clarsimp
   apply (drule same_type_as_weakened; simp?)
   apply (drule_tac ?\<Gamma>2.0 = \<Gamma>2b in split_preservation_some_right; simp?)
   apply (drule split_preservation_some_left; simp?)
   apply clarsimp
  apply clarsimp
  apply (erule upd.u_t_p_absE; clarsimp)
  apply (clarsimp simp: wordarray_fold_no_break_0'_def upd_wa_foldnb_def \<xi>1.simps)
  apply (subst unknown_bind_ignore)+
  apply clarsimp
  apply wp 
      apply (clarsimp simp: split_def unknown_bind_ignore)
      apply (subst whileLoop_add_inv
              [where M = "\<lambda>((_, r), _). unat (t5_C.to_C v') - unat r" and 
                     I = "\<lambda>(a, b) s. 
                        (\<exists>func. cogent_function_val_rel x (sint (t5_C.f_C v')) \<and> func = x \<and>
                        is_uval_fun func \<and> (\<Xi>, [], [option.Some abbreviatedType1] \<turnstile> 
                          (App (uvalfun_to_exprfun func) (Var 0)) : TPrim (Num U32)) \<and>
                        upd_wa_foldnb_bod \<xi>0 \<sigma> (ptr_val (t5_C.arr_C v')) (t5_C.frm_C v') b 
                          (uvalfun_to_exprfun func) (UPrim (LU32 (t5_C.acc_C v'))) UUnit {} 
                          (\<sigma>, UPrim (LU32 (t3_C.acc_C a)))) \<and> 
                        (\<sigma>, s) \<in> state_rel \<and> t5_C.frm_C v' \<le> b \<and>
                        ret = min (t5_C.to_C v') ((SCAST(32 signed \<rightarrow> 32))(len_C (heap_WordArray_u32_C s (t5_C.arr_C v')))) \<and>
                        (t5_C.frm_C v' \<le> ret \<longrightarrow> b \<le> ret) \<and> (t5_C.frm_C v' \<ge> ret \<longrightarrow> b = t5_C.frm_C v')"])
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
                             FUN_ENUM_mul_def
                             FUN_ENUM_mul_arr_def
                             FUN_ENUM_sum_arr_def
                             FUN_ENUM_wordarray_get_0_def
                             FUN_ENUM_wordarray_length_0_def
                             FUN_ENUM_wordarray_put2_0_def
                             FUN_ENUM_wordarray_fold_no_break_0_def
                             FUN_ENUM_wordarray_get_u32_def
                             FUN_ENUM_wordarray_length_u32_def
                             FUN_ENUM_wordarray_put2_u32_def)
       apply (thin_tac "upd.uval_typing _ _ _ _ _ _")
       apply (clarsimp simp: wa_abs_typing_u_def)
       apply (thin_tac "_ \<in> state_rel")
       apply (clarsimp split: atyp.splits type.splits prim_type.splits)
       apply (erule_tac x = b in allE)
       apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta heap_rel_ptr_w32_meta)
       apply (drule_tac p = "t5_C.arr_C v'" and uv = "UAbstract (UWA (TPrim (Num U32)) x12 x13)" in all_heap_rel_ptrD; 
              clarsimp simp: type_rel_simps is_valid_simp heap_simp wa_abs_repr_def val_rel_simps) 
       apply (drule_tac p = "values_C (heap_WordArray_u32_C sa (t5_C.arr_C v')) +\<^sub>p uint b" and 
                       uv = "UPrim xa" in all_heap_rel_ptrD; clarsimp simp: type_rel_simps)
       apply (rule conjI; clarsimp)
        apply (rule conjI)
         apply (rule_tac r = "UPrim (LU32 (t3_C.acc_C aa))" and 
                       len = "(SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C sa (t5_C.arr_C v'))))" and
                       arr = "(ptr_val (values_C (heap_WordArray_u32_C sa (t5_C.arr_C v'))))" and
                         v = "UPrim xa" and \<sigma> = \<sigma> and \<sigma>' = \<sigma> and \<sigma>'' = \<sigma> and ?w1.0 = "{}" and 
                         ?w2.0 = "{}"
                       in upd_wa_foldnb_bod_step; simp?)
           apply clarsimp
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
                              URecord [(UPrim xa, RPrim (Num U32)),
                                 (UPrim (LU32 (t3_C.acc_C aa)), RPrim (Num U32)), (UUnit, RUnit)],
                              UPrim (LU32 (t3_C.acc_C aa)),
                              URecord [(UPrim xa, RPrim (Num U32)), 
                                 (UPrim (LU32 (t3_C.acc_C aa)), RPrim (Num U32)), (UUnit, RUnit)],
                              UPrim xa,
                              URecord [(UPrim xa, RPrim (Num U32)),
                                 (UPrim (LU32 (t3_C.acc_C aa)), RPrim (Num U32)), (UUnit, RUnit)],
                              URecord [(UPrim xa, RPrim (Num U32)),
                                 (UPrim (LU32 (t3_C.acc_C aa)), RPrim (Num U32)),
                                 (UUnit, RUnit)]]" and
                        \<sigma> = \<sigma> and 
                       \<sigma>' = \<sigma> and
                        p = "Times U32" and
                       as = "[Var 4, Var 2]" in u_sem_prim)
          apply (rule u_sem_all_cons)
           apply (rule u_sem_var)
          apply (rule u_sem_all_cons)
           apply (rule u_sem_var)
          apply (rule u_sem_all_empty)
         apply (clarsimp simp: eval_prim_u_def val_rel_simps)
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
                      len = "(SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C sa (t5_C.arr_C v'))))" and
                      arr = "(ptr_val (values_C (heap_WordArray_u32_C sa (t5_C.arr_C v'))))" and
                        v = "UPrim xa" and \<sigma> = \<sigma> and \<sigma>' = \<sigma> and \<sigma>'' = \<sigma> and ?w1.0 = "{}" and
                        ?w2.0 = "{}"
                      in upd_wa_foldnb_bod_step; simp?)
          apply clarsimp
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
                             URecord [(UPrim xa, RPrim (Num U32)),
                                (UPrim (LU32 (t3_C.acc_C aa)), RPrim (Num U32)), (UUnit, RUnit)],
                             UPrim (LU32 (t3_C.acc_C aa)),
                             URecord [(UPrim xa, RPrim (Num U32)), 
                                (UPrim (LU32 (t3_C.acc_C aa)), RPrim (Num U32)), (UUnit, RUnit)],
                             UPrim xa,
                             URecord [(UPrim xa, RPrim (Num U32)),
                                (UPrim (LU32 (t3_C.acc_C aa)), RPrim (Num U32)), (UUnit, RUnit)],
                             URecord [(UPrim xa, RPrim (Num U32)),
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
       apply (rule conjI)  
        apply (metis (no_types, hide_lams) max_word_max word_Suc_le word_le_less_eq word_not_le)
       apply (rule conjI)
        apply clarsimp
        apply (metis (no_types, hide_lams) max_word_max word_Suc_le word_not_le)
       apply (rule conjI)
        apply (meson min_less_iff_conj word_not_le)
       apply (metis (no_types, hide_lams) add.commute diff_less_mono2 max_word_max unat_mono word_Suc_le word_le_less_eq word_less_nat_alt word_not_le)
      apply (thin_tac "_ \<in> state_rel")
      apply (clarsimp split: atyp.splits type.splits prim_type.splits simp: wa_abs_typing_u_def)
      apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta heap_rel_ptr_w32_meta)
      apply (rule_tac x = \<sigma> in exI; clarsimp?)
      apply (rule conjI; clarsimp?)
      apply (drule_tac p = "t5_C.arr_C v'" and uv = "UAbstract (UWA (TPrim (Num U32)) x12 x13)" in all_heap_rel_ptrD; 
             clarsimp simp: type_rel_simps is_valid_simp heap_simp wa_abs_repr_def val_rel_simps) 
      apply (thin_tac "cogent_function_val_rel _ _")
      apply (thin_tac "upd.uval_typing _ _ _ _ _ _")
      apply (rule_tac x = "TPrim (Num U32)" in exI)
      apply (rule_tac x = "TUnit" in exI)
      apply (rule_tac x = "''elem''" in exI)
      apply (rule_tac x = "''acc''" in exI)
      apply (rule_tac x = "''obsv''" in exI)
      apply (rule_tac x = "{}" in exI)
      apply (rule conjI)
       apply (rule_tac x = "{}" in exI)
       apply (rule upd.u_t_prim'; clarsimp)
      apply (rule_tac x = "{}" in exI; clarsimp)
      apply (rule conjI)
       apply (rule upd.u_t_unit)
      apply (clarsimp simp: \<Xi>_def abbreviatedType1_def wordarray_fold_no_break_0_type_def)
      apply (case_tac "t5_C.to_C v' = b"; clarsimp?)
      apply (case_tac "b < t5_C.to_C v'"; clarsimp)
       apply (case_tac x; clarsimp)
        apply (drule_tac arr = "ptr_val (values_C (heap_WordArray_u32_C sa (t5_C.arr_C v')))" and 
                         len = "SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C sa (t5_C.arr_C v')))" 
                         in upd_wa_foldnb_bod_to_geq_lenD; simp?)
        apply (rule_tac arr = "ptr_val (values_C (heap_WordArray_u32_C sa (t5_C.arr_C v')))" and 
                        len = "SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C sa (t5_C.arr_C v')))" 
                        in upd_wa_foldnb_bod_to_geq_len; simp)
       apply (drule_tac arr = "ptr_val (values_C (heap_WordArray_u32_C sa (t5_C.arr_C v')))" and 
                        len = "SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C sa (t5_C.arr_C v')))" 
                        in upd_wa_foldnb_bod_to_geq_lenD; simp?)
       apply (rule_tac arr = "ptr_val (values_C (heap_WordArray_u32_C sa (t5_C.arr_C v')))" and 
                       len = "SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C sa (t5_C.arr_C v')))" 
                       in upd_wa_foldnb_bod_to_geq_len; simp)
      apply (case_tac "min (t5_C.to_C v') (SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C sa (t5_C.arr_C v')))) \<le> t5_C.frm_C v'")
       apply clarsimp
       apply (case_tac x; clarsimp)
        apply (erule upd_wa_foldnb_bod.elims; clarsimp)
        apply (clarsimp simp: min_def split: if_splits)
         apply (subst upd_wa_foldnb_bod.simps; clarsimp)
        apply (subst upd_wa_foldnb_bod.simps; clarsimp)
       apply (erule upd_wa_foldnb_bod.elims; clarsimp)
       apply (clarsimp simp: min_def split: if_splits)
        apply (subst upd_wa_foldnb_bod.simps; clarsimp)
       apply (subst upd_wa_foldnb_bod.simps; clarsimp)
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
                        FUN_ENUM_mul_def
                        FUN_ENUM_mul_arr_def
                        FUN_ENUM_sum_arr_def
                        FUN_ENUM_wordarray_get_0_def
                        FUN_ENUM_wordarray_length_0_def
                        FUN_ENUM_wordarray_put2_0_def
                        FUN_ENUM_wordarray_fold_no_break_0_def
                        FUN_ENUM_wordarray_get_u32_def
                        FUN_ENUM_wordarray_length_u32_def
                        FUN_ENUM_wordarray_put2_u32_def)
  apply (case_tac x; clarsimp)
   apply (subst upd_wa_foldnb_bod.simps)
   apply clarsimp
   apply (subst upd_wa_foldnb_bod.simps)
   apply clarsimp
   apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta wa_abs_typing_u_def)
   apply (clarsimp split: atyp.splits type.splits prim_type.splits)
   apply (drule_tac p = "t5_C.arr_C v'" and uv = "UAbstract (UWA (TPrim (Num U32)) x12 x13)" in all_heap_rel_ptrD;
          clarsimp simp: wa_abs_repr_def type_rel_simps is_valid_simp)
   apply (thin_tac "upd.uval_typing _ _ _ _ _ _")
   apply (thin_tac "is_valid_WordArray_u32_C _ _")
   apply (thin_tac "val_rel _ _")
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
thm corres_sum corres_app_concrete

lemma 
" \<And>v' i \<gamma> \<Gamma> \<sigma> s.
        \<lbrakk>f_C v' = FUN_ENUM_mul; i < length \<gamma>; val_rel (\<gamma> ! i) v';
         \<Gamma> ! i =
         option.Some
          (prod.fst
            (prod.snd
              (assoc_lookup
                [(''wordarray_get_0'', wordarray_get_0_type), (''wordarray_length_0'', wordarray_length_0_type),
                 (''wordarray_put2_0'', wordarray_put2_0_type), (''wordarray_fold_no_break_0'', wordarray_fold_no_break_0_type),
                 (''wordarray_get_u32'', Generated_TypeProof.wordarray_get_u32_type),
                 (''wordarray_length_u32'', Generated_TypeProof.wordarray_length_u32_type),
                 (''wordarray_put2_u32'', Generated_TypeProof.wordarray_put2_u32_type), (''mul'', Generated_TypeProof.mul_type),
                 (''mul_arr'', Generated_TypeProof.mul_arr_type), (''sum'', Generated_TypeProof.sum_type),
                 (''sum_arr'', Generated_TypeProof.sum_arr_type)]
                ([], TUnit, TUnit) ''wordarray_fold_no_break_0'')))\<rbrakk>
        \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr)
             (App (AFun ''wordarray_fold_no_break_0'' []) (Var i)) (do x <- wordarray_fold_no_break_0' v';
      gets (\<lambda>s. x)
   od)
             \<xi>1 \<gamma>
             (assoc_lookup
               [(''wordarray_get_0'', wordarray_get_0_type), (''wordarray_length_0'', wordarray_length_0_type),
                (''wordarray_put2_0'', wordarray_put2_0_type), (''wordarray_fold_no_break_0'', wordarray_fold_no_break_0_type),
                (''wordarray_get_u32'', Generated_TypeProof.wordarray_get_u32_type),
                (''wordarray_length_u32'', Generated_TypeProof.wordarray_length_u32_type),
                (''wordarray_put2_u32'', Generated_TypeProof.wordarray_put2_u32_type), (''mul'', Generated_TypeProof.mul_type),
                (''mul_arr'', Generated_TypeProof.mul_arr_type), (''sum'', Generated_TypeProof.sum_type),
                (''sum_arr'', Generated_TypeProof.sum_arr_type)]
               ([], TUnit, TUnit))
             \<Gamma> \<sigma> s"
  
  by (drule_tac ?\<Gamma>' = \<Gamma> and \<sigma> = \<sigma> and s = s in upd_C_wordarray_fold_no_break_corres[simplified]; simp add: \<Xi>_def)
 *)
(*
High level:
  * Cogent is a language which eases proving things
    (ASPLOS Paper: we verified Cogent shallow embedding up to a function spec and it was easy)
  * Can't do everything in Cogent
    (No iteration or recursion,
     linear type system enforces restrictions which are too strict sometimes
        TODO: 
          Find examples:
            - vnode pointers in FS file tables esp. if things like dup2 or Linux fork semantic are
              implemented (i.e. multiple references to the same vnode)
            -
          Note here that the C foreign functions  have to respect the type system + frame
          Easy in C but hard/impossible in Cogent due to linear types but still respects type system and frame
    ) 
  * We have an FFI to C
    (Introduced in ICFP paper with no examples or verification work)
  * Amortise C verification cost
    (Intuitive because of ADT reuse, assuming the ssumptions about the C functions are all provable in a reasonable time.
    Note it is not only the usual correctness assumptions but also frame conditions)
  * If we verify Cogent bits and verify C bits then the FFI tells us how to put everything together
    so the entire system is verified
    (FFI specified some interface which gets you from C all the way up to the shallow embedding
     The interface we defined was never tested
     What we did before?
        Here is a Cogent program that uses a bunch of C. The FFI defines how to compose the Cogent and
          the C to get an overall proof of correctness. Note however, that this FFI assumes that it
          has access to a bunch of abstraction functions on types, values, representations, etc, that
          relate C \<rightarrow> Update \<rightarrow> Value_m \<rightarrow> Value_p \<rightarrow> Shallow and that the abstraction functions respect
          a bunch of assumptions..
        Can we actually provide these and discharge the assumptions in order to instantiate the FFI?
          - abs typing that satisfy locale assumptions
          - abstractions for abstract values in the update, value and shallow semantics
          - value relations between C and update, update and value, and value and shallow
          - abstractions for the abstract functions in the update, value and shallow semantics
          - proofs for preservation in the update and value semantics for each abstract function
          - proofs for mono renaming for each abstract function
          - proofs for correspondence between C and update, update and value, and value and shallow
          - proofs that the abstraction for the abstract functions in the value semantics execute
            if the the abstraction for the corresponding abstract function in the update semantics
            executes



  * Verified library for word arrays
      * BilbyFS, Ext2FS
*)
thm corres_def corres_app_concrete corres_app_abstract
thm wordarray_fold_no_break_0'_def hoare_add_K dispatch_t4'_def

abbreviation "mk_urecord xs \<equiv> URecord (map (\<lambda>x. (x, upd.uval_repr x)) xs)"
definition "foldmap_measure i end \<equiv> unat end - unat i"
definition "foldmap_bounds frm to len i e 
  \<equiv> frm \<le> i \<and> e = min to len \<and> (frm < e \<longrightarrow> i \<le> e) \<and> ((\<not>(frm < e)) \<longrightarrow> frm = i)"
definition "foldmap_inv foldmap \<xi>' \<sigma> p frm i f acc obsv r \<sigma>' res s' res'
  \<equiv> foldmap \<xi>' \<sigma> p frm i f acc obsv r (\<sigma>', res) \<and> val_rel res res' \<and> (\<sigma>', s') \<in> state_rel"
definition "foldmap_inv_stat obsv obsv' \<equiv> val_rel obsv obsv'"
lemma state_rel_ex: 
  "\<exists>\<sigma>. (\<sigma>, s) \<in> state_rel"
  apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_def heap_rel_ptr_w32_def)
  apply (rule_tac x = "\<lambda>_. option.None" in exI)
  apply clarsimp
  done

lemma whileLoop_add_invI:
  assumes "\<lbrace> P \<rbrace> whileLoop_inv c b init I (measure M) \<lbrace> Q \<rbrace>!"
  shows "\<lbrace> P \<rbrace> whileLoop c b init \<lbrace> Q \<rbrace>!"
  by (metis assms whileLoop_inv_def)

lemma validNF_select_UNIV:
  "\<lbrace>\<lambda>s. \<forall>x. Q x s\<rbrace> select UNIV \<lbrace>Q\<rbrace>!"
  apply (subst select_UNIV_unknown)
  apply (rule validNF_unknown)
  done

lemma
  "cogent_function_val_rel f (sint FUN_ENUM_mul) \<Longrightarrow> 
    \<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr) 
      (App (uvalfun_to_exprfun f) (Var 0)) (do ret <- dispatch_t4' FUN_ENUM_mul x'; gets (\<lambda>s. ret) od) 
      \<xi>_0 [x] \<Xi> [option.Some (foldmap_funarg_type ''wordarray_fold_no_break_0'')] \<sigma> s"
  apply (clarsimp simp: cogent_function_val_rel untyped_func_enum_defs)
  apply (rule corres_app_concrete[simplified]; simp?)
  apply (subgoal_tac "foldmap_funarg_type ''wordarray_fold_no_break_0'' = prod.fst (prod.snd Generated_TypeProof.mul_type)")
   apply (monad_eq simp: dispatch_t4'_def FUN_ENUM_mul_def unknown_bind_ignore \<Xi>_def)
   apply (rule corres_mul; simp)
  apply (clarsimp simp: \<Xi>_def wordarray_fold_no_break_0_type_def mul_type_def abbreviated_type_defs)
  done

lemma \<Xi>_wordarray_fold_no_break_0:
  "\<Xi> ''wordarray_fold_no_break_0'' = wordarray_fold_no_break_0_type"
  by (clarsimp simp: \<Xi>_def)

lemma fold_dispatch_wp:
  "\<lbrakk>proc_ctx_wellformed \<Xi>; upd.proc_env_matches_ptrs \<xi>0 \<Xi>;
    wa_abs_typing_u (UWA (TPrim (Num U32)) len arr) ''WordArray'' [TPrim (Num U32)] (Boxed ReadOnly ptrl) r w \<sigma>;
    \<sigma> p = option.Some (UAbstract (UWA (TPrim (Num U32)) len arr));
    upd.uval_typing \<Xi> \<sigma> acc (foldmap_acc_type ''wordarray_fold_no_break_0'') ra wa;
    upd.uval_typing \<Xi> \<sigma> obsv (foldmap_obsv_type ''wordarray_fold_no_break_0'') ro {};
    wa \<inter> r = {}; wa \<inter> ro = {}; p \<notin> wa;
    (\<Xi>, [], [option.Some (foldmap_funarg_type ''wordarray_fold_no_break_0'')] \<turnstile> 
    (App f (Var 0)) : (foldmap_funret_type ''wordarray_fold_no_break_0''));
    \<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow>
      update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr) 
        (App f (Var 0)) (do ret <- dispatch_t4' f_num x'; gets (\<lambda>s. ret) od) 
        \<xi>0 [x] \<Xi> [option.Some (foldmap_funarg_type ''wordarray_fold_no_break_0'')] \<sigma> s\<rbrakk> \<Longrightarrow>
    \<lbrace>\<lambda>sa. (a', n') = (a, n) \<and> n < e \<and>
      (\<exists>\<sigma>' res x v. args = t3_C.elem_C_update (\<lambda>_. v) a \<and>
        \<sigma>' (arr + size_of_num_type U32 * n) = option.Some x \<and> val_rel x v \<and>
      foldmap_inv upd_wa_foldnb_bod \<xi>0 \<sigma> p frm n f acc obsv (ra \<union> ro) \<sigma>' res sa (t3_C.acc_C args)) \<and>
      foldmap_bounds frm to len n e \<and> foldmap_inv_stat obsv (t3_C.obsv_C args)\<rbrace>
      dispatch_t4' f_num args 
    \<lbrace>\<lambda>ret sb. (\<exists>\<sigma>' res.
        foldmap_inv upd_wa_foldnb_bod \<xi>0 \<sigma> p frm (n + 1) f acc obsv (ra \<union> ro) \<sigma>' res sb ret) \<and>
      foldmap_inv_stat obsv (t3_C.obsv_C args) \<and> foldmap_bounds frm to len (n + 1) e \<and> 
      foldmap_measure (n + 1) to < foldmap_measure n' to\<rbrace>!"
  apply (subst validNF_def)
  apply (clarsimp simp: \<Xi>_wordarray_fold_no_break_0 wordarray_fold_no_break_0_type_def abbreviated_type_defs)
  apply (subst valid_def)
  apply (subst no_fail_def)
  apply clarsimp
  apply (subst all_imp_conj_distrib[symmetric])
  apply (clarsimp simp: foldmap_inv_def)
  apply (rename_tac sa \<sigma>' res x v)
  apply (erule_tac x = "mk_urecord [x, res, obsv]" in allE)
  apply (erule_tac x = args in allE)
  apply (erule impE)
   apply (subst val_rel_simp; simp add: foldmap_inv_stat_def)
  apply (erule_tac x = \<sigma>' in allE)
  apply (erule_tac x = sa in allE)
  apply (clarsimp simp: corres_def)
  apply (frule_tac t = "TPrim (Num U32)" in upd_wa_foldnb_bod_preservation[rotated 2]; simp?; clarsimp?)
  apply (rename_tac r' w')
  apply (subgoal_tac "upd.matches_ptrs \<Xi> \<sigma>' [(mk_urecord [x, res, obsv])]
      [option.Some (foldmap_funarg_type ''wordarray_fold_no_break_0'')] (r' \<union> ro) w'")
   apply (clarsimp simp: \<Xi>_wordarray_fold_no_break_0 wordarray_fold_no_break_0_type_def abbreviated_type_defs)
    apply (erule impE, blast)
   apply clarsimp
   apply (rename_tac ret sb)
   apply (erule_tac x = ret in allE)
   apply (erule_tac x = sb in allE)
   apply clarsimp
   apply (drule upd.preservation[where \<tau>s = "[]" and K = "[]", simplified]; simp?)
   apply clarsimp
   apply (rename_tac \<sigma>'' res' rb wb)
   apply (clarsimp simp: foldmap_bounds_def)
   apply (case_tac "frm < to \<and> frm < len"; clarsimp)
   apply (frule wa_abs_typing_u_elims(5))
   apply (erule_tac x = n in allE; clarsimp)
   apply (frule_tac p = "arr + 4 * n" in valid_ptr_not_in_frame_same; simp?)
    apply (drule_tac x = "arr + 4 * n" and S' = r in orthD2; simp?)
    apply (drule_tac t = U32 in  wa_abs_typing_u_elims(2)[where \<tau>s = "[_]", simplified]; simp)
    apply blast
   apply clarsimp
   apply (drule_tac t = U32 and arr = arr and len = len and r' = res' 
      in upd_wa_foldnb_bod_step; simp?; clarsimp?)
    apply (rule conjI)
     apply (drule_tac p = p in readonly_not_in_frame; simp?)
    apply (subst Int_Un_distrib2)+
    apply clarsimp
    apply (rule conjI)
     apply (rule disjointI)
     apply (frule_tac p = x and r = ra and w = wa in upd.uval_typing_valid(1)[rotated 1]; simp?)
     apply clarsimp
     apply (drule_tac p = y in readonly_not_in_frame; simp?)
     apply (drule upd.uval_typing_pointers_noalias; blast)
    apply (rule conjI)
     apply (rule disjointI)
     apply (frule_tac p = x and r = ro and w = "{}" in upd.uval_typing_valid(1)[rotated 1]; simp?)
     apply clarsimp
     apply (drule_tac p = y in readonly_not_in_frame; simp?)
     apply blast
    apply (rule disjointI)
    apply (frule wa_abs_typing_u_elims(5))
    apply clarsimp
    apply (erule_tac x = i in allE; clarsimp)
    apply (drule_tac p = "arr + 4 * i" in readonly_not_in_frame; simp?)
    apply (drule wa_abs_typing_u_elims(2); clarsimp)
    apply blast
   apply (rule conjI)
    apply (rule_tac x = \<sigma>'' in exI)
    apply (rule_tac x = res' in exI; simp)
   apply (frule_tac a = n and k = to in less_is_non_zero_p1)
   apply (drule unatSuc2; clarsimp simp: word_less_nat_alt word_le_nat_alt foldmap_measure_def)
   apply linarith
  apply (clarsimp simp: \<Xi>_wordarray_fold_no_break_0 wordarray_fold_no_break_0_type_def abbreviated_type_defs)
  apply (rule upd.matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
   apply (rule upd.u_t_struct; simp?)
   apply (rule upd.u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
     apply (subst (asm) val_rel_word; clarsimp)
     apply (rule upd.u_t_prim'; clarsimp)
    apply (rule upd.u_t_r_cons1[where r' = ro and w' = "{}", simplified]; simp?)
      apply (drule_tac u = obsv in upd.uval_typing_frame(1); simp?)
       apply blast
      apply (rule upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
       apply (rule upd.u_t_r_empty)
      apply (drule_tac v = obsv in upd.type_repr_uval_repr(1); simp)
     apply (rule disjointI)
     apply (frule_tac p = y and r = ro in upd.uval_typing_valid(1)[where w = "{}", simplified]; simp?)
     apply clarsimp
     apply (drule_tac p = y in readonly_not_in_frame; simp?)
     apply (drule_tac x = y and S' = ro in orthD2; simp?)
    apply (drule_tac v = res in upd.type_repr_uval_repr(1); simp)
  apply (subst (asm) val_rel_word; clarsimp)
  apply (rule upd.matches_ptrs_empty[where \<tau>s = "[]", simplified])
  done


lemma upd_C_wordarray_fold_no_break_corres':
  "\<lbrakk>upd.proc_env_matches_ptrs \<xi>0 \<Xi>; i < length \<gamma>; val_rel (\<gamma> ! i) v'; 
    \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_fold_no_break_0'')));
    \<gamma> ! i = URecord fs; f = prod.fst (fs ! 3); obsv = prod.fst (fs ! 5);
    upd.uval_typing \<Xi> \<sigma> obsv (foldmap_obsv_type ''wordarray_fold_no_break_0'') ro {};
    (\<Xi>, [], [option.Some (foldmap_funarg_type ''wordarray_fold_no_break_0'')] \<turnstile> 
    (App (uvalfun_to_exprfun f) (Var 0)) : (foldmap_funret_type ''wordarray_fold_no_break_0''));
    \<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr) 
      (App (uvalfun_to_exprfun f) (Var 0)) (do ret <- dispatch_t4' (t5_C.f_C v') x'; gets (\<lambda>s. ret) od) 
      \<xi>0 [x] \<Xi> [option.Some (foldmap_funarg_type ''wordarray_fold_no_break_0'')] \<sigma> s\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr)
         (App (AFun ''wordarray_fold_no_break_0'' []) (Var i)) (do x <- main_pp_inferred.wordarray_fold_no_break_0' v';
gets (\<lambda>s. x)
                                                                od)
         \<xi>1 \<gamma> \<Xi>  \<Gamma>' \<sigma> s"
  apply (rule absfun_corres; simp)
  apply (clarsimp simp: abs_fun_rel_def'; rename_tac r w)
  apply (thin_tac "\<Gamma>' ! i = _")
  apply (subst \<xi>1.simps)
  apply (subst (asm) val_rel_simp; clarsimp)
  apply (subst (asm) val_rel_ptr_def; clarsimp)
  apply (subst (asm) val_rel_fun_tag)
  apply (subst (asm) val_rel_word)
  apply (subst (asm) val_rel_word)
  apply (clarsimp simp: upd_wa_foldnb_def wordarray_fold_no_break_0'_def)
  apply (rename_tac pwa_rep frm_rep to_rep f_rep acc a_rep o_rep wa_rep)
  apply (erule upd.u_t_recE; clarsimp)
  apply (clarsimp simp: \<Xi>_wordarray_fold_no_break_0 wordarray_fold_no_break_0_type_def abbreviated_type_defs)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_p_absE; clarsimp)
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule upd.u_t_primE)+
  apply (drule_tac t = "lit_type _" in sym)+
  apply clarsimp
  apply (erule upd.u_t_r_consE; clarsimp)+
  apply (erule upd.u_t_r_emptyE; clarsimp)
  apply (frule upd.tfun_no_pointers(1))
  apply (frule upd.tfun_no_pointers(2))
  apply clarsimp
  apply (rename_tac acc ra wa ro' wo)
  apply (drule_tac x = obsv in upd.uval_typing_unique_ptrs(1); simp?)
  apply clarsimp
  apply (subst unknown_bind_ignore)+
  apply (clarsimp simp: join_guards)
  apply wp
      apply (clarsimp simp: unknown_bind_ignore split: prod.split)
      apply (rename_tac var e)
      apply (rule_tac M = "\<lambda>((_, i), _). foldmap_measure i (t5_C.to_C v')" and 
      I = "\<lambda>(a, b) s. (\<exists>\<sigma>' res. foldmap_inv upd_wa_foldnb_bod \<xi>0 \<sigma> (ptr_val (t5_C.arr_C v'))
          (t5_C.frm_C v') b (uvalfun_to_exprfun f) acc obsv (ra \<union> ro) \<sigma>' res s (t3_C.acc_C a)) \<and>
          foldmap_inv_stat obsv (t3_C.obsv_C a) \<and>
          foldmap_bounds (t5_C.frm_C v') (t5_C.to_C v') len b e" in whileLoop_add_invI; simp?)
      apply (wp; clarsimp simp: unknown_bind_ignore split: prod.splits)
          apply (rename_tac sa a n args a' n')
          apply (rule_tac a = a and wa = wa and ra = ra and ro = ro and w = "{}" and r = r and
            ptrl = undefined in fold_dispatch_wp[rotated 2]; simp?)
             apply (clarsimp simp: \<Xi>_wordarray_fold_no_break_0 wordarray_fold_no_break_0_type_def abbreviated_type_defs)+
         apply wp
        apply wp
       apply clarsimp
       apply (rename_tac args j \<sigma>' res)
       apply (clarsimp simp: foldmap_bounds_def foldmap_inv_def)
       apply (frule wa_abs_typing_u_elims(5))
       apply (erule_tac x = j in allE; clarsimp)
       apply (drule_tac acc = acc and obsv = obsv and rb = ra and wb = wa and rc = ro
          in upd_wa_foldnb_bod_preservation; simp?; clarsimp?)
       apply (frule_tac p = "ptr_val (t5_C.arr_C v')" in valid_ptr_not_in_frame_same; simp?)
       apply (drule_tac p = "arr + 4 * j" in valid_ptr_not_in_frame_same; simp?)
        apply (drule_tac x = "arr + 4 * j" and S = wa and S' = r in orthD2; simp?)
        apply (drule wa_abs_typing_u_elims(2); clarsimp)
        apply blast
       apply (thin_tac "_ \<in> state_rel")
       apply (rule conjI)
        apply (rule_tac x = \<sigma>' in exI)
        apply (rule_tac x = res in exI)
        apply (rule_tac x = "UPrim x" in exI)
        apply clarsimp
        apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_w32_meta heap_rel_ptr_meta)
        apply (rotate_tac -1)
        apply (drule_tac p = "Ptr(arr + 4 * j)" in all_heap_rel_ptrD; simp?)
         apply (clarsimp simp: type_rel_simp)
        apply (rule_tac x = "heap_w32 s (PTR(32 word) (arr + 4 * j))" in exI)
        apply (drule_tac p = "t5_C.arr_C v'" in all_heap_rel_ptrD; simp?)
         apply (clarsimp simp: type_rel_simp wa_abs_repr_def)
        apply (clarsimp simp: val_rel_WordArray_u32_C_def ptr_add_def heap_simp mult.commute)
       apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_w32_meta heap_rel_ptr_meta)
       apply (rotate_tac -1)
       apply (drule_tac p = "Ptr(arr + 4 * j)" in all_heap_rel_ptrD; simp?)
        apply (clarsimp simp: type_rel_simp)
       apply (drule_tac p = "t5_C.arr_C v'" in all_heap_rel_ptrD; simp?)
        apply (clarsimp simp: type_rel_simp wa_abs_repr_def)
       apply (clarsimp simp: is_valid_simp heap_simp val_rel_WordArray_u32_C_def ptr_add_def mult.commute)
      apply (rule conjI)
       apply (erule u_t_primtE; clarsimp)
      apply (rule conjI)
       apply (drule_tac v = obsv in upd.type_repr_uval_repr(1); simp?)
      apply (rule conjI)
       apply (drule wa_abs_typing_u_elims(5); simp)
      apply (rule conjI)
       apply (erule u_t_funafuntE; clarsimp)
      apply (rename_tac x' j \<sigma>' res)
      apply (rule_tac x = \<sigma>' in exI)
      apply (rule_tac x = res in exI)
      apply (clarsimp simp: foldmap_inv_def)
      apply (rule_tac x = "foldmap_acc_type ''wordarray_fold_no_break_0''" in exI)
      apply (rule_tac x = "foldmap_obsv_type ''wordarray_fold_no_break_0''" in exI)
      apply (rule_tac x = "''elem''" in exI)
      apply (rule_tac x = "''acc''" in exI)
      apply (rule_tac x = "''obsv''" in exI)
      apply (clarsimp simp: \<Xi>_wordarray_fold_no_break_0 wordarray_fold_no_break_0_type_def abbreviated_type_defs)
      apply (rule_tac x = ra in exI)
      apply (rule conjI)
       apply (intro exI, assumption)
      apply (rule_tac x = ro in exI)
      apply (rule conjI, simp)
      apply (unfold foldmap_bounds_def)
      apply (erule conjE)+
      apply (case_tac "t5_C.frm_C v' < e")
       apply (erule impE, assumption)
       apply (thin_tac "_ \<longrightarrow> _")
       apply clarsimp
       apply (case_tac "j < t5_C.to_C v'"; clarsimp)
       apply (rule upd_wa_foldnb_bod_to_geq_len; simp?)
      apply (erule impE, assumption)
      apply (thin_tac "_ \<longrightarrow> _")
      apply clarsimp
      apply (erule upd_wa_foldnb_bod.elims; clarsimp)
      apply (case_tac "t5_C.frm_C v' < t5_C.to_C v'"; subst upd_wa_foldnb_bod.simps; clarsimp)
     apply wp
    apply wp
   apply (rule validNF_select_UNIV)
  apply (clarsimp simp: foldmap_inv_stat_def)
  apply (clarsimp simp: order.strict_implies_order)
  apply (clarsimp simp: foldmap_inv_def state_rel_def heap_rel_def heap_rel_ptr_meta)
  apply (frule_tac p = "t5_C.arr_C v'" in all_heap_rel_ptrD; simp?)
   apply (clarsimp simp: type_rel_simp wa_abs_repr_def)
  apply (clarsimp simp: is_valid_simp val_rel_WordArray_u32_C_def heap_simp)
  apply (rule conjI; clarsimp)
   apply (rule conjI)
    apply (rule_tac x = \<sigma> in exI)
    apply (rule_tac x = acc in exI)
    apply clarsimp
    apply (drule wa_abs_typing_u_elims(5))
    apply (subst upd_wa_foldnb_bod.simps; clarsimp)
    apply (rule conjI; clarsimp)
    apply (rename_tac j)
    apply (erule_tac x = j in allE; clarsimp)
   apply (subst min_def)
   apply (subst (asm) not_le[symmetric])+
   apply (subst if_not_P; simp?)
  apply (rule conjI)
   apply (rule_tac x = \<sigma> in exI)
   apply (rule_tac x = acc in exI)
   apply clarsimp
   apply (drule wa_abs_typing_u_elims(5))
   apply (subst upd_wa_foldnb_bod.simps; clarsimp)
   apply (rule conjI; clarsimp)
   apply (rename_tac j)
   apply (erule_tac x = j in allE; clarsimp)
  apply (subst min_def)
  apply (clarsimp simp: not_le)
  done

lemma \<Xi>_wordarray_map_no_break_0:
  "\<Xi> ''wordarray_map_no_break_0'' = wordarray_map_no_break_0_type"
  by (clarsimp simp: \<Xi>_def)

lemma map_dispatch_wp:
  "\<lbrakk>proc_ctx_wellformed \<Xi>; upd.proc_env_matches_ptrs \<xi>0 \<Xi>;
    wa_abs_typing_u (UWA (TPrim (Num U32)) len arr) ''WordArray'' [TPrim (Num U32)] (Boxed Writable ptrl) r w \<sigma>;
    \<sigma> p = option.Some (UAbstract (UWA (TPrim (Num U32)) len arr));
    upd.uval_typing \<Xi> \<sigma> acc (foldmap_acc_type ''wordarray_map_no_break_0'') ra wa;
    upd.uval_typing \<Xi> \<sigma> obsv (foldmap_obsv_type ''wordarray_map_no_break_0'') ro {}; wa \<inter> r = {}; p \<notin> w;
    p \<notin> r; w \<inter> wa = {}; w \<inter> (ra \<union> ro) = {}; wa \<inter> ro = {}; p \<notin> wa; p \<notin> ra; p \<notin> ro; p = ptr_val p';
    (\<Xi>, [], [option.Some (foldmap_funarg_type ''wordarray_map_no_break_0'')] \<turnstile> 
    (App f (Var 0)) : (foldmap_funret_type ''wordarray_map_no_break_0''));
    \<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow>
      update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr) 
        (App f (Var 0)) (do ret <- dispatch_t8' f_num x'; gets (\<lambda>s. ret) od) 
        \<xi>0 [x] \<Xi> [option.Some (foldmap_funarg_type ''wordarray_map_no_break_0'')] \<sigma> s\<rbrakk> \<Longrightarrow>
    \<lbrace>\<lambda>sa. (a', n') = (a, n) \<and> n < e \<and>
      (\<exists>\<sigma>' res x v. args = t6_C.elem_C_update (\<lambda>_. v) a \<and>
        \<sigma>' (arr + size_of_num_type U32 * n) = option.Some x \<and> val_rel x v \<and>
      foldmap_inv upd_wa_mapAccumnb_bod \<xi>0 \<sigma> p frm n f acc obsv (ra \<union> ro) \<sigma>' res sa (t10_C p' (t6_C.acc_C args))) \<and>
      foldmap_bounds frm to len n e \<and> foldmap_inv_stat obsv (t6_C.obsv_C args)\<rbrace>
      dispatch_t8' f_num args 
     \<lbrace>\<lambda>ret sb. (\<exists>\<sigma>' res. 
        foldmap_inv upd_wa_mapAccumnb_bod \<xi>0 \<sigma> p frm (n + 1) f acc obsv (ra \<union> ro) \<sigma>' res 
          (heap_w32_update (\<lambda>x a. if a = values_C (heap_WordArray_u32_C sb p') +\<^sub>p uint n 
            then t7_C.p1_C ret else x a) sb) (t10_C p' (t7_C.p2_C ret))) \<and>
        foldmap_inv_stat obsv (t6_C.obsv_C args) \<and>
        foldmap_bounds frm to len (n + 1) e \<and>
        foldmap_measure (n + 1) to < foldmap_measure n' to \<and>
        is_valid_WordArray_u32_C sb p' \<and>
        is_valid_w32 sb (values_C (heap_WordArray_u32_C sb p') +\<^sub>p uint n)\<rbrace>!"
  apply (subst validNF_def)
  apply (clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (subst valid_def)
  apply (subst no_fail_def)
  apply clarsimp
  apply (subst all_imp_conj_distrib[symmetric])
  apply (clarsimp simp: foldmap_inv_def)
  apply (rename_tac sa \<sigma>' res x v)
  apply (frule upd_wa_mapAccumnb_bod_preservation'; simp?)
  apply clarsimp
  apply (rename_tac racc)
  apply (erule_tac x = "mk_urecord [x, racc, obsv]" in allE)
  apply (erule_tac x = args in allE)
  apply clarsimp
  apply (erule impE)
   apply (clarsimp simp: val_rel_simp foldmap_inv_stat_def)
  apply (erule_tac x = \<sigma>' in allE)
  apply (erule_tac x = sa in allE)
  apply (clarsimp simp: corres_def)
  apply (frule_tac t = "TPrim (Num U32)" in upd_wa_mapAccumnb_bod_preservation; simp?; clarsimp?)
    apply (subst Int_Un_distrib2; clarsimp)
    apply (subst (asm) Int_Un_distrib; clarsimp)
   apply (subst (asm) Int_Un_distrib; clarsimp)
  apply (rename_tac r' w')
  apply (erule upd.u_t_recE; clarsimp)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_r_emptyE; clarsimp)
  apply (rename_tac w' rb wb racc rc wc)
  apply (erule upd.u_t_p_con_wrE)
  apply (drule_tac t = "RCon _ _" in sym; clarsimp)
  apply (frule_tac p = p in valid_ptr_not_in_frame_same; simp?)
  apply clarsimp
  apply (frule_tac p = p in readonly_not_in_frame; simp?)
  apply (subst (asm) insert_ident; clarsimp)
  apply (rename_tac wb)
  apply (subgoal_tac "upd.matches_ptrs \<Xi> \<sigma>' [(mk_urecord [x, racc, obsv])]
      [option.Some (foldmap_funarg_type ''wordarray_map_no_break_0'')] (rc \<union> ro) wc")
   apply (clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs)
   apply (erule impE, blast)
   apply clarsimp
   apply (rename_tac ret sb)
   apply (erule_tac x = ret in allE)
   apply (erule_tac x = sb in allE)
   apply clarsimp
   apply (drule upd.preservation[where \<tau>s = "[]" and K = "[]", simplified]; simp?)
   apply clarsimp
   apply (rename_tac \<sigma>'' res' r' w')
   apply (erule u_t_rectE; clarsimp)
   apply (erule u_t_r_contE; clarsimp)
   apply (erule u_t_r_contE; clarsimp)
   apply (erule u_t_r_contE; clarsimp)
   apply (rename_tac x' rd wd racc' r' w')
   apply (frule_tac v = x' in upd.tprim_no_pointers(1); clarsimp)
   apply (frule_tac v = x' in upd.tprim_no_pointers(2); clarsimp)
   apply (clarsimp simp: foldmap_bounds_def)
   apply (case_tac "frm < to \<and> frm < len"; clarsimp)
   apply (thin_tac "wa_abs_typing_u _ _ _ _ _ _ _")
   apply (drule_tac t = U32 and arr = arr and len = len and v' = x' and r' = racc'
      in upd_wa_mapAccumnb_bod_step; simp?; clarsimp?)
      apply (drule wa_abs_typing_u_elims(6); simp?)
     apply (subst Int_Un_distrib2)+
     apply clarsimp
     apply (rule conjI)
      apply (rule disjointI)
      apply (rename_tac y y')
      apply (frule_tac p = y and r = ra and w = wa in upd.uval_typing_valid(1)[rotated 1]; simp?)
      apply clarsimp
      apply (drule_tac p = y' in readonly_not_in_frame; simp?)
      apply (drule_tac x = y' and S' = "ra \<union> ro" in orthD2; simp?)
      apply (drule upd.uval_typing_pointers_noalias)
      apply (drule_tac x = y' and S = ra and S' = wa in orthD1; simp?)
     apply (rule conjI)
      apply (rule disjointI)
      apply (rename_tac y y')
      apply (frule_tac p = y and r = ro and w = "{}" in upd.uval_typing_valid(1)[rotated 1]; simp?)
      apply clarsimp
      apply (drule_tac p = y' in readonly_not_in_frame; simp?)
      apply blast
     apply (drule wa_abs_typing_u_elims(3); clarsimp)
    apply (drule_tac v = x' in upd.type_repr_uval_repr(1); simp)
    apply (drule_tac v = racc' in upd.type_repr_uval_repr(1); simp)
   apply (thin_tac "_ \<in> state_rel")
   apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta heap_rel_ptr_w32_meta)
   apply (frule_tac p = p and \<sigma> = \<sigma>' in valid_ptr_not_in_frame_same; simp?)
   apply (drule_tac p = "arr + 4 * n" and \<sigma> = \<sigma>' in valid_ptr_not_in_frame_same; simp?)
    apply (drule_tac x = "arr + 4 * n" and S' = wc in orthD1; simp?)
    apply (drule wa_abs_typing_u_elims(3); clarsimp)
    apply (rule_tac x = n in exI; clarsimp)
   apply (frule_tac p = p' in all_heap_rel_ptrD; simp?)
    apply (clarsimp simp: type_rel_simp wa_abs_repr_def)
   apply (frule_tac p = "values_C (heap_WordArray_u32_C sb p') +\<^sub>p uint n" and uv = x in all_heap_rel_ptrD; simp?)
     apply (clarsimp simp: val_rel_simp heap_simp)
    apply (clarsimp simp: type_rel_simp val_rel_simp)
   apply (rule conjI)
    apply (rule_tac x = "\<sigma>''(arr + 4 * n \<mapsto> x')" in exI)
    apply (rule_tac x = "mk_urecord [UPtr (ptr_val p') (RCon ''WordArray'' [RPrim (Num U32)]), racc']" in exI)
    apply clarsimp
    apply (rule conjI)
     apply (clarsimp simp: val_rel_simp)
    apply (clarsimp simp: heap_simp is_valid_simp)
    apply (drule_tac upd_h = "(heap_w32_update 
      (\<lambda>x a. if a = values_C (heap_WordArray_u32_C sb p') +\<^sub>p uint n then t7_C.p1_C ret else x a) sb)" and
      uv = x and uv' = x' and x = "values_C (heap_WordArray_u32_C sb p') +\<^sub>p uint n"
      in all_heap_rel_updE; simp?; clarsimp?)
       apply (clarsimp simp: val_rel_simp)
      apply (drule_tac v = x' in upd.type_repr_uval_repr(1); simp add: val_rel_simp)
     apply (clarsimp simp: val_rel_simp type_rel_simp)
    apply (drule_tac upd_h = "(heap_w32_update 
      (\<lambda>x a. if a = values_C (heap_WordArray_u32_C sb p') +\<^sub>p uint n then t7_C.p1_C ret else x a) sb)" and
      uv = x and uv' = x' and x = "values_C (heap_WordArray_u32_C sb p') +\<^sub>p uint n"
      in all_heap_rel_updE; simp?; clarsimp?)
       apply (clarsimp simp: val_rel_simp)
      apply (drule_tac v = x' in upd.type_repr_uval_repr(1); simp add: val_rel_simp)
     apply (rule conjI)
      apply (clarsimp simp: val_rel_simp)
     apply (cut_tac p = pa and q = "values_C (heap_WordArray_u32_C sb p') +\<^sub>p uint n" in ptr_val_inj)
     apply clarsimp
    apply (clarsimp simp: ptr_add_def mult.commute val_rel_simp)
   apply (clarsimp simp: is_valid_simp)
   apply (frule_tac a = n and k = to in less_is_non_zero_p1)
   apply (drule unatSuc2; clarsimp simp: word_less_nat_alt word_le_nat_alt foldmap_measure_def)
   apply linarith
  apply (clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (rule upd.matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
   apply (rule upd.u_t_struct; simp?)
   apply (rule upd.u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
     apply (subst (asm) val_rel_word; clarsimp)
     apply (rule upd.u_t_prim'; clarsimp)
    apply (rule upd.u_t_r_cons1[where r' = ro and w' = "{}", simplified]; simp?)
     apply (drule_tac u = obsv in upd.uval_typing_frame(1); simp?)
      apply blast
     apply (rule upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (rule upd.u_t_r_empty)
     apply (drule_tac v = obsv in upd.type_repr_uval_repr(1); simp)
    apply (rule disjointI)
    apply (frule_tac p = y and r = ro in upd.uval_typing_valid(1)[where w = "{}", simplified]; simp?)
    apply clarsimp
    apply (drule_tac p = y in readonly_not_in_frame; simp?)
    apply (drule_tac x = y and S' = ro in orthD2; simp?)
    apply (drule_tac x = y and S' = "ra \<union> ro" in orthD2; simp?)
   apply (subst (asm) val_rel_word; clarsimp)
  apply (rule upd.matches_ptrs_empty[where \<tau>s = "[]", simplified])
  done

lemma upd_C_wordarray_map_no_break_corres':
  "\<lbrakk>upd.proc_env_matches_ptrs \<xi>0 \<Xi>; i < length \<gamma>; val_rel (\<gamma> ! i) v';
    \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_map_no_break_0'')));
    \<gamma> ! i = URecord fs; f = prod.fst (fs ! 3); obsv = prod.fst (fs ! 5);
    upd.uval_typing \<Xi> \<sigma> obsv (foldmap_obsv_type ''wordarray_map_no_break_0'') ro {};
    (\<Xi>, [], [option.Some (foldmap_funarg_type ''wordarray_map_no_break_0'')] \<turnstile> 
    (App (uvalfun_to_exprfun f) (Var 0)) : (foldmap_funret_type ''wordarray_map_no_break_0''));
    \<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr) 
      (App (uvalfun_to_exprfun f) (Var 0)) (do ret <- dispatch_t8' (t9_C.f_C v') x'; gets (\<lambda>s. ret) od) 
      \<xi>0 [x] \<Xi> [option.Some (foldmap_funarg_type ''wordarray_map_no_break_0'')] \<sigma> s\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr)
         (App (AFun ''wordarray_map_no_break_0'' []) (Var i)) (do x <- main_pp_inferred.wordarray_map_no_break_0' v';
gets (\<lambda>s. x)
                                                                od)
         \<xi>1 \<gamma> \<Xi>  \<Gamma>' \<sigma> s"
  apply (rule absfun_corres; simp)
  apply (clarsimp simp: abs_fun_rel_def'; rename_tac r w)
  apply (thin_tac "\<Gamma>' ! i = _")
  apply (subst \<xi>1.simps)
  apply (subst (asm) val_rel_simp; clarsimp)
  apply (subst (asm) val_rel_ptr_def; clarsimp)
  apply (subst (asm) val_rel_fun_tag)
  apply (subst (asm) val_rel_word)
  apply (subst (asm) val_rel_word)
  apply (clarsimp simp: upd_wa_mapAccumnb_def wordarray_map_no_break_0'_def)
  apply (rename_tac pwa_rep frm_rep to_rep f_rep acc a_rep o_rep wa_rep)
  apply (erule upd.u_t_recE; clarsimp)
  apply (clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (rename_tac r w r' w')
  apply (erule upd.u_t_p_absE; clarsimp)
  apply (rename_tac w)
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule upd.u_t_primE)+
  apply (drule_tac t = "lit_type _" in sym)+
  apply clarsimp
  apply (erule upd.u_t_r_consE; clarsimp)+
  apply (erule upd.u_t_r_emptyE; clarsimp)
  apply (frule upd.tfun_no_pointers(1))
  apply (frule upd.tfun_no_pointers(2))
  apply clarsimp
  apply (rename_tac acc ra wa ro' wo)
  apply (drule_tac x = obsv in upd.uval_typing_unique_ptrs(1); simp?)
  apply (subst unknown_bind_ignore)+
  apply (clarsimp simp: join_guards) 
  apply wp
      apply (clarsimp simp: unknown_bind_ignore split: prod.split)
       apply (rename_tac var e)
       apply (rule_tac M = "\<lambda>((_, i), _). foldmap_measure i (t9_C.to_C v')" and 
      I = "\<lambda>(a, b) s. (\<exists>\<sigma>' res. foldmap_inv upd_wa_mapAccumnb_bod \<xi>0 \<sigma> (ptr_val (t9_C.arr_C v'))
          (t9_C.frm_C v') b (uvalfun_to_exprfun f) acc obsv (ra \<union> ro) \<sigma>' res s (t10_C (t9_C.arr_C v') (t6_C.acc_C a))) \<and>
          foldmap_inv_stat obsv (t6_C.obsv_C a) \<and>
          foldmap_bounds (t9_C.frm_C v') (t9_C.to_C v') len b e" in whileLoop_add_invI; simp?)
       apply (wp; clarsimp simp: unknown_bind_ignore split: prod.splits)
           apply (rename_tac sa a n args a' n')
           apply (clarsimp simp: conj_left_commute[of "is_valid_w32 _ _", simplified])
           apply (clarsimp simp: conj_commute[of "is_valid_w32 _ _", simplified])
           apply (rule_tac a = a and wa = wa and ra = ra and ro = ro and w = w and r = r and
              ptrl = undefined in map_dispatch_wp; simp?)
              apply (clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs)+
          apply wp
         apply wp
        apply clarsimp
        apply (rename_tac args j \<sigma>' res)
        apply (clarsimp simp: foldmap_inv_def foldmap_bounds_def)
        apply (drule upd_wa_mapAccumnb_bod_preservation; simp?; clarsimp?)
          apply (subst Int_Un_distrib2; clarsimp)
          apply (cut_tac A = w and B = ra and C = ro in Int_Un_distrib; clarsimp)
         apply (cut_tac A = w and B = ra and C = ro in Int_Un_distrib; clarsimp)
        apply (frule_tac p = "ptr_val (t9_C.arr_C v')" in valid_ptr_not_in_frame_same; simp?)
        apply (thin_tac "_ \<in> state_rel")
        apply (frule_tac upd_wa_mapAccumnb_bod_preservation'; simp?)
        apply clarsimp
        apply (erule upd.u_t_recE; clarsimp)
        apply (erule upd.u_t_r_consE; simp)
        apply (erule conjE)+
        apply (drule_tac t = "type_repr _" in sym; clarsimp)
        apply (erule upd.u_t_p_con_wrE)
        apply (drule_tac t = "RCon _ _" in sym; clarsimp)
        apply (thin_tac "wa_abs_typing_u _ _ _ _ _ _ _")
        apply (drule wa_abs_typing_u_elims(5))
        apply (erule_tac x = j in allE; clarsimp)
        apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta heap_rel_ptr_w32_meta)
        apply (frule_tac p = "t9_C.arr_C v'" in all_heap_rel_ptrD; simp?)
         apply (clarsimp simp: type_rel_simp wa_abs_repr_def)
        apply (rotate_tac -2)
         apply (frule_tac p = "Ptr(arr + 4 * j)" in all_heap_rel_ptrD; simp?)
         apply (clarsimp simp: type_rel_simp)
        apply (rule conjI)
         apply (rule_tac x = \<sigma>' in exI)
         apply (rule_tac x = "mk_urecord [UPtr (ptr_val (t9_C.arr_C v'))
          (RCon ''WordArray'' [RPrim (Num U32)]), racc]" in exI)
         apply (rule_tac x = "UPrim x" in exI)
         apply (rule_tac x = "heap_w32 s (PTR(32 word) (arr + 4 * j))" in exI)
         apply (clarsimp simp: val_rel_WordArray_u32_C_def ptr_add_def heap_simp mult.commute)
        apply (clarsimp simp: val_rel_WordArray_u32_C_def ptr_add_def is_valid_simp heap_simp mult.commute)
       apply (rule conjI)
        apply (drule_tac v = acc in upd.type_repr_uval_repr(1); simp)
       apply (rule conjI)
        apply (drule_tac v = obsv in upd.type_repr_uval_repr(1); simp)
       apply (rule conjI)
        apply (drule wa_abs_typing_u_elims(5); simp)
       apply (rule conjI)
        apply (erule u_t_funafuntE; clarsimp)
       apply (rule_tac x = \<sigma>' in exI)
       apply (rule_tac x = res in exI)
       apply (clarsimp simp: foldmap_inv_def)
       apply (rule conjI)
        apply (rule_tac x = "foldmap_acc_type ''wordarray_map_no_break_0''" in exI)
        apply (rule_tac x = "foldmap_obsv_type ''wordarray_map_no_break_0''" in exI)
        apply (rule_tac x = "''elem''" in exI)
        apply (rule_tac x = "''acc''" in exI)
        apply (rule_tac x = "''obsv''" in exI)
        apply (rule_tac x = "''p1''" in exI)
        apply (rule_tac x = "''p2''" in exI)
        apply (rule_tac x = ra in exI)
        apply (clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs)
        apply (rule conjI)
         apply (intro exI, assumption)
        apply (rule_tac x = ro in exI)
        apply clarsimp
        apply (rename_tac j \<sigma>' res)
        apply (unfold foldmap_bounds_def)
        apply (erule conjE)+
        apply (case_tac "t9_C.frm_C v' < e")
         apply (erule impE, assumption)
         apply (thin_tac "_ \<longrightarrow> _")
         apply clarsimp
         apply (case_tac "j < t9_C.to_C v'"; clarsimp)
         apply (rule upd_wa_mapAccumnb_bod_to_geq_len; simp?)
        apply (erule impE, assumption)
        apply (thin_tac "_ \<longrightarrow> _")
        apply clarsimp
        apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp)
        apply (case_tac "t9_C.frm_C v' < t9_C.to_C v'"; subst upd_wa_mapAccumnb_bod.simps; clarsimp)
       apply (clarsimp simp: val_rel_simp)
      apply wp
     apply wp
    apply (rule validNF_select_UNIV)
   apply (rule validNF_select_UNIV)
  apply (clarsimp simp: foldmap_inv_stat_def)
  apply (clarsimp simp: order.strict_implies_order)
  apply (clarsimp simp: foldmap_inv_def state_rel_def heap_rel_def heap_rel_ptr_meta)
  apply (frule_tac p = "t9_C.arr_C v'" in all_heap_rel_ptrD; simp?)
   apply (clarsimp simp: type_rel_simp wa_abs_repr_def)
  apply (clarsimp simp: is_valid_simp val_rel_WordArray_u32_C_def heap_simp)
  apply (rule conjI; clarsimp)
   apply (rule conjI)
    apply (rule_tac x = \<sigma> in exI)
    apply (rule_tac x = "mk_urecord [UPtr (ptr_val (t9_C.arr_C v'))
      (RCon ''WordArray'' [RPrim (Num U32)]), acc]" in exI)
    apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
    apply (rule conjI)
     apply (drule wa_abs_typing_u_elims(5); clarsimp)
     apply (rename_tac j)
     apply (erule_tac x = j in allE; clarsimp)
    apply (rule conjI)
     apply (drule wa_abs_typing_u_elims(3); clarsimp)
    apply (rule conjI)
     apply (clarsimp simp: val_rel_simp)
    apply (rule conjI; clarsimp)
   apply (subst min_def)
   apply (subst (asm) not_le[symmetric])+
   apply (subst if_not_P; simp?)
  apply (rule conjI)
   apply (rule_tac x = \<sigma> in exI)
   apply (rule_tac x = "mk_urecord [UPtr (ptr_val (t9_C.arr_C v'))
      (RCon ''WordArray'' [RPrim (Num U32)]), acc]" in exI)
   apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
   apply (rule conjI)
    apply (drule wa_abs_typing_u_elims(5); clarsimp)
    apply (rename_tac j)
    apply (erule_tac x = j in allE; clarsimp)
   apply (rule conjI)
    apply (drule wa_abs_typing_u_elims(3); clarsimp)
   apply (rule conjI)
    apply (clarsimp simp: val_rel_simp)
   apply (rule conjI; clarsimp)
  apply (subst min_def)
  apply (clarsimp simp: not_le)
  done

lemma 
" \<And>v' i \<gamma> \<Gamma> \<sigma> s.
        \<lbrakk>t9_C.f_C v' = FUN_ENUM_dec; i < length \<gamma>; val_rel (\<gamma> ! i) v';
         \<Gamma> ! i =
         option.Some
          (prod.fst
            (prod.snd
              (assoc_lookup
                [(''wordarray_get_0'', wordarray_get_0_type), (''wordarray_length_0'', wordarray_length_0_type),
                 (''wordarray_put2_0'', wordarray_put2_0_type), (''wordarray_fold_no_break_0'', wordarray_fold_no_break_0_type),
                 (''wordarray_map_no_break_0'', wordarray_map_no_break_0_type),
                 (''wordarray_get_u32'', Generated_TypeProof.wordarray_get_u32_type),
                 (''wordarray_length_u32'', Generated_TypeProof.wordarray_length_u32_type),
                 (''wordarray_put2_u32'', Generated_TypeProof.wordarray_put2_u32_type), (''dec'', Generated_TypeProof.dec_type),
                 (''dec_arr'', Generated_TypeProof.dec_arr_type), (''inc'', Generated_TypeProof.inc_type),
                 (''inc_arr'', Generated_TypeProof.inc_arr_type), (''mul'', Generated_TypeProof.mul_type),
                 (''mul_arr'', Generated_TypeProof.mul_arr_type), (''sum'', Generated_TypeProof.sum_type),
                 (''sum_arr'', Generated_TypeProof.sum_arr_type)]
                ([], TUnit, TUnit) ''wordarray_map_no_break_0'')))\<rbrakk>
        \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr)
             (App (AFun ''wordarray_map_no_break_0'' []) (Var i)) (do x <- wordarray_map_no_break_0' v';
     gets (\<lambda>s. x)
  od)
             \<xi>1 \<gamma>
             (assoc_lookup
               [(''wordarray_get_0'', wordarray_get_0_type), (''wordarray_length_0'', wordarray_length_0_type),
                (''wordarray_put2_0'', wordarray_put2_0_type), (''wordarray_fold_no_break_0'', wordarray_fold_no_break_0_type),
                (''wordarray_map_no_break_0'', wordarray_map_no_break_0_type),
                (''wordarray_get_u32'', Generated_TypeProof.wordarray_get_u32_type),
                (''wordarray_length_u32'', Generated_TypeProof.wordarray_length_u32_type),
                (''wordarray_put2_u32'', Generated_TypeProof.wordarray_put2_u32_type), (''dec'', Generated_TypeProof.dec_type),
                (''dec_arr'', Generated_TypeProof.dec_arr_type), (''inc'', Generated_TypeProof.inc_type),
                (''inc_arr'', Generated_TypeProof.inc_arr_type), (''mul'', Generated_TypeProof.mul_type),
                (''mul_arr'', Generated_TypeProof.mul_arr_type), (''sum'', Generated_TypeProof.sum_type),
                (''sum_arr'', Generated_TypeProof.sum_arr_type)]
               ([], TUnit, TUnit))
             \<Gamma> \<sigma> s"
  apply (subst (asm) \<Xi>_def[symmetric])
  apply (subst \<Xi>_def[symmetric])
  apply (subst (asm) val_rel_simp; clarsimp)
  apply (rename_tac wp wpr frm frmr to tor f fr acc accr obsv obsvr)
  apply (drule_tac v' = v' and \<sigma> = \<sigma> and s = s and ro = "{}" in upd_C_wordarray_map_no_break_corres'[rotated 1]; simp?)
       apply (clarsimp simp: val_rel_simp)
      apply (clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs val_rel_simp)
      apply (rule upd.u_t_unit)
     apply (rule typing_app[of _ _ 
        "[option.Some (foldmap_funarg_type ''wordarray_map_no_break_0'')]"
        "[option.Some (foldmap_funarg_type ''wordarray_map_no_break_0'')]"
        _ _  "(foldmap_funarg_type ''wordarray_map_no_break_0'')"]; simp?)
       apply (rule split_cons[where xs = "[]" and ys = "[]" and zs = "[]", simplified])
        apply (rule_tac k = "kinding_fn [] (foldmap_funarg_type ''wordarray_map_no_break_0'')" in share; simp?)
         apply (rule kindingI; simp?)
         apply (clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs)
        apply (clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs)
       apply (rule split_empty)
      apply (clarsimp simp: \<Xi>_def cogent_function_val_rel val_rel_fun_tag untyped_func_enum_defs wordarray_map_no_break_0_type_def abbreviated_type_defs)
      apply (rule typing_fun; simp?; clarsimp?)
       apply (subst abbreviated_type_defs[symmetric])+
       apply (subst wordarray_map_no_break_0_type_def[symmetric])+
       apply (subst \<Xi>_def[symmetric])
       apply (cut_tac dec_typecorrect')
       apply (clarsimp simp: dec_type_def)
      apply (clarsimp simp: empty_def weakening_Cons[where xs = "[]" and ys = "[]", simplified])
      apply (rule conjI)
       apply (rule_tac k = "{D, S, E}" in drop; simp?)
       apply (rule kindingI; clarsimp)
      apply (rule weakening_nil)
     apply (rule typing_var; clarsimp)
     apply (clarsimp simp: empty_def weakening_Cons[where xs = "[]" and ys = "[]", simplified])
     apply (rule conjI)
      apply (rule keep; clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs)
     apply (rule weakening_nil)
  


  oops


end (* of context *)
end
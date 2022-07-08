theory BinarySearchAsm
  imports
    RepeatCorres
    RepeatCorrespondence
    RepeatMono
    RepeatScorres
    WordArrayCorres
    WordArrayCorrespondence
    WordArrayMono
    WordArrayScorres
   "build/Generated_AllRefine"
begin
section "Function types wellformed"

lemma proc_ctx_wellformed_\<Xi>:
  "proc_ctx_wellformed \<Xi>"
  unfolding proc_ctx_wellformed_def \<Xi>_def
            Generated_Deep_Normal.abbreviated_type_defs 
            Generated_TypeProof.abbreviated_type_defs 
            Generated_TypeProof.repeat_0_type_def Generated_TypeProof.repeat_1_type_def Generated_TypeProof.repeat_2_type_def
            Generated_TypeProof.log2stop_type_def Generated_TypeProof.log2step_type_def Generated_TypeProof.mylog2_type_def
            Generated_TypeProof.myexp_type_def Generated_TypeProof.expstep_type_def Generated_TypeProof.expstop_type_def
            Generated_TypeProof.searchStop_type_def Generated_TypeProof.searchNext_type_def Generated_TypeProof.binarySearch_type_def
            Generated_TypeProof.wordarray_get_0_type_def Generated_TypeProof.wordarray_length_0_type_def
            Generated_TypeProof.wordarray_put_0_type_def Generated_TypeProof.wordarray_get_opt_0_type_def
            Generated_TypeProof.wordarray_put32_type_def Generated_TypeProof.wordarray_get_opt32_type_def
  by (clarsimp simp: assoc_lookup.simps)

lemma \<Xi>_simps:
  "\<Xi> ''repeat_0'' = repeat_0_type"
  "\<Xi> ''repeat_1'' = repeat_1_type"
  "\<Xi> ''repeat_2'' = repeat_2_type"
  "\<Xi> ''wordarray_length_0'' = wordarray_length_0_type"
  "\<Xi> ''wordarray_get_0'' = wordarray_get_0_type"
  "\<Xi> ''wordarray_put_0'' = wordarray_put_0_type"
  "\<Xi> ''wordarray_get_opt_0'' = wordarray_get_opt_0_type"
  apply (clarsimp simp: \<Xi>_def)+
  done

abbreviation 
"acctyp \<Xi>' name \<equiv> (\<lambda>(_,a,_,b,c). c) (\<Xi>' name)"

abbreviation
"obsvtyp \<Xi>' name \<equiv> (\<lambda>(L,a,C,b,c). case b of TRecord [a, b, c, d, (n, t, p)] Unboxed \<Rightarrow> t | _ \<Rightarrow> undefined) (\<Xi>' name)"

abbreviation
"stoptyp \<Xi>' name \<equiv> (\<lambda>(L,a,C,b,c). case b of TRecord [a, (n, TFun t t', p), b, c, d] Unboxed \<Rightarrow> t | _ \<Rightarrow> undefined) (\<Xi>' name)"

abbreviation
"steptyp \<Xi>' name \<equiv> (\<lambda>(L,a,C,b,c). case b of TRecord [a, b, (n, TFun t t', p), c, d] Unboxed \<Rightarrow> t | _ \<Rightarrow> undefined) (\<Xi>' name)"

section "Abstract functions specification for the update semantics"

text "If user defines \<xi>n, we can derive \<xi>i for i < n" 

overloading \<xi>0 \<equiv> \<xi>_0
begin
definition \<xi>0 :: "(funtyp, abstyp, ptrtyp) uabsfuns"
  where
"\<xi>0 f x y = 
  (if f = ''wordarray_length_0'' then uwa_length x y
   else if f = ''wordarray_get_0'' then uwa_get x y
   else if f = ''wordarray_put_0'' then uwa_put x y
   else if f = ''wordarray_get_opt_0'' then uwa_get_opt x y
   else False)"
end

overloading \<xi>1 \<equiv> \<xi>_1
begin
definition \<xi>1 :: "(funtyp, abstyp, ptrtyp) uabsfuns"
  where
"\<xi>1 f x y =                    
  (if f = ''repeat_0'' then urepeat \<Xi> \<xi>_0 (acctyp \<Xi> f) (obsvtyp \<Xi> f) x y 
   else if f = ''repeat_1'' then urepeat \<Xi> \<xi>_0 (acctyp \<Xi> f) (obsvtyp \<Xi> f) x y
   else if f = ''repeat_2'' then urepeat \<Xi> \<xi>_0 (acctyp \<Xi> f) (obsvtyp \<Xi> f) x y
   else \<xi>_0 f x y)"
end

lemma \<xi>_1_simps:
  "\<xi>_1 ''repeat_0'' = urepeat \<Xi> \<xi>_0 (acctyp \<Xi> ''repeat_0'') (obsvtyp \<Xi> ''repeat_0'')"
  "\<xi>_1 ''repeat_1'' = urepeat \<Xi> \<xi>_0 (acctyp \<Xi> ''repeat_1'') (obsvtyp \<Xi> ''repeat_1'')"
  "\<xi>_1 ''repeat_2'' = urepeat \<Xi> \<xi>_0 (acctyp \<Xi> ''repeat_2'') (obsvtyp \<Xi> ''repeat_2'')"
  apply (clarsimp simp: \<xi>1_def fun_eq_iff)+
  done

subsection "Preservation for abstract functions"


sublocale WordArrayUpdate \<subseteq> update_sem_init wa_abs_typing_u wa_abs_repr 
  by (unfold_locales)

context WordArrayUpdate begin

text "If user proves for \<xi>n, we can derive \<xi>i for i < n" 

lemma \<xi>_0_matchesu_\<Xi>:
  "proc_env_matches_ptrs \<xi>_0  \<Xi>"
  unfolding proc_env_matches_ptrs_def \<xi>0_def
  apply clarsimp
  apply (intro conjI impI;
         simp add: \<Xi>_simps Generated_TypeProof.wordarray_get_0_type_def
                   Generated_TypeProof.wordarray_length_0_type_def
                   Generated_TypeProof.wordarray_put_0_type_def
                   Generated_TypeProof.wordarray_get_opt_0_type_def
                   Generated_TypeProof.abbreviated_type_defs;
         clarsimp simp: uwa_get_opt_preservation
                        uwa_put_preservation
                        uwa_get_preservation
                        uwa_length_preservation)
  done
 
lemma \<xi>_1_matchesu_\<Xi>:
  "proc_env_matches_ptrs \<xi>_1 \<Xi>"
  unfolding proc_env_matches_ptrs_def \<xi>1_def
  apply clarsimp
  apply (intro conjI impI; clarsimp simp: \<Xi>_simps)
    apply (clarsimp simp: repeat_1_type_def repeat_0_type_def repeat_2_type_def;
           rule_tac urepeat_preservation[OF proc_ctx_wellformed_\<Xi> \<xi>_0_matchesu_\<Xi>];
           (simp add: Generated_TypeProof.abbreviated_type_defs))+
  apply (cut_tac \<xi>_0_matchesu_\<Xi>[unfolded proc_env_matches_ptrs_def]; clarsimp split: prod.splits)
  apply (elim allE impE conjE; assumption?)
  apply blast
  done

end (* of context *)

subsection "Partial ordering on abstract functions"

text "These should be automatable"

lemma \<xi>_0_le_\<xi>_1:
  "rel_leq \<xi>_0 \<xi>_1"
  unfolding \<xi>1_def rel_leq_def
  apply clarsimp
  apply (rename_tac n ac bb ad bc)
  apply (rule_tac x = n in exI; simp?)
  apply (intro exI conjI impI; simp?)
  apply (simp add: \<xi>0_def)+
  done

subsection "Abstract functions are deterministic"

text "If user proves for \<xi>n, we can derive \<xi>i for i < n" 

lemma \<xi>_0_determ:
  "determ \<xi>_0"
  unfolding determ_def \<xi>0_def
  apply simp
  apply clarsimp
  apply (rule conjI; clarsimp simp: uwa_get_determ uwa_length_determ uwa_put_determ uwa_get_opt_determ)+
  done

lemma \<xi>_1_determ:
  "determ \<xi>_1"
  unfolding determ_def \<xi>1_def
  apply clarsimp
  apply (intro conjI impI allI; clarsimp?)
   apply (drule (1) urepeat_deterministic[OF \<xi>_0_determ]; simp)+
   apply (drule (1) determD[OF \<xi>_0_determ]; simp)+
  done


section "Abstract functions specifications for the monomorphic value semantics"

sublocale WordArrayValue \<subseteq> monomorph_sem wa_abs_typing_v
  by (unfold_locales)

context WordArrayValue begin

text "If user defines for \<xi>n, we can derive \<xi>i for i < n" 

definition \<xi>m0 :: "funtyp \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> bool "
  where
"\<xi>m0 f x y =
  (if f = ''wordarray_length_0'' then vwa_length x y
   else if f = ''wordarray_get_0'' then vwa_get x y
   else if f = ''wordarray_put_0'' then vwa_put x y
   else if f = ''wordarray_get_opt_0'' then vwa_get_opt x y
   else False)"

definition \<xi>m1 :: "funtyp \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> bool "
  where
"\<xi>m1 f x y = 
  (if f = ''repeat_0'' then vrepeat \<Xi> \<xi>m0 (acctyp \<Xi> f) (obsvtyp \<Xi> f) x y 
   else if f = ''repeat_1'' then vrepeat \<Xi> \<xi>m0 (acctyp \<Xi> f) (obsvtyp \<Xi> f) x y
   else if f = ''repeat_2'' then vrepeat \<Xi> \<xi>m0 (acctyp \<Xi> f) (obsvtyp \<Xi> f) x y
   else \<xi>m0 f x y)"

subsection "Preservation for abstract functions"

text "If user proves for \<xi>n, we can derive \<xi>i for i < n" 

lemma \<xi>m0_matches_\<Xi>:
  "proc_env_matches \<xi>m0  \<Xi>"
  unfolding proc_env_matches_def \<xi>m0_def
  apply clarsimp
  apply (intro conjI impI;
         simp add: \<Xi>_simps Generated_TypeProof.wordarray_get_0_type_def
                   Generated_TypeProof.wordarray_length_0_type_def
                   Generated_TypeProof.wordarray_put_0_type_def
                   Generated_TypeProof.wordarray_get_opt_0_type_def
                   Generated_TypeProof.abbreviated_type_defs;
         clarsimp)
     apply (rule vwa_get_opt_preservation; simp?)
    apply (rule vwa_put_preservation; simp?)
   apply (rule vwa_get_preservation; simp?)
  apply (rule vwa_length_preservation; simp?)
  done

lemma \<xi>m1_matches_\<Xi>:
  "proc_env_matches \<xi>m1 \<Xi>"
  unfolding proc_env_matches_def \<xi>m1_def
  apply clarsimp
  apply (intro conjI impI)
    apply (clarsimp simp: \<Xi>_simps repeat_1_type_def repeat_0_type_def repeat_2_type_def;
           rule vrepeat_preservation[OF proc_ctx_wellformed_\<Xi> \<xi>m0_matches_\<Xi>];
           (simp add: Generated_TypeProof.abbreviated_type_defs)?)+
  apply (cut_tac \<xi>m0_matches_\<Xi>[unfolded proc_env_matches_def]; clarsimp split: prod.splits)
  done

subsection "Partial ordering on abstract functions"

text "Should be automatable"

lemma \<xi>m0_le_\<xi>m1:
  "rel_leq \<xi>m0 \<xi>m1"
  unfolding \<xi>m1_def rel_leq_def
  apply clarsimp
  apply (rename_tac n a b)
  apply (rule_tac x = n in exI; simp?)
  apply (intro exI conjI impI; simp?)
  apply (simp add: \<xi>m0_def)+
  done

subsection "Abstract functions are deterministic"

text "If user proves for \<xi>n, we can derive \<xi>i for i < n" 

lemma \<xi>m0_determ:
  "determ \<xi>m0"
  unfolding determ_def \<xi>m0_def
  apply clarsimp
  apply (rule conjI; clarsimp simp: vwa_get_determ vwa_length_determ vwa_get_opt_determ vwa_put_determ)+
  done

lemma \<xi>m1_determ:
  "determ \<xi>m1"
  unfolding determ_def \<xi>m1_def
  apply clarsimp
  apply safe
    apply (drule (1) vrepeat_deterministic[OF \<xi>m0_determ]; simp)+
  apply (drule (1) determD[OF \<xi>m0_determ]; simp)
  done

end (* of context *)

section "Abstract functions specifications for the polymorphic value semantics"

text "If user defines \<xi>n, we can derive \<xi>i for i < n" 

definition \<xi>p0 :: "funtyp \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> bool"
  where
"\<xi>p0 f x y =
  (if f = ''wordarray_length'' then vwa_length x y
   else if f = ''wordarray_get'' then vwa_get x y
   else if f = ''wordarray_put'' then vwa_put x y
   else if f = ''wordarray_get_opt'' then vwa_get_opt x y
   else False)"

definition \<xi>p1 :: "funtyp \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> bool"
  where
"\<xi>p1 f x y = (if f = ''repeat'' then prepeat \<xi>p0 x y else \<xi>p0 f x y)"

subsection "Partial ordering on abstract functions"

text "Should be automatable"

lemma \<xi>p0_le_\<xi>p1:
  "rel_leq \<xi>p0 \<xi>p1"
  unfolding \<xi>p1_def rel_leq_def
  apply clarsimp
  apply (rename_tac n a b)
  apply (rule_tac x = n in exI; simp?)
  apply (intro exI conjI impI; simp?)
  apply (simp add: \<xi>p0_def)+
  done

subsection "Abstract functions are deterministic"

text "If user proves for \<xi>n, we can derive \<xi>i for i < n" 

lemma \<xi>p0_determ:
  "determ \<xi>p0"
  unfolding determ_def \<xi>p0_def
  apply clarsimp
  apply (rule conjI; clarsimp simp: vwa_get_determ vwa_length_determ vwa_get_opt_determ vwa_put_determ)+
  done

lemma \<xi>p1_determ:
  "determ \<xi>p1"
  unfolding determ_def \<xi>p1_def
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (drule (1) prepeat_deterministic[OF \<xi>p0_determ]; simp)
  apply (drule (1) determD[OF \<xi>p0_determ]; simp)
  done

section "Correspondence between abstract functions in the update semantics and C"

context Generated begin

lemma repeat_0'_simp:
  "repeat_0' = crepeat t6_C.n_C t6_C.stop_C t6_C.step_C t6_C.acc_C t6_C.obsv_C t3_C.acc_C t3_C.acc_C_update t3_C.obsv_C_update dispatch_t4' dispatch_t5'"
  unfolding crepeat_def[polish] repeat_0'_def[simplified L2polish, polish]
  apply clarsimp
  done

lemma mylog2_repeat_corres:
  "\<And>v' i \<gamma> \<Gamma> \<sigma> s.
    \<lbrakk>t6_C.stop_C v' = FUN_ENUM_log2stop; t6_C.step_C v' = FUN_ENUM_log2step; 
     i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma> ! i = Some (fst (snd (snd (snd repeat_0_type))))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''repeat_0'' [] []) (Var i)) (do x <- repeat_0' v';
 gets (\<lambda>s. x)
                                                               od)
         \<xi>_1 \<gamma> \<Xi> \<Gamma> \<sigma> s"
  apply simp
  apply (subst (asm) \<Xi>_simps[symmetric])
  apply (cut_tac uv = "\<gamma>!i" and x = v' in val_rel_t6_C_def)
  apply (rule crepeat_corres_bang_fun_fun[
      where  o1C = t3_C.obsv_C,
      OF _ _ _ \<Xi>_simps(1)[unfolded Generated_TypeProof.repeat_0_type_def]  _ _ _  _ _
      \<xi>_0_le_\<xi>_1 \<xi>_1_determ _
      log2stop_typecorrect'[simplified Generated_TypeProof.log2stop_type_def fst_conv snd_conv]
      log2step_typecorrect'[simplified Generated_TypeProof.log2step_type_def fst_conv snd_conv]
      _ _ _ _ _ _ _ _ repeat_0'_simp]; (simp add: Generated_TypeProof.abbreviated_type_defs)?)
        apply simp
       apply (simp add: \<xi>_1_simps \<Xi>_simps Generated_TypeProof.repeat_0_type_def Generated_TypeProof.abbreviated_type_defs)
      apply (clarsimp simp: cogent_function_val_rel untyped_func_enum_defs val_rel_simp)
     apply (subst Generated_TypeProof.abbreviated_type_defs[symmetric])+
     apply (rule corres_app_concrete[simplified]; simp?)
     apply (simp add: dispatch_t4'_def unknown_bind_ignore)
     apply (erule corres_log2stop[folded \<Xi>_def, simplified fst_conv snd_conv Generated_TypeProof.log2stop_type_def])
    apply (subst Generated_TypeProof.abbreviated_type_defs[symmetric])+
    apply (rule corres_app_concrete[simplified]; simp?)
    apply (simp add: dispatch_t5'_def unknown_bind_ignore)
    apply (erule corres_log2step[folded \<Xi>_def, simplified fst_conv snd_conv Generated_TypeProof.log2step_type_def])
   apply (clarsimp simp: val_rel_simp)
  apply (clarsimp simp: val_rel_simp)
  done

lemma repeat_1'_simp:
  "repeat_1' = crepeat t16_C.n_C t16_C.stop_C t16_C.step_C t16_C.acc_C t16_C.obsv_C t13_C.acc_C t13_C.acc_C_update t13_C.obsv_C_update dispatch_t14' dispatch_t15'"
  unfolding crepeat_def[polish] repeat_1'_def[simplified L2polish, polish]
  apply clarsimp
  done

lemma myexp_repeat_corres:
  "\<And>v' i \<gamma> \<Gamma> \<sigma> s.
    \<lbrakk>t16_C.stop_C v' = FUN_ENUM_expstop; t16_C.step_C v' = FUN_ENUM_expstep; i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma> ! i = Some (fst (snd (snd (snd repeat_1_type))))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''repeat_1'' [] []) (Var i)) (do x <- repeat_1' v';
 gets (\<lambda>s. x)
                                                               od)
         \<xi>_1 \<gamma> \<Xi> \<Gamma> \<sigma> s"
  apply simp
  apply (subst (asm) \<Xi>_simps[symmetric])
  apply (cut_tac uv = "\<gamma>!i" and x = v' in val_rel_t16_C_def)
  apply (rule crepeat_corres_bang_fun_fun[
      where o1C = t13_C.obsv_C,
      OF _ _ _ \<Xi>_simps(2)[unfolded Generated_TypeProof.repeat_1_type_def]  _ _ _  _ _
      \<xi>_0_le_\<xi>_1 \<xi>_1_determ _
      expstop_typecorrect'[simplified Generated_TypeProof.expstop_type_def fst_conv snd_conv]
      expstep_typecorrect'[simplified Generated_TypeProof.expstep_type_def fst_conv snd_conv]
      _ _ _ _ _ _ _ _ repeat_1'_simp]; (simp add: Generated_TypeProof.abbreviated_type_defs)?)
        apply simp
       apply (simp add: \<xi>_1_simps \<Xi>_simps Generated_TypeProof.repeat_1_type_def Generated_TypeProof.abbreviated_type_defs)
      apply (clarsimp simp: cogent_function_val_rel untyped_func_enum_defs val_rel_simp)
     apply (subst Generated_TypeProof.abbreviated_type_defs[symmetric])+
     apply (rule corres_app_concrete[simplified]; simp?)
     apply (simp add: dispatch_t14'_def unknown_bind_ignore)
     apply (erule corres_expstop[folded \<Xi>_def, simplified fst_conv snd_conv Generated_TypeProof.expstop_type_def])
    apply (subst Generated_TypeProof.abbreviated_type_defs[symmetric])+
    apply (rule corres_app_concrete[simplified]; simp?)
    apply (simp add: dispatch_t15'_def unknown_bind_ignore)
    apply (erule corres_expstep[folded \<Xi>_def, simplified fst_conv snd_conv Generated_TypeProof.expstep_type_def])
   apply (clarsimp simp: val_rel_simp)
  apply (clarsimp simp: val_rel_simp)
  done

end (* of context *)

sublocale WordArrayUpdate \<subseteq> Generated _ wa_abs_typing_u wa_abs_repr
  by (unfold_locales)

sublocale WordArrayUpdate \<subseteq> update_sem_init wa_abs_typing_u wa_abs_repr
  by (unfold_locales)

context WordArrayUpdate begin

lemma wordarray_length_0_corres:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = Some (fst (snd (snd (snd (\<Xi> ''wordarray_length_0'')))))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''wordarray_length_0'' [] []) (Var i)) (do x <- wordarray_length_0' v';
        gets (\<lambda>s. x)
     od)
         \<xi>_0 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (rule_tac is_v = is_valid and h = heap and
      l_c = WordArray_u32_C.len_C and v_c = WordArray_u32_C.values_C 
      in cwa_length_corres_base; simp add: \<Xi>_simps wordarray_length_0_type_def fun_eq_iff;
      clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta type_rel_simp \<xi>1_def \<xi>0_def val_rel_simp
      wordarray_length_0'_def cwa_length_def unknown_bind_ignore is_valid_simp heap_simp)
  done

lemma wordarray_get_0'_simp:
  "wordarray_get_0' = cwa_get is_valid_WordArray_u32_C heap_WordArray_u32_C is_valid_w32 heap_w32 t1_C.arr_C t1_C.idx_C t1_C.val_C WordArray_u32_C.len_C WordArray_u32_C.values_C"
  unfolding wordarray_get_0'_def[polish] cwa_get_def
  by (simp add: unknown_bind_ignore)

lemma wordarray_get_0_corres:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = Some (fst (snd (snd (snd (\<Xi> ''wordarray_get_0'')))))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''wordarray_get_0'' [] []) (Var i)) (do x <- wordarray_get_0' v';
        gets (\<lambda>s. x)
     od)
         \<xi>_0 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (rule_tac  cwa_get_corres_base[rotated -1, OF  wordarray_get_0'_simp]; 
      simp add: \<Xi>_simps wordarray_get_0_type_def fun_eq_iff;
      clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta type_rel_simp \<xi>1_def \<xi>0_def val_rel_simp
      wordarray_length_0'_def cwa_length_def unknown_bind_ignore is_valid_simp heap_simp)
  done

lemma repeat_2'_simp:
  "repeat_2' = crepeat t12_C.n_C t12_C.stop_C t12_C.step_C t12_C.acc_C t12_C.obsv_C t9_C.acc_C t9_C.acc_C_update t9_C.obsv_C_update dispatch_t10' dispatch_t11'"
  unfolding crepeat_def[polish] repeat_2'_def[simplified L2polish, polish]
  apply clarsimp
  done

lemma binarySearch_repeat_corres:
  "\<And>v' i \<gamma> \<Gamma> \<sigma> s.
    \<lbrakk>t12_C.stop_C v' = FUN_ENUM_searchStop; t12_C.step_C v' = FUN_ENUM_searchNext; i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma> ! i = Some (fst (snd (snd (snd repeat_2_type))))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''repeat_2'' [] []) (Var i)) (do x <- repeat_2' v';
 gets (\<lambda>s. x)
                                                               od)
         \<xi>_1 \<gamma> \<Xi> \<Gamma> \<sigma> s"
  apply simp
  apply (subst (asm) \<Xi>_simps[symmetric])
  apply (cut_tac uv = "\<gamma>!i" and x = v' in val_rel_t12_C_def)
  apply (rule crepeat_corres_bang_fun_fun[
        where o1C = t9_C.obsv_C and \<xi>' = \<xi>_0,
        OF _ _ _ _  _ _ _  _ _ \<xi>_0_le_\<xi>_1 \<xi>_1_determ _
        searchStop_typecorrect'[simplified Generated_TypeProof.searchStop_type_def fst_conv snd_conv]
        searchNext_typecorrect'[simplified Generated_TypeProof.searchNext_type_def fst_conv snd_conv]
        _ _ _ _ _ _ _ _ repeat_2'_simp]; 
        (simp add: \<Xi>_simps \<xi>_1_simps
            Generated_TypeProof.repeat_2_type_def Generated_TypeProof.abbreviated_type_defs)?)
        apply (clarsimp simp: cogent_function_val_rel untyped_func_enum_defs val_rel_simp)
     apply (subst Generated_TypeProof.abbreviated_type_defs[symmetric])+
     apply (rule corres_app_concrete[simplified]; simp?)
     apply (simp add: dispatch_t10'_def unknown_bind_ignore)
     apply (erule corres_searchStop[folded \<Xi>_def, simplified fst_conv snd_conv Generated_TypeProof.searchStop_type_def])
    apply (subst Generated_TypeProof.abbreviated_type_defs[symmetric])+
    apply (rule corres_app_concrete[simplified]; simp?)
    apply (simp add: dispatch_t11'_def unknown_bind_ignore)
    apply (rule corres_searchNext[folded \<Xi>_def, simplified fst_conv snd_conv Generated_TypeProof.searchNext_type_def])
     apply (rule wordarray_get_0_corres; (simp add: \<Xi>_simps)?)
    apply simp
   apply (clarsimp simp: val_rel_simp)
  apply (clarsimp simp: val_rel_simp)
  done

lemma wordarray_get_opt_0_simp:
  "wordarray_get_opt_0' = cwa_get_opt is_valid heap is_valid_w32 heap_w32 t17_C.arr_C t17_C.idx_C len_C values_C tag_C_update TAG_ENUM_Nothing TAG_ENUM_Something Something_C_update"
  unfolding wordarray_get_opt_0'_def cwa_get_opt_def
  apply (clarsimp simp: unknown_bind_ignore heap_simp is_valid_simp)
  done

lemma wordarray_get_opt_0_corres:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
        \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v';
         \<Gamma>' ! i = Some (fst (snd (snd (snd wordarray_get_opt_0_type))))\<rbrakk>
        \<Longrightarrow> corres state_rel
             (App (AFun ''wordarray_get_opt_0'' [] []) (Var i)) (do x <- wordarray_get_opt_0' v';
                                                                 gets (\<lambda>s. x)
                                                              od)
             \<xi>_0 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (rule_tac tag_c = tag_C and n_c = Nothing_C and s_c = Something_C
      in cwa_get_opt_corres_base[rotated -1, OF wordarray_get_opt_0_simp]; simp add:
      \<Xi>_simps wordarray_get_opt_0_type_def fun_eq_iff Generated_TypeProof.abbreviated_type_defs uwa_get_opt_def \<xi>0_def;
      clarsimp simp: val_rel_simp type_rel_simp state_rel_def heap_rel_def heap_rel_ptr_meta)
  done

lemma wordarray_put_0_simp:
  "wordarray_put_0' = cwa_put is_valid heap is_valid_w32 heap_w32_update t1_C.arr_C t1_C.idx_C t1_C.val_C WordArray_u32_C.len_C WordArray_u32_C.values_C"
  unfolding wordarray_put_0'_def cwa_put_def
  apply (clarsimp simp: unknown_bind_ignore heap_simp is_valid_simp)
  done

lemma wordarray_put_0_corres:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
        \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v';
         \<Gamma>' ! i = Some (fst (snd (snd (snd wordarray_put_0_type))))\<rbrakk>
        \<Longrightarrow> corres state_rel
             (App (AFun ''wordarray_put_0'' [] []) (Var i)) (do x <- wordarray_put_0' v';
                                                                 gets (\<lambda>s. x)
                                                              od)
             \<xi>_0 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (rule_tac hw = heap_w32 and t= "TPrim (Num U32)"
      in cwa_put_corres_base_all[rotated -1, OF wordarray_put_0_simp]; simp add:
      \<Xi>_simps wordarray_put_0_type_def fun_eq_iff Generated_TypeProof.abbreviated_type_defs cwa_put_def \<xi>0_def;
      clarsimp simp: val_rel_simp type_rel_simp state_rel_def heap_rel_def heap_rel_ptr_meta)
  apply (rule conjI)
   apply (erule all_heap_rel_updE; (simp add: heap_simp is_valid_simp type_rel_simp)?)
    apply (drule  type_repr_uval_repr; simp)+
  apply (erule all_heap_rel_updE; (simp add: heap_simp is_valid_simp type_rel_simp val_rel_simp)?)
  apply (rule sym; assumption)
  done
end (* of context *)


section "Correspondence between abstract functions in the update and value semantics"
sublocale WordArray \<subseteq> correspondence_init upd.wa_abs_repr val.wa_abs_typing_v upd.wa_abs_typing_u wa_abs_upd_val
  by (unfold_locales)

context WordArray begin

lemma \<xi>_0_\<xi>m0_matchesuv_\<Xi>:
  "proc_env_u_v_matches \<xi>_0 val.\<xi>m0  \<Xi>"
  unfolding proc_env_u_v_matches_def \<xi>0_def val.\<xi>m0_def
  apply clarsimp
  apply (rule conjI; clarsimp simp: \<Xi>_simps
                                    wordarray_get_0_type_def
                                    wordarray_length_0_type_def
                                    wordarray_get_opt_0_type_def
                                    wordarray_put_0_type_def
                                    Generated_TypeProof.abbreviated_type_defs
                                    uvwa_get_opt_monocorrespond_upward_propagation
                                    uvwa_get_monocorrespond_upward_propagation
                                    uvwa_put_monocorrespond_upward_propagation
                                    uvwa_length_monocorrespond_upward_propagation)+
  done

lemma \<xi>_1_\<xi>m1_matchesuv_\<Xi>:
  "proc_env_u_v_matches \<xi>_1 val.\<xi>m1 \<Xi>"
  unfolding proc_env_u_v_matches_def \<xi>1_def val.\<xi>m1_def   
  apply (clarsimp)
  apply (cut_tac \<xi>_0_\<xi>m0_matchesuv_\<Xi>[unfolded proc_env_u_v_matches_def, simplified])
  apply (intro conjI impI; clarsimp simp: subst_wellformed_def \<Xi>_simps)
     apply (clarsimp simp: repeat_1_type_def repeat_0_type_def repeat_2_type_def;
           rule uvrepeat_monocorrespond_upward_propagation[OF proc_ctx_wellformed_\<Xi> \<xi>_0_\<xi>m0_matchesuv_\<Xi>]; 
           (simp add: Generated_TypeProof.abbreviated_type_defs)?)+
  apply (fastforce split: prod.splits)
  done

end (* of context *)

section "Monomorphisation of abstract functions"

context WordArrayValue begin

lemma rename_mono_prog_\<xi>m0_\<xi>p0:
  "rename_mono_prog rename \<Xi> \<xi>m0 \<xi>p0"
  unfolding rename_mono_prog_def \<xi>m0_def \<xi>p0_def
  apply clarsimp
  apply (intro conjI impI; clarsimp?)
    apply (subst (asm) rename_def,
           clarsimp simp: assoc_lookup.simps 
                          vwa_get_monoexpr_correct
                          vwa_length_monoexpr_correct
                          vwa_get_opt_monoexpr_correct
                          vwa_put_monoexpr_correct
                    split: if_splits)+
  done

lemma rename_mono_prog_\<Xi>_\<xi>m1_\<xi>p1:
  "rename_mono_prog rename \<Xi> \<xi>m1 \<xi>p1"
  unfolding rename_mono_prog_def
  apply (clarsimp simp: \<xi>m1_def \<xi>p1_def)
  apply (intro conjI impI; clarsimp?)
    apply (subst (asm) rename_def,
           clarsimp simp: assoc_lookup.simps split: if_splits;
           rule prepeat_monoexpr_correct[OF _ \<xi>m0_matches_\<Xi> rename_mono_prog_\<xi>m0_\<xi>p0]; simp?)+
  apply (cut_tac rename_mono_prog_\<xi>m0_\<xi>p0[unfolded rename_mono_prog_def];
      clarsimp simp: \<xi>m0_matches_\<Xi>)
  apply (elim allE impE, assumption, clarsimp)
  apply (intro exI conjI impI; simp?)
  apply (clarsimp simp: \<xi>m0_def rename_def assoc_lookup.simps split: if_splits)
  done

end (* of context *)

section "Correspondence between shallow and polymorphic value semantics"

sublocale WordArrayValue \<subseteq> shallow wa_abs_typing_v
  by (unfold_locales)

lemma (in WordArrayValue) scorres_repeat:
  "scorres repeat (AFun ''repeat'' ts []) \<gamma> \<xi>p1"
  by (rule repeat_scorres[OF \<xi>p0_le_\<xi>p1]; simp add: \<xi>p1_def fun_eq_iff)

lemma (in WordArrayValue) scorres_wordarray_get32:
  "scorres (wordarray_get :: (32 word WordArray, 32 word, 32 word ) WordArrayGetP \<Rightarrow> 32 word)(AFun ''wordarray_get'' ts []) \<gamma> \<xi>p0"
  by (rule wordarray_get_u32_scorres; simp add: \<xi>p0_def fun_eq_iff)

section "All refine"

sublocale WordArray \<subseteq> Generated_cogent_shallow _ upd.wa_abs_repr val.wa_abs_typing_v upd.wa_abs_typing_u wa_abs_upd_val
  by (unfold_locales)

lemmas (in WordArray) corres_shallow_C_log2step_concrete = corres_shallow_C_log2step
  [OF correspondence_init_axioms val.rename_mono_prog_\<xi>m0_\<xi>p0 _ _ proc_ctx_wellformed_\<Xi> val.\<xi>m0_matches_\<Xi>]

lemmas (in WordArray) corres_shallow_C_log2stop_concrete = corres_shallow_C_log2stop
  [OF correspondence_init_axioms val.rename_mono_prog_\<xi>m0_\<xi>p0 _ _ proc_ctx_wellformed_\<Xi> val.\<xi>m0_matches_\<Xi>]

lemmas (in WordArray) corres_shallow_C_mylog2_concrete = corres_shallow_C_mylog2
  [folded \<Xi>_def, OF _ correspondence_init_axioms val.rename_mono_prog_\<Xi>_\<xi>m1_\<xi>p1 _ _ proc_ctx_wellformed_\<Xi> val.\<xi>m1_matches_\<Xi>,
   simplified, OF upd.mylog2_repeat_corres[simplified], simplified, simplified \<Xi>_simps, simplified]

lemmas (in WordArray) corres_shallow_C_expstep_concrete = corres_shallow_C_expstep
  [OF correspondence_init_axioms val.rename_mono_prog_\<xi>m0_\<xi>p0 _ _ proc_ctx_wellformed_\<Xi> val.\<xi>m0_matches_\<Xi>]

lemmas (in WordArray) corres_shallow_C_expstop_concrete = corres_shallow_C_expstop
  [OF correspondence_init_axioms val.rename_mono_prog_\<xi>m0_\<xi>p0 _ _ proc_ctx_wellformed_\<Xi> val.\<xi>m0_matches_\<Xi>]

lemmas (in WordArray) corres_shallow_C_myexp_concrete = corres_shallow_C_myexp
  [folded \<Xi>_def, OF _ correspondence_init_axioms val.rename_mono_prog_\<Xi>_\<xi>m1_\<xi>p1 _ _ proc_ctx_wellformed_\<Xi> val.\<xi>m1_matches_\<Xi>,
   simplified, OF upd.myexp_repeat_corres[simplified], simplified, simplified \<Xi>_simps, simplified]

lemmas (in WordArray) corres_shallow_C_searchStop_concrete = corres_shallow_C_searchStop
  [OF correspondence_init_axioms val.rename_mono_prog_\<xi>m0_\<xi>p0 _ _ proc_ctx_wellformed_\<Xi> val.\<xi>m0_matches_\<Xi>]

lemmas (in WordArray) corres_shallow_C_searchNext_concrete = corres_shallow_C_searchNext
  [folded \<Xi>_def, OF _ correspondence_init_axioms val.rename_mono_prog_\<xi>m0_\<xi>p0 _ _ proc_ctx_wellformed_\<Xi> val.\<xi>m0_matches_\<Xi>,
   simplified, OF upd.wordarray_get_0_corres[simplified], simplified, simplified \<Xi>_simps, simplified]

lemmas (in WordArray) corres_shallow_C_binarySearch_concrete = corres_shallow_C_binarySearch
  [folded \<Xi>_def, OF _ _ correspondence_init_axioms val.rename_mono_prog_\<Xi>_\<xi>m1_\<xi>p1 _ _ proc_ctx_wellformed_\<Xi> val.\<xi>m1_matches_\<Xi>,
   simplified, 
   OF _ upd.binarySearch_repeat_corres[simplified], simplified,
   OF upd.corres_rel_leqD[OF \<xi>_0_le_\<xi>_1 upd.wordarray_length_0_corres[simplified]],
   simplified, simplified \<Xi>_simps, simplified]

lemmas (in WordArray) corres_shallow_C_wordarray_put32 = corres_shallow_C_wordarray_put32
  [folded \<Xi>_def, OF _ correspondence_init_axioms val.rename_mono_prog_\<xi>m0_\<xi>p0 _ _ proc_ctx_wellformed_\<Xi> val.\<xi>m0_matches_\<Xi>,
   simplified,
   OF upd.wordarray_put_0_corres[simplified], simplified, simplified \<Xi>_simps, simplified]

lemmas (in WordArray) corres_shallow_C_wordarray_get_opt32 = corres_shallow_C_wordarray_get_opt32
  [folded \<Xi>_def, OF _ correspondence_init_axioms val.rename_mono_prog_\<xi>m0_\<xi>p0 _ _ proc_ctx_wellformed_\<Xi> val.\<xi>m0_matches_\<Xi>,
   simplified,
   OF upd.wordarray_get_opt_0_corres[simplified], simplified, simplified \<Xi>_simps, simplified]

end
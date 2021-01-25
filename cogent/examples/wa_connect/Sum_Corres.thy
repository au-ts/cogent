theory Sum_Corres
imports WordArray_SVCorres WordArray_UpdCCorres WordArray_CorresProof_Asm

begin

text
  "This is an example of proving that @{term main_pp_inferred.sum_arr'} refines
  @{term Generated_Shallow_Desugar.sum_arr}. We can show this if we can prove that
  @{thm Generated_cogent_shallow.corres_shallow_C_sum_arr} is true without
  assuming that the abstract functions refine their corresponding shallow embeddings.

  @{term Generated_Shallow_Desugar.sum_arr} depends on the abstract functions defined for word
  arrays. So if we want to prove that our compilation is correct for 
  @{term Generated_Shallow_Desugar.sum_arr}, we need to prove that the "

context WordArray begin
text 
  "The two word array functions that we need to manually verify are @{term wordarray_length} and
   @{term wordarray_fold_no_break}"
lemma sum_corres:
  "val_rel a a' \<Longrightarrow>
  corres state_rel Generated_TypeProof.sum (local.sum' a') \<xi>' [a] \<Xi>
  [option.Some (prod.fst (prod.snd Generated_TypeProof.sum_type))] \<sigma> s"
  apply (unfold sum_def sum'_def sum_type_def abbreviated_type_defs val_rel_simp)
  apply (elim exE conjE)
  apply (subst unknown_bind_ignore)
  apply (subst snd_conv)
  apply (subst fst_conv)
  apply (monad_eq simp: corres_def)
  apply (intro exI conjI; (simp add: val_rel_simp)?)
  apply (rule u_sem_take_ub)
   apply (rule u_sem_var[of _ "[_]" _ 0, simplified])
  apply clarsimp
  apply (rule u_sem_take_ub; simp?)
   apply (rule u_sem_var[of _ "[_, _, _]" _ "Suc 0", simplified])
  apply clarsimp
  apply (rule u_sem_take_ub; simp?)
   apply (rule u_sem_var[of _ "[_, _, _, _, _]" _ "Suc 0", simplified])
  apply clarsimp
  apply (rename_tac b ba bb r x)
  apply (cut_tac 
      \<gamma> = "[UUnit,
            URecord [(UPrim (LU32 (t3_C.elem_C a')), b), (UPrim (LU32 (t3_C.acc_C a')), ba), (UUnit, bb)],
            UPrim (LU32 (t3_C.acc_C a')),
            URecord [(UPrim (LU32 (t3_C.elem_C a')), b), (UPrim (LU32 (t3_C.acc_C a')), ba), (UUnit, bb)],
            UPrim (LU32 (t3_C.elem_C a')),
            URecord [(UPrim (LU32 (t3_C.elem_C a')), b), (UPrim (LU32 (t3_C.acc_C a')), ba), (UUnit, bb)],
            URecord [(UPrim (LU32 (t3_C.elem_C a')), b), (UPrim (LU32 (t3_C.acc_C a')), ba), (UUnit, bb)]]"
      in u_sem_prim[of \<xi>' _ \<sigma> "[Var 4, Var 2]" \<sigma> 
        "[UPrim (LU32 (t3_C.elem_C a')), UPrim (LU32 (t3_C.acc_C a'))]" "Plus U32"])
   apply (rule u_sem_all_cons[of _ _ _ _ \<sigma>])
    apply (rule u_sem_var[of _ "[_, _, _, _, _, _, _]" _ "4", simplified])
   apply (rule u_sem_all_cons[of _ _ _ _ \<sigma>])
    apply (rule u_sem_var[of _ "[_, _, _, _, _, _, _]" _ "2", simplified])
   apply (rule u_sem_all_empty)
  apply (clarsimp simp: eval_prim_u_def)
  done

lemma sum_arr_corres:
  "\<lbrakk>\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''wordarray_length_0'' []) (Var i))
      (do x <- wordarray_length_0' v'; gets (\<lambda>s. x) od) \<xi>' \<gamma> \<Xi>  \<Gamma>' \<sigma> st;
    \<And>v' i \<gamma> \<Gamma> \<sigma> s.
    \<lbrakk>t5_C.f_C v' = FUN_ENUM_sum; i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma> ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_fold_no_break_0'')))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''wordarray_fold_no_break_0'' []) (Var i))
      (do x <- wordarray_fold_no_break_0' v'; gets (\<lambda>s. x) od) \<xi>' \<gamma> \<Xi> \<Gamma> \<sigma> s;
    val_rel a a'\<rbrakk>
    \<Longrightarrow> corres state_rel Generated_TypeProof.sum_arr (sum_arr' a') \<xi>' [a] \<Xi>
     [option.Some (prod.fst (prod.snd Generated_TypeProof.sum_arr_type))] \<sigma> s"
  apply (unfold sum_arr_def sum_arr'_def sum_arr_type_def abbreviated_type_defs val_rel_simp cogent_function_val_rel)
  apply (elim exE conjE)
  apply (subst unknown_bind_ignore)
  apply (subst snd_conv)
  apply (subst fst_conv)
  apply (monad_eq simp: corres_def)
  apply (drule_tac x = 0 in meta_spec)
  apply (drule_tac x = "[a]" in meta_spec)
  apply (drule_tac x = a' in meta_spec)
  apply clarsimp
  apply (drule_tac x = "[option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))]" in meta_spec)
  apply (drule_tac x = \<sigma> in meta_spec)
  apply (drule_tac x = s in meta_spec)
  apply clarsimp
  apply (rename_tac repr r w)
  apply (erule impE)
   apply (rule_tac x = r in exI)
   apply (rule_tac x = w in exI)
   apply (clarsimp simp: \<Xi>_def wordarray_length_0_type_def abbreviated_type_defs)
  apply clarsimp
  apply (intro exI conjI; (simp add: val_rel_simp)?)
   apply (rule allI)+
   apply (rename_tac r' s')
   apply (erule_tac x = r' in allE)
   apply (erule_tac x = s' in allE)
   apply (rule impI)
   apply (erule impE, assumption)
   apply (drule_tac x = "t5_C a' 0 r' FUN_ENUM_sum 0 (unit_t_C 0)" in meta_spec)
   apply (drule_tac x = 0 in meta_spec)
   apply clarsimp
   apply (drule_tac 
      x = "[mk_urecord [UPtr (ptr_val a') repr, 
            UPrim (LU32 0), UPrim (LU32 r'),  
            UFunction Generated_TypeProof.sum [], 
            UPrim (LU32 0), 
            UUnit]]" in meta_spec)
   apply clarsimp
   apply (drule_tac x = "[option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_fold_no_break_0'')))]" in meta_spec)
   apply (rename_tac \<sigma>')
   apply (drule_tac x = \<sigma>' in meta_spec)
   apply (drule_tac x = s' in meta_spec)
   apply clarsimp
   apply (elim u_sem_appE u_sem_afunE u_sem_funE u_sem_varE; simp?)
   apply (erule upd.matches_ptrs_consE; clarsimp)
   apply (rename_tac ra wa rb wb)
   apply (drule upd.proc_env_matches_ptrs_abstract[where \<tau>s = "[]", simplified]; simp?,
      (simp add: \<Xi>_def wordarray_length_0_type_def abbreviated_type_defs)?)
   apply (clarsimp simp: abbreviated_type_defs[symmetric] wordarray_length_0_type_def[symmetric] \<Xi>_def[symmetric])
   apply (frule_tac k = "{D, S}" and K = "[]" in upd.shareable_not_writable(1)[rotated 1]; simp?)
    apply (rule kindingI; simp?)
   apply (drule upd.uval_typing_frame; simp?)
   apply (erule_tac x = ra in allE)
   apply (erule_tac x = "{}" in allE)
  apply (rotate_tac -1)
   apply (erule notE)
   apply (clarsimp simp: wordarray_fold_no_break_0_type_def abbreviated_type_defs)
  apply (intro upd.matches_ptrs_some[where r' = "{}" and w' = "{}", simplified]
      upd.matches_ptrs_empty[where \<tau>s = "[]", simplified])
   apply (rule upd.u_t_struct; simp?)
   apply (intro upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified] 
      upd.u_t_prim' upd.u_t_unit upd.u_t_r_empty; simp?)
    apply (rule upd.u_t_function[OF sum_typecorrect']; (simp add: sum_type_def abbreviated_type_defs subtyping_refl)?)
   apply (drule upd.type_repr_uval_repr; simp)
  apply clarsimp
  apply (rename_tac r'a s'a r' s')
  apply (erule_tac x = r' in allE)
  apply (erule_tac x = s' in allE)
  apply (erule impE, assumption)
  apply (drule_tac x = "t5_C a' 0 r' FUN_ENUM_sum 0 (unit_t_C 0)" in meta_spec)
  apply (drule_tac x = 0 in meta_spec)
  apply clarsimp
  apply (drule_tac 
      x = "[mk_urecord [UPtr (ptr_val a') repr, 
            UPrim (LU32 0), UPrim (LU32 r'),  
            UFunction Generated_TypeProof.sum [], 
            UPrim (LU32 0), 
            UUnit]]" in meta_spec)
  apply clarsimp
  apply (drule_tac x = "[option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_fold_no_break_0'')))]" in meta_spec)
  apply (rename_tac \<sigma>')
  apply (drule_tac x = \<sigma>' in meta_spec)
  apply (drule_tac x = s' in meta_spec)
  apply clarsimp
  apply (erule impE)
   apply (elim u_sem_appE u_sem_afunE u_sem_funE u_sem_varE; simp?)
   apply (erule upd.matches_ptrs_consE; clarsimp)
   apply (rename_tac ra wa rb wb)
   apply (drule upd.proc_env_matches_ptrs_abstract[where \<tau>s = "[]", simplified]; simp?,
      (simp add: \<Xi>_def wordarray_length_0_type_def abbreviated_type_defs)?)
   apply (clarsimp simp: abbreviated_type_defs[symmetric] wordarray_length_0_type_def[symmetric] \<Xi>_def[symmetric])
   apply (frule_tac k = "{D, S}" and K = "[]" in upd.shareable_not_writable(1)[rotated 1]; simp?)
    apply (rule kindingI; simp?)
   apply (drule upd.uval_typing_frame; simp?)
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = "{}" in exI)
   apply (clarsimp simp: wordarray_fold_no_break_0_type_def abbreviated_type_defs)
   apply (intro upd.matches_ptrs_some[where r' = "{}" and w' = "{}", simplified]
      upd.matches_ptrs_empty[where \<tau>s = "[]", simplified])
   apply (rule upd.u_t_struct; simp?)
   apply (intro upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified] 
      upd.u_t_prim' upd.u_t_unit upd.u_t_r_empty; simp?)
    apply (rule upd.u_t_function[OF sum_typecorrect']; (simp add: sum_type_def abbreviated_type_defs subtyping_refl)?)
   apply (drule upd.type_repr_uval_repr; simp)
  apply clarsimp
  apply (erule_tac x = r'a in allE)
  apply (erule_tac x = s'a in allE)
  apply clarsimp
  apply (rename_tac \<sigma>'')
  apply (intro exI conjI; simp?)
  apply (elim u_sem_appE u_sem_afunE u_sem_funE; simp)
  apply clarsimp
  apply (intro u_sem_let u_sem_var u_sem_afun u_sem_abs_app u_sem_lit u_sem_fun u_sem_unit u_sem_struct; simp?; clarsimp?)
          apply (rule u_sem_afun)
         apply (rule u_sem_var[of _ "[_, _]" _ 0, simplified])
        apply (rule u_sem_lit)
       apply (rule u_sem_fun)
      apply (rule u_sem_lit)
     apply (rule u_sem_unit)
    apply (rule u_sem_struct)
    apply (rule u_sem_all_cons, rule u_sem_var)+
    apply (rule u_sem_all_empty)
   apply (rule u_sem_afun)
  apply clarsimp
  apply (elim u_sem_varE; clarsimp)
  apply (erule upd.matches_ptrs_consE; clarsimp)
  apply (drule upd.type_repr_uval_repr; simp)
  apply (rule u_sem_var[of _ "[_, _, _, _, _, _, _, _]" _ 0, simplified])
  done

lemma sum_scorres:
  "valRel \<xi>' v v' \<Longrightarrow> val.scorres (Generated_Shallow_Normal.sum v) (specialise ts Generated_Deep_Normal.sum) [v'] \<xi>'"
  apply (unfold Generated_Shallow_Normal.sum_def Generated_Deep_Normal.sum_def[simplified])
  apply (simp only: specialise.simps valRel_records)
  apply (elim exE conjE)
  apply (simp only: valRel_unit.simps valRel_u32.simps)
  apply (intro val.scorres_take val.scorres_var[simplified val.shallow_tac__var_def]
      scorres_rec_fields[simplified] val.scorres_prim_add; 
      simp add: valRel_records val.shallow_tac__var_def)
     apply (fastforce intro: scorres_rec_fields[simplified])+
  apply (intro val.scorres_prim_add val.scorres_var[simplified val.shallow_tac__var_def];
      simp add: valRel_records)
  done

lemma sum_arr_scorres:
  "\<lbrakk>\<And>i \<gamma> v ts. \<lbrakk>i < length \<gamma>; valRel \<xi>' (v::(32 word) WordArray) (\<gamma> ! i)\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_length v) (App (AFun ''wordarray_length'' ts) (Var i)) \<gamma> \<xi>';
    \<And>i \<gamma> v ts. \<lbrakk>i < length \<gamma>; valRel \<xi>' (v::((32 word) WordArray, 32 word, 32 word,
      (32 word, 32 word, unit) ElemAO \<Rightarrow> 32 word, 32 word, unit) WordArrayMapP) (\<gamma> ! i);
      WordArrayMapP.f\<^sub>f v = Generated_Shallow_Normal.sum;
      \<exists>fs. \<gamma> ! i = VRecord fs \<and> fs ! 3 = (VFunction Generated_Deep_Normal.sum [])\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_fold_no_break v) (App (AFun ''wordarray_fold_no_break'' ts) (Var i)) \<gamma> \<xi>';
    valRel \<xi>' v v'\<rbrakk>
  \<Longrightarrow> val.scorres (Generated_Shallow_Normal.sum_arr v) (specialise ts Generated_Deep_Normal.sum_arr) [v'] \<xi>'"
  apply (unfold Generated_Shallow_Normal.sum_arr_def Generated_Deep_Normal.sum_arr_def)
  apply (simp only: specialise.simps)
  apply (clarsimp simp: val.scorres_def)
  apply (erule v_sem_varE)+
  apply clarsimp
  apply (drule_tac x = 0 in meta_spec)
  apply (rename_tac r len)
  apply (drule_tac x = "[v', v']" in meta_spec)
  apply (drule_tac x = v in meta_spec)
  apply (drule_tac x = "[TPrim (Num U32)]" in meta_spec)
  apply clarsimp
  apply (erule_tac x = len in allE)
  apply clarsimp
  apply (drule_tac x = 0  in meta_spec)
  apply (drule_tac x = "[VRecord [v', VPrim (LU32 0), VPrim (LU32 (wordarray_length v)), 
      VFunction Generated_Deep_Normal.sum [], VPrim (LU32 0), VUnit],
    VUnit, VPrim (LU32 0), VFunction Generated_Deep_Normal.sum [], VPrim (LU32 0),
    VPrim (LU32 (wordarray_length v)), v', v']" in meta_spec)
  apply (drule_tac x = "\<lparr>WordArrayMapP.arr\<^sub>f = v, frm\<^sub>f = 0, to\<^sub>f = (wordarray_length v),
    f\<^sub>f = Generated_Shallow_Normal.sum, acc\<^sub>f = 0, obsv\<^sub>f = ()\<rparr>" in meta_spec)
  apply (drule_tac x = "[TPrim (Num U32), TPrim (Num U32), TUnit]" in meta_spec)
  apply clarsimp
  apply (erule meta_impE)
   apply (simp add: valRel_records)
   apply clarsimp
   apply (cut_tac v' = "VRecord [VPrim (LU32 (ElemAO.elem\<^sub>f x)), VPrim (LU32 (ElemAO.acc\<^sub>f x)), VUnit]"
      in sum_scorres[where \<xi>' = \<xi>' and ts = "[]", simplified val.scorres_def specialise.simps],
      (simp add: valRel_records)?)
   apply (rename_tac s)
   apply (erule_tac x = s in allE)
   apply clarsimp
  apply (erule_tac x = r in allE)
  apply (clarsimp simp: valRel_records)
  done

section "The Shallow to C Correspondence With Assumptions"

lemma sum_arr_corres_shallow_C:
  "\<lbrakk>\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr)
         (App (AFun ''wordarray_length_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_length_0' v'; gets (\<lambda>s. x) od)
         \<xi>1' \<gamma> \<Xi> \<Gamma>' \<sigma> st;
    \<And>v' i \<gamma> \<Gamma> \<sigma> s.
    \<lbrakk>t5_C.f_C v' = FUN_ENUM_sum; i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma> ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_fold_no_break_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr)
         (App (AFun ''wordarray_fold_no_break_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_fold_no_break_0' v'; gets (\<lambda>s. x) od)
         \<xi>1' \<gamma> \<Xi> \<Gamma> \<sigma> s;
    \<And>i \<gamma> v ts.
    \<lbrakk>i < length \<gamma>; valRel \<xi>\<^sub>p (v::(32 word) WordArray) (\<gamma> ! i)\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_length v) (App (AFun ''wordarray_length'' ts) (Var i)) \<gamma> \<xi>\<^sub>p;
    \<And>i \<gamma> v ts.
    \<lbrakk>i < length \<gamma>; valRel \<xi>\<^sub>p (v::((32 word) WordArray, 32 word, 32 word,
      (32 word, 32 word, unit) ElemAO \<Rightarrow> 32 word, 32 word, unit) WordArrayMapP) (\<gamma> ! i);
     WordArrayMapP.f\<^sub>f v = Generated_Shallow_Normal.sum;
     \<exists>fs. \<gamma> ! i = VRecord fs \<and> fs ! 3 = (VFunction Generated_Deep_Normal.sum [])\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_fold_no_break v) (App (AFun ''wordarray_fold_no_break'' ts) (Var i)) \<gamma> \<xi>\<^sub>p;
    value_sem.rename_mono_prog wa_abs_typing_v rename \<Xi> \<xi>\<^sub>m \<xi>\<^sub>p; vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
    correspondence_init.val_rel_shallow_C wa_abs_repr wa_abs_upd_val rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>\<^sub>p \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
    value_sem.proc_env_matches wa_abs_typing_v \<xi>\<^sub>m \<Xi>;
    value_sem.matches wa_abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.sum_arr_type))]\<rbrakk>
    \<Longrightarrow> correspondence_init.corres_shallow_C wa_abs_repr wa_abs_typing_u wa_abs_upd_val rename (Generated.state_rel wa_abs_repr)
     (Generated_Shallow_Desugar.sum_arr vv\<^sub>s) Generated_TypeProof.sum_arr (main_pp_inferred.sum_arr' uv\<^sub>C) \<xi>1' \<xi>\<^sub>m \<xi>\<^sub>p
     [uv\<^sub>m] [vv\<^sub>m] \<Xi> [option.Some (prod.fst (prod.snd Generated_TypeProof.sum_arr_type))] \<sigma> s"
  apply (subgoal_tac "Generated_Shallow_Desugar.sum_arr = Generated_Shallow_Normal.sum_arr")
   apply (rule corres_shallow_C_intro[OF _ _ _ _ sum_arr_typecorrect',
        of rename Generated_Deep_Normal.sum_arr vv\<^sub>m vv\<^sub>p _ _ _ _ uv\<^sub>C _ _ _ _ _ vv\<^sub>s]; simp)
     apply (simp add: Generated_TypeProof.sum_arr_def Generated_Deep_Normal.sum_arr_def)
     apply (subst rename_def; simp)+
     apply (simp add: Generated_Deep_Normal.sum_def Generated_TypeProof.sum_def 
      Generated_TypeProof.abbreviated_type_defs Generated_Deep_Normal.abbreviated_type_defs)
    apply (rule sum_arr_corres; simp?)
    apply (drule val_rel_shallow_C_elim; simp)
   apply (rule sum_arr_scorres[where ts = "[]", simplified])
     apply (drule val_rel_shallow_C_elim; simp)+
   apply (clarsimp simp: Generated_Shallow_Desugar.sum_arr_def Generated_Shallow_Normal.sum_arr_def fun_eq_iff)
   apply (unfold Generated_Shallow_Desugar.sum_def Generated_Shallow_Normal.sum_def)
   apply simp
  done

lemma \<xi>1_wordarray_length:
  "\<xi>1 ''wordarray_length_0'' = upd_wa_length_0"
  apply (clarsimp simp: fun_eq_iff)
  done

lemmas wordarray_length_u32_corres = upd_C_wordarray_length_corres_gen[rotated -1, of \<xi>1, OF \<xi>1_wordarray_length]

lemma wordarray_fold_no_break_u32_corres:
  "\<And>v' i \<gamma> \<Gamma> \<sigma> s.
    \<lbrakk>t5_C.f_C v' = FUN_ENUM_sum; i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma> ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_fold_no_break_0'')))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''wordarray_fold_no_break_0'' []) (Var i)) (do x <- wordarray_fold_no_break_0' v';
                  gets (\<lambda>s. x)
               od)
         \<xi>1 \<gamma> \<Xi> \<Gamma> \<sigma> s"
  thm upd_C_wordarray_fold_no_break_corres_gen
  apply (subgoal_tac "\<exists>fs. (\<gamma> ! i) = URecord fs")
   apply (erule exE)
   apply (rule_tac k = "kinding_fn [] (foldmap_obsv_type ''wordarray_fold_no_break_0'')" and
      \<xi>0' = \<xi>0 and K' = "[]" and num = U32
      in upd_C_wordarray_fold_no_break_corres_gen; simp?)
          apply (rule upd_proc_env_matches_ptrs_\<xi>0_\<Xi>)
         apply (rule disjI1)
         apply (clarsimp simp: \<Xi>_def wordarray_fold_no_break_0_type_def)
        apply (clarsimp simp: \<Xi>_def wordarray_fold_no_break_0_type_def)
       apply (rule kindingI; simp)
      apply (clarsimp simp: \<Xi>_def  wordarray_fold_no_break_0_type_def val_rel_simp
      abbreviated_type_defs cogent_function_val_rel untyped_func_enum_defs)
    apply (rule typing_app[of _ 
      "[option.Some (TRecord [(''elem'', TPrim (Num U32), Present),
        (''acc'', TPrim (Num U32), Present), (''obsv'', TUnit, Present)] Unboxed)]"
      "[option.Some (TRecord [(''elem'', TPrim (Num U32), Present),
        (''acc'', TPrim (Num U32), Present), (''obsv'', TUnit, Present)] Unboxed)]"
      "[option.Some (TRecord [(''elem'', TPrim (Num U32), Present),
        (''acc'', TPrim (Num U32), Present), (''obsv'', TUnit, Present)] Unboxed)]"
      _ _
      "TRecord [(''elem'', TPrim (Num U32), Present), (''acc'', TPrim (Num U32), Present),
        (''obsv'', TUnit, Present)] Unboxed"] ; simp?)
      apply (clarsimp simp: split_def)
      apply (rule_tac k = "{D, S}" in share, rule kindingI; simp?)
     apply (rule typing_fun; simp?)
       apply (subst abbreviated_type_defs[symmetric])+
       apply (subst wordarray_fold_no_break_0_type_def[symmetric])
       apply (subst \<Xi>_def[symmetric])
       apply (rule sum_typecorrect'[simplified sum_type_def snd_conv fst_conv])
      apply (clarsimp simp: empty_def weakening_def)
      apply (rule_tac k = "{D, S}" in drop, rule kindingI; simp?)
     apply clarsimp
    apply (subst abbreviated_type_defs[symmetric])+
    apply (subst wordarray_fold_no_break_0_type_def[symmetric])
    apply (subst \<Xi>_def[symmetric])
    apply (rule typing_var)
     apply (clarsimp simp: weakening_def empty_def)
     apply (rule keep)
     apply (clarsimp simp: abbreviated_type_defs)
      apply clarsimp
     apply (clarsimp simp: val_rel_simp cogent_function_val_rel untyped_func_enum_defs)
     apply (subst dispatch_t4'_def; simp)
     apply (subst unknown_bind_ignore)
     apply (simp add: untyped_func_enum_defs)
     apply (rule corres_app_concrete[simplified]; (simp del: \<xi>0.simps)?)
     apply (simp add: \<Xi>_def wordarray_fold_no_break_0_type_def del: \<xi>0.simps)
     apply (subst wordarray_fold_no_break_0_type_def[symmetric])
     apply (subst \<Xi>_def[symmetric])
     apply (rule sum_corres[simplified sum_type_def snd_conv fst_conv])
     apply (clarsimp simp: val_rel_simp)
    apply (clarsimp simp: fun_eq_iff)
   apply (clarsimp simp: \<Xi>_def wordarray_fold_no_break_0_type_def abbreviated_type_defs)
  apply (clarsimp simp: val_rel_simp)
  done

lemma wordarray_length_u32_scorres:
  "\<And>i \<gamma> v ts.
   \<lbrakk>i < length \<gamma>; valRel \<xi>p1 (v::32 word WordArray) (\<gamma> ! i)\<rbrakk> 
    \<Longrightarrow> val.scorres (wordarray_length v) (App (AFun ''wordarray_length'' ts) (Var i)) \<gamma> \<xi>p1"
  apply (rule scorres_wordarray_length; clarsimp simp: fun_eq_iff \<xi>p.simps)
  done

lemma wordarray_fold_no_break_u32_scorres:
  "\<And>i \<gamma> v ts.
   \<lbrakk>i < length \<gamma>; valRel \<xi>p1 (v::((32 word) WordArray, 32 word, 32 word,
      (32 word, 32 word, unit) ElemAO \<Rightarrow> 32 word, 32 word, unit) WordArrayMapP) (\<gamma> ! i);
    WordArrayMapP.f\<^sub>f v = Generated_Shallow_Normal.sum;
    \<exists>fs. \<gamma> ! i = VRecord fs \<and> fs ! 3 = VFunction Generated_Deep_Normal.sum []\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_fold_no_break v) (App (AFun ''wordarray_fold_no_break'' ts) (Var i)) \<gamma> \<xi>p1"
  apply (subgoal_tac "\<exists>arr frm to f acc obsv. v = \<lparr>WordArrayMapP.arr\<^sub>f = arr, frm\<^sub>f = frm, to\<^sub>f = to,
    f\<^sub>f = f, acc\<^sub>f = acc, obsv\<^sub>f = obsv\<rparr>")
   apply clarsimp
   apply (rule_tac \<xi>p' = \<xi>p in scorres_wordarray_fold_no_break_u32; simp?)
  apply (clarsimp simp: fun_eq_iff )
   apply (clarsimp simp: valRel_records valRel_WordArray_simps)
   apply (rename_tac x v')
   apply (cut_tac v = x and ts = "[]" and \<xi>' = \<xi>p and 
      v' = "VRecord [VPrim (LU32 (ElemAO.elem\<^sub>f x)), VPrim (LU32 (ElemAO.acc\<^sub>f x)), VUnit]" in sum_scorres)
    apply (clarsimp simp: valRel_records)
   apply (clarsimp simp: val.scorres_def)
  apply (clarsimp simp: valRel_records valRel_WordArray_simps)
  apply (rule_tac x = "WordArrayMapP.arr\<^sub>f v" in exI)
  apply (rule_tac x = "WordArrayMapP.frm\<^sub>f v" in exI)
  apply (rule_tac x = "WordArrayMapP.to\<^sub>f v" in exI)
  apply (rule_tac x = "Generated_Shallow_Normal.sum" in exI)
  apply (rule_tac x = "WordArrayMapP.acc\<^sub>f v" in exI)
  apply clarsimp
  done

section "Putting It All Together"

text
  "Now with @{thm wordarray_length_u32_corres wordarray_fold_no_break_u32_corres
   wordarray_length_u32_scorres wordarray_fold_no_break_u32_scorres} we can remove the assumptions
   about about @{term corres} and @{term val.scorres} for @{term wordarray_length} and
   @{term wordarray_fold_no_break}."

lemma sum_arr_corres_shallow_C_concrete:
  "\<lbrakk>value_sem.rename_mono_prog wa_abs_typing_v rename \<Xi> \<xi>m1 \<xi>p1; vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
    correspondence_init.val_rel_shallow_C wa_abs_repr wa_abs_upd_val rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p1 \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
    value_sem.proc_env_matches wa_abs_typing_v \<xi>m1 \<Xi>;
    value_sem.matches wa_abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.sum_arr_type))]\<rbrakk>
    \<Longrightarrow> correspondence_init.corres_shallow_C wa_abs_repr wa_abs_typing_u wa_abs_upd_val rename (Generated.state_rel wa_abs_repr)
     (Generated_Shallow_Desugar.sum_arr vv\<^sub>s) Generated_TypeProof.sum_arr (main_pp_inferred.sum_arr' uv\<^sub>C) \<xi>1 \<xi>m1 \<xi>p1
     [uv\<^sub>m] [vv\<^sub>m] \<Xi> [option.Some (prod.fst (prod.snd Generated_TypeProof.sum_arr_type))] \<sigma> s"
  apply (rule sum_arr_corres_shallow_C; simp?)
     apply (rule wordarray_length_u32_corres[simplified]; simp)
    apply (rule wordarray_fold_no_break_u32_corres[simplified]; simp)
   apply (rule wordarray_length_u32_scorres; simp)
  apply (rule wordarray_fold_no_break_u32_scorres; simp)
  done

section "Further Improvements"

text
  "We can go one step further by removing the assumptions:
    * @{term \<open>value_sem.rename_mono_prog wa_abs_typing_v rename \<Xi> \<xi>m1 \<xi>p1\<close>},
    * @{term \<open>proc_ctx_wellformed \<Xi>\<close>},
    * @{term \<open>value_sem.proc_env_matches wa_abs_typing_v \<xi>m1 \<Xi>\<close>}.

   The @{term \<open>value_sem.rename_mono_prog\<close>} assumption ensures that  monomorphisation of the whole
   Cogent program preserves the semantics of abstract functions. With this assumption, we can prove
   that the monomorphic deep embedding of Cogent expressions refine their polymorphic deep embeddings.
   We prove this is the case in  @{thm value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m1_\<xi>p1}. Note that the
   renaming that occurs due to monomorphisation only really affects abstract functions due to their
   deep embedding being of the form @{term \<open>VAFunction f ts\<close>}, where @{term \<open>(f:: string)\<close>} is the
   name of the monomorphised abstract function. @{term \<open>value_sem.rename_mono_prog\<close>} is proved
   by unfolding the definitions of the deep embeddings of the abstract function and case analysis on
   the arguments and return values. For functions such as @{term wordarray_length}, whose deep
   embedding is very simple, this proof is very simple. For more complex functions such as
   @{term wordarray_fold_no_break}, is more tricky due to the fact that
   @{term wordarray_fold_no_break} is a higher order function, so we need to know that the function
   it takes as an argument preserves it semantics when monomorphisation. We solve this by first
   proving @{term \<open>value_sem.rename_mono_prog\<close>} for first order abstract function and then use that
   result in conjunction with @{thm val.rename_monoexpr_correct} to prove
   @{term \<open>value_sem.rename_mono_prog\<close>} for second order functions. Note that
   @{thm val.rename_monoexpr_correct} assumes @{term \<open>proc_ctx_wellformed\<close>} and
   @{term \<open>value_sem.proc_env_matches\<close>}, which we can prove as described below.
   We proved @{term \<open>value_sem.rename_mono_prog\<close>} in @{thm value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p
   value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m1_\<xi>p1} for first order and second order abstract functions
   defined in @{term \<xi>m}, @{term \<xi>m1}, @{term \<xi>p} and @{term \<xi>p1}.

   The @{term \<open>proc_ctx_wellformed\<close>} assumption states that the types of our abstract functions
   are type well-formed. This was fairly easy to prove as it follows from the definition of the
   types of abstract functions (@{thm proc_ctx_wellformed_\<Xi>}.

   The @{term \<open>value_sem.proc_env_matches\<close>} assumption guarantees the preservation of types for
   abstract functions. The key theorems @{thm val.mono_correct val.rename_monoexpr_correct}, which
   are used to prove that the monomorphised Cogent expressions refine their polymorphic counterparts.
   For abstract functions which are not higher order and do not do any recursion/iteration, it is
   fairly easy to prove type preservation as this follows from the definition and by using the
   the @{term val.vval_typing} and @{term val.vval_typing_record} rules. For recursive/iterative
   functions, this becomes more complex as one would typically need to rely on some sort of
   invariant. For higher order functions, we need to know that all functions that they could possibly
   call also preserve typing, however, in our definition of higher order abstract functions, abstract
   functions can only call first order functions, and we only support up to (and including) second
   order functions. So we can first prove type preservation for all first order functions, and use
   this to prove type preservation for higher order functions. We proved
   @{term \<open>value_sem.proc_env_matches\<close>} in @{thm val_proc_env_matches_\<xi>m_\<Xi>
   val_proc_env_matches_\<xi>m1_\<Xi>} for first order and second order abstract functions defined in
   @{term \<xi>m} and @{term \<xi>m1}."

lemmas sum_arr_corres_shallow_C_concrete_strong = 
  sum_arr_corres_shallow_C_concrete[OF value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m1_\<xi>p1 _ _ 
                                       proc_ctx_wellformed_\<Xi> val_proc_env_matches_\<xi>m1_\<Xi>]

section "Even More Improvement"

text 
  "If we look at the definition of @{term corres_shallow_C}, you will notice that we are implicitly
   assuming that type preservation holds for the deep embedding of abstract functions in the update
   semantics, abstract functions satisfy the @{term frame} constraints. the the deep embeddings of
   abstract functions in the update and value semantics correspond, and that the if the deep embedding
   of an abstract function executes in the update semantics, the corresponding deep embedding in the
   value semantics will also execute (upward propagation of evaluation). These assumptions are
   contained in @{term upd.proc_env_matches_ptrs} and @{term proc_env_u_v_matches}.

   Type preservation for abstract functions in the update semantics and @{term frame} constraint
   satisfiability is contained in @{term upd.proc_env_matches_ptrs}, and can be proved in a similar
   fashion to proving @{term \<open>value_sem.proc_env_matches\<close>} with the addition of using some lemmas
   @{term frame} constraints. We proved @{term upd.proc_env_matches_ptrs} in
   @{thm upd_proc_env_matches_ptrs_\<xi>0_\<Xi> upd_proc_env_matches_ptrs_\<xi>1_\<Xi>} for first order and second
   order abstract functions defined in @{term \<xi>0} and @{term \<xi>1}.
  
   Proving correspondence and upward propagation is contained in @{term proc_env_u_v_matches}.
   For non higher order functions, we can prove this by unfolding the definitions of the two deep
   embeddings and use the rules on @{term upd_val_rel} and @{term upd_val_rel_record}. For higher
   order functions, it is easier to first prove correspondence separately, and use this result to
   prove upward propagation using the  @{thm val_executes_from_upd_executes}. Note that proving
   correspondence requires the knowledge that all the deep embeddings of the functions that could be
   called correspond and upward propagation is true. So we need to first prove 
   @{term proc_env_u_v_matches} for all the orders below the current and then we can apply the
   @{thm mono_correspondence} to prove correspondence for the function argument. We proved
   @{term proc_env_u_v_matches} in @{thm proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi> proc_env_u_v_matches_\<xi>1_\<xi>m1_\<Xi>}
   for first order and second order abstract functions defined in @{term \<xi>0}, @{term \<xi>1}, @{term \<xi>m}
   and @{term \<xi>m1}."

lemma sum_arr_corres_shallow_C_concrete_stronger:
  "\<lbrakk>vv\<^sub>m = val.rename_val rename (val.monoval vv\<^sub>p); val_rel_shallow_C rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p1 \<sigma> \<Xi>;
    val.matches \<Xi> [val.rename_val rename (val.monoval vv\<^sub>p)] 
      [option.Some (prod.fst (prod.snd Generated_TypeProof.sum_arr_type))]\<rbrakk>
    \<Longrightarrow> 
    (\<sigma>, s) \<in> state_rel \<longrightarrow>
    (\<exists>r w. u_v_matches \<Xi> \<sigma> [uv\<^sub>m] [val.rename_val rename (val.monoval vv\<^sub>p)]
            [option.Some (prod.fst (prod.snd Generated_TypeProof.sum_arr_type))] r w) \<longrightarrow>
    \<not> prod.snd (sum_arr' uv\<^sub>C s) \<and>
    (\<forall>r' s'.
        (r', s') \<in> prod.fst (sum_arr' uv\<^sub>C s) \<longrightarrow>
        (\<exists>\<sigma>' v\<^sub>u\<^sub>m v\<^sub>p.
            \<xi>1, [uv\<^sub>m] \<turnstile> (\<sigma>, Generated_TypeProof.sum_arr) \<Down>! (\<sigma>', v\<^sub>u\<^sub>m) \<and>
            \<xi>m1 , [val.rename_val rename
                    (val.monoval vv\<^sub>p)] \<turnstile> Generated_TypeProof.sum_arr \<Down> val.rename_val rename (val.monoval v\<^sub>p) \<and>
            (\<sigma>', s') \<in> state_rel \<and> val_rel_shallow_C rename (Generated_Shallow_Desugar.sum_arr vv\<^sub>s) r' v\<^sub>p v\<^sub>u\<^sub>m \<xi>p1 \<sigma>' \<Xi>))"
  apply (frule sum_arr_corres_shallow_C_concrete_strong[simplified corres_shallow_C_def
        proc_ctx_wellformed_\<Xi> upd_proc_env_matches_ptrs_\<xi>1_\<Xi> proc_env_u_v_matches_\<xi>1_\<xi>m1_\<Xi>]; simp?)
  done

section "Proving Functional Correctness"

text
  "We can now easily prove the functional correctness of our @{term sum_arr'} C function. In this
   case, our @{term sum_arr'} C function should sum all the elements of the list which is of type
   @{typ \<open>32 word list\<close>} in our shallow embeeding. Our functional correctness specification would
   look like following:"

definition sum_list :: "32 word list \<Rightarrow> 32 word"
  where
"sum_list xs = fold (+) xs 0"

text
  "Our functional correctness specification @{term sum_list} calls the @{term fold} function to
   iterate of the list and add up all of its elements.

   Before we prove functional correctness, we need to observe that @{term wordarray_length} returns
   a value of type @{typ \<open>32 word\<close>}. This means that any list that refines to a word array in our
   C code should in fact be of length at most @{term \<open>max_word :: 32 word\<close>}. In fact, it should
   actually be less depending on the maximum heap size. You may notice that in our abstract typing
   in the update semantics @{thm wa_abs_typing_u_def}, we enforced that the length of an array times
   the size of an element in the array, should in fact be less than the maximum word, since an array
   larger than that would not fit in memory. So a using thing to prove is the following:"

lemma len_eq_walen_if_le_max32:
  "length xs \<le> unat (max_word :: 32 word)
    \<Longrightarrow> unat (wordarray_length xs) = length xs"
  apply (clarsimp simp: wordarray_length')
  apply (rule le_unat_uoi; simp)
  done

text
  "With this we can now prove functional correctness."

lemma sum_arr_correct:
  "length xs \<le> unat (max_word :: 32 word)
    \<Longrightarrow> sum_list xs = Generated_Shallow_Desugar.sum_arr xs"
  apply (clarsimp simp: sum_list_def Generated_Shallow_Desugar.sum_arr_def
      valRel_records wordarray_fold_no_break' Generated_Shallow_Desugar.sum_def
      len_eq_walen_if_le_max32 take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def)
  done

(*
term "{(a, b, c) | a b c. \<xi>0 a b c}"
definition \<xi>_le
  where "\<xi>_le \<xi>a \<xi>b = ({(a, b, c) | a b c. \<xi>a a b c} \<subseteq> {(a, b, c) | a b c. \<xi>b a b c})"

lemma "\<xi>_le \<xi>0 \<xi>1"
  apply (clarsimp simp: \<xi>_le_def)
  apply (drule Meson.imp_to_disjD; clarsimp)
  apply (drule Meson.imp_to_disjD; clarsimp)
  apply (erule disjE; clarsimp)
  apply (drule Meson.imp_to_disjD; clarsimp)
  apply (drule Meson.imp_to_disjD; clarsimp)
  apply (drule Meson.imp_to_disjD; clarsimp)
  apply (erule disjE; clarsimp)
   apply (intro exI conjI impI; simp)
  apply (intro exI conjI impI; simp)
  done


lemma "\<xi>_le \<xi>m \<xi>m1"
  apply (clarsimp simp: \<xi>_le_def)
  apply (drule Meson.imp_to_disjD; clarsimp)
  apply (drule Meson.imp_to_disjD; clarsimp)
  apply (erule disjE; clarsimp)
  apply (drule Meson.imp_to_disjD; clarsimp)
  apply (drule Meson.imp_to_disjD; clarsimp)
  apply (drule Meson.imp_to_disjD; clarsimp)
  apply (erule disjE; clarsimp)
   apply (intro exI conjI impI; simp)
  apply (intro exI conjI impI; simp)
  done

lemma \<xi>_le_imp: "\<xi>_le \<xi>a \<xi>b \<Longrightarrow> \<xi>a a b c \<longrightarrow> \<xi>b a b c"
  apply (clarsimp simp: \<xi>_le_def subset_eq)
  done

lemma "\<lbrakk>\<xi>_le \<xi>a \<xi>b; valRel \<xi>a (a :: 'c \<Rightarrow> 'd) b\<rbrakk> \<Longrightarrow> valRel \<xi>b a b"
  apply (clarsimp simp: valRel_records)
  apply (erule disjE; clarsimp)
  oops
*)
end (* of context *)

end
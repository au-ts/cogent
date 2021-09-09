theory RepeatAssm
  imports
    RepeatUpdate
    RepeatValue
    RepeatMono
    RepeatCorres
    RepeatCorrespondence
    RepeatScorres
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
  by (clarsimp simp: assoc_lookup.simps)

lemma \<Xi>_simps:
  "\<Xi> ''repeat_0'' = repeat_0_type"
  "\<Xi> ''repeat_1'' = repeat_1_type"
  "\<Xi> ''repeat_2'' = repeat_2_type"
  apply (clarsimp simp: \<Xi>_def)+
  done

section "Abstract functions specification for the update semantics"

text "If user defines \<xi>n, we can derive \<xi>i for i < n" 

overloading \<xi>0 \<equiv> \<xi>_0
begin
definition \<xi>0 :: "(funtyp, abstyp, ptrtyp) uabsfuns"
  where
"\<xi>0 f x y = False"
end
thm repeat_2_type_def
overloading \<xi>1 \<equiv> \<xi>_1
begin
definition \<xi>1 :: "(funtyp, abstyp, ptrtyp) uabsfuns"
  where
"\<xi>1 f x y = 
  (if f = ''repeat_0'' then urepeat \<Xi> \<xi>_0 Generated_TypeProof.abbreviatedType4 (TPrim (Num U64)) x y 
   else if f = ''repeat_1'' then urepeat \<Xi> \<xi>_0 (TPrim (Num U32)) (TPrim (Num U32)) x y
   else if f = ''repeat_2'' then urepeat \<Xi> \<xi>_0 Generated_TypeProof.abbreviatedType1 Generated_TypeProof.abbreviatedType2 x y
   else \<xi>_0 f x y)"
end

lemma \<xi>_1_simps:
  "\<xi>_1 ''repeat_0'' = urepeat \<Xi> \<xi>_0 Generated_TypeProof.abbreviatedType4 (TPrim (Num U64))"
  "\<xi>_1 ''repeat_1'' = urepeat \<Xi> \<xi>_0 (TPrim (Num U32)) (TPrim (Num U32))"
  "\<xi>_1 ''repeat_2'' = urepeat \<Xi> \<xi>_0 Generated_TypeProof.abbreviatedType1 Generated_TypeProof.abbreviatedType2"
  apply (clarsimp simp: \<xi>1_def fun_eq_iff)+
  done

subsection "Preservation for abstract functions"

context update_sem_init begin

text "If user proves for \<xi>n, we can derive \<xi>i for i < n" 

lemma \<xi>_0_matchesu_\<Xi>:
  "\<xi>_0 matches-u \<Xi>'"
  unfolding proc_env_matches_ptrs_def \<xi>0_def
  by clarsimp
 
lemma \<xi>_1_matchesu_\<Xi>:
  "\<xi>_1 matches-u \<Xi>"
  unfolding proc_env_matches_ptrs_def \<xi>1_def
  apply clarsimp
  apply (intro conjI impI; clarsimp simp: \<Xi>_simps)
    apply (clarsimp simp: repeat_1_type_def repeat_0_type_def repeat_2_type_def;
           rule_tac urepeat_preservation[OF proc_ctx_wellformed_\<Xi> \<xi>_0_matchesu_\<Xi>];
           (simp add: Generated_TypeProof.abbreviated_type_defs))+
  apply (cut_tac \<Xi>' = \<Xi> in  \<xi>_0_matchesu_\<Xi>[unfolded proc_env_matches_ptrs_def]; clarsimp split: prod.splits)
  apply (elim allE impE conjE; assumption?)
  apply blast
  done
end (* of context *)

subsection "Partial ordering on abstract functions"

text "These should be automatable"

lemma \<xi>_0_le_\<xi>_1:
  "rel_leq \<xi>_0 \<xi>_1"
  unfolding \<xi>0_def rel_leq_def
  by simp

subsection "Abstract functions are deterministic"

text "If user proves for \<xi>n, we can derive \<xi>i for i < n" 

lemma \<xi>_0_determ:
  "determ \<xi>_0"
  unfolding determ_def \<xi>0_def
  by simp

lemma \<xi>_1_determ:
  "determ \<xi>_1"
  unfolding determ_def \<xi>1_def
  apply clarsimp
  apply (intro conjI impI allI; clarsimp?)
   apply (drule (1) urepeat_deterministic[OF \<xi>_0_determ]; simp)+
   apply (drule (1) determD[OF \<xi>_0_determ]; simp)+
  done


section "Abstract functions specifications for the monomorphic value semantics"

context monomorph_sem begin

text "If user defines for \<xi>n, we can derive \<xi>i for i < n" 

definition \<xi>m0 :: "'b \<Rightarrow> ('b, 'a) vval \<Rightarrow> ('b, 'a) vval \<Rightarrow> bool "
  where
"\<xi>m0 f x y = False"

definition \<xi>m1 :: "funtyp \<Rightarrow> (funtyp, 'a) vval \<Rightarrow> (funtyp, 'a) vval \<Rightarrow> bool "
  where
"\<xi>m1 f x y = 
  (if f = ''repeat_0'' then vrepeat \<Xi> \<xi>m0 Generated_TypeProof.abbreviatedType4 (TPrim (Num U64)) x y 
   else if f = ''repeat_1'' then vrepeat \<Xi> \<xi>m0 (TPrim (Num U32)) (TPrim (Num U32)) x y
   else if f = ''repeat_2'' then vrepeat \<Xi> \<xi>m0 Generated_TypeProof.abbreviatedType1 Generated_TypeProof.abbreviatedType2 x y
   else \<xi>m0 f x y)"

subsection "Preservation for abstract functions"

text "If user proves for \<xi>n, we can derive \<xi>i for i < n" 

lemma \<xi>m0_matches_\<Xi>:
  "\<xi>m0 matches \<Xi>'"
  unfolding proc_env_matches_def \<xi>m0_def
  by clarsimp

lemma \<xi>m1_matches_\<Xi>:
  "\<xi>m1 matches \<Xi>"
  unfolding proc_env_matches_def \<xi>m1_def
  apply clarsimp
  apply (intro conjI impI)
    apply (clarsimp simp: \<Xi>_simps repeat_1_type_def repeat_0_type_def repeat_2_type_def;
           rule vrepeat_preservation[OF proc_ctx_wellformed_\<Xi> \<xi>m0_matches_\<Xi>];
           (simp add: Generated_TypeProof.abbreviated_type_defs)?)+
  apply (cut_tac \<Xi>' = \<Xi> in \<xi>m0_matches_\<Xi>[unfolded proc_env_matches_def]; clarsimp split: prod.splits)
  done

subsection "Partial ordering on abstract functions"

text "Should be automatable"

lemma \<xi>m0_le_\<xi>m1:
  "rel_leq \<xi>m0 \<xi>m1"
  unfolding \<xi>m0_def rel_leq_def
  by simp

subsection "Abstract functions are deterministic"

text "If user proves for \<xi>n, we can derive \<xi>i for i < n" 

lemma \<xi>m0_determ:
  "determ \<xi>m0"
  unfolding determ_def \<xi>m0_def
  by simp

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

definition \<xi>p0 :: "'b \<Rightarrow> ('b, 'c) vval \<Rightarrow> ('b, 'c) vval \<Rightarrow> bool"
  where
"\<xi>p0 f x y = False"

definition \<xi>p1 :: "funtyp \<Rightarrow> (funtyp, 'c) vval \<Rightarrow> (funtyp, 'c) vval \<Rightarrow> bool"
  where
"\<xi>p1 f x y = (if f = ''repeat'' then prepeat \<xi>p0 x y else \<xi>p0 f x y)"

subsection "Partial ordering on abstract functions"

text "Should be automatable"

lemma \<xi>p0_le_\<xi>p1:
  "rel_leq \<xi>p0 \<xi>p1"
  unfolding \<xi>p0_def rel_leq_def
  by simp

subsection "Abstract functions are deterministic"

text "If user proves for \<xi>n, we can derive \<xi>i for i < n" 

lemma \<xi>p0_determ:
  "determ \<xi>p0"
  unfolding determ_def \<xi>p0_def
  by simp

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
    \<lbrakk>t6_C.stop_C v' = FUN_ENUM_log2stop; t6_C.step_C v' = FUN_ENUM_log2step; i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma> ! i = Some (fst (snd repeat_0_type))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''repeat_0'' []) (Var i)) (do x <- repeat_0' v';
 gets (\<lambda>s. x)
                                                               od)
         \<xi>_1 \<gamma> \<Xi> \<Gamma> \<sigma> s"
  apply simp
  apply (subst (asm) \<Xi>_simps[symmetric])
  apply (cut_tac uv = "\<gamma>!i" and x = v' in val_rel_t6_C_def)
  apply (rule crepeat_corres_bang_fun_fun[
      where \<tau>f = Generated_TypeProof.abbreviatedType5 and \<tau>a = Generated_TypeProof.abbreviatedType4 and \<tau>o = "TPrim (Num U64)" and o1C = t3_C.obsv_C,
      OF _ _ _ \<Xi>_simps(1)[unfolded Generated_TypeProof.repeat_0_type_def]  _ _ _  _  \<xi>_1_simps(1)
      \<xi>_0_le_\<xi>_1 \<xi>_1_determ _
      log2stop_typecorrect'[simplified Generated_TypeProof.log2stop_type_def fst_conv snd_conv]
      log2step_typecorrect'[simplified Generated_TypeProof.log2step_type_def fst_conv snd_conv]
      _ _ _ _ _ _ _ _ repeat_0'_simp]; (simp add: Generated_TypeProof.abbreviated_type_defs)?)
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
     \<Gamma> ! i = Some (fst (snd repeat_1_type))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''repeat_1'' []) (Var i)) (do x <- repeat_1' v';
 gets (\<lambda>s. x)
                                                               od)
         \<xi>_1 \<gamma> \<Xi> \<Gamma> \<sigma> s"
  apply simp
  apply (subst (asm) \<Xi>_simps[symmetric])
  apply (cut_tac uv = "\<gamma>!i" and x = v' in val_rel_t16_C_def)
  apply (rule crepeat_corres_bang_fun_fun[
      where \<tau>f = Generated_TypeProof.abbreviatedType6 and \<tau>a = "TPrim (Num U32)" and \<tau>o = "TPrim (Num U32)" and o1C = t13_C.obsv_C,
      OF _ _ _ \<Xi>_simps(2)[unfolded Generated_TypeProof.repeat_1_type_def]  _ _ _  _  \<xi>_1_simps(2)
      \<xi>_0_le_\<xi>_1 \<xi>_1_determ _
      expstop_typecorrect'[simplified Generated_TypeProof.expstop_type_def fst_conv snd_conv]
      expstep_typecorrect'[simplified Generated_TypeProof.expstep_type_def fst_conv snd_conv]
      _ _ _ _ _ _ _ _ repeat_1'_simp]; (simp add: Generated_TypeProof.abbreviated_type_defs)?)
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

section "Correspondence between abstract functions in the update and value semantics"

context correspondence_init begin

lemma \<xi>_0_\<xi>m0_matchesuv_\<Xi>:
  "\<xi>_0 \<sim> \<xi>m0 matches-u-v \<Xi>'"
  unfolding proc_env_u_v_matches_def \<xi>0_def \<xi>m0_def
  by clarsimp

lemma \<xi>_1_\<xi>m1_matchesuv_\<Xi>:
  "\<xi>_1 \<sim> \<xi>m1 matches-u-v \<Xi>"
  unfolding proc_env_u_v_matches_def \<xi>1_def \<xi>m1_def
  apply clarsimp
  apply (intro conjI impI; clarsimp)
    apply (subst (asm) \<Xi>_def;
           clarsimp simp: Generated_TypeProof.repeat_1_type_def Generated_TypeProof.repeat_0_type_def Generated_TypeProof.repeat_2_type_def;
           rule uvrepeat_monocorrespond_upward_propagation[OF proc_ctx_wellformed_\<Xi> \<xi>_0_\<xi>m0_matchesuv_\<Xi>];
           (simp add: Generated_TypeProof.abbreviated_type_defs)?)+
  apply (cut_tac  \<xi>_0_\<xi>m0_matchesuv_\<Xi>[where \<Xi>' = \<Xi>, unfolded proc_env_u_v_matches_def, simplified])
  apply (clarsimp split: prod.splits)
  apply (elim allE impE conjE; assumption?)
  apply blast
  done

end (* of context *)

section "Monomorphisation of abstract functions"

context monomorph_sem begin

lemma rename_mono_prog_\<xi>m0_\<xi>p0:
  "rename_mono_prog rename' \<Xi>' \<xi>m0 \<xi>p0"
  unfolding rename_mono_prog_def \<xi>m0_def \<xi>p0_def
  by clarsimp

lemma rename_mono_prog_\<Xi>_\<xi>m1_\<xi>p1:
  "rename_mono_prog rename \<Xi> \<xi>m1 \<xi>p1"
  unfolding rename_mono_prog_def
  apply (clarsimp simp: \<xi>m1_def \<xi>p1_def)  apply (intro conjI impI; clarsimp?)
    apply (subst (asm) rename_def;
           clarsimp simp: assoc_lookup.simps split: if_splits;
           rule prepeat_monoexpr_correct[OF _ \<xi>m0_matches_\<Xi> rename_mono_prog_\<xi>m0_\<xi>p0]; simp?)+
  apply (cut_tac rename' = rename and \<Xi>' = \<Xi> in rename_mono_prog_\<xi>m0_\<xi>p0[unfolded rename_mono_prog_def];
      clarsimp simp: \<xi>m0_matches_\<Xi>)
  apply (elim allE impE, assumption, clarsimp)
  apply (intro exI conjI impI; simp?)
  apply (clarsimp simp: \<xi>m0_def)
  done

end (* of context *)

section "Correspondence between shallow and polymorphic value semantics"

lemma (in shallow) scorres_repeat:
  "scorres repeat (AFun ''repeat'' ts) \<gamma> \<xi>p1"
  by (rule repeat_scorres[OF \<xi>p0_le_\<xi>p1]; simp add: \<xi>p1_def fun_eq_iff)

section "All refine"

lemmas (in Generated_cogent_shallow) corres_shallow_C_log2step_concrete = corres_shallow_C_log2step
  [OF _ rename_mono_prog_\<xi>m0_\<xi>p0 _ _ proc_ctx_wellformed_\<Xi> \<xi>m0_matches_\<Xi>]

lemmas (in Generated_cogent_shallow) corres_shallow_C_log2stop_concrete = corres_shallow_C_log2stop
  [OF _ rename_mono_prog_\<xi>m0_\<xi>p0 _ _ proc_ctx_wellformed_\<Xi> \<xi>m0_matches_\<Xi>]

lemmas (in Generated_cogent_shallow) corres_shallow_C_mylog2_concrete = corres_shallow_C_mylog2
  [folded \<Xi>_def, OF _ _ rename_mono_prog_\<Xi>_\<xi>m1_\<xi>p1 _ _ proc_ctx_wellformed_\<Xi> \<xi>m1_matches_\<Xi>,
   simplified, OF mylog2_repeat_corres[simplified]]

lemmas (in Generated_cogent_shallow) corres_shallow_C_expstep_concrete = corres_shallow_C_expstep
  [OF _ rename_mono_prog_\<xi>m0_\<xi>p0 _ _ proc_ctx_wellformed_\<Xi> \<xi>m0_matches_\<Xi>]

lemmas (in Generated_cogent_shallow) corres_shallow_C_expstop_concrete = corres_shallow_C_expstop
  [OF _ rename_mono_prog_\<xi>m0_\<xi>p0 _ _ proc_ctx_wellformed_\<Xi> \<xi>m0_matches_\<Xi>]

lemmas (in Generated_cogent_shallow) corres_shallow_C_myexp_concrete = corres_shallow_C_myexp
  [folded \<Xi>_def, OF _ _ rename_mono_prog_\<Xi>_\<xi>m1_\<xi>p1 _ _ proc_ctx_wellformed_\<Xi> \<xi>m1_matches_\<Xi>,
   simplified, OF myexp_repeat_corres[simplified]]

end
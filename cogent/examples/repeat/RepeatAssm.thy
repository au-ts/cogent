theory RepeatAssm
  imports
    RepeatUpdate
    RepeatValue
    RepeatMono
    RepeatCorrespondence
    RepeatScorres
    "build/Generated_AllRefine"
begin

section "Function types wellformed"

lemma proc_ctx_wellformed_\<Xi>:
  "proc_ctx_wellformed \<Xi>"
  unfolding proc_ctx_wellformed_def \<Xi>_def
            abbreviated_type_defs repeat_0_type_def
            log2stop_type_def log2step_type_def mylog2_type_def
  by (clarsimp simp: assoc_lookup.simps)

section "Abstract functions specification for the update semantics"

overloading \<xi>1 \<equiv> \<xi>_1
begin
definition \<xi>1 :: "(funtyp, abstyp, ptrtyp) uabsfuns"
  where
"\<xi>1 f x y = (if f = ''repeat_0'' then urepeat \<Xi> \<xi>_0 abbreviatedType1 (TPrim (Num U64)) x y  else \<xi>_0 f x y)"
end

overloading \<xi>0 \<equiv> \<xi>_0
begin
definition \<xi>0 :: "(funtyp, abstyp, ptrtyp) uabsfuns"
  where
"\<xi>0 f x y = False"
end

subsection "Preservation for abstract functions"

context update_sem_init begin

lemma \<xi>_0_matchesu_\<Xi>:
  "\<xi>_0 matches-u \<Xi>'"
  unfolding proc_env_matches_ptrs_def \<xi>0_def
  by clarsimp
 
lemma \<xi>_1_matchesu_\<Xi>:
  "\<xi>_1 matches-u \<Xi>"
  unfolding proc_env_matches_ptrs_def \<xi>1_def
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (subst (asm) \<Xi>_def; clarsimp)
   apply (clarsimp simp: repeat_0_type_def)
   apply (rule urepeat_preservation[OF proc_ctx_wellformed_\<Xi> \<xi>_0_matchesu_\<Xi>]; (simp add: abbreviated_type_defs)?)
  apply (clarsimp simp: \<xi>0_def)
  done
end (* of context *)

subsection "Partial ordering on abstract functions"

lemma \<xi>_0_le_\<xi>_1:
  "\<xi>ule \<xi>_0 \<xi>_1"
  unfolding \<xi>0_def \<xi>ule_def
  by simp

section "Abstract functions specifications for the monomorphic value semantics"

context value_sem begin

definition \<xi>m0 :: "'b \<Rightarrow> ('b, 'a) vval \<Rightarrow> ('b, 'a) vval \<Rightarrow> bool "
  where
"\<xi>m0 f x y = False"

definition \<xi>m1 :: "funtyp \<Rightarrow> (funtyp, 'a) vval \<Rightarrow> (funtyp, 'a) vval \<Rightarrow> bool "
  where
"\<xi>m1 f x y = (if f = ''repeat_0'' then vrepeat \<Xi> \<xi>m0 abbreviatedType1 (TPrim (Num U64)) x y else \<xi>m0 f x y)"

subsection "Preservation for abstract functions"

lemma \<xi>m0_matches_\<Xi>:
  "\<xi>m0 matches \<Xi>'"
  unfolding proc_env_matches_def \<xi>m0_def
  by clarsimp

lemma \<xi>m1_matches_\<Xi>:
  "\<xi>m1 matches \<Xi>"
  unfolding proc_env_matches_def \<xi>m1_def
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (subst (asm) \<Xi>_def; clarsimp simp: repeat_0_type_def)
   apply (rule vrepeat_preservation[OF proc_ctx_wellformed_\<Xi> \<xi>m0_matches_\<Xi>]; (simp add: abbreviated_type_defs)?)
  apply (clarsimp simp: \<xi>m0_def)
  done

subsection "Partial ordering on abstract functions"

lemma \<xi>m0_le_\<xi>m1:
  "\<xi>vle \<xi>m0 \<xi>m1"
  unfolding \<xi>m0_def \<xi>vle_def
  by simp

end (* of context *)

section "Abstract functions specifications for the polymorphic value semantics"

definition \<xi>p0 :: "'b \<Rightarrow> ('b, 'c) vval \<Rightarrow> ('b, 'c) vval \<Rightarrow> bool"
  where
"\<xi>p0 f x y = False"

definition \<xi>p1 :: "funtyp \<Rightarrow> (funtyp, 'c) vval \<Rightarrow> (funtyp, 'c) vval \<Rightarrow> bool"
  where
"\<xi>p1 f x y = (if f = ''repeat'' then prepeat \<xi>p0 x y else \<xi>p0 f x y)"

subsection "Partial ordering on abstract functions"

lemma \<xi>p0_le_\<xi>p1:
  "\<xi>vle \<xi>p0 \<xi>p1"
  unfolding \<xi>p0_def \<xi>vle_def
  by simp

section "Correspondence between abstract functions in the update and value semantics"

context correspondence_init begin

lemma \<xi>_0_\<xi>m0_matchesuv_\<Xi>:
  "\<xi>_0 \<sim> val.\<xi>m0 matches-u-v \<Xi>'"
  unfolding proc_env_u_v_matches_def \<xi>0_def val.\<xi>m0_def
  by clarsimp

lemma \<xi>_1_\<xi>m1_matchesuv_\<Xi>:
  "\<xi>_1 \<sim> val.\<xi>m1 matches-u-v \<Xi>"
  unfolding proc_env_u_v_matches_def \<xi>1_def val.\<xi>m1_def
  apply clarsimp
  apply (rule conjI; clarsimp)
  apply (subst (asm) \<Xi>_def; clarsimp simp: repeat_0_type_def)
   apply (rule uvrepeat_monocorrespond_upward_propagation[OF proc_ctx_wellformed_\<Xi> \<xi>_0_\<xi>m0_matchesuv_\<Xi>];
      (simp add: abbreviated_type_defs)?)
  apply (clarsimp simp: \<xi>0_def val.\<xi>m0_def)
  done

end (* of context *)

section "Monomorphisation of abstract functions"

context value_sem begin

lemma rename_mono_prog_\<xi>m0_\<xi>p0:
  "rename_mono_prog rename' \<Xi>' \<xi>m0 \<xi>p0"
  unfolding rename_mono_prog_def \<xi>m0_def \<xi>p0_def
  by clarsimp

lemma rename_mono_prog_\<Xi>_\<xi>m1_\<xi>p1:
  "rename_mono_prog rename \<Xi> \<xi>m1 \<xi>p1"
  unfolding rename_mono_prog_def
  apply (clarsimp simp: \<xi>m1_def \<xi>p1_def)
  apply (rule conjI; clarsimp)
   apply (subst (asm) rename_def; clarsimp simp: assoc_lookup.simps split: if_splits)
   apply (rule prepeat_monoexpr_correct[OF _ \<xi>m0_matches_\<Xi> rename_mono_prog_\<xi>m0_\<xi>p0]; simp?)
  apply (clarsimp simp: \<xi>m0_def)
  done

end (* of context *)

section "Correspondence between shallow and polymorphic value semantics"

lemma (in shallow) scorres_repeat:
  "scorres repeat (AFun ''repeat'' ts) \<gamma> \<xi>p1"
  by (rule repeat_scorres[OF \<xi>p0_le_\<xi>p1]; simp add: \<xi>p1_def fun_eq_iff)


end
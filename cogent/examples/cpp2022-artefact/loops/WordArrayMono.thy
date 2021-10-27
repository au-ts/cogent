theory WordArrayMono
  imports 
    WordArrayValue
    Cogent.Mono
    MonoHelper
begin

section "Word Array Methods"

subsection "wordarray_length"

lemma (in WordArrayValue) vwa_length_monoexpr_correct:
  "\<And>v v'.
       vwa_length (rename_val rename' (monoval v)) v'
       \<Longrightarrow> \<exists>v''. v' = rename_val rename' (monoval v'') \<and> vwa_length v v''"
  apply (clarsimp simp: vwa_length_def)
  apply (case_tac v; clarsimp)
  done

subsection "wordarray_get"

lemma (in WordArrayValue) vwa_get_monoexpr_correct:
  "\<And>v v'.
       vwa_get (rename_val rename' (monoval v)) v'
       \<Longrightarrow> \<exists>v''. v' = rename_val rename' (monoval v'') \<and> vwa_get v v''"
  apply (clarsimp simp: vwa_get_def)
  apply (case_tac v; clarsimp)
  apply (rename_tac z za zb)
  apply (case_tac z; clarsimp)
  apply (case_tac za; clarsimp)
  apply (clarsimp split: if_splits)
   apply (rule_tac x = "xs ! unat i" in exI)
   apply (clarsimp simp: no_vfuns_rename_monoval)
   apply fastforce
  apply (rule_tac x = zb in exI)
  apply (clarsimp simp: no_vfuns_rename_monoval)
  apply (rule exI, rule exI, rule_tac x = i in exI, intro exI conjI impI; simp?)
  apply (clarsimp simp: rename_monoval_no_vfuns)
  done

subsection "wordarray_put"

lemma (in WordArrayValue) vwa_put_monoexpr_correct:
  "\<And>v v'.
       vwa_put (rename_val rename' (monoval v)) v'
       \<Longrightarrow> \<exists>v''. v' = rename_val rename' (monoval v'') \<and> vwa_put v v''"
  apply (clarsimp simp: vwa_put_def)
  apply (case_tac v; clarsimp)
  apply (rename_tac z za zb)
  apply (case_tac z; clarsimp)
  apply (case_tac za; clarsimp)
  apply (clarsimp simp: rename_monoval_no_vfuns[THEN no_vfuns_rename_monoval] rename_monoval_no_vfuns)
  done

subsection "wordarray_get_opt"

lemma (in WordArrayValue) vwa_get_opt_monoexpr_correct:
  "\<And>v v'.
       vwa_get_opt (rename_val rename' (monoval v)) v'
       \<Longrightarrow> \<exists>v''. v' = rename_val rename' (monoval v'') \<and> vwa_get_opt v v''"
  apply (clarsimp simp: vwa_get_opt_def)
  apply (case_tac v; clarsimp)
  apply (rename_tac v' t xs i z za)
  apply (case_tac z; clarsimp)
  apply (case_tac za; clarsimp)
  apply (clarsimp split: if_splits)
   apply (rule_tac x = " VSum ''Something'' (xs ! unat i)" in exI)
   apply (clarsimp simp: no_vfuns_rename_monoval)
   apply fastforce
  apply (rule_tac x = "VSum ''Nothing'' VUnit" in exI)
  apply (clarsimp simp: no_vfuns_rename_monoval)
  apply (rule exI, rule exI, rule_tac x = i in exI, intro exI conjI impI; simp?)
  done

end
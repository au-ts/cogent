theory MonoHelper
  imports
    Cogent.Mono
    ValueSemHelper
begin

section "Renaming and Monomorphisation Helpers" 

context value_sem begin

lemma no_vfuns_rename_val:
  "no_vfuns x \<longleftrightarrow> no_vfuns (rename_val rename' x)"
  apply (induct x; clarsimp)
  apply (clarsimp simp: find_None_iff)
  done

lemma no_vfuns_rename_monoval:
  "no_vfuns v \<Longrightarrow> rename_val rename (monoval v) = v"
  apply (induct v; clarsimp split: if_splits)
  apply (clarsimp simp: list_eq_iff_nth_eq find_None_iff_nth)
  done

lemma rename_monoval_no_vfuns:
  "no_vfuns (rename_val rename' (monoval v)) \<Longrightarrow> no_vfuns v"
  apply (induct v; clarsimp split: if_splits simp: find_None_iff_nth)
  done
end (* context *)

end
theory RepeatShallow
  imports Main
begin

section "Repeat"

fun repeatatm :: "nat \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a"
  where
"repeatatm 0 _ _ acc _ = acc" |
"repeatatm (Suc n) f g acc obsv = (if f acc obsv then acc else repeatatm n f g (g acc obsv) obsv)"

declare repeatatm.simps[simp del]

subsection "Step and early termination lemmas"

lemma repeatatm_step_stop_Suc:
  "f (repeatatm n f g a b) b 
    \<Longrightarrow> repeatatm (Suc n) f g a b = repeatatm n f g a b"
  apply (induct n arbitrary: a)
   apply (simp add: repeatatm.simps)
  apply (subst repeatatm.simps)
  apply clarsimp
  apply (rule conjI, simp add: repeatatm.simps, clarsimp)
  apply (rule sym)
  apply (subst repeatatm.simps)
  apply clarsimp
  apply (rotate_tac 1, subst (asm) repeatatm.simps)
  apply clarsimp
  done

lemma repeatatm_step:
  "\<not>f (repeatatm n f g a b) b 
    \<Longrightarrow> repeatatm (Suc n) f g a b = g (repeatatm n f g a b) b"
  apply (induct n arbitrary: a)
   apply (simp add: repeatatm.simps)
  apply (subst repeatatm.simps)
  apply clarsimp
  apply (rule conjI, simp add: repeatatm.simps, clarsimp, clarsimp)
  apply (rule sym)
  apply (subst repeatatm.simps)
  apply clarsimp
  apply (rotate_tac 1, subst (asm) repeatatm.simps)
  apply clarsimp
  done

lemma repeatatm_stop_Suc:
  "\<lbrakk>f (repeatatm n f g a b) b\<rbrakk> \<Longrightarrow> f (repeatatm (Suc n) f g a b) b"
  apply (induct n arbitrary: a)
   apply (simp add: repeatatm.simps)
  apply (subst repeatatm.simps)
  apply clarsimp
  apply (rotate_tac 1, subst (asm) repeatatm.simps)
  apply clarsimp
  done

lemma repeatatm_stop:
  "\<lbrakk>f (repeatatm n f g a b) b; n \<le> m\<rbrakk> \<Longrightarrow> f (repeatatm m f g a b) b"
  apply (induct m arbitrary: a n)
   apply simp
  apply (case_tac "n < Suc m")
   apply (rule_tac f = f in repeatatm_stop_Suc)
   apply clarsimp
  apply clarsimp
  done

lemma repeatatm_step_stop:
  "\<lbrakk>f (repeatatm n f g a b) b; n \<le> m\<rbrakk> \<Longrightarrow> repeatatm m f g a b = repeatatm n f g a b"
  apply (induct m arbitrary: a n)
   apply simp
  apply (case_tac "n < Suc m")
   apply (subst repeatatm_step_stop_Suc)
    apply clarsimp
   apply clarsimp
  apply clarsimp
  done

lemma repeatatm_not_stop_Suc:
  "\<not>f (repeatatm (Suc n) f g a b) b \<Longrightarrow> \<not>f (repeatatm n f g a b) b"
  apply (rule_tac Q = "f (repeatatm (Suc n) f g a b) b" in  contrapos_nn; simp)
  apply (cut_tac n = n and f = f and g = g and a = a and b = b in repeatatm_stop_Suc; simp)
  done

end
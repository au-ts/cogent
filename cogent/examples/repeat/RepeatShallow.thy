theory RepeatShallow
  imports Main
begin

section "Repeat"

fun repeatatl :: "nat \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a"
  where
"repeatatl 0 _ _ acc _ = acc" |
"repeatatl (Suc n) f g acc obsv = (if f acc obsv then acc else repeatatl n f g (g acc obsv) obsv)"

declare repeatatl.simps[simp del]

subsection "Step and early termination lemmas"

lemma repeatatl_step_stop_Suc:
  "f (repeatatl n f g a b) b 
    \<Longrightarrow> repeatatl (Suc n) f g a b = repeatatl n f g a b"
  apply (induct n arbitrary: a)
   apply (simp add: repeatatl.simps)
  apply (subst repeatatl.simps)
  apply clarsimp
  apply (rule conjI, simp add: repeatatl.simps, clarsimp)
  apply (rule sym)
  apply (subst repeatatl.simps)
  apply clarsimp
  apply (rotate_tac 1, subst (asm) repeatatl.simps)
  apply clarsimp
  done

lemma repeatatl_step:
  "\<not>f (repeatatl n f g a b) b 
    \<Longrightarrow> repeatatl (Suc n) f g a b = g (repeatatl n f g a b) b"
  apply (induct n arbitrary: a)
   apply (simp add: repeatatl.simps)
  apply (subst repeatatl.simps)
  apply clarsimp
  apply (rule conjI, simp add: repeatatl.simps, clarsimp, clarsimp)
  apply (rule sym)
  apply (subst repeatatl.simps)
  apply clarsimp
  apply (rotate_tac 1, subst (asm) repeatatl.simps)
  apply clarsimp
  done

lemma repeatatl_stop_Suc:
  "\<lbrakk>f (repeatatl n f g a b) b\<rbrakk> \<Longrightarrow> f (repeatatl (Suc n) f g a b) b"
  apply (induct n arbitrary: a)
   apply (simp add: repeatatl.simps)
  apply (subst repeatatl.simps)
  apply clarsimp
  apply (rotate_tac 1, subst (asm) repeatatl.simps)
  apply clarsimp
  done

lemma repeatatl_stop:
  "\<lbrakk>f (repeatatl n f g a b) b; n \<le> m\<rbrakk> \<Longrightarrow> f (repeatatl m f g a b) b"
  apply (induct m arbitrary: a n)
   apply simp
  apply (case_tac "n < Suc m")
   apply (rule_tac f = f in repeatatl_stop_Suc)
   apply clarsimp
  apply clarsimp
  done

lemma repeatatl_step_stop:
  "\<lbrakk>f (repeatatl n f g a b) b; n \<le> m\<rbrakk> \<Longrightarrow> repeatatl m f g a b = repeatatl n f g a b"
  apply (induct m arbitrary: a n)
   apply simp
  apply (case_tac "n < Suc m")
   apply (subst repeatatl_step_stop_Suc)
    apply clarsimp
   apply clarsimp
  apply clarsimp
  done

lemma repeatatl_not_stop_Suc:
  "\<not>f (repeatatl (Suc n) f g a b) b \<Longrightarrow> \<not>f (repeatatl n f g a b) b"
  apply (rule_tac Q = "f (repeatatl (Suc n) f g a b) b" in  contrapos_nn; simp)
  apply (cut_tac n = n and f = f and g = g and a = a and b = b in repeatatl_stop_Suc; simp)
  done

end
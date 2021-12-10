theory DeterministicRelation3
  imports PartialOrderRelation3
begin

text "Deterministic relation of three inputs"

definition determ :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"
  where
"determ r = (\<forall>f a b c. r f a b \<and> r f a c \<longrightarrow> b = c)"

lemma determD:
  "\<lbrakk>determ r; r f a b; r f a c\<rbrakk> \<Longrightarrow> b = c" 
  unfolding determ_def
  by blast

text "Any relation that is less than or equal to a deterministic relation is also deterministic"

lemma determ_rel_leqD:
  "\<lbrakk>rel_leq f g; determ g\<rbrakk> \<Longrightarrow> determ f"
  unfolding determ_def
  apply clarsimp
  apply (drule (1) rel_leqD[rotated 1]; simp?)
  apply (drule (1) rel_leqD[rotated 1]; simp?)
  done

end
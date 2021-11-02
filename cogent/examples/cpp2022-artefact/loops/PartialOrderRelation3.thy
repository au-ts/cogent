theory PartialOrderRelation3
  imports Main
begin

text "Partial order on relations that take three inputs"

definition rel_leq :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool)\<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"
  where
"rel_leq f g = ({(n, a, b) | n a b. f n a b} \<subseteq> {(n, a, b) | n a b. g n a b})"

lemma rel_leqD:
  "\<lbrakk>rel_leq f g; f a b c\<rbrakk> \<Longrightarrow> g a b c"
  unfolding rel_leq_def
  apply (drule_tac c = "(a, b, c)" in subsetD; blast)
  done

end
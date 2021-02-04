theory Util
  imports Main
begin

lemma prod_split_asmE: 
  "\<lbrakk> (a,b) = x; P (fst x) (snd x) \<rbrakk> \<Longrightarrow> P a b"
  by (clarsimp split: prod.split)

lemma prod_eq: 
  "\<lbrakk> a = fst x ; b = snd x \<rbrakk> \<Longrightarrow> x = (a,b)"
  by simp

end
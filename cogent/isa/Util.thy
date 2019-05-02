(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Util
  imports "HOL-Word.Word"
begin


definition
  checked_shift :: "(('a :: len) word \<Rightarrow> nat \<Rightarrow> 'a word) \<Rightarrow> 'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where
  checked_shift_def[simp]:
  "checked_shift shifter x y = (if y < of_nat (len_of TYPE('a)) then shifter x (unat y) else 0)"

definition
  checked_div :: "'a \<Rightarrow> 'a \<Rightarrow> ('a :: {zero, Rings.divide})"
where
  "checked_div x y = (if y = 0 then 0 else x div y)"

definition
  checked_mod :: "'a \<Rightarrow> 'a \<Rightarrow> ('a :: {zero, Rings.modulo})"
where
  checked_mod_def[simp]:
  "checked_mod x y = (if y = 0 then 0 else x mod y)"


section {* Utility lemmas *}

lemma map_snd_app [simp]: 
shows "map (snd \<circ> (\<lambda> (a , b). (a , f b))) l  =  map (f \<circ> snd) l" 
by (induct l, auto)

lemma map_snd_ignore [simp]: 
shows "map (snd \<circ> (\<lambda> (a , b). (f a , b))) l  =  map (snd) l" 
by (induct l, auto)

lemma map_fst_app [simp]:
shows "map (fst \<circ> (\<lambda> (a , b). (f a , b))) l =  map (f \<circ> fst) l" 
by (induct l, auto)

lemma map_fst_ignore [simp]:
shows "map (fst \<circ> (\<lambda> (a , b). (a , f b))) l = map fst l" 
by (induct l, auto)

lemma map_fst_update:
assumes "ts ! f = (t, x)"
and     "f < length ts"
shows "map fst (ts[f := (t,x')]) = map fst ts"
proof -
from assms have  "map fst ts ! f = t" by (clarsimp)
then show ?thesis by (auto simp add: map_update)
qed

lemma map_zip [simp]:
shows "map (\<lambda> (a , b). (f a, g b)) (zip as bs) = zip (map f as) (map g bs)"
by (induct as arbitrary:bs, simp, case_tac bs, simp_all)

lemma distinct_fst:
assumes "distinct (map fst ls)"
and     "(a, b) \<in> set ls"
and     "(a, b') \<in> set ls"
shows   "b = b'"
using assms
  apply (clarsimp simp: set_conv_nth distinct_conv_nth)
  apply (drule_tac x = i in spec, simp)
  apply (drule_tac x = ia in spec, simp)
  apply (case_tac "ls ! i")
  apply (case_tac "ls ! ia")
  apply (auto)
done

lemma map_filter_fst:
shows "map (\<lambda>(c, t). (c, f t)) [x\<leftarrow>ts . P (fst x)]
     = [x \<leftarrow> map (\<lambda>(c,t). (c, f t)) ts. P (fst x)]"
proof -
have "(\<lambda>x. P (fst x)) \<circ> (\<lambda>(c, t). (c, f t)) = (\<lambda>x. P (fst x))"
  by (rule ext, case_tac x, simp)
then show ?thesis by (simp add: filter_map)
qed

lemma set_subset_map:
assumes "set a \<subseteq> set b"
shows   "set (map f a) \<subseteq> set (map f b)"
using assms by auto


lemma prod_in_set:
assumes "(a, b) \<in> set l"
shows   "a \<in> set (map fst l)"
and     "b \<in> set (map snd l)"
using assms by (force intro: imageI)+ 

lemma filter_fst_ignore:
shows "filter (\<lambda> x. P (fst x)) (map (\<lambda>(a,b). (a, f b)) ls) 
     = map (\<lambda>(a,b). (a, f b)) (filter (\<lambda> x. P (fst x)) ls)"
by (induct_tac ls, auto)


end
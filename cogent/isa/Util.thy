(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory Util
  imports Main
    "~~/src/HOL/Word/Word"
begin

section {* Word related lemmas *}
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


section {* Tuple lemmas *}

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

lemma map_fst3_app2 [simp]:
  shows "map ((fst \<circ> snd) \<circ> (\<lambda> (a, b, c). (a, f b, c))) l = map (f \<circ> (fst \<circ> snd)) l"
  by (induct l, auto)

lemma map_fst3_ignore2[simp]:
  shows "map (fst \<circ> (\<lambda> (a, b, c). (a, f b, c))) l = map fst l"
  by (induct l, auto)

lemma map_snd3_ignore3[simp]:
  shows "map (fst \<circ> snd \<circ> (\<lambda> (a, b, c). (a, b, f c))) l = map (fst \<circ> snd) l"
  by (induct l, auto)


(* making these simp makes the final force on specalise take forever? / v.jackson *)
lemma comp_fst_tuple_lambda: "fst \<circ> (\<lambda>(a,b). (f a b, g a b)) = (\<lambda>(a,b). f a b)"
  by force

lemma comp_snd_tuple_lambda: "snd \<circ> (\<lambda>(a,b). (f a b, g a b)) = (\<lambda>(a,b). g a b)"
  by force

lemma assoc_comp_fst_tuple_lambda: "h \<circ> fst \<circ> (\<lambda>(a,b). (f a b, g a b)) = h \<circ> (\<lambda>(a,b). f a b)"
  by force

lemma assoc_comp_snd_tuple_lambda: "h \<circ> snd \<circ> (\<lambda>(a,b). (f a b, g a b)) = h \<circ> (\<lambda>(a,b). g a b)"
  by force


section {* Misc lemmas *}

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
  assumes "distinct (map fst xs)"
    and     "(a, b) \<in> set xs"
    and     "(a, b') \<in> set xs"
  shows   "b = b'"
  using assms image_iff
  by (induct xs, fastforce+)

lemma set_subset_map:
  assumes "set a \<subseteq> set b"
  shows   "set (map f a) \<subseteq> set (map f b)"
  using assms by auto

lemma prod_in_set:
  assumes "(a, b) \<in> set l"
  shows   "a \<in> set (map fst l)"
    and     "b \<in> set (map snd l)"
  using assms by (force intro: imageI)+

lemma list_all2_update_second:
  assumes "list_all2 f xs (ys[i := a])"
    and "f (xs ! i) a \<Longrightarrow> f (xs ! i) b"
  shows "list_all2 f xs (ys[i := b])"
  using assms
  by (clarsimp simp add: list_all2_conv_all_nth, metis nth_list_update_eq nth_list_update_neq)



lemma filter_fst_ignore_tuple:
  shows "filter (\<lambda>x. P (fst x)) (map (\<lambda>(a,b). (a, f b)) ls)
     = map (\<lambda>(a,b). (a, f b)) (filter (\<lambda>x. P (fst x)) ls)"
  by (induct_tac ls, auto)

lemma filter_fst_ignore_triple:
  shows "filter (\<lambda>x. P (fst x)) (map (\<lambda>(a,b,c). (a, f b, c)) ls)
     = map (\<lambda>(a,b,c). (a, f b, c)) (filter (\<lambda>x. P (fst x)) ls)"
  by (induct_tac ls, auto)

lemma filter_fst_ignore_app2:
  shows "filter (\<lambda>x. P (fst x)) (map (\<lambda>(a,b,c). (a,f b,c)) ls)
     = map (\<lambda>(a,b,c). (a,f b,c)) (filter (\<lambda>x. P (fst x)) ls)"
  by (induct_tac ls, auto)

lemma filter_map_map_filter_thd3_app2:
  shows "filter (P \<circ> snd \<circ> snd) (map (\<lambda>(a, b, c). (a, f b, c)) ls) = map (\<lambda>(a, b, c). (a, f b, c)) (filter (P \<circ> snd \<circ> snd) ls)"
  by (induct_tac ls, (simp split: prod.splits)+)

lemma filtered_member: "[a] = filter f x \<Longrightarrow> a \<in> set x"
  apply (induction x)
  by (auto split: if_splits)


section {* TSum as map lemmas *}

abbreviation map_pairs :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<times> 'b) set" where
  "map_pairs m \<equiv> { z. m (fst z) = Some (snd z)}"

lemma map_pairs_map_of_set:
  assumes distinct_fst_xs: "distinct (map fst xs)"
  shows "map_pairs (map_of xs) = set xs"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  moreover then have "{z. ((fst z = fst x \<longrightarrow> snd x = snd z) \<and> (fst z \<noteq> fst x \<longrightarrow> map_of xs (fst z) = Some (snd z)))}
      = insert x ({z. fst z \<noteq> fst x} \<inter> set xs)"
    by force
  moreover have "set xs \<subseteq> {z. fst z \<noteq> fst x}"
    using Cons.prems prod_in_set(1) by force
  ultimately show ?case
    by (clarsimp, blast)
qed

lemma append_filter_fst_eqiv_map_update:
  assumes "set xs = map_pairs (map_of xs)"
  shows "(set ((fst z, f z) # [x\<leftarrow>xs. fst x \<noteq> fst z])) = (map_pairs ((map_of xs) (fst z \<mapsto> f z)))"
  using assms
  apply clarsimp
  apply (subst insert_def)
  apply (subst Collect_disj_eq[symmetric])
  apply force
  done

section {* Tagged List lemmas *}

subsection {* Tagged list update *}

primrec tagged_list_update :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "tagged_list_update a' b' [] = []"
| "tagged_list_update a' b' (x # xs) = (case x of (a, b) \<Rightarrow>
                                      (if a = a'
                                       then (a, b') # xs
                                       else (a, b) # tagged_list_update a' b' xs))"

lemma tagged_list_update_tag_not_present[simp]:
  assumes "\<forall>i<length xs. fst (xs ! i) \<noteq> tag"
  shows "tagged_list_update tag b xs = xs"
  using assms
  by (induct xs, fastforce+)

lemma tagged_list_update_tag_present[simp]:
  assumes "\<forall>j<i. fst (xs ! j) \<noteq> tag"
    and "i<length xs"
    and "fst (xs ! i) = tag"
  shows "tagged_list_update tag b' xs = xs[i := (tag, b')]"
  using assms
proof (induct xs arbitrary: i)
  case (Cons x xs)
  then show ?case
  proof (cases i)
    case (Suc nat)
    then show ?thesis
      using Cons
    proof (cases "fst x = fst (xs ! nat)")
      case False
      then show ?thesis
        using Cons Suc
        by (simp add: case_prod_beta, metis Suc_mono nth_Cons_Suc)
    qed auto
  qed (simp add: case_prod_beta)
qed simp

lemma tagged_list_update_map_over1:
  fixes f g
  assumes inj_f: "inj f"
  shows "map (\<lambda>(tag,b). (f tag, g tag b)) (tagged_list_update tag b' xs) = tagged_list_update (f tag) (g tag b') (map (\<lambda>(tag,b). (f tag, g tag b)) xs)"
  by (induct xs, (simp add: inj_eq case_prod_beta inj_f)+)

lemma tagged_list_update_map_over2:
  assumes "\<And>tag b'. f (tag, b') = (tag, g b')"
  shows "map f (tagged_list_update tag b' xs) = tagged_list_update tag (g b') (map f xs)"
  using assms by (induct xs, clarsimp+)

lemma tagged_list_update_map_over_indistinguishable:
  assumes xs_at_i: "xs ! i = (tag, b)"
    and i_in_bounds: "i < length xs"
    and distinct_fst: "distinct (map fst xs)"
  shows "map (f \<circ> snd) (tagged_list_update tag b' xs) = (map (f \<circ> snd) xs)[i := (f b')]"
  using assms
proof (induct xs arbitrary: i)
  case (Cons x xs)
  then show ?case
  proof (cases i)
    case (Suc j)
    then show ?thesis
    proof (cases x)
      case (Pair tag' q)
      have "tag' \<noteq> tag"
        using Cons Suc Pair
        using nth_mem prod_in_set(1) by fastforce
      then show ?thesis
        using Cons Suc Pair
        by clarsimp
    qed
  qed simp
qed simp


lemma tagged_list_update_preserves_tags[simp]:
  shows "map fst (tagged_list_update tag b' xs) = map fst xs"
  by (induct xs, clarsimp+)

lemma tagged_list_update_different_tag_preserves_values1[simp]:
  "fst (xs ! i) \<noteq> tag \<Longrightarrow> (tagged_list_update tag b' xs) ! i = xs ! i"
  by (induct xs arbitrary: i, (fastforce simp add: nth_Cons')+)

lemma tagged_list_update_different_tag_preserves_values2:
  "tag \<noteq> tag' \<Longrightarrow> (tag, b) \<in> set xs \<longleftrightarrow> (tag, b) \<in> set (tagged_list_update tag' b' xs)"
proof (induct xs)
  case (Cons a xs)
  then show ?case
  proof (cases "a = (tag,b)")
    case False
    then show ?thesis
      by (clarsimp, metis Cons.hyps Cons.prems surj_pair)
  qed (simp add: Cons.prems)
qed simp+

lemma tagged_list_update_distinct:
  assumes "distinct (map fst xs)"
    and "i < length xs"
    and "fst (xs ! i) = tag"
  shows "(tagged_list_update tag b' xs) = (xs[i := (tag, b')])"
proof -
  have "\<And>j. j < length xs \<Longrightarrow> i \<noteq> j \<Longrightarrow> fst (xs ! j) \<noteq> tag"
    using assms
    by (clarsimp simp add: distinct_conv_nth)
  then have "\<forall>j<i. fst (xs ! j) \<noteq> tag"
    using assms(2) by auto
  then show ?thesis
    using tagged_list_update_tag_present assms
    by simp
qed

lemma tagged_list_update_same_distinct_is_equal:
  assumes distinct_fst_xs: "distinct (map fst xs)"
    and "i < length xs"
    and "(xs ! i) = (tag, b)"
  shows "tagged_list_update tag b xs = xs"
  using assms
proof (induct xs arbitrary: i)
  case (Cons a xs)
  then show ?case
    by (metis fst_conv list_update_id tagged_list_update_distinct)
qed simp+

end
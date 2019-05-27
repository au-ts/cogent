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

subsection {* list_all *}

lemma list_all_antitone_lists:
  assumes
    "set xs \<subseteq> set ys"
    "list_all P ys"
  shows "list_all P xs"
  using assms
  by (metis list_all_iff subset_iff)

lemma list_all_nil: "list_all P []"
  by simp
lemma list_all_cons: "P x \<Longrightarrow> list_all P xs \<Longrightarrow> list_all P (x # xs)"
  by simp

lemma list_all_imp_list_all_filtered: "list_all P xs \<Longrightarrow> list_all P (filter Q xs)"
  by (induct xs) simp+

lemma list_all_update_weak:
  "\<lbrakk> i < length xs; P x'; list_all P xs \<rbrakk> \<Longrightarrow> list_all P (xs[i := x'])"
  by (clarsimp simp add: list_all_length, case_tac "n = i"; simp)


subsection {* list_all2 *}

lemmas list_all2_nil = List.list.rel_intros(1)
lemmas list_all2_cons = List.list.rel_intros(2)

lemma list_all_zip_iff_list_all2:
  assumes "length xs = length ys"
  shows "list_all P (zip xs ys) \<longleftrightarrow> list_all2 (curry P) xs ys"
  using assms
  by (induct xs ys rule: list_induct2) simp+


subsection {* list_all3 *}

inductive list_all3 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> bool" where
  all3Nil : "list_all3 P [] [] []"
| all3Cons : "P x y z \<Longrightarrow> list_all3 P xs ys zs \<Longrightarrow> list_all3 P (x # xs) (y # ys) (z # zs)"

lemma list_all3_induct
  [consumes 1, case_names Nil Cons, induct set: list_all3]:
  assumes P: "list_all3 P xs ys zs"
  assumes Nil: "R [] [] []"
  assumes Cons: "\<And>x xs y ys z zs.
    \<lbrakk>P x y z; list_all3 P xs ys zs; R xs ys zs\<rbrakk> \<Longrightarrow> R (x # xs) (y # ys) (z # zs)"
  shows "R xs ys zs"
  using P
  by (induct xs arbitrary: ys zs) (auto elim: list_all3.cases simp add: Nil Cons)

lemma list_induct3':
  "\<lbrakk> P [] [] [];
   \<And>x xs. P (x#xs) [] [];
   \<And>y ys. P [] (y#ys) [];
   \<And>z zs. P [] [] (z#zs);
   \<And>x xs y ys. P (x#xs) (y#ys) [];
   \<And>y ys z zs. P [] (y#ys) (z#zs);
   \<And>x xs z zs. P (x#xs) [] (z#zs);
   \<And>x xs y ys z zs. P xs ys zs  \<Longrightarrow> P (x#xs) (y#ys) (z # zs) \<rbrakk>
 \<Longrightarrow> P xs ys zs"
  apply (induct xs arbitrary: ys zs)
   apply (rename_tac ys zs, case_tac ys; case_tac zs; force)
  apply (rename_tac x xs ys zs, case_tac ys; case_tac zs; force)
  done

lemma list_all3_cases:
  assumes P: "list_all3 P xs ys zs"
  assumes Nil: "\<lbrakk> xs = [] ; ys = [] ; zs = [] \<rbrakk> \<Longrightarrow> R"
  assumes Cons: "\<And>x xsa y ysa z zsa.
    \<lbrakk> xs = x # xsa ; ys = y # ysa ; zs = z # zsa \<rbrakk> \<Longrightarrow> R"
  shows "R"
  using P by (auto elim: list_all3.cases simp add: Nil Cons)

lemma list_all3_iff:
  "list_all3 P xs ys zs \<longleftrightarrow> length xs = length ys \<and> length ys = length zs \<and> (\<forall>(x, y, z) \<in> set (zip xs (zip ys zs)). P x y z)"
  apply (rule iffI)
   apply (induct xs ys zs rule: list_all3.induct; simp)
  apply (induct xs ys zs rule: list_induct3'; simp add: list_all3.intros)
  done

lemma list_all3_Nil1 [iff, code]: "list_all3 P [] ys zs = (ys = [] \<and> zs = [])"
  by (force simp add: list_all3_iff)

lemma list_all3_Nil2 [iff, code]: "list_all3 P xs [] zs = (xs = [] \<and> zs = [])"
  by (simp add: list_all3_iff)

lemma list_all3_Nil3 [iff, code]: "list_all3 P xs ys [] = (xs = [] \<and> ys = [])"
  by (force simp add: list_all3_iff)

lemma list_all3_Cons[iff, code]: "list_all3 P (x # xs) (y # ys) (z # zs) = (P x y z \<and> list_all3 P xs ys zs)"
  by (force simp add: list_all3_iff)

lemma list_all3_Cons1: "list_all3 P (x # xs') ys zs = (\<exists>y ys' z zs'. ys = y # ys' \<and> zs = z # zs'  \<and> (P x y z \<and> list_all3 P xs' ys' zs'))"
  by (cases ys; cases zs; force simp add: list_all3_iff)

lemma list_all3_Cons2: "list_all3 P xs (y # ys') zs = (\<exists>x xs' z zs'. xs = x # xs' \<and> zs = z # zs'  \<and> (P x y z \<and> list_all3 P xs' ys' zs'))"
  by (cases xs; cases zs; force simp add: list_all3_iff)

lemma list_all3_Cons3: "list_all3 P xs ys (z # zs') = (\<exists>x xs' y ys'. xs = x # xs' \<and> ys = y # ys'  \<and> (P x y z \<and> list_all3 P xs' ys' zs'))"
  by (cases xs; cases ys; force simp add: list_all3_iff)

lemma list_all3_mono[intro?]:
  assumes "list_all3 P xs ys zs"
    and "\<And>x y z. P x y z \<Longrightarrow> Q x y z"
  shows "list_all3 Q xs ys zs"
  using assms
  by (force simp add: list_all3_iff)

lemma list_all3_mono'[mono]: "P \<le> Q \<Longrightarrow> list_all3 P \<le> list_all3 Q"
  apply (clarsimp intro!: le_funI)
  apply (induct_tac rule: list_all3_induct)
    apply assumption
   apply (auto dest: le_funD)[2]
  done

lemma list_all3_conv_all_nth:
  "list_all3 P xs ys zs \<longleftrightarrow> length xs = length ys \<and> length ys = length zs \<and> (\<forall>i<length xs. P (xs ! i) (ys ! i) (zs ! i))"
  by (force simp add: list_all3_iff set_zip)

lemma list_all3_same:
  "list_all3 P xs xs xs = (\<forall>x\<in>set xs. P x x x)"
  by (induct xs; simp)

lemma list_all3_split_conj:
  shows "list_all3 (\<lambda> x y z. P x y z \<and> Q x y z) xs ys zs \<longleftrightarrow> list_all3 P xs ys zs \<and> list_all3 Q xs ys zs"
  apply (rule iffI)
   apply (induct rule: list_all3_induct, simp+)
  apply (clarsimp, induct rule: list_all3_induct, simp+)
  done

lemma list_all3_split_all:
  shows "list_all3 (\<lambda> x y z. \<forall>a. P x y z a) xs ys zs \<longleftrightarrow> (\<forall>a. list_all3 (\<lambda>x y z. P x y z a) xs ys zs)"
  apply (rule iffI)
   apply (induct rule: list_all3_induct, simp+)
  apply (induct xs arbitrary: ys zs; case_tac ys; case_tac zs; clarsimp)
  done

lemma list_all3_impD:
  assumes
    "list_all3 (\<lambda> x y z. P x y z \<longrightarrow> Q x y z) xs ys zs"
    "list_all3 P xs ys zs"
  shows
    "list_all3 Q xs ys zs"
  using assms
  by (induct rule: list_all3_induct, simp+)


(* n.b. the conditions are essentially functor laws *)
lemma list_all3_map_over:
  assumes "list_all3 P xs ys zs"
  and "f [] = []" and "g [] = []" and "h [] = []"
  and "\<And>a as. f (a # as) = f' a # f as"
  and "\<And>a as. g (a # as) = g' a # g as"
  and "\<And>a as. h (a # as) = h' a # h as"
  and "\<And>x y z. P x y z \<Longrightarrow> Q (f' x) (g' y) (h' z)"
  shows "list_all3 Q (f xs) (g ys) (h zs)"
  using assms
  by (induct rule: list_all3_induct; simp)


lemma list_all3_product_over_list_all2:
  assumes "list_all3 P xs ys zs"
    and "\<And>a x y z. P x y z \<Longrightarrow> A a x \<Longrightarrow> A a y \<and> A a z"
    and "list_all2 A as xs"
  shows "list_all2 A as ys"
    and "list_all2 A as zs"
  using assms
  by (induct arbitrary: as rule: list_all3_induct, (clarsimp simp add: list_all2_Cons2)+)

subsection {* list_all4 *}

inductive list_all4 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'd list \<Rightarrow> bool" where
  all4Nil : "list_all4 P [] [] [] []"
| all4Cons : "P x y z w \<Longrightarrow> list_all4 P xs ys zs ws \<Longrightarrow> list_all4 P (x # xs) (y # ys) (z # zs) (w # ws)"

lemma list_all4_induct[consumes 1, case_names Nil Cons]:
  assumes P: "list_all4 P xs ys zs ws"
  assumes Nil: "R [] [] [] []"
  assumes Cons: "\<And>x xs y ys z zs  w ws.
    \<lbrakk>P x y z w; list_all4 P xs ys zs ws; R xs ys zs ws\<rbrakk> \<Longrightarrow> R (x # xs) (y # ys) (z # zs) (w # ws)"
  shows "R xs ys zs ws"
  using P
  by (induct xs arbitrary: ys zs ws) (auto elim: list_all4.cases simp add: Nil Cons)

lemma list_induct4':
  "\<lbrakk> P [] [] [] [];
   \<And>x xs y ys z zs w ws. P xs ys zs ws \<Longrightarrow> P (x#xs) (y#ys) (z#zs) (w#ws);
   \<And>x xs               . P (x#xs) []     []     [];
   \<And>     y ys          . P []     (y#ys) []     [];
   \<And>x xs y ys          . P (x#xs) (y#ys) []     [];
   \<And>          z zs     . P []     []     (z#zs) [];
   \<And>x xs      z zs     . P (x#xs) []     (z#zs) [];
   \<And>     y ys z zs     . P []     (y#ys) (z#zs) [];
   \<And>x xs y ys z zs     . P (x#xs) (y#ys) (z#zs) [];
   \<And>               w ws. P []     []     []     (w#ws);
   \<And>x xs           w ws. P (x#xs) []     []     (w#ws);
   \<And>     y ys      w ws. P []     (y#ys) []     (w#ws);
   \<And>x xs y ys      w ws. P (x#xs) (y#ys) []     (w#ws);
   \<And>          z zs w ws. P []     []     (z#zs) (w#ws);
   \<And>x xs      z zs w ws. P (x#xs) []     (z#zs) (w#ws);
   \<And>     y ys z zs w ws. P []     (y#ys) (z#zs) (w#ws) \<rbrakk>
 \<Longrightarrow> P xs ys zs ws"
  by (induct xs arbitrary: ys zs ws; rename_tac ys zs ws, case_tac ys; case_tac zs; case_tac ws; simp)

lemmas list_induct4_simple = list_induct4'[case_names Nil Cons]

lemma list_all4_iff:
  "list_all4 P xs ys zs ws \<longleftrightarrow>
    length xs = length ys \<and> length ys = length zs \<and> length zs = length ws \<and>
    (\<forall>(x, y, z, w) \<in> set (zip xs (zip ys (zip zs ws))). P x y z w)"
  apply (rule iffI)
   apply (induct xs ys zs ws rule: list_all4.induct; simp)
  apply (induct xs ys zs ws rule: list_induct4'; force intro!: list_all4.intros)
  done

lemma list_all4_Nil1 [iff, code]: "list_all4 P [] ys zs ws = (ys = [] \<and> zs = [] \<and> ws = [])"
  by (force simp add: list_all4_iff)

lemma list_all4_Nil2 [iff, code]: "list_all4 P xs [] zs ws = (xs = [] \<and> zs = [] \<and> ws = [])"
  by (force simp add: list_all4_iff)

lemma list_all4_Nil3 [iff, code]: "list_all4 P xs ys [] ws = (xs = [] \<and> ys = [] \<and> ws = [])"
  by (force simp add: list_all4_iff)

lemma list_all4_Nil4 [iff, code]: "list_all4 P xs ys zs [] = (xs = [] \<and> ys = [] \<and> zs = [])"
  by (force simp add: list_all4_iff)

lemma list_all4_Cons[iff, code]: "list_all4 P (x # xs) (y # ys) (z # zs) (w # ws) = (P x y z w \<and> list_all4 P xs ys zs ws)"
  by (force simp add: list_all4_iff)

lemma list_all4_Cons1: "list_all4 P (x # xs') ys zs ws =
  (\<exists>y ys' z zs' w ws'. ys = y # ys' \<and> zs = z # zs' \<and> ws = w # ws' \<and> (P x y z w \<and> list_all4 P xs' ys' zs' ws'))"
  by (cases ys; cases zs; cases ws; force simp add: list_all4_iff)

lemma list_all4_Cons2: "list_all4 P xs (y # ys') zs ws =
  (\<exists>x xs' z zs' w ws'. xs = x # xs' \<and> zs = z # zs' \<and> ws = w # ws' \<and> (P x y z w \<and> list_all4 P xs' ys' zs' ws'))"
  by (cases xs; cases zs; cases ws; force simp add: list_all4_iff)

lemma list_all4_Cons3: "list_all4 P xs ys (z # zs') ws =
  (\<exists>x xs' y ys' w ws'. xs = x # xs' \<and> ys = y # ys' \<and> ws = w # ws' \<and> (P x y z w \<and> list_all4 P xs' ys' zs' ws'))"
  by (cases xs; cases ys; cases ws; force simp add: list_all4_iff)

lemma list_all4_Cons4: "list_all4 P xs ys zs (w # ws') =
  (\<exists>x xs' y ys' z zs'. xs = x # xs' \<and> ys = y # ys' \<and> zs = z # zs' \<and> (P x y z w \<and> list_all4 P xs' ys' zs' ws'))"
  by (cases xs; cases ys; cases zs; force simp add: list_all4_iff)

lemma list_all4_mono[intro?]:
  assumes "list_all4 P xs ys zs ws"
    and "\<And>x y z w. P x y z w \<Longrightarrow> Q x y z w"
  shows "list_all4 Q xs ys zs ws"
  using assms
  by (clarsimp simp add: list_all4_iff split: prod.splits)

lemma list_all4_mono'[mono]: "P \<le> Q \<Longrightarrow> list_all4 P \<le> list_all4 Q"
  apply (clarsimp intro!: le_funI)
  apply (induct_tac rule: list_all4_induct)
    apply assumption
   apply (auto dest: le_funD)[2]
  done

lemma list_all4_conv_all_nth:
  "list_all4 P xs ys zs ws \<longleftrightarrow> length xs = length ys \<and> length ys = length zs \<and> length zs = length ws \<and>
    (\<forall>i<length xs. P (xs ! i) (ys ! i) (zs ! i) (ws ! i))"
  by (force simp add: list_all4_iff set_zip)

lemma list_all4_same:
  "list_all4 P xs xs xs xs = (\<forall>x\<in>set xs. P x x x x)"
  by (induct xs; simp)

lemma list_all4_split_conj:
  shows "list_all4 (\<lambda> x y z w. P x y z w \<and> Q x y z w) xs ys zs ws \<longleftrightarrow> list_all4 P xs ys zs ws \<and> list_all4 Q xs ys zs ws"
  apply (rule iffI)
   apply (induct rule: list_all4_induct, simp+)
  apply (clarsimp, induct rule: list_all4_induct, simp+)
  done

lemma list_all4_split_all:
  shows "list_all4 (\<lambda> x y z w. \<forall>a. P x y z w a) xs ys zs ws \<longleftrightarrow> (\<forall>a. list_all4 (\<lambda>x y z w. P x y z w a) xs ys zs ws)"
  apply (rule iffI)
   apply (induct rule: list_all4_induct, simp+)
  apply (induct xs arbitrary: ys zs ws; case_tac ys; case_tac zs; case_tac ws; clarsimp)
  done

lemma list_all4_impD:
  assumes
    "list_all4 (\<lambda>x y z w. P x y z w \<longrightarrow> Q x y z w) xs ys zs ws"
    "list_all4 P xs ys zs ws"
  shows
    "list_all4 Q xs ys zs ws"
  using assms
  by (induct rule: list_all4_induct, simp+)


section {* Unzip *}

(* slow *)
fun unzip where
  "unzip [] = ([], [])"
| "unzip (xy # xys) = (let (x,y) = xy ; (xs,ys) = unzip xys in (x # xs, y # ys))"

fun revunzip_fast_go where
  "revunzip_fast_go ((x,y) # zs) xs ys = revunzip_fast_go zs (x # xs) (y # ys)"
| "revunzip_fast_go [] xs ys = (xs, ys)"

fun rev_fast_go where
  "rev_fast_go [] ys = ys"
| "rev_fast_go (x # xs) ys = rev_fast_go xs (x # ys)"

definition "unzip_fast xs = revunzip_fast_go (rev_fast_go xs []) [] []"

subsection {* rev and fast rev *}

lemma rev_fast_sndarg_append_end: "rev_fast_go xs ys @ zs = rev_fast_go xs (ys @ zs)"
  by (induct xs ys arbitrary: zs rule: rev_fast_go.induct) simp+

lemma rev_fast_sndarg_nil_append_end: "rev_fast_go xs [] @ ys = rev_fast_go xs ys"
  by (metis append_Nil rev_fast_sndarg_append_end)

lemma rev_eq_rev_fast': "rev_fast_go xs ys = rev xs @ ys"
  by (induct xs arbitrary: ys) (simp add: rev_fast_sndarg_nil_append_end)+

lemma rev_eq_rev_fast: "rev_fast_go xs [] = rev xs"
  by (metis fold_Cons_rev rev_conv_fold rev_eq_rev_fast')

subsection {* unzip and fast unzip *}

lemma unzip_as_foldr: "unzip xys = foldr (\<lambda>(x,y) (xs,ys). (x # xs, y # ys)) xys ([],[])"
  by (induct xys) clarsimp+

lemma revunzip_fast_as_fold: "revunzip_fast_go xys xsi ysi = fold (\<lambda>(x,y) (xs,ys). (x # xs, y # ys)) xys (xsi,ysi)"
  by (induct xys arbitrary: xsi ysi) clarsimp+

lemma unzip_eq_revunziprev_fast: "revunzip_fast_go xys [] [] = unzip (rev xys)"
proof -
  have "revunzip_fast_go xys [] [] = fold (\<lambda>(x,y) (xs,ys). (x # xs, y # ys)) xys ([],[])"
    by (simp add: revunzip_fast_as_fold)
  also have "... = foldr (\<lambda>(x,y) (xs,ys). (x # xs, y # ys)) (rev xys) ([],[])"
    by (simp add: foldr_conv_fold)
  also have "... = unzip (rev xys)"
    by (metis unzip_as_foldr)
  finally show ?thesis
    by blast
qed

lemma unzip_eq_unzip_fast: "unzip xys = unzip_fast xys"
  by (simp add: rev_eq_rev_fast unzip_eq_revunziprev_fast unzip_fast_def)

lemma unzip_preserves_length:
  "length (fst (unzip xys)) = length xys"
  "length (snd (unzip xys)) = length xys"
  by (induct xys) (clarsimp split: prod.splits)+

end
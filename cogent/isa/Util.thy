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
  imports Main "HOL-Word.Word"

"HOL-Library.Char_ord"
begin

section \<open> Ordered strings using lexical order \<close>
(* If List_Lexorder were imported, strings (as list of chars) would 
automatically inherit from the lexical order we want.
Unfortunately, we can't import it because it clashes with the prefix
order on lists imported by the word lib, so we are left with
defining or own order. 
As it is not possible to instantiate a class for a compound type such
as string (as a list of chars), we need to define a stupid datatype.
*)

datatype sortable_string = SString string
fun string_from_sstring :: "sortable_string \<Rightarrow> string" where
"string_from_sstring (SString s) = s"
(* 
The remaining of this section is copied from List_Lexorder
*)
instantiation sortable_string ::  ord
begin

definition
  sstring_less_def: "xs < ys \<longleftrightarrow> (string_from_sstring xs, string_from_sstring ys) \<in> lexord {(u, v). u < v}"

definition
 sstring_le_def: "(xs :: sortable_string) \<le> ys \<longleftrightarrow> xs < ys \<or> xs = ys"

instance ..

end

instance sortable_string :: order
proof
  fix xs :: "sortable_string"
  show "xs \<le> xs" by (simp add: sstring_le_def)
next
  fix xs ys zs :: "sortable_string"
  assume "xs \<le> ys" and "ys \<le> zs"
  then show "xs \<le> zs"
    apply (auto simp add: sstring_le_def sstring_less_def)
    apply (rule lexord_trans)
    apply (auto intro: transI)
    done
next
  fix xs ys :: "sortable_string"
  assume "xs \<le> ys" and "ys \<le> xs"
  then show "xs = ys"
    apply (auto simp add: sstring_le_def sstring_less_def)
    apply (rule lexord_irreflexive [THEN notE])
    defer
    apply (rule lexord_trans)
    apply (auto intro: transI)
    done
next
  fix xs ys :: "sortable_string"
  show "xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs"
    apply (auto simp add: sstring_less_def sstring_le_def)
    defer
    apply (rule lexord_irreflexive [THEN notE])
    apply auto
    apply (rule lexord_irreflexive [THEN notE])
    defer
    apply (rule lexord_trans)
    apply (auto intro: transI)
    done
qed

lemma not_less_Nil [simp]: "\<not> x < SString []"
  by (simp add: sstring_less_def)

lemma Nil_less_Cons [simp]: "SString [] < SString (a # x)"
  by (simp add: sstring_less_def)

lemma Cons_less_Cons [simp]: "SString (a # x) < SString (b # y) \<longleftrightarrow> 
    a <  b \<or>  a =  b \<and> SString x < SString y"
  by (simp add: sstring_less_def)

lemma le_Nil [simp]: "x \<le> SString [] \<longleftrightarrow> x = SString []"
  unfolding sstring_le_def by (cases x) auto

lemma Nil_le_Cons [simp]: "SString [] \<le> x"
  unfolding sstring_le_def 
  by (cases x,rename_tac x', case_tac x') auto
  

lemma Cons_le_Cons [simp]: "SString (a # x) \<le> SString (b # y) \<longleftrightarrow> a < b \<or> a = b \<and> SString x \<le> SString y"
  unfolding sstring_le_def by auto


instance sortable_string :: linorder
proof
  fix xss yss :: "sortable_string"
  let "?xs"  = "string_from_sstring xss"
  let "?ys"  = "string_from_sstring yss"

  have "(?xs, ?ys) \<in> lexord {(u, v). u < v} \<or> ?xs = ?ys \<or> (?ys, ?xs) \<in> lexord {(u, v). u < v}"
    by (rule lexord_linear) auto
  then show "xss \<le> yss \<or> yss \<le> xss"
   apply (cases xss ) 
    apply(cases yss)
    by (auto simp add: sstring_le_def sstring_less_def)
 
qed


section \<open> Word related lemmas \<close>

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


section \<open> Tuple lemmas \<close>

lemma compose_triple:
  "(\<lambda>(a,b,c). f a b c) \<circ> (\<lambda>(a,b,c). g a b c) = 
(\<lambda>(a,b,c). f (fst (g a b c)) (fst (snd (g a b c))) (snd (snd (g a b c))))"
  by (force simp add: comp_def split:prod.split)

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

lemma map_fst3_keep:
  shows "(\<lambda>(a,b,c). (f a, b, c)) = apfst f"
  by fastforce

lemma map_snd3_keep:
  shows "(\<lambda>(a,b,c). (a, f b, c)) = apsnd (apfst f)"
  by fastforce

lemma map_thd3_keep:
  shows "(\<lambda>(a,b,c). (a, b, f c)) = apsnd (apsnd f)"
  by fastforce

lemma fst_apfst_compcomp: "f \<circ> fst \<circ> apfst g = f \<circ> g \<circ> fst"
  by (clarsimp simp add: comp_assoc)

lemma snd_apsnd_compcomp: "f \<circ> snd \<circ> apsnd g = f \<circ> g \<circ> snd"
  by (clarsimp simp add: comp_assoc)


(* making these simp makes the final force on specialise take forever? / v.jackson *)
lemma comp_tuple_in2_out2_fst: "fst \<circ> (\<lambda>(a,b). (f a b, g a b)) = (\<lambda>(a,b). f a b)"
  by force

lemma comp_tuple_in2_out2_snd: "snd \<circ> (\<lambda>(a,b). (f a b, g a b)) = (\<lambda>(a,b). g a b)"
  by force


lemma comp_tuple_in3_out2_fst: "fst \<circ> (\<lambda>(a,b,c). (f a b c, g a b c)) = (\<lambda>(a,b,c). f a b c)"
  by force

lemma comp_tuple_in3_out2_snd: "snd \<circ> (\<lambda>(a,b,c). (f a b c, g a b c)) = (\<lambda>(a,b,c). g a b c)"
  by force


lemma assoc_comp_fst_tuple_lambda: "h \<circ> fst \<circ> (\<lambda>(a,b). (f a b, g a b)) = h \<circ> (\<lambda>(a,b). f a b)"
  by force

lemma assoc_comp_snd_tuple_lambda: "h \<circ> snd \<circ> (\<lambda>(a,b). (f a b, g a b)) = h \<circ> (\<lambda>(a,b). g a b)"
  by force


lemma prod_split_asmE: 
  "\<lbrakk> (a,b) = x; P (fst x) (snd x) \<rbrakk> \<Longrightarrow> P a b"
  by (clarsimp split: prod.split)

lemma prod_eq: 
  "\<lbrakk> a = fst x ; b = snd x \<rbrakk> \<Longrightarrow> x = (a,b)"
  by simp


lemma if_args_cong_weak[cong]: "ab = bb \<Longrightarrow> at = bt \<Longrightarrow> af = bf \<Longrightarrow> (if ab then at else af) = (if bb then bt else bf)"
  by blast


section \<open> list related lemmas \<close>

lemma map_eq_iff_nth_eq: "(map f xs = map g ys) = (length xs = length ys \<and> (\<forall>i < length xs. f (xs ! i) = g (ys ! i)))"
  by (force simp add: list_eq_iff_nth_eq)

lemma map2_mapL: "List.map2 h (map f xs) xs = map (\<lambda>x. h (f x) x) xs"
  by (induction xs) (auto)

lemma map2_mapR: "List.map2 h xs (map g xs) = map (\<lambda>x. h x (g x)) xs"
  by (induction xs) (auto)

lemma map_nth_same  :"i < length ts \<Longrightarrow> f (ts ! i) = f t \<Longrightarrow>  map f (ts [i := t]) = map f ts"
  by(simp add:map_update list_update_same_conv)

lemma map_fst_update:
  assumes "ts ! f = (t, x)"
    and     "f < length ts" 
  shows "map fst (ts[f := (t,x')]) = map fst ts"
  using assms
  by(simp add: map_nth_same)
(*
proof -
  from assms have  "map fst ts ! f = t" by (clarsimp)
  then show ?thesis by (auto simp add: map_update)
qed
*)
lemma map_zip [simp]:
  shows "map (\<lambda> (a , b). (f a, g b)) (zip as bs) = zip (map f as) (map g bs)"
  by (induct as arbitrary:bs, simp, case_tac bs, simp_all)

lemma map_zip3 [simp]:
  shows "map (\<lambda> (a,b,c). (f a, g b, h c)) (zip as (zip bs cs)) = zip (map f as) (zip (map g bs) (map h cs))"
  by (induct as arbitrary: bs cs; case_tac bs; case_tac cs; simp)

lemma zip_eq_conv_sym: "length xs = length ys \<Longrightarrow> (zs = zip xs ys) = (map fst zs = xs \<and> map snd zs = ys)"
  using zip_eq_conv
  by metis


lemma replicate_eq_map_conv_nth: "length xs = n \<Longrightarrow> map f xs = replicate n x \<longleftrightarrow> (\<forall>i<length xs. f (xs ! i) = x)" 
proof (induct xs arbitrary: n)
  case (Cons a as)
  moreover obtain n' where "n = Suc n'"
    using Cons.prems by auto
  moreover then have "(map f as = replicate n' x) = (length as = n' \<and> (\<forall>i<length as. f (as ! i) = x))"
    using Cons by simp
  ultimately show ?case
    by (force simp add: All_less_Suc2)
qed simp


lemma eq_updated_same_pace_imp_eq:
  assumes "length xs = length ys"
    and "i < length xs"
    and "xs[i := x] = ys[i := y]"
  shows "x = y"
  using assms
  by (induct "length xs" arbitrary: xs ys i; metis nth_list_update_eq)

lemma map_update_eq_if_indistinguishable:
  assumes
    "xs ! i = a"
    "i < length xs"
    "f (g (xs ! i)) = f (xs ! i)"
  shows "map f xs = map f (xs[i := g a])"
  using assms
  by (metis list_update_id map_update)

lemma map_proj_eq_set_zip_impl_proj_eq:
  "map P as = map Q bs \<Longrightarrow>
  (a,b) \<in> set (zip as bs) \<Longrightarrow>
  P a = Q b"
proof -
  assume A:
    "map P as = map Q bs"
    "(a,b) \<in> set (zip as bs)"
  have L: "length as = length bs"
    using A map_eq_imp_length_eq by auto
  from L A show "P a = Q b"
    by (induct as bs rule: list_induct2; auto)
qed

lemma list_all2_update_second:
  assumes "list_all2 f xs (ys[i := a])"
    and "f (xs ! i) a \<Longrightarrow> f (xs ! i) b"
  shows "list_all2 f xs (ys[i := b])"
  using assms
  by (clarsimp simp add: list_all2_conv_all_nth, metis nth_list_update_eq nth_list_update_neq)

lemma elem_in_list_set_update:
  assumes
    "x \<in> set xs \<or> x = y"
    "xs ! i \<noteq> x"
    "i < length xs"
  shows "x \<in> set (xs[i := y])"
proof -
  have "x \<in> insert y (set xs)"
    using assms by auto
  then show "x \<in> set (xs[i := y])"
    by (metis assms in_set_conv_nth length_list_update nth_list_update_neq set_update_memI)
qed
  

lemma distinct_fst_tags_update:
  assumes
    "distinct (map fst xs)"
    "fst (xs ! i) = a"
    "i < length xs"
  shows "distinct (map fst (xs[i := (a, b, c)]))"
  using assms
  apply (clarsimp simp add: map_update)
  apply (induct xs arbitrary: i)
   apply (simp split: nat.split add: image_set map_update[symmetric] del: image_set[symmetric])+
  done


lemma list_all_nil: "list_all P []" by simp
lemma list_all_cons: "P x \<Longrightarrow> list_all P xs \<Longrightarrow> list_all P (x # xs)" by simp

subsection \<open> list_all2 \<close>

lemmas list_all2_nil = List.list.rel_intros(1)
lemmas list_all2_cons = List.list.rel_intros(2)

lemma list_all2_eq_iff_map_eq: "list_all2 (\<lambda>x y. f x = g y) xs ys = (map f xs = map g ys)"
  by (induct xs arbitrary: ys; simp add: Cons_eq_map_conv list_all2_Cons1)

lemma list_all2_split_conj:
  shows "list_all2 (\<lambda>x y. P x y \<and> Q x y) xs ys \<longleftrightarrow> list_all2 P xs ys \<and> list_all2 Q xs ys"
  apply (rule iffI)
   apply (induct rule: list_all2_induct, simp+)
  apply (clarsimp, induct rule: list_all2_induct, simp+)
  done

lemma list_all2_split_all:
  shows "list_all2 (\<lambda>x y. \<forall>a. P x y a) xs ys \<longleftrightarrow> (\<forall>a. list_all2 (\<lambda>x y. P x y a) xs ys)"
  apply (rule iffI)
   apply (induct rule: list_all2_induct, simp+)
  apply (induct xs arbitrary: ys; case_tac ys; clarsimp)
  done

lemma list_all2_in_set1_impl_in_set_zip12_sat:
  assumes
    "list_all2 P xs ys"
    "x \<in> set xs"
  obtains y where
    "(x,y) \<in> set (zip xs ys)"
    "P x y"
  using assms by (metis fst_conv in_set_impl_in_set_zip1 in_set_zip list_all2_conv_all_nth snd_conv)

lemma list_all2_in_set_impl_sat:
  assumes
    "list_all2 P xs ys"
    "(x,y) \<in> set (zip xs ys)"
  shows
    "P x y"
  using assms
  by (metis fst_conv in_set_zip list_all2_nthD snd_conv)

lemma list_all_zip_iff_list_all2:
  assumes "length xs = length ys"
  shows "list_all P (zip xs ys) \<longleftrightarrow> list_all2 (curry P) xs ys"
  using assms
  by (induct xs ys rule: list_induct2) simp+


subsection \<open> list_all3 \<close>

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

lemma list_all3_comm1:
"list_all3 (\<lambda> x y z. P x y z) xs ys zs \<longleftrightarrow> list_all3 (\<lambda> x y z. P y x z) ys xs zs"
  by (metis (mono_tags, lifting) list_all3_conv_all_nth)

lemma list_all3_comm2:
"list_all3 (\<lambda> x y z. P x y z) xs ys zs \<longleftrightarrow> list_all3 (\<lambda> x y z. P x z y) xs zs ys"
  by (metis (mono_tags, lifting) list_all3_conv_all_nth)

lemma list_all3_comm3:
"list_all3 (\<lambda> x y z. P x y z) xs ys zs \<longleftrightarrow> list_all3 (\<lambda> x y z. P z y x) zs ys xs"
  by (metis (mono_tags, lifting) list_all3_conv_all_nth)


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

subsection \<open> list_all4 \<close>

inductive list_all4 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'd list \<Rightarrow> bool" where
  all4Nil : "list_all4 P [] [] [] []"
| all4Cons : "P x y z w \<Longrightarrow> list_all4 P xs ys zs ws \<Longrightarrow> list_all4 P (x # xs) (y # ys) (z # zs) (w # ws)"

lemma list_all4_induct
  [consumes 1, case_names Nil Cons, induct set: list_all4]:
  assumes P: "list_all4 P xs ys zs ws"
  assumes Nil: "R [] [] [] []"
  assumes Cons: "\<And>x xs y ys z zs  w ws.
    \<lbrakk>P x y z w; list_all4 P xs ys zs ws; R xs ys zs ws\<rbrakk> \<Longrightarrow> R (x # xs) (y # ys) (z # zs) (w # ws)"
  shows "R xs ys zs ws"
  using P
  by (induct xs arbitrary: ys zs ws) (auto elim: list_all4.cases simp add: Nil Cons)

lemma list_induct4':
  "\<lbrakk> P [] [] [] [];
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
   \<And>     y ys z zs w ws. P []     (y#ys) (z#zs) (w#ws);
   \<And>x xs y ys z zs w ws. P xs ys zs ws \<Longrightarrow> P (x#xs) (y#ys) (z#zs) (w#ws) \<rbrakk>
 \<Longrightarrow> P xs ys zs ws"
  by (induct xs arbitrary: ys zs ws; rename_tac ys zs ws, case_tac ys; case_tac zs; case_tac ws; simp)

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

section \<open> Misc lemmas \<close>

lemma distinct_fst:
  assumes "distinct (map fst xs)"
    and     "(a, b) \<in> set xs"
    and     "(a, b') \<in> set xs"
  shows   "b = b'"
  using assms image_iff
  by (induct xs, fastforce+)

lemma distinct_fst_nth:
  assumes "distinct (map fst xs)"
    and "i < length xs"
    and "xs ! i = (a, b)"
    and "j < length xs"
    and "xs ! j = (a, b')"
  shows
    "i = j"
    "b = b'"
  using assms
  by (induct xs arbitrary: i j)
      (fastforce dest: nth_mem simp add: image_iff less_Suc_eq_0_disj nth_Cons)+

lemma set_subset_map:
  assumes "set a \<subseteq> set b"
  shows   "set (map f a) \<subseteq> set (map f b)"
  using assms by auto

lemma prod_in_set:
  assumes "(a, b) \<in> set l"
  shows   "a \<in> set (map fst l)"
    and     "b \<in> set (map snd l)"
  using assms by (force intro: imageI)+


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

lemma filter_empty_conv2: "([] = filter P xs) = (\<forall>x\<in>set xs. \<not> P x)"
  using filter_empty_conv by metis

lemma filter_eq_singleton_iff:
  shows "(filter P ys = [x]) = (\<exists>us vs. ys = us @ x # vs \<and> (\<forall>u\<in>set us. \<not> P u) \<and> P x \<and> (\<forall>u\<in>set vs. \<not> P u))"
  by (simp add: filter_eq_Cons_iff filter_empty_conv2)

lemma filter_eq_singleton_iff2:
  shows "([x] = filter P ys) = (\<exists>us vs. ys = us @ x # vs \<and> (\<forall>u\<in>set us. \<not> P u) \<and> P x \<and> (\<forall>u\<in>set vs. \<not> P u))"
  by (fastforce simp add: filter_eq_singleton_iff[symmetric])


lemma filter_member:
  assumes
    "filter P xs = ys"
    "y \<in> set ys"
  shows "y \<in> set xs"
  using assms
  apply (induct xs arbitrary: ys)
   apply clarsimp
  apply (case_tac "P a"; clarsimp)
  done

lemma filter_member2:
  assumes
    "ys = filter P xs"
    "y \<in> set ys"
  shows "y \<in> set xs"
  using assms filter_member
  by fast

lemma filter_member_unique_nth:
  assumes "filter P xs = [a]"
  shows "\<exists>!i. i < length xs \<and> xs ! i = a"
proof -
  obtain us vs where xs_decomp:
    "xs = us @ a # vs"
    "\<forall>u\<in>set us. \<not> P u"
    "P a"
    "\<forall>u\<in>set vs. \<not> P u"
    using assms 
    by (clarsimp simp add: filter_eq_Cons_iff filter_empty_conv2)
  then have a_not_left_right:
    "a \<notin> set us"
    "a \<notin> set vs"
    by blast+

  have "\<And>i. \<lbrakk> i < length xs ; xs ! i = a \<rbrakk> \<Longrightarrow> i = length us"
    using a_not_left_right
    apply (clarsimp simp add: xs_decomp nth_append)
    apply (metis (no_types, lifting) add.right_neutral add_Suc_right add_diff_inverse_nat add_less_cancel_left less_Suc_eq_le nth_equal_first_eq nth_mem)
    done
  then show ?thesis
    apply (clarsimp simp add: Ex1_def Ex_less_Suc)
    apply (metis length_append length_pos_if_in_set less_add_same_cancel1 list.set_intros(1) nth_append_length xs_decomp(1))
    done
qed

lemma all_imp_conj_distrib: "(\<forall>x. P x \<longrightarrow> Q x \<and> R x) = ((\<forall>x. P x \<longrightarrow> Q x) \<and> (\<forall>x. P x \<longrightarrow> R x))"
  by blast

lemma imp2_conj_pull_out_common: "(A \<longrightarrow> B \<longrightarrow> C) \<and> (A' \<longrightarrow> B \<longrightarrow> C') \<longleftrightarrow> (B \<longrightarrow> (A \<longrightarrow> C) \<and> (A' \<longrightarrow> C'))"
  by blast

section \<open> TSum as map lemmas \<close>

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


section \<open> Tagged List lemmas \<close>

subsection \<open> Tagged list update \<close>

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

lemma tagged_list_update_tag_present:
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
    using assms
    by (simp add: tagged_list_update_tag_present)
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

lemma tagged_list_update_success_contains_updated_elem:
  assumes "i \<in> fst ` set xs"
  shows "(i, a) \<in> set (tagged_list_update i a xs)"
  using assms
  by (induct xs; fastforce)

end
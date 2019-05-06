(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory TypeTrackingTyping imports
  Cogent
begin

datatype type_split_kind = TSK_L | TSK_S | TSK_NS

lemma type_split_kind_option_splits:
  fixes tsko :: "type_split_kind option"
  shows
    "P (case tsko of None \<Rightarrow> f1 | Some x \<Rightarrow> f2 x) \<longleftrightarrow> (
        (tsko = None \<longrightarrow> P f1)
      \<and> (tsko = Some TSK_L \<longrightarrow> P (f2 TSK_L))
      \<and> (tsko = Some TSK_S \<longrightarrow> P (f2 TSK_S))
      \<and> (tsko = Some TSK_NS \<longrightarrow> P (f2 TSK_NS)))"
    "P (case (tsko :: type_split_kind option) of None \<Rightarrow> f1 | Some x \<Rightarrow> f2 x) \<longleftrightarrow> \<not> (
        (tsko = None \<and> \<not> P f1)
      \<or> (tsko = Some TSK_L \<and> \<not> P (f2 TSK_L))
      \<or> (tsko = Some TSK_S \<and> \<not> P (f2 TSK_S))
      \<or> (tsko = Some TSK_NS \<and> \<not> P (f2 TSK_NS)))"
  by (case_tac tsko, simp, case_tac a; clarsimp)+

lemma type_split_kind_option_exhaust:
  fixes y :: "type_split_kind option"
  obtains
    "y = None"
  | "y = Some TSK_L"
  | "y = Some TSK_S"
  | "y = Some TSK_NS"
  by (case_tac y, simp, case_tac a; clarsimp)


datatype typing_tree = TyTrLeaf
    | TyTrSplit "type_split_kind option list" ctx typing_tree ctx typing_tree

type_synonym tree_ctx = "typing_tree * ctx"

fun apply_tsk :: "type_split_kind option \<Rightarrow> type option \<Rightarrow> type option \<times> type option"
where
    "apply_tsk None t = (None, t)"
  | "apply_tsk (Some TSK_L) t = (t, None)"
  | "apply_tsk (Some TSK_S) t = (t, t)"
  | "apply_tsk (Some TSK_NS) t = (map_option bang t, t)"

fun
  follow_typing_tree :: "tree_ctx \<Rightarrow> tree_ctx \<times> tree_ctx"
where
  "follow_typing_tree (TyTrSplit sps xs T1 ys T2, \<Gamma>)
    = ((T1, xs @ map (fst o case_prod apply_tsk) (zip sps \<Gamma>)),
        (T2, ys @ map (snd o case_prod apply_tsk) (zip sps \<Gamma>)))"

fun
  new_tt_types :: "tree_ctx \<Rightarrow> ctx"
where
    "new_tt_types (TyTrSplit sps xs T1 ys T2, \<Gamma>) = ys"
  | "new_tt_types (TyTrLeaf, v) = []"

fun
  follow_typing_tree_triv :: "tree_ctx \<Rightarrow> tree_ctx \<times> tree_ctx"
where
  "follow_typing_tree_triv (TyTrSplit sps xs T1 ys T2, \<Gamma>) = ((T1, xs @ \<Gamma>), (T2, ys @ \<Gamma>))"

definition
  composite_anormal_expr :: "'f expr \<Rightarrow> bool"
where
  "composite_anormal_expr x \<equiv> case x of Let _ _ \<Rightarrow> True
    | LetBang _ _ _ \<Rightarrow> True
    | Case _ _ _ _ \<Rightarrow> True
    | If _ _ _ \<Rightarrow> True
    | Split _ _ \<Rightarrow> True
    | Take _ _ _ \<Rightarrow> True
    | _ \<Rightarrow> False"


inductive ttsplit_inner_comp  :: "kind env \<Rightarrow> bool \<Rightarrow> type_split_kind option \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> bool" where
  "\<lbrakk> t1 = t; t2 = None; \<forall>ta. t = Some ta \<longrightarrow> kndng \<longrightarrow> Ex (kinding K ta) \<rbrakk> \<Longrightarrow> ttsplit_inner_comp K kndng (Some TSK_L) t t1 t2"
| "\<lbrakk> t1 = t; t2 = t; \<exists>ta k. t = Some ta \<and> K \<turnstile> ta :\<kappa> k \<and> S \<in> k \<rbrakk> \<Longrightarrow> ttsplit_inner_comp K kndng (Some TSK_S) t t1 t2"
| "\<lbrakk> t1 = None; t2 = t; \<forall>y. t = Some y \<longrightarrow> kndng \<longrightarrow> Ex (kinding K y) \<rbrakk> \<Longrightarrow> ttsplit_inner_comp K kndng None t t1 t2"

definition ttsplit_inner :: "kind env \<Rightarrow> type_split_kind option list \<Rightarrow> bool \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool"
where
  "ttsplit_inner K sps kndng \<Gamma> \<Gamma>1 \<Gamma>2 = list_all4 (ttsplit_inner_comp K kndng) sps \<Gamma> \<Gamma>1 \<Gamma>2"

definition ttsplit_inner' :: "kind env \<Rightarrow> type_split_kind option list \<Rightarrow> bool \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool"
where
  "ttsplit_inner' K sps kndng \<Gamma>b \<Gamma>1 \<Gamma>2 = (
          length sps = length \<Gamma>b
        \<and> \<Gamma>1 = map (\<lambda> (sp, v). if sp \<in> {Some TSK_L, Some TSK_S} then v else None)
                        (zip sps \<Gamma>b)
        \<and> \<Gamma>2 = map (\<lambda> (sp, v). if sp = Some TSK_L then None else v)
                        (zip sps \<Gamma>b)
        \<and> list_all ((\<noteq>) (Some TSK_NS)) sps
        \<and> list_all (\<lambda>t. t \<noteq> None \<longrightarrow> kndng \<longrightarrow> (K \<turnstile> the t wellformed)) \<Gamma>b
        \<and> (\<forall>i < length \<Gamma>b. nth sps i = Some TSK_S
            \<longrightarrow> (\<exists>t. \<Gamma>b ! i = Some t \<and> (\<exists>k. K \<turnstile> t :\<kappa> k \<and> S \<in> k))))"


lemmas ttsplit_inner_induct =
  list_all4_induct[where P=\<open>ttsplit_inner_comp K kndng\<close> for K kndng,
    simplified ttsplit_inner_def[symmetric],
    consumes 1,
    case_names Nil Cons]

lemmas ttsplit_inner_nil =
  all4Nil[where P=\<open>ttsplit_inner_comp K kndng\<close> for K kndng , simplified ttsplit_inner_def[symmetric]]
lemmas ttsplit_inner_cons =
  all4Cons[where P=\<open>ttsplit_inner_comp K kndng\<close> for K kndng, simplified ttsplit_inner_def[symmetric]]
lemmas ttsplit_inner_intros = ttsplit_inner_nil ttsplit_inner_cons

lemmas ttsplit_inner_conv_all_nth =
  list_all4_conv_all_nth[where P=\<open>ttsplit_inner_comp K kndng\<close> for K kndng, simplified ttsplit_inner_def[symmetric]]

lemmas ttsplit_inner_Cons =
  list_all4_Cons[where P=\<open>ttsplit_inner_comp K kndng\<close> for K kndng, simplified ttsplit_inner_def[symmetric]]

lemmas ttsplit_inner_ConsD = ttsplit_inner_Cons[THEN iffD2, OF conjI]

lemmas ttsplit_inner_Cons1 =
  list_all4_Cons1[where P=\<open>ttsplit_inner_comp K kndng\<close> for K kndng, simplified ttsplit_inner_def[symmetric]]
lemmas ttsplit_inner_Cons2 =
  list_all4_Cons2[where P=\<open>ttsplit_inner_comp K kndng\<close> for K kndng, simplified ttsplit_inner_def[symmetric]]


lemma ttsplit_inner_iff_ttsplit_inner':
  "ttsplit_inner K sps kndng \<Gamma>b \<Gamma>1 \<Gamma>2 \<longleftrightarrow> ttsplit_inner' K sps kndng \<Gamma>b \<Gamma>1 \<Gamma>2"
proof (rule iffI)
  assume "ttsplit_inner K sps kndng \<Gamma>b \<Gamma>1 \<Gamma>2"
  then  show "ttsplit_inner' K sps kndng \<Gamma>b \<Gamma>1 \<Gamma>2"
  proof (induct rule: ttsplit_inner_induct)
    case Cons then show ?case
      apply (clarsimp simp add: ttsplit_inner'_def)
      apply (erule ttsplit_inner_comp.cases)
        apply (force simp add: list_all_length All_less_Suc2)+
      done
  qed (clarsimp simp add: ttsplit_inner'_def)
next
  assume "ttsplit_inner' K sps kndng \<Gamma>b \<Gamma>1 \<Gamma>2"
  then show "ttsplit_inner K sps kndng \<Gamma>b \<Gamma>1 \<Gamma>2"
    apply (clarsimp simp add: ttsplit_inner'_def ttsplit_inner_conv_all_nth)
    apply (case_tac "sps ! i" rule: type_split_kind_option_exhaust)
       apply (fastforce simp add: list_all_length ttsplit_inner_comp.simps)+
    done
qed

definition ttsplit :: "kind env \<Rightarrow> tree_ctx \<Rightarrow> type_split_kind option list
        \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> bool"
where
  "ttsplit K \<Gamma> sps xs \<Gamma>1 ys \<Gamma>2 =
    (\<exists>\<Gamma>b \<Gamma>1a \<Gamma>2a T1 T2. \<Gamma> = (TyTrSplit sps xs T1 ys T2, \<Gamma>b)
        \<and> \<Gamma>1 = (T1, xs @ \<Gamma>1a)
        \<and> \<Gamma>2 = (T2, ys @ \<Gamma>2a)
        \<and> ttsplit_inner K sps True \<Gamma>b \<Gamma>1a \<Gamma>2a)"

lemma ttsplitI:
  "ttsplit_inner K sps True \<Gamma>b \<Gamma>1 \<Gamma>2 \<Longrightarrow> xs' = xs @ \<Gamma>1 \<Longrightarrow> ys' = ys @ \<Gamma>2
    \<Longrightarrow> ttsplit K (TyTrSplit sps xs T1 ys T2, \<Gamma>b) sps xs (T1, xs') ys (T2, ys')"
  by (simp add: ttsplit_def)

lemma forall_less_Suc_eq:
  "(\<forall>j < Suc i. P j) = (P 0 \<and> (\<forall>j < i. P (Suc j)))"
  by (auto simp add: less_Suc_eq_0_disj)

lemma ttsplit_innerI:
  "ttsplit_inner K sps kndng \<Gamma>b \<Gamma>1 \<Gamma>2
    \<Longrightarrow> ttsplit_inner K (None # sps) kndng (None # \<Gamma>b) (None # \<Gamma>1) (None # \<Gamma>2)"
  "(kndng \<Longrightarrow> K \<turnstile> \<gamma> :\<kappa>  k) \<Longrightarrow> ttsplit_inner K sps kndng \<Gamma>b \<Gamma>1 \<Gamma>2
    \<Longrightarrow> ttsplit_inner K (None # sps) kndng (Some \<gamma> # \<Gamma>b) (None # \<Gamma>1) (Some \<gamma> # \<Gamma>2)"
  "(kndng \<Longrightarrow> K \<turnstile> \<gamma> :\<kappa>  k) \<Longrightarrow> ttsplit_inner K sps kndng \<Gamma>b \<Gamma>1 \<Gamma>2
    \<Longrightarrow> ttsplit_inner K (Some TSK_L # sps) kndng (Some \<gamma> # \<Gamma>b) (Some \<gamma> # \<Gamma>1) (None # \<Gamma>2)"
  "K \<turnstile> \<gamma> :\<kappa>  k \<Longrightarrow> S \<in> k \<Longrightarrow> ttsplit_inner K sps kndng \<Gamma>b \<Gamma>1 \<Gamma>2
    \<Longrightarrow> ttsplit_inner K (Some TSK_S # sps) kndng (Some \<gamma> # \<Gamma>b) (Some \<gamma> # \<Gamma>1) (Some \<gamma> # \<Gamma>2)"
  "ttsplit_inner K [] kndng [] [] []"  
  by (force intro!: ttsplit_inner_intros simp add: ttsplit_inner_comp.simps)+

lemma split_list_zip:
  "split K \<Gamma> \<Gamma>1 \<Gamma>2 = (length \<Gamma>1 = length \<Gamma> \<and> length \<Gamma>2 = length \<Gamma>
        \<and> (\<forall>(x, (y, z)) \<in> set (zip \<Gamma> (zip \<Gamma>1 \<Gamma>2)). split_comp K x y z))"
  apply (induct \<Gamma> arbitrary: \<Gamma>1 \<Gamma>2)
   apply (force elim: split_cases intro: split_empty)
  apply (force
      simp add: length_Suc_conv all_set_conv_all_nth split_Cons1 nth.nth_Cons
      split: nat.split)
  done

lemma ttsplit_imp_split:
  "ttsplit K \<Gamma> ijs xs \<Gamma>1 ys \<Gamma>2 \<Longrightarrow> (\<exists>\<Gamma>1a \<Gamma>2a. split K (snd \<Gamma>) \<Gamma>1a \<Gamma>2a
    \<and> snd \<Gamma>1 = xs @ \<Gamma>1a \<and> snd \<Gamma>2 = ys @ \<Gamma>2a)"
  apply (clarsimp simp add: ttsplit_def split_comp.simps split_conv_all_nth ttsplit_inner_conv_all_nth list_all_length)
  apply (drule_tac x=i in spec)
  apply (auto elim!: ttsplit_inner_comp.cases)
  done

lemma split_imp_ttsplit:
  "split K \<Gamma> \<Gamma>1 \<Gamma>2
    \<Longrightarrow> sps = map (\<lambda>i. if \<Gamma>1 ! i = None then None
                       else if \<Gamma>2 ! i = None then Some TSK_L else Some TSK_S) [0 ..< length \<Gamma>]
    \<Longrightarrow> \<Gamma>1' = xs @ \<Gamma>1
    \<Longrightarrow> \<Gamma>2' = ys @ \<Gamma>2
    \<Longrightarrow> ttsplit K (TyTrSplit sps xs tt ys tt2, \<Gamma>) sps xs
        (tt, \<Gamma>1') ys (tt2, \<Gamma>2')"
  apply (clarsimp
      simp: ttsplit_def ttsplit_inner_conv_all_nth split_conv_all_nth list_all_length
      cong: if_cong)
  apply (case_tac "\<Gamma>2 ! i"; case_tac "\<Gamma>1 ! i")
     apply (fastforce simp add: split_comp.simps ttsplit_inner_comp.simps)+
  done

definition ttsplit_triv :: "tree_ctx \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> bool"
where
  "ttsplit_triv \<Gamma> xs \<Gamma>1 ys \<Gamma>2 = (\<exists>ijs \<Gamma>1a \<Gamma>2a.
    fst \<Gamma> = TyTrSplit ijs xs \<Gamma>1a ys \<Gamma>2a \<and> \<Gamma>1 = (\<Gamma>1a, xs @ snd \<Gamma>) \<and> \<Gamma>2 = (\<Gamma>2a, ys @ snd \<Gamma>))"

lemma ttsplit_trivI:
  "\<Gamma>1b = (\<Gamma>1a, xs @ \<Gamma>b) \<Longrightarrow> \<Gamma>2b = (\<Gamma>2a, ys @ \<Gamma>b) \<Longrightarrow> ttsplit_triv (TyTrSplit ijs xs \<Gamma>1a ys \<Gamma>2a, \<Gamma>b) xs \<Gamma>1b ys \<Gamma>2b"
  by (simp add: ttsplit_triv_def)

subsection {* ttsplit_bang *}

inductive ttsplit_bang_inner_comp :: "kind env \<Rightarrow> type_split_kind option \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> bool" where
  "\<lbrakk> t1 = t; t2 = None; \<forall>ta. t = Some ta \<longrightarrow> Ex (kinding K ta) \<rbrakk> \<Longrightarrow> ttsplit_bang_inner_comp K (Some TSK_L) t t1 t2"
| "\<lbrakk> t1 = t; t2 = t; \<exists>ta k. t = Some ta \<and> K \<turnstile> ta :\<kappa> k \<and> S \<in> k \<rbrakk> \<Longrightarrow> ttsplit_bang_inner_comp K (Some TSK_S) t t1 t2"
| "\<lbrakk> t1 = map_option bang t; t2 = t; \<exists>y. t = Some y \<rbrakk> \<Longrightarrow> ttsplit_bang_inner_comp K (Some TSK_NS) t t1 t2"
| "\<lbrakk> t1 = None; t2 = t; \<forall>y. t = Some y \<longrightarrow> Ex (kinding K y) \<rbrakk> \<Longrightarrow> ttsplit_bang_inner_comp K None t t1 t2"

definition ttsplit_bang_inner :: "kind env \<Rightarrow> type_split_kind option list \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool"
where
  "ttsplit_bang_inner K \<equiv> list_all4 (ttsplit_bang_inner_comp K)"

lemmas ttsplit_bang_inner_induct =
  list_all4_induct[where P=\<open>ttsplit_bang_inner_comp K\<close> for K,
    simplified ttsplit_bang_inner_def[symmetric],
    consumes 1,
    case_names Nil Cons]

lemmas ttsplit_bang_inner_nil =
  all4Nil[where P=\<open>ttsplit_bang_inner_comp K\<close> for K, simplified ttsplit_bang_inner_def[symmetric]]
lemmas ttsplit_bang_inner_cons =
  all4Cons[where P=\<open>ttsplit_bang_inner_comp K\<close> for K, simplified ttsplit_bang_inner_def[symmetric]]
lemmas ttsplit_bang_inner_intros = ttsplit_bang_inner_nil ttsplit_bang_inner_cons

lemmas ttsplit_bang_inner_conv_all_nth =
  list_all4_conv_all_nth[where P=\<open>ttsplit_bang_inner_comp K\<close> for K, simplified ttsplit_bang_inner_def[symmetric]]

lemmas ttsplit_bang_inner_Cons =
  list_all4_Cons[where P=\<open>ttsplit_bang_inner_comp K\<close> for K, simplified ttsplit_bang_inner_def[symmetric]]

lemmas ttsplit_bang_inner_ConsD = ttsplit_bang_inner_Cons[THEN iffD2, OF conjI]

lemmas ttsplit_bang_inner_Cons1 =
  list_all4_Cons1[where P=\<open>ttsplit_bang_inner_comp K\<close> for K, simplified ttsplit_bang_inner_def[symmetric]]
lemmas ttsplit_bang_inner_Cons2 =
  list_all4_Cons2[where P=\<open>ttsplit_bang_inner_comp K\<close> for K, simplified ttsplit_bang_inner_def[symmetric]]

subsubsection {* ttsplit_bang alt *}

definition ttsplit_bang_inner' :: "kind env \<Rightarrow> type_split_kind option list \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool"
where
  "ttsplit_bang_inner' K sps \<Gamma>b \<Gamma>1 \<Gamma>2 = (
          length sps = length \<Gamma>b
        \<and> \<Gamma>1 = map (\<lambda> (sp, v). if sp \<in> {Some TSK_L, Some TSK_S} then v
                            else if sp = Some TSK_NS then map_option bang v else None)
                        (zip sps \<Gamma>b)
        \<and> \<Gamma>2 = map (\<lambda> (sp, v). if sp \<noteq> Some TSK_L then v else None)
                        (zip sps \<Gamma>b)
        \<and> (\<forall>i < length \<Gamma>b. nth sps i \<noteq> Some TSK_NS \<and> \<Gamma>b ! i \<noteq> None \<longrightarrow> (\<exists>k. K \<turnstile> the (\<Gamma>b ! i) :\<kappa> k))
        \<and> (\<forall>i < length \<Gamma>b. nth sps i = Some TSK_NS \<longrightarrow> nth \<Gamma>b i \<noteq> None) 
        \<and> (\<forall>i < length \<Gamma>b. nth sps i = Some TSK_S
            \<longrightarrow> nth \<Gamma>b i \<noteq> None \<and> (\<exists>k. K \<turnstile> (the (nth \<Gamma>b i)) :\<kappa> k \<and> S \<in> k)))"

lemma ttsplit_bang_inner_iff_ttsplit_bang_inner':
  "ttsplit_bang_inner K sps \<Gamma> \<Gamma>1 \<Gamma>2 \<longleftrightarrow> ttsplit_bang_inner' K sps \<Gamma> \<Gamma>1 \<Gamma>2"
proof safe
  {
    fix x y z w
    have "ttsplit_bang_inner_comp K x y z w \<longleftrightarrow> ttsplit_bang_inner' K [x] [y] [z] [w]"
      apply (clarsimp simp add: ttsplit_bang_inner_comp.simps ttsplit_bang_inner'_def)
      apply (cases x rule: type_split_kind_option_exhaust; force)
      done
  } note comp_to_comp' = this
  {
    fix x xs y ys z zs w ws
    have "ttsplit_bang_inner' K (x # xs) (y # ys) (z # zs) (w # ws) \<longleftrightarrow>
            ttsplit_bang_inner' K [x] [y] [z] [w] \<and> ttsplit_bang_inner' K xs ys zs ws"
      unfolding ttsplit_bang_inner'_def
      apply (rule iffI)
       apply safe
                          apply ((simp add: All_less_Suc2)+)[10]
                apply (clarsimp simp add: All_less_Suc2, metis option.sel)
               apply ((clarsimp simp add: All_less_Suc2)+)[6]
         apply (clarsimp simp add: All_less_Suc2 nth.nth_Cons split: nat.splits, metis option.sel)
        apply (clarsimp simp add: All_less_Suc2 nth.nth_Cons split: nat.splits)+
      done
  } note inner'_Cons = this
  {
    assume "ttsplit_bang_inner K sps \<Gamma> \<Gamma>1 \<Gamma>2"
    then show "ttsplit_bang_inner' K sps \<Gamma> \<Gamma>1 \<Gamma>2"
    proof (induct rule: ttsplit_bang_inner_induct)
      case (Cons x xs y ys z zs w ws)
      then show ?case
        using comp_to_comp' inner'_Cons
        by blast
    qed (simp add: ttsplit_bang_inner'_def)
  }
  {
    assume "ttsplit_bang_inner' K sps \<Gamma> \<Gamma>1 \<Gamma>2"
    moreover then have
      "length \<Gamma>1 = length sps"
      "length \<Gamma>2 = length sps"
      "length \<Gamma> = length sps"
      using ttsplit_bang_inner'_def by auto
    ultimately show "ttsplit_bang_inner K sps \<Gamma> \<Gamma>1 \<Gamma>2"
    proof (induct sps \<Gamma> \<Gamma>1 \<Gamma>2 rule: list_induct4_simple)
      case (Cons x xs y ys z zs w ws)
      then show ?case
        by (clarsimp, metis comp_to_comp' inner'_Cons ttsplit_bang_inner_Cons)
    qed (auto intro: ttsplit_bang_inner_intros)
  }
qed


definition
  "ttsplit_bang is sps K \<Gamma> xs \<Gamma>1 ys \<Gamma>2 =
    (\<exists>\<Gamma>b \<Gamma>1a \<Gamma>2a T1 T2. \<Gamma> = (TyTrSplit sps xs T1 ys T2, \<Gamma>b)
        \<and> length \<Gamma>b = length sps
        \<and> ttsplit_bang_inner K sps \<Gamma>b \<Gamma>1a \<Gamma>2a
        \<and> (\<forall>i < length \<Gamma>b. (i \<in> is) = (nth sps i = Some TSK_NS))
        \<and> \<Gamma>1 = (T1, xs @ \<Gamma>1a)
        \<and> \<Gamma>2 = (T2, ys @ \<Gamma>2a))"

lemma ttsplit_bangI:
  "xs' = xs @ \<Gamma>1a
    \<Longrightarrow> ys' = ys @ \<Gamma>2a
    \<Longrightarrow> is = set (map fst (filter (\<lambda>(i, v). v = Some TSK_NS) (enumerate 0 sps)))
    \<Longrightarrow> ttsplit_bang_inner K sps \<Gamma>b \<Gamma>1a \<Gamma>2a
    \<Longrightarrow> ttsplit_bang is sps K (TyTrSplit sps xs T1 ys T2, \<Gamma>b) xs (T1, xs') ys (T2, ys')"
  by (clarsimp simp add: ttsplit_bang_def image_Collect in_set_enumerate_eq ttsplit_bang_inner_conv_all_nth)

lemma ttsplit_bang_innerI:
  "ttsplit_bang_inner K sps \<Gamma>b \<Gamma>1 \<Gamma>2
    \<Longrightarrow> ttsplit_bang_inner K (None # sps) (None # \<Gamma>b) (None # \<Gamma>1) (None # \<Gamma>2)"
  "K \<turnstile> \<gamma> :\<kappa>  k \<Longrightarrow> ttsplit_bang_inner K sps \<Gamma>b \<Gamma>1 \<Gamma>2
    \<Longrightarrow> ttsplit_bang_inner K (None # sps) (Some \<gamma> # \<Gamma>b) (None # \<Gamma>1) (Some \<gamma> # \<Gamma>2)"
  "K \<turnstile> \<gamma> :\<kappa>  k \<Longrightarrow> ttsplit_bang_inner K sps \<Gamma>b \<Gamma>1 \<Gamma>2
    \<Longrightarrow> ttsplit_bang_inner K (Some TSK_L # sps) (Some \<gamma> # \<Gamma>b) (Some \<gamma> # \<Gamma>1) (None # \<Gamma>2)"
  "K \<turnstile> \<gamma> :\<kappa>  k \<Longrightarrow> S \<in> k \<Longrightarrow> ttsplit_bang_inner K sps \<Gamma>b \<Gamma>1 \<Gamma>2
    \<Longrightarrow> ttsplit_bang_inner K (Some TSK_S # sps) (Some \<gamma> # \<Gamma>b) (Some \<gamma> # \<Gamma>1) (Some \<gamma> # \<Gamma>2)"
  "K \<turnstile> \<gamma> :\<kappa>  k \<Longrightarrow> \<gamma>' = bang \<gamma> \<Longrightarrow> ttsplit_bang_inner K sps \<Gamma>b \<Gamma>1 \<Gamma>2
    \<Longrightarrow> ttsplit_bang_inner K (Some TSK_NS # sps) (Some \<gamma> # \<Gamma>b) (Some \<gamma>' # \<Gamma>1) (Some \<gamma> # \<Gamma>2)"
  "ttsplit_bang_inner K [] [] [] []"
  by (auto simp add: ttsplit_bang_inner_def forall_less_Suc_eq ttsplit_bang_inner_comp.simps)

lemma Suc_mem_image_pred:
  "0 \<notin> js \<Longrightarrow> (Suc n \<in> js) = (n \<in> pred ` js)"
  apply (simp add: image_def pred_def)
  apply (auto elim: rev_bexI split: nat.split_asm)
  done

lemma Suc_mem_image_pred_remove:
  "(n \<in> pred ` Set.remove 0 js) = (Suc n \<in> js)"
  by (simp add: Suc_mem_image_pred[symmetric])

lemma split_bang_nth:
  "split_bang K is \<Gamma> \<Gamma>1 \<Gamma>2 = (length \<Gamma>1 = length \<Gamma> \<and> length \<Gamma>2 = length \<Gamma>
        \<and> (\<forall>i < length \<Gamma>. K , i \<in> is \<turnstile> \<Gamma> ! i \<leadsto>b \<Gamma>1 ! i \<parallel> \<Gamma>2 ! i))"
proof (induct \<Gamma> arbitrary: "is" \<Gamma>1 \<Gamma>2)
  case (Cons a \<Gamma>)
  then show ?case
    apply -
    apply (intro iffI)

     apply (clarsimp simp add: split_bang_Cons1)
     apply (case_tac i; fastforce simp add: Suc_mem_image_pred_remove)

    apply (clarsimp simp add: split_bang_Cons1 Suc_mem_image_pred_remove length_Suc_conv All_less_Suc2)

    done
qed (fastforce elim: split_bang.cases intro: split_bang_nil)

lemma split_bang_nth_old:
  "split_bang K is \<Gamma> \<Gamma>1 \<Gamma>2 = (length \<Gamma>1 = length \<Gamma> \<and> length \<Gamma>2 = length \<Gamma>
        \<and> (\<forall>i < length \<Gamma>. if i \<in> is then \<Gamma>2 ! i = \<Gamma> ! i \<and> \<Gamma> ! i \<noteq> None
                \<and> \<Gamma>1 ! i = map_option bang (\<Gamma> ! i)
            else split_comp K (\<Gamma> ! i) (\<Gamma>1 ! i) (\<Gamma>2 ! i)))"
  apply (clarsimp simp add: split_bang_nth)
  apply (rule iffI)
   apply (force elim!: split_bang_comp.cases)
  apply clarsimp
  apply (case_tac "i \<in> is")
   apply (drule_tac x=i in spec)
   apply (force intro!: split_bang_comp.intros)+
  done

lemma ttsplit_bang_imp_split_bang:
  "ttsplit_bang is sps K \<Gamma> xs \<Gamma>1 ys \<Gamma>2 \<Longrightarrow>
    (\<exists>\<Gamma>1a \<Gamma>2a. split_bang K is (snd \<Gamma>) \<Gamma>1a \<Gamma>2a
        \<and> snd \<Gamma>1 = xs @ \<Gamma>1a \<and> snd \<Gamma>2 = ys @ \<Gamma>2a)"
  apply (clarsimp simp: ttsplit_bang_def ttsplit_inner_def split_bang_nth nth_enumerate_eq)
  apply (clarsimp simp add: ttsplit_bang_inner_conv_all_nth)
  apply (drule_tac x=i in spec)+
  apply (case_tac "sps ! i" rule: type_split_kind_option_exhaust)
     apply (clarsimp simp add: split_bang_comp.simps split_comp.simps ttsplit_bang_inner_comp.simps,
      (meson option.exhaust)?)+ 
  done

lemma split_bang_comp_imp_ttsplit_bang_inner_comp:
  assumes "K , 0 \<in> is \<turnstile> x \<leadsto>b a \<parallel> b"
  shows "\<exists>sp. ttsplit_bang_inner_comp K sp x a b \<and> (0 \<in> is) = (sp = Some TSK_NS)"
  using assms
  by (fastforce elim!: split_bang_comp.cases split_comp.cases simp add: ttsplit_bang_inner_comp.simps)

lemma split_bang_imp_ttsplit:
  "split_bang K is \<Gamma> \<Gamma>1 \<Gamma>2
    \<Longrightarrow> \<exists>sps. \<forall>xs ys \<Gamma>1' \<Gamma>2'. (\<Gamma>1' = xs @ \<Gamma>1 \<longrightarrow> \<Gamma>2' = ys @ \<Gamma>2
    \<longrightarrow> ttsplit_bang is sps K (TyTrSplit sps xs tt ys tt2, \<Gamma>) xs
        (tt, \<Gamma>1') ys (tt2, \<Gamma>2'))"
proof (induct rule: split_bang.induct)
  case split_bang_cons then show ?case
    by (fastforce
        simp add: All_less_Suc2 Suc_length_conv ttsplit_bang_def ttsplit_bang_inner_Cons2
        Suc_mem_image_pred_remove
        dest: split_bang_comp_imp_ttsplit_bang_inner_comp)
qed (clarsimp simp add: ttsplit_bang_def ttsplit_bang_inner_nil)

lemma split_follow_typing_tree:
  "ttsplit K \<Gamma> sps' xs' \<Gamma>1 ys' \<Gamma>2 \<Longrightarrow> (\<Gamma>1, \<Gamma>2) = follow_typing_tree \<Gamma> \<and> new_tt_types \<Gamma> = ys'"
  "ttsplit_triv \<Gamma> xs' \<Gamma>1 ys' \<Gamma>2 \<Longrightarrow> (\<Gamma>1, \<Gamma>2) = follow_typing_tree_triv \<Gamma> \<and> new_tt_types \<Gamma> = ys'"
  "ttsplit_bang is sps' K \<Gamma> xs' \<Gamma>1 ys' \<Gamma>2 \<Longrightarrow> (\<Gamma>1, \<Gamma>2) = follow_typing_tree \<Gamma> \<and> new_tt_types \<Gamma> = ys'"
    apply (clarsimp simp: ttsplit_def ttsplit_inner_conv_all_nth)
    apply (fastforce
      simp add: list_eq_iff_nth_eq ttsplit_inner_comp.simps
      elim: type_split_kind_option_exhaust)
   apply (cases \<Gamma>, clarsimp simp: ttsplit_triv_def)
  apply (clarsimp simp add: ttsplit_bang_def ball_conj_distrib[symmetric] ttsplit_bang_inner_conv_all_nth)
  apply (fastforce
      simp add: list_eq_iff_nth_eq ttsplit_bang_inner_comp.simps
      elim: type_split_kind_option_exhaust)
  done

inductive ttyping :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> tree_ctx \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> bool" 
          ("_, _, _ T\<turnstile> _ : _" [30,0,0,0,20] 60)
where

  ttyping_default: "\<lbrakk> \<not> composite_anormal_expr x
                    ; \<Xi>, K, \<Gamma> \<turnstile> x : t
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, (tt, \<Gamma>) T\<turnstile> x : t"

| ttyping_split  : "\<lbrakk> ttsplit K \<Gamma> ijs [] \<Gamma>1 [Some t, Some u] \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 T\<turnstile> x : TProduct t u
                   ; \<Xi>, K, \<Gamma>2 T\<turnstile> y : t'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Split x y : t'" 

| ttyping_let    : "\<lbrakk> ttsplit K \<Gamma> ijs [] \<Gamma>1 [Some t] \<Gamma>2 
                   ; \<Xi>, K, \<Gamma>1 T\<turnstile> x : t
                   ; \<Xi>, K, \<Gamma>2 T\<turnstile> y : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Let x y : u"

| ttyping_letb   : "\<lbrakk> ttsplit_bang is sps K \<Gamma> [] \<Gamma>1 [Some t] \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 T\<turnstile> x : t
                   ; \<Xi>, K, \<Gamma>2 T\<turnstile> y : u
                   ; K \<turnstile> t :\<kappa> k
                   ; E \<in> k
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> LetBang is x y : u"

| ttyping_case   : "\<lbrakk> ttsplit K \<Gamma> ijs [] \<Gamma>1 [] \<Gamma>2
                   ; ttsplit_triv \<Gamma>2 [Some t] \<Gamma>3 [Some (TSum (filter (\<lambda> x. fst x \<noteq> tag) ts))] \<Gamma>4
                   ; \<Xi>, K, \<Gamma>1 T\<turnstile> x : TSum ts
                   ; (tag, t) \<in> set ts
                   ; \<Xi>, K, \<Gamma>3 T\<turnstile> a : u
                   ; \<Xi>, K, \<Gamma>4 T\<turnstile> b : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Case x tag a b : u" 

| ttyping_if     : "\<lbrakk> ttsplit K \<Gamma> ijs [] \<Gamma>1 [] \<Gamma>2
                   ; ttsplit_triv \<Gamma>2 [] \<Gamma>3 [] \<Gamma>4
                   ; \<Xi>, K, \<Gamma>1 T\<turnstile> x : TPrim Bool
                   ; \<Xi>, K, \<Gamma>3 T\<turnstile> a : t
                   ; \<Xi>, K, \<Gamma>4 T\<turnstile> b : t
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> If x a b : t"

| ttyping_take   : "\<lbrakk> ttsplit K \<Gamma> ijs [] \<Gamma>1 [Some t, Some (TRecord (ts [f := (t, taken)]) s)] \<Gamma>2 
                   ; \<Xi>, K, \<Gamma>1 T\<turnstile> e : TRecord ts s
                   ; s \<noteq> ReadOnly
                   ; f < length ts
                   ; ts ! f = (t, False)
                   ; K \<turnstile> t :\<kappa> k
                   ; S \<in> k \<or> taken
                   ; \<Xi>, K, \<Gamma>2 T\<turnstile> e' : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Take e f e' : u"


lemma ttyping_imp_typing:
assumes "\<Xi>, K, \<Gamma> T\<turnstile> e : u"
shows   "\<Xi>, K, (snd \<Gamma>) \<turnstile> e : u"
using assms by ( induct rule: ttyping.induct
               , auto simp:  ttsplit_triv_def
                      dest!: ttsplit_imp_split ttsplit_bang_imp_split_bang
                      intro: typing_typing_all.intros)

lemma typing_imp_ttyping_induct:
shows " (\<Xi>, K, \<Gamma> \<turnstile> e : u \<Longrightarrow> (\<exists> tt. \<Xi>, K, (tt, \<Gamma>) T\<turnstile> e : u))"
and   " (\<Xi>, K, \<Gamma> \<turnstile>* es : us \<Longrightarrow> True)"
proof (induct rule: typing_typing_all.inducts)
  
qed (fastforce intro: ttyping_split[rotated] ttyping_let[rotated] ttyping_letb[rotated]
                      ttyping_case[rotated 2] ttyping_if[rotated 2] ttyping_take[rotated 2]
                      ttyping_default typing_typing_all.intros
            simp: composite_anormal_expr_def ttsplit_triv_def
            elim: split_imp_ttsplit
    | metis split_bang_imp_ttsplit ttyping_letb append.simps)+


lemma ttyping_eq_typing:
shows "\<Xi>, K, \<Gamma> \<turnstile> e : u = (\<exists> tt. \<Xi>, K, (tt, \<Gamma>) T\<turnstile> e : u)"
by (auto dest: ttyping_imp_typing typing_imp_ttyping_induct)


lemma split_type_wellformed:
  "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2 \<Longrightarrow> Some t \<in> set \<Gamma>
    \<Longrightarrow> K \<turnstile>  t wellformed"
  by (induct rule: split_inducts, auto elim!: split_comp.cases)

lemma split_bang_type_wellformed:
  "split_bang K is \<Gamma> \<Gamma>1 \<Gamma>2 \<Longrightarrow> Some t \<in> set \<Gamma>
    \<Longrightarrow> Some t \<in> set \<Gamma>1 \<or> Some t \<in> set \<Gamma>2 \<or> K \<turnstile>  t wellformed"
  by (induct arbitrary: "is" rule: split_bang.induct,
    auto elim!: split_bang_comp.cases split_comp.cases)

lemma weakening_type_wellformed:
  "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>' \<Longrightarrow> Some t \<in> set \<Gamma>
    \<Longrightarrow> K \<turnstile>  t wellformed"
  apply (clarsimp simp: weakening_def in_set_conv_decomp
                        list_all2_append1 list_all2_Cons1)
  apply (erule weakening_comp.cases, auto)
  done

lemma typing_to_kinding_env:
  "\<Xi>, K, \<Gamma> \<turnstile> e : u \<Longrightarrow> Some t \<in> set \<Gamma>
    \<Longrightarrow> K \<turnstile>  t wellformed"
  "\<Xi>, K, \<Gamma> \<turnstile>* es : us \<Longrightarrow> Some t \<in> set \<Gamma>
    \<Longrightarrow> K \<turnstile>  t wellformed"
  by (induct rule: typing_typing_all.inducts,
    auto simp add: Cogent.empty_def
      dest: split_bang_type_wellformed weakening_type_wellformed split_type_wellformed)

lemma ttyping_type_wellformed:
  "\<lbrakk> \<Xi>, K, \<Gamma> T\<turnstile> x : \<tau> \<rbrakk>
    \<Longrightarrow> \<forall>t. Some t \<in> set (snd \<Gamma>) \<longrightarrow> K \<turnstile>  t wellformed"
  by (induct rule: ttyping.induct,
    auto dest!: ttsplit_imp_split ttsplit_bang_imp_split_bang
      dest: split_bang_type_wellformed split_type_wellformed typing_to_kinding_env)


end

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

theory TypeTrackingTyping
  imports Cogent
begin

text \<open>TypeTrackingTyping are a rewrite of some Cogent typing rules to handle splitting
  deterministically.

  The Cogent verification process starts with the compiler handing us several expressions, and
  their typings. Our goal is to prove these typings are correct. The typing rules in `Cogent.thy`,
  while an adequate specification of a correct typing, do not give us a very good way to
  deterministically prove such a typing. The issue is that you can't tell how the contexts should
  split when doing backwards reasoning; moreover, the number of possible splittings is exponential.
\<close>

datatype type_split_op =
  TSK_R    \<comment>\<open> Split Right \<close>
  | TSK_L  \<comment>\<open> Split Left  \<close>
  | TSK_S  \<comment>\<open> Split Share \<close>
  | TSK_NS \<comment>\<open> Split Bang  \<close>

(* TODO this should be stronger than this. Whenever a type is None, the splitting should be None
  too. We can enforce this with a `(type, type_split_op) option list`, but that would be too big of
  a rewrite for now.

  n.b. This may be not a good idea, even if we have more time, because then converting between
  ttyping and typing would become harder.
*)
datatype typing_tree =
  TyTrLeaf
  | TyTrSplit "type_split_op option list" ctx typing_tree ctx typing_tree

type_synonym tree_ctx = "typing_tree * ctx"

fun apply_tsk :: "type_split_op option \<Rightarrow> type option \<Rightarrow> type option \<times> type option" where
    "apply_tsk (Some TSK_R)  t = (None, t)"
  | "apply_tsk (Some TSK_L)  t = (t, None)"
  | "apply_tsk (Some TSK_S)  t = (t, t)"
  | "apply_tsk (Some TSK_NS) t = (map_option bang t, t)"
  | "apply_tsk None None       = (None, None)"

fun split_tsk :: "type option \<Rightarrow> type option \<Rightarrow> type_split_op option" where
    "split_tsk (Some _) (Some _) = Some TSK_S"
  | "split_tsk None (Some _) = Some TSK_R"
  | "split_tsk (Some _) None = Some TSK_L"
  | "split_tsk None None = None"

fun split_bang_tsk :: "bool \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> type_split_op option" where
    "split_bang_tsk True (Some _) (Some _) = Some TSK_NS"
  | "split_bang_tsk False t1 t2 = split_tsk t1 t2"

lemma split_tsk_never_ns: "split_tsk t1 t2 \<noteq> Some TSK_NS"
  using split_tsk.elims by auto

lemma split_tsk_ns_imp_b: "split_bang_tsk b t1 t2 = Some TSK_NS \<Longrightarrow> b"
  by (metis (full_types) split_bang_tsk.simps(2) split_tsk_never_ns)

lemma split_comp_by_split_tsk:
  assumes
    "i < length \<Gamma>"
    "L, K, C \<turnstile> \<Gamma> ! i \<leadsto> \<Gamma>1 ! i \<parallel> \<Gamma>2 ! i"
  shows
    "(split_tsk (\<Gamma>1 ! i) (\<Gamma>2 ! i) = None) = (\<Gamma> ! i = None)"
    "split_tsk (\<Gamma>1 ! i) (\<Gamma>2 ! i) = Some TSK_L \<longrightarrow> (\<exists>t. \<Gamma> ! i = Some t \<and> type_wellformed L (length K) C t)"
    "split_tsk (\<Gamma>1 ! i) (\<Gamma>2 ! i) = Some TSK_R \<longrightarrow> (\<exists>t. \<Gamma> ! i = Some t \<and> type_wellformed L (length K) C t)"
    "split_tsk (\<Gamma>1 ! i) (\<Gamma>2 ! i) = Some TSK_S \<longrightarrow> (\<exists>t. \<Gamma> ! i = Some t \<and> L, K, C \<turnstile> t :\<kappa> {S})"
  using assms
  by (auto elim!: split_comp.cases simp: kinding_def)

lemma split_bang_comp_by_split_bang_tsk:
  assumes
    "i < length \<Gamma>"
    "L, K, C, i \<in> is \<turnstile> \<Gamma> ! i \<leadsto>b \<Gamma>1 ! i \<parallel> \<Gamma>2 ! i"
  shows
    "(split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i) = None) = (\<Gamma> ! i = None)"
    "split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i) = Some TSK_L \<Longrightarrow> (\<exists>t. \<Gamma> ! i = Some t \<and> type_wellformed L (length K) C t)"
    "split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i) = Some TSK_R \<Longrightarrow> (\<exists>t. \<Gamma> ! i = Some t \<and> type_wellformed L (length K) C t)"
    "split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i) = Some TSK_NS \<Longrightarrow> (\<exists>t. \<Gamma> ! i = Some t \<and> type_wellformed L (length K) C t)"
    "split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i) = Some TSK_S \<Longrightarrow> (\<exists>t. \<Gamma> ! i = Some t \<and> L, K, C \<turnstile> t :\<kappa> {S})"
  using assms
  by (auto elim!: split_bang_comp.cases split_comp.cases simp: kinding_def)

lemma split_bang_comp_with_true_forces_ns:
  assumes
    "i < length \<Gamma>"
    "L, K , C, True \<turnstile> \<Gamma> ! i \<leadsto>b \<Gamma>1 ! i \<parallel> \<Gamma>2 ! i"
  shows
    "split_bang_tsk True (\<Gamma>1 ! i) (\<Gamma>2 ! i) = Some TSK_NS"
  using assms
  by (auto elim!: split_bang_comp.cases split_comp.cases simp: kinding_def)

lemma split_bang_imp_\<Gamma>1_\<Gamma>2_are:
  assumes
    "L, K, C , is \<turnstile> \<Gamma> \<leadsto>b \<Gamma>1 | \<Gamma>2"
  shows
    "\<Gamma>1 =
    List.map2 (\<lambda>x y. if x = Some TSK_L \<or> x = Some TSK_S then y else if x = Some TSK_NS then map_option bang y else None)
     (map (\<lambda>i. split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i)) [0..<length \<Gamma>]) \<Gamma>"
    "\<Gamma>2 =
    List.map2 (\<lambda>x y. if x = Some TSK_R \<or> x = Some TSK_S \<or> x = Some TSK_NS then y else None)
     (map (\<lambda>i. split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i)) [0..<length \<Gamma>]) \<Gamma>"
  using assms
proof (induct rule: split_bang.inducts)
  case (split_bang_cons L K C "is" xs as bs x a b)
  let ?orig = "(map (\<lambda>i. split_bang_tsk (i \<in> is) ((a # as) ! i) ((b # bs) ! i)) [0..<length (x # xs)])"
  let ?new = "split_bang_tsk (0 \<in> is) a b # (map (\<lambda>i. split_bang_tsk (i \<in> pred ` Set.remove 0 is) (as ! i) (bs ! i)) [0..<length xs])"
  have f1: "?orig = ?new"
    by (clarsimp simp del: upt_Suc simp add: map_upt_Suc Suc_mem_image_pred_remove)
  
  show "a # as =
       List.map2 (\<lambda>x y. if x = Some TSK_L \<or> x = Some TSK_S then y else if x = Some TSK_NS then map_option bang y else None)
        (map (\<lambda>i. split_bang_tsk (i \<in> is) ((a # as) ! i) ((b # bs) ! i)) [0..<length (x # xs)]) (x # xs)"
    using split_bang_cons f1
    by (fastforce elim!: split_bang_comp.cases split_comp.cases)
  show "b # bs =
       List.map2 (\<lambda>x y. if x = Some TSK_R \<or> x = Some TSK_S \<or> x = Some TSK_NS then y else None)
        (map (\<lambda>i. split_bang_tsk (i \<in> is) ((a # as) ! i) ((b # bs) ! i)) [0..<length (x # xs)]) (x # xs)"
    using split_bang_cons f1
    by (fastforce elim!: split_bang_comp.cases split_comp.cases)
qed simp+


fun
  follow_typing_tree :: "tree_ctx \<Rightarrow> tree_ctx \<times> tree_ctx"
where
  "follow_typing_tree (TyTrSplit sps xs T1 ys T2, \<Gamma>)
    = (let split\<Gamma> = List.map2 apply_tsk sps \<Gamma>
       in ((T1, xs @ map fst split\<Gamma>), (T2, ys @ map snd split\<Gamma>)))"

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

definition ttsplit_inner :: "lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> type_split_op option list \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool"
where
  "ttsplit_inner L K C sps \<Gamma>a \<Gamma>1a \<Gamma>2a = (
          length sps = length \<Gamma>a
        \<and> \<Gamma>1a = List.map2 (\<lambda>sp v. (if sp \<in> {Some TSK_L, Some TSK_S} then v
                                      else if sp = Some TSK_NS then map_option bang v
                                      else None))
                            sps \<Gamma>a
        \<and> \<Gamma>2a = List.map2 (\<lambda>sp v. if sp \<in> {Some TSK_R, Some TSK_S, Some TSK_NS} then v
                                     else None)
                            sps \<Gamma>a
        \<and> (\<forall>i < length \<Gamma>a. sps ! i = None \<longleftrightarrow> \<Gamma>a ! i = None)
        \<and> (\<forall>i < length \<Gamma>a. sps ! i \<in> {Some TSK_L, Some TSK_R, Some TSK_NS} \<longrightarrow> (\<exists>t. \<Gamma>a ! i = Some t \<and> L, K, C \<turnstile> t wellformed))
        \<and> (\<forall>i < length \<Gamma>a. sps ! i = Some TSK_S \<longrightarrow> (\<exists>t. \<Gamma>a ! i = Some t \<and> (L, K, C \<turnstile> t :\<kappa> {S}))))"

definition ttsplit :: "lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> tree_ctx \<Rightarrow> type_split_op option list
        \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> bool"
where
  "ttsplit L K C \<Gamma> sps xs \<Gamma>1 ys \<Gamma>2 =
    (\<exists>\<Gamma>a \<Gamma>1a \<Gamma>2a T1 T2. \<Gamma> = (TyTrSplit sps xs T1 ys T2, \<Gamma>a)
        \<and> \<Gamma>1 = (T1, xs @ \<Gamma>1a)
        \<and> \<Gamma>2 = (T2, ys @ \<Gamma>2a)
        \<and> (\<forall>i < length sps. sps ! i \<noteq> Some TSK_NS)
        \<and> ttsplit_inner L K C sps \<Gamma>a \<Gamma>1a \<Gamma>2a)"

lemma ttsplitI:
  assumes
    "ttsplit_inner L K C sps \<Gamma>a \<Gamma>1a \<Gamma>2a"
    "xs' = xs @ \<Gamma>1a"
    "ys' = ys @ \<Gamma>2a"
    "list_all ((\<noteq>) (Some TSK_NS)) sps"
  shows "ttsplit L K C (TyTrSplit sps xs T1 ys T2, \<Gamma>a) sps xs (T1, xs') ys (T2, ys')"
  using assms
  by (force simp add: ttsplit_def list_all_length)

lemma ttsplit_innerI:
  "ttsplit_inner L K C sps \<Gamma>a \<Gamma>1a \<Gamma>2a
    \<Longrightarrow> ttsplit_inner L K C (None # sps) (None # \<Gamma>a) (None # \<Gamma>1a) (None # \<Gamma>2a)"
  "\<lbrakk> L, K, C \<turnstile> t wellformed ; ttsplit_inner L K C sps \<Gamma>a \<Gamma>1a \<Gamma>2a \<rbrakk>
    \<Longrightarrow> ttsplit_inner L K C (Some TSK_R # sps) (Some t # \<Gamma>a) (None # \<Gamma>1a) (Some t # \<Gamma>2a)"
  "\<lbrakk> L, K, C \<turnstile> t wellformed ; ttsplit_inner L K C sps \<Gamma>a \<Gamma>1a \<Gamma>2a \<rbrakk>
    \<Longrightarrow> ttsplit_inner L K C (Some TSK_L # sps) (Some t # \<Gamma>a) (Some t # \<Gamma>1a) (None # \<Gamma>2a)"
  "\<lbrakk> L, K, C \<turnstile> t :\<kappa> k; S \<in> k; ttsplit_inner L K C sps \<Gamma>a \<Gamma>1a \<Gamma>2a \<rbrakk>
    \<Longrightarrow> ttsplit_inner L K C (Some TSK_S # sps) (Some t # \<Gamma>a) (Some t # \<Gamma>1a) (Some t # \<Gamma>2a)"
  "\<lbrakk> L, K, C \<turnstile> t wellformed ; ttsplit_inner L K C sps \<Gamma>a \<Gamma>1a \<Gamma>2a \<rbrakk>
    \<Longrightarrow> ttsplit_inner L K C (Some TSK_NS # sps) (Some t # \<Gamma>a) (Some (bang t) # \<Gamma>1a) (Some t # \<Gamma>2a)"
  "ttsplit_inner L K C [] [] [] []"
  by (fastforce simp add: kinding_def ttsplit_inner_def All_less_Suc2)+

lemma ttsplit_imp_split:
  assumes
    "ttsplit L K C \<Gamma> sps xs \<Gamma>1 ys \<Gamma>2"
  shows "\<exists>\<Gamma>1a \<Gamma>2a. split L K C (snd \<Gamma>) \<Gamma>1a \<Gamma>2a \<and> snd \<Gamma>1 = xs @ \<Gamma>1a \<and> snd \<Gamma>2 = ys @ \<Gamma>2a"
  using assms
  apply (clarsimp simp: ttsplit_def ttsplit_inner_def split_def list_all3_conv_all_nth)
  apply (case_tac "sps ! i")
   apply (force simp add: split_comp.simps)
  apply (rename_tac s)
  apply (case_tac s)
     apply (fastforce simp add: kinding_def split_comp.simps)+
  done

lemma split_imp_ttsplit:
  assumes
    "split L K C \<Gamma> \<Gamma>1 \<Gamma>2"
    "sps = map (\<lambda>i. split_tsk (\<Gamma>1 ! i) (\<Gamma>2 ! i)) [0 ..< length \<Gamma>]"
    "\<Gamma>1' = xs @ \<Gamma>1"
    "\<Gamma>2' = ys @ \<Gamma>2"
  shows "ttsplit L K C (TyTrSplit sps xs tt ys tt2, \<Gamma>) sps xs (tt, \<Gamma>1') ys (tt2, \<Gamma>2')"
  using assms
  apply (clarsimp simp: ttsplit_def ttsplit_inner_def split_def list_all3_conv_all_nth image_def)
  apply (subst (0 1) list_eq_iff_nth_eq)
  apply (fastforce simp add: kinding_def split_comp.simps in_set_conv_nth)
  done

definition ttsplit_triv :: "tree_ctx \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> bool"
where
  "ttsplit_triv \<Gamma> xs \<Gamma>1 ys \<Gamma>2 = (\<exists>ijs \<Gamma>1a \<Gamma>2a.
    fst \<Gamma> = TyTrSplit ijs xs \<Gamma>1a ys \<Gamma>2a \<and> \<Gamma>1 = (\<Gamma>1a, xs @ snd \<Gamma>) \<and> \<Gamma>2 = (\<Gamma>2a, ys @ snd \<Gamma>))"

lemma ttsplit_trivI:
  "\<Gamma>1b = (\<Gamma>1a, xs @ \<Gamma>b) \<Longrightarrow> \<Gamma>2b = (\<Gamma>2a, ys @ \<Gamma>b) \<Longrightarrow> ttsplit_triv (TyTrSplit ijs xs \<Gamma>1a ys \<Gamma>2a, \<Gamma>b) xs \<Gamma>1b ys \<Gamma>2b"
  by (simp add: ttsplit_triv_def)

(* TODO args are in a different order to ttsplit *)
definition
  "ttsplit_bang is sps L K C \<Gamma> xs \<Gamma>1 ys \<Gamma>2 =
    (\<exists>\<Gamma>b \<Gamma>1a \<Gamma>2a T1 T2. \<Gamma> = (TyTrSplit sps xs T1 ys T2, \<Gamma>b)
        \<and> ttsplit_inner L K C sps \<Gamma>b \<Gamma>1a \<Gamma>2a
        \<and> (\<forall>i < length \<Gamma>b. (i \<in> is) = (sps ! i = Some TSK_NS))
        \<and> \<Gamma>1 = (T1, xs @ \<Gamma>1a)
        \<and> \<Gamma>2 = (T2, ys @ \<Gamma>2a))"

lemma ttsplit_bangI:
  assumes
    "xs' = xs @ \<Gamma>1a"
    "ys' = ys @ \<Gamma>2a"
    "is = set (map fst (filter (\<lambda>(i, v). v = Some TSK_NS) (enumerate 0 sps)))"
    "ttsplit_inner L K C sps \<Gamma>b \<Gamma>1a \<Gamma>2a"
  shows "ttsplit_bang is sps L K C (TyTrSplit sps xs T1 ys T2, \<Gamma>b) xs (T1, xs') ys (T2, ys')"
  using assms
  by (simp add: ttsplit_bang_def ttsplit_inner_def in_set_enumerate_eq image_def)


lemma ttsplit_bang_imp_split_bang:
  "ttsplit_bang is sps L K C \<Gamma> xs \<Gamma>1 ys \<Gamma>2 \<Longrightarrow>
    (\<exists>\<Gamma>1a \<Gamma>2a. split_bang L K C is (snd \<Gamma>) \<Gamma>1a \<Gamma>2a
        \<and> snd \<Gamma>1 = xs @ \<Gamma>1a \<and> snd \<Gamma>2 = ys @ \<Gamma>2a)"
  apply (clarsimp simp: ttsplit_bang_def ttsplit_inner_def split_bang_nth nth_enumerate_eq)
  apply (case_tac "sps ! i")
   apply (clarsimp simp add: split_bang_comp.simps split_comp.simps kinding_def)
  apply (case_tac a)
     apply (clarsimp simp add: split_bang_comp.simps split_comp.simps)
    apply (clarsimp simp add: split_bang_comp.simps split_comp.simps)
   apply (force simp add: split_bang_comp.simps split_comp.simps)
  apply (clarsimp simp add: split_bang_comp.simps split_comp.simps, blast) 
  done

lemma ttsplit_bang_inner_Cons:
  "ttsplit_inner L K C sps \<Gamma>b \<Gamma>1 \<Gamma>2
    \<Longrightarrow> ttsplit_inner L K C [sp] [\<gamma>] [\<gamma>1] [\<gamma>2]
    \<Longrightarrow> ttsplit_inner L K C (sp # sps) (\<gamma> # \<Gamma>b) (\<gamma>1 # \<Gamma>1) (\<gamma>2 # \<Gamma>2)"
  by (simp add: ttsplit_inner_def All_less_Suc2)

lemma split_bang_imp_ttsplit_bang:
  assumes
    "L, K, C , is \<turnstile> \<Gamma> \<leadsto>b \<Gamma>1 | \<Gamma>2"
    "sps = map (\<lambda>i. split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i)) [0 ..< length \<Gamma>]"
    "\<Gamma>1' = xs @ \<Gamma>1"
    "\<Gamma>2' = ys @ \<Gamma>2"
  shows "ttsplit_bang is sps L K C (TyTrSplit sps xs tt ys tt2, \<Gamma>) xs (tt, \<Gamma>1') ys (tt2, \<Gamma>2')"
proof -
  show ?thesis
    using assms
    unfolding ttsplit_bang_def ttsplit_inner_def
    using split_bang_imp_\<Gamma>1_\<Gamma>2_are split_bang_comp_by_split_bang_tsk
      split_bang_comp_with_true_forces_ns
    by (auto simp add: split_bang_nth dest: split_tsk_ns_imp_b)
qed

lemma split_bang_imp_ttsplit:
  "split_bang L K C is \<Gamma> \<Gamma>1 \<Gamma>2
    \<Longrightarrow> \<exists>sps. \<forall>xs ys \<Gamma>1' \<Gamma>2'. (\<Gamma>1' = xs @ \<Gamma>1 \<longrightarrow> \<Gamma>2' = ys @ \<Gamma>2
    \<longrightarrow> ttsplit_bang is sps L K C (TyTrSplit sps xs tt ys tt2, \<Gamma>) xs
        (tt, \<Gamma>1') ys (tt2, \<Gamma>2'))"
proof (clarsimp simp: ttsplit_bang_def, induct rule: split_bang.induct)
  case (split_bang_cons L K C "is" xs as bs x a b)
  then show ?case
    apply (clarsimp simp: All_less_Suc2 Suc_mem_image_pred)
    apply (rule exI, rule conjI, erule_tac sp="split_bang_tsk (0 \<in> is) a b" in ttsplit_bang_inner_Cons)
     apply (elim split_bang_comp.cases split_comp.cases; force simp add: ttsplit_inner_def kinding_def)
    apply (elim split_bang_comp.cases split_comp.cases; simp add: Suc_mem_image_pred_remove)
    done
qed (simp add: ttsplit_bang_def ttsplit_inner_def)

lemma split_follow_typing_tree:
  "ttsplit L K C \<Gamma> sps' xs' \<Gamma>1 ys' \<Gamma>2 \<Longrightarrow> (\<Gamma>1, \<Gamma>2) = follow_typing_tree \<Gamma> \<and> new_tt_types \<Gamma> = ys'"
  "ttsplit_triv \<Gamma> xs' \<Gamma>1 ys' \<Gamma>2 \<Longrightarrow> (\<Gamma>1, \<Gamma>2) = follow_typing_tree_triv \<Gamma> \<and> new_tt_types \<Gamma> = ys'"
  "ttsplit_bang is sps' L K C \<Gamma> xs' \<Gamma>1 ys' \<Gamma>2 \<Longrightarrow> (\<Gamma>1, \<Gamma>2) = follow_typing_tree \<Gamma> \<and> new_tt_types \<Gamma> = ys'"
    apply (clarsimp simp: ttsplit_def ttsplit_inner_def ball_conj_distrib[symmetric])
    apply (clarsimp elim!: in_set_zipE simp add: in_set_conv_nth)
    apply (case_tac "sps' ! i")
     apply auto[1]
    apply (case_tac a; clarsimp)
   apply (cases \<Gamma>, clarsimp simp: ttsplit_triv_def)
  apply (clarsimp simp: ttsplit_bang_def ttsplit_inner_def ball_conj_distrib[symmetric])
  apply (clarsimp elim!: in_set_zipE simp add: in_set_conv_nth)
  apply (case_tac "sps' ! i")
   apply auto[1]
  apply (case_tac a; clarsimp)
  done

inductive ttyping :: "('f \<Rightarrow> poly_type) \<Rightarrow> lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> tree_ctx \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> bool"
          ("_, _, _, _, _ T\<turnstile> _ : _" [30,0,0,0,0,0,20] 60)
where

  ttyping_default: "\<lbrakk> \<not> composite_anormal_expr x
                    ; \<Xi>, L, K, C, \<Gamma> \<turnstile> x : t
                    \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, (tt, \<Gamma>) T\<turnstile> x : t"

| ttyping_split  : "\<lbrakk> ttsplit L K C \<Gamma> ijs [] \<Gamma>1 [Some t, Some u] \<Gamma>2
                   ; \<Xi>, L, K, C, \<Gamma>1 T\<turnstile> x : TProduct t u
                   ; \<Xi>, L, K, C, \<Gamma>2 T\<turnstile> y : t'
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> T\<turnstile> Split x y : t'"

| ttyping_let    : "\<lbrakk> ttsplit L K C \<Gamma> ijs [] \<Gamma>1 [Some t] \<Gamma>2
                   ; \<Xi>, L, K, C, \<Gamma>1 T\<turnstile> x : t
                   ; \<Xi>, L, K, C, \<Gamma>2 T\<turnstile> y : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> T\<turnstile> Let x y : u"

| ttyping_letb   : "\<lbrakk> ttsplit_bang is sps L K C \<Gamma> [] \<Gamma>1 [Some t] \<Gamma>2
                   ; \<Xi>, L, K, C, \<Gamma>1 T\<turnstile> x : t
                   ; \<Xi>, L, K, C, \<Gamma>2 T\<turnstile> y : u
                   ; L, K, C \<turnstile> t :\<kappa> k
                   ; E \<in> k
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> T\<turnstile> LetBang is x y : u"

| ttyping_case   : "\<lbrakk> ttsplit L K C \<Gamma> ijs [] \<Gamma>1 [] \<Gamma>2
                   ; ttsplit_triv \<Gamma>2 [Some t] \<Gamma>3 [Some (TSum (tagged_list_update tag (t, Checked) ts))] \<Gamma>4
                   ; \<Xi>, L, K, C, \<Gamma>1 T\<turnstile> x : TSum ts
                   ; (tag, t, Unchecked) \<in> set ts
                   ; \<Xi>, L, K, C, \<Gamma>3 T\<turnstile> a : u
                   ; \<Xi>, L, K, C, \<Gamma>4 T\<turnstile> b : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> T\<turnstile> Case x tag a b : u"

| ttyping_if     : "\<lbrakk> ttsplit L K C \<Gamma> ijs [] \<Gamma>1 [] \<Gamma>2
                   ; ttsplit_triv \<Gamma>2 [] \<Gamma>3 [] \<Gamma>4
                   ; \<Xi>, L, K, C, \<Gamma>1 T\<turnstile> x : TPrim Bool
                   ; \<Xi>, L, K, C, \<Gamma>3 T\<turnstile> a : t
                   ; \<Xi>, L, K, C, \<Gamma>4 T\<turnstile> b : t
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> T\<turnstile> If x a b : t"

| ttyping_take   : "\<lbrakk> ttsplit L K C \<Gamma> ijs [] \<Gamma>1 [Some t, Some (TRecord (ts [f := (n, t, taken)]) s)] \<Gamma>2
                   ; \<Xi>, L, K, C, \<Gamma>1 T\<turnstile> e : TRecord ts s
                   ; sigil_perm s \<noteq> Some ReadOnly
                   ; f < length ts
                   ; ts ! f = (n, t, Present)
                   ; L, K, C \<turnstile> t :\<kappa> k
                   ; S \<in> k \<or> taken = Taken
                   ; \<Xi>, L, K, C, \<Gamma>2 T\<turnstile> e' : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> T\<turnstile> Take e f e' : u"

inductive_cases ttyping_splitE[elim]: "\<Xi>, L, K, C, \<Gamma> T\<turnstile> Split x y : t'"
inductive_cases ttyping_letE[elim]: "\<Xi>, L, K, C, \<Gamma> T\<turnstile> Let x y : u"
inductive_cases ttyping_letbE[elim]: "\<Xi>, L, K, C, \<Gamma> T\<turnstile> LetBang is x y : u"
inductive_cases ttyping_caseE[elim]: "\<Xi>, L, K, C, \<Gamma> T\<turnstile> Case x tag a b : u"
inductive_cases ttyping_ifE[elim]: "\<Xi>, L, K, C, \<Gamma> T\<turnstile> If x a b : t"
inductive_cases ttyping_takeE[elim]: "\<Xi>, L, K, C, \<Gamma> T\<turnstile> Take e f e' : u"

lemma ttyping_imp_typing:
assumes "\<Xi>, L, K, C, \<Gamma> T\<turnstile> e : u"
shows   "\<Xi>, L, K, C, (snd \<Gamma>) \<turnstile> e : u"
  using assms
proof (induct rule: ttyping.induct)
  case (ttyping_case L K C t\<Gamma> ijs t\<Gamma>1 t\<Gamma>2 t t\<Gamma>3 tag ts t\<Gamma>4 \<Xi> x a u b)
  then show ?case
  proof (intro typing_typing_all.intros)
    show "L, K, C \<turnstile> snd t\<Gamma> \<leadsto> snd t\<Gamma>1 | snd t\<Gamma>2"
      using ttsplit_imp_split ttyping_case.hyps(1) by fastforce
  next
    show "\<Xi>, L, K, C, Some t # snd t\<Gamma>2 \<turnstile> a : u"
      using ttsplit_triv_def ttyping_case.hyps(2,7) by auto
  next
    show "\<Xi>, L, K, C, Some (TSum (tagged_list_update tag (t, Checked) ts)) # snd t\<Gamma>2 \<turnstile> b : u"
      using ttsplit_triv_def ttyping_case.hyps(2,9) by auto
  qed simp+
qed (auto simp: ttsplit_triv_def
         dest!: ttsplit_imp_split ttsplit_bang_imp_split_bang
         intro: typing_typing_all.intros)

lemma typing_imp_ttyping_induct:
  shows "(\<Xi>, L, K, C, \<Gamma> \<turnstile> e : u \<Longrightarrow> (\<exists> tt. \<Xi>, L, K, C, (tt, \<Gamma>) T\<turnstile> e : u))"
    and "(\<Xi>, L, K, C, \<Gamma> \<turnstile>* es : us \<Longrightarrow> True)"
proof (induct rule: typing_typing_all.inducts)
  case (typing_letb L K C "is" \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t y u k)
  then obtain tt1 tt2
    where IH_ex_elims:
      "\<Xi>, L, K, C, (tt1, \<Gamma>1) T\<turnstile> x : t"
      "\<Xi>, L, K, C, (tt2, Some t # \<Gamma>2) T\<turnstile> y : u"
    by blast
  let ?sps = "map (\<lambda>i. split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i)) [0 ..< length \<Gamma>]"
  let ?tt = "TyTrSplit ?sps [] tt1 [Some t] tt2"
  have "ttsplit_bang is ?sps L K C (?tt, \<Gamma>) [] (tt1, \<Gamma>1) [Some t] (tt2, Some t # \<Gamma>2)"
    using typing_letb
    by (force dest: split_bang_imp_ttsplit_bang[where xs="[]" and ys="[Some t]"])
  then show ?case
    using typing_letb IH_ex_elims
    by (force intro: ttyping_letb)
qed (fastforce
        simp add: composite_anormal_expr_def ttsplit_triv_def
        intro: typing_typing_all.intros ttyping.intros split_imp_ttsplit)+

lemma ttyping_eq_typing:
shows "\<Xi>, L, K, C, \<Gamma> \<turnstile> e : u = (\<exists> tt. \<Xi>, L, K, C, (tt, \<Gamma>) T\<turnstile> e : u)"
by (auto dest: ttyping_imp_typing typing_imp_ttyping_induct)


lemma split_type_wellformed:
  "L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2 \<Longrightarrow> Some t \<in> set \<Gamma> \<Longrightarrow> L, K, C \<turnstile> t wellformed"
  by (auto simp add: split_def split_comp.simps in_set_conv_nth list_all3_conv_all_nth kinding_def)

lemma split_bang_type_wellformed:
  "split_bang L K C is \<Gamma> \<Gamma>1 \<Gamma>2 \<Longrightarrow> Some t \<in> set \<Gamma>
    \<Longrightarrow> Some t \<in> set \<Gamma>1 \<or> Some t \<in> set \<Gamma>2 \<or> L, K, C \<turnstile> t wellformed"
  apply (induct arbitrary: "is" rule: split_bang.induct)
   apply (auto elim!: split_bang_comp.cases split_comp.cases)
  done

lemma weakening_type_wellformed:
  "L, K, C \<turnstile> \<Gamma> \<leadsto>w \<Gamma>' \<Longrightarrow> Some t \<in> set \<Gamma> \<Longrightarrow> L, K, C \<turnstile> t wellformed"
  by (fastforce simp add: kinding_def weakening_def weakening_comp.simps in_set_conv_nth list_all2_conv_all_nth)

lemma typing_to_kinding_env:
  "\<Xi>, L, K, C, \<Gamma> \<turnstile> e : u \<Longrightarrow> Some t \<in> set \<Gamma>
    \<Longrightarrow> L, K, C \<turnstile> t wellformed"
  "\<Xi>, L, K, C, \<Gamma> \<turnstile>* es : us \<Longrightarrow> Some t \<in> set \<Gamma>
    \<Longrightarrow> L, K, C \<turnstile> t wellformed"
  by (induct rule: typing_typing_all.inducts,
    auto simp add: Cogent.empty_def
      dest: split_bang_type_wellformed weakening_type_wellformed split_type_wellformed)

lemma ttyping_type_wellformed:
  "\<lbrakk> \<Xi>, L, K, C, \<Gamma> T\<turnstile> x : \<tau> \<rbrakk>
    \<Longrightarrow> \<forall>t. Some t \<in> set (snd \<Gamma>) \<longrightarrow> L, K, C \<turnstile> t wellformed"
  by (induct rule: ttyping.induct,
    auto dest!: ttsplit_imp_split ttsplit_bang_imp_split_bang
      dest: split_bang_type_wellformed split_type_wellformed typing_to_kinding_env)

end

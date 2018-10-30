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

theory TypeTrackingSemantics imports
  UpdateSemantics

begin

datatype type_split_kind = TSK_L | TSK_S | TSK_NS

datatype typing_tree = TyTrLeaf
    | TyTrSplit "type_split_kind option list" ctx typing_tree ctx typing_tree

type_synonym tree_ctx = "typing_tree * ctx"

fun
  apply_tsk :: "type_split_kind option \<Rightarrow> type option \<Rightarrow> type option \<times> type option"
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

definition ttsplit_inner :: "kind env \<Rightarrow> type_split_kind option list \<Rightarrow> bool \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool"
where
  "ttsplit_inner K sps kndng \<Gamma>b \<Gamma>1 \<Gamma>2 = (
          length sps = length \<Gamma>b
        \<and> \<Gamma>1 = map (\<lambda> (sp, v). if sp \<in> {Some TSK_L, Some TSK_S} then v else None)
                        (zip sps \<Gamma>b)
        \<and> \<Gamma>2 = map (\<lambda> (sp, v). if sp = Some TSK_L then None else v)
                        (zip sps \<Gamma>b)
        \<and> Some TSK_NS \<notin> set sps
        \<and> (\<forall>t \<in> set \<Gamma>b. t \<noteq> None \<longrightarrow> kndng \<longrightarrow> (K \<turnstile> the t wellkinded))
        \<and> (\<forall>i < length \<Gamma>b. nth sps i = Some TSK_S
            \<longrightarrow> nth \<Gamma>b i \<noteq> None \<and> (\<exists>k. K \<turnstile> (the (nth \<Gamma>b i)) :\<kappa> k \<and> S \<in> k)))"

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
  by (auto simp add: kinding_def ttsplit_inner_def forall_less_Suc_eq)

lemma ttsplit_imp_split:
  "ttsplit K \<Gamma> ijs xs \<Gamma>1 ys \<Gamma>2 \<Longrightarrow> (\<exists>\<Gamma>1a \<Gamma>2a. split K (snd \<Gamma>) \<Gamma>1a \<Gamma>2a
    \<and> snd \<Gamma>1 = xs @ \<Gamma>1a & snd \<Gamma>2 = ys @ \<Gamma>2a)"
  apply (clarsimp simp: ttsplit_def ttsplit_inner_def split_def list_all3_conv_all_nth)
  apply (case_tac "\<Gamma>b ! i")
   apply (clarsimp simp add: split_comp.simps)
  apply (case_tac "ijs ! i = Some TSK_S")
   apply (force simp add: split_comp.simps)
  apply (fastforce dest: nth_mem simp add: kinding_def split_comp.simps)
  done

lemma split_imp_ttsplit:
  "split K \<Gamma> \<Gamma>1 \<Gamma>2 \<Longrightarrow> sps = map (\<lambda>i. if \<Gamma>1 ! i = None then None
            else if \<Gamma>2 ! i = None then Some TSK_L else Some TSK_S) [0 ..< length \<Gamma>]
    \<Longrightarrow> \<Gamma>1' = xs @ \<Gamma>1 \<Longrightarrow> \<Gamma>2' = ys @ \<Gamma>2
    \<Longrightarrow> ttsplit K (TyTrSplit sps xs tt ys tt2, \<Gamma>) sps xs
        (tt, \<Gamma>1') ys (tt2, \<Gamma>2')"
  apply (clarsimp simp: ttsplit_def ttsplit_inner_def split_def list_all3_conv_all_nth image_def)
  apply (subst (0 1) list_eq_iff_nth_eq)
  apply (fastforce simp add: split_comp.simps in_set_conv_nth)
  done

definition ttsplit_triv :: "tree_ctx \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> bool"
where
  "ttsplit_triv \<Gamma> xs \<Gamma>1 ys \<Gamma>2 = (\<exists>ijs \<Gamma>1a \<Gamma>2a.
    fst \<Gamma> = TyTrSplit ijs xs \<Gamma>1a ys \<Gamma>2a \<and> \<Gamma>1 = (\<Gamma>1a, xs @ snd \<Gamma>) \<and> \<Gamma>2 = (\<Gamma>2a, ys @ snd \<Gamma>))"

lemma ttsplit_trivI:
  "\<Gamma>1b = (\<Gamma>1a, xs @ \<Gamma>b) \<Longrightarrow> \<Gamma>2b = (\<Gamma>2a, ys @ \<Gamma>b) \<Longrightarrow> ttsplit_triv (TyTrSplit ijs xs \<Gamma>1a ys \<Gamma>2a, \<Gamma>b) xs \<Gamma>1b ys \<Gamma>2b"
  by (simp add: ttsplit_triv_def)

definition ttsplit_bang_inner :: "kind env \<Rightarrow> type_split_kind option list \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool"
where
  "ttsplit_bang_inner K sps \<Gamma>b \<Gamma>1 \<Gamma>2 = (
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

definition
  "ttsplit_bang is sps K \<Gamma> xs \<Gamma>1 ys \<Gamma>2 =
    (\<exists>\<Gamma>b \<Gamma>1a \<Gamma>2a T1 T2. \<Gamma> = (TyTrSplit sps xs T1 ys T2, \<Gamma>b)
        \<and> ttsplit_bang_inner K sps \<Gamma>b \<Gamma>1a \<Gamma>2a
        \<and> (\<forall>i < length \<Gamma>b. (i \<in> is) = (nth sps i = Some TSK_NS))
        \<and> \<Gamma>1 = (T1, xs @ \<Gamma>1a)
        \<and> \<Gamma>2 = (T2, ys @ \<Gamma>2a))"

lemma ttsplit_bangI:
  "xs' = xs @ \<Gamma>1a \<Longrightarrow> ys' = ys @ \<Gamma>2a
    \<Longrightarrow> is = set (map fst (filter (\<lambda>(i, v). v = Some TSK_NS) (enumerate 0 sps)))
    \<Longrightarrow> ttsplit_bang_inner K sps \<Gamma>b \<Gamma>1a \<Gamma>2a
    \<Longrightarrow> ttsplit_bang is sps K (TyTrSplit sps xs T1 ys T2, \<Gamma>b) xs (T1, xs') ys (T2, ys')"
  by (simp add: ttsplit_bang_def ttsplit_bang_inner_def in_set_enumerate_eq image_def)

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
  by (auto simp add: ttsplit_bang_inner_def forall_less_Suc_eq)

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
        \<and> (\<forall>i < length \<Gamma>. if i \<in> is then \<Gamma>2 ! i = \<Gamma> ! i \<and> \<Gamma> ! i \<noteq> None
                \<and> \<Gamma>1 ! i = map_option bang (\<Gamma> ! i)
            else split_comp K (\<Gamma> ! i) (\<Gamma>1 ! i) (\<Gamma>2 ! i)))"
  apply (induct \<Gamma> arbitrary: "is" \<Gamma>1 \<Gamma>2)
   apply (auto elim: split_bang.cases intro: split_bang_empty)[1]
  apply (rule iffI)
   apply (erule split_bang.cases, simp)
    apply clarsimp
    apply (case_tac i)
     apply simp
    apply (simp add: Suc_mem_image_pred cong: if_cong)
   apply clarsimp
   apply (case_tac i)
    apply simp
   apply (simp add: Suc_mem_image_pred_remove cong: if_cong)
  apply (clarsimp simp: length_Suc_conv forall_less_Suc_eq)
  apply (frule_tac x=0 in spec, simp(no_asm_use))
  apply (case_tac "0 \<in> is", simp_all)
   apply clarsimp
   apply (erule split_bang_bang, rule refl)
   apply (simp add: Suc_mem_image_pred_remove cong: if_cong)
  apply (rule split_bang_cons, (simp_all add: Suc_mem_image_pred cong: if_cong))
  done

lemma ttsplit_bang_imp_split_bang:
  "ttsplit_bang is sps K \<Gamma> xs \<Gamma>1 ys \<Gamma>2 \<Longrightarrow>
    (\<exists>\<Gamma>1a \<Gamma>2a. split_bang K is (snd \<Gamma>) \<Gamma>1a \<Gamma>2a
        \<and> snd \<Gamma>1 = xs @ \<Gamma>1a & snd \<Gamma>2 = ys @ \<Gamma>2a)"
  apply (clarsimp simp: ttsplit_bang_def ttsplit_bang_inner_def
                        split_bang_nth nth_enumerate_eq
             split del: if_splits cong: if_cong)
  apply clarsimp
  apply (case_tac "\<Gamma>b ! i")
   apply (simp add: split_comp.none)
  apply (drule spec, drule(1) mp)+
  apply (auto intro: split_comp.intros)
  done

lemma ttsplit_bang_inner_Cons:
  "ttsplit_bang_inner K sps \<Gamma>b \<Gamma>1 \<Gamma>2
    \<Longrightarrow> ttsplit_bang_inner K [sp] [\<gamma>] [\<gamma>1] [\<gamma>2]
    \<Longrightarrow> ttsplit_bang_inner K (sp # sps) (\<gamma> # \<Gamma>b) (\<gamma>1 # \<Gamma>1) (\<gamma>2 # \<Gamma>2)"
  by (simp add: ttsplit_bang_inner_def forall_less_Suc_eq)

lemma split_bang_imp_ttsplit:
  "split_bang K is \<Gamma> \<Gamma>1 \<Gamma>2
    \<Longrightarrow> \<exists>sps. \<forall>xs ys \<Gamma>1' \<Gamma>2'. (\<Gamma>1' = xs @ \<Gamma>1 \<longrightarrow> \<Gamma>2' = ys @ \<Gamma>2
    \<longrightarrow> ttsplit_bang is sps K (TyTrSplit sps xs tt ys tt2, \<Gamma>) xs
        (tt, \<Gamma>1') ys (tt2, \<Gamma>2'))"
  apply (clarsimp simp: ttsplit_bang_def)
  apply (induct rule: split_bang.induct)
    apply (simp add: ttsplit_bang_def ttsplit_bang_inner_def)
   apply (clarsimp simp: forall_less_Suc_eq Suc_mem_image_pred)
   apply (rule exI, rule conjI, erule_tac sp="if a = None then None
        else if b = None then Some TSK_L else Some TSK_S" in ttsplit_bang_inner_Cons)
    apply (auto simp: ttsplit_bang_inner_def elim!: split_comp.cases)[1]
   apply (simp add: Set.remove_def)
  apply (clarsimp simp: forall_less_Suc_eq Suc_mem_image_pred_remove)
  apply (rule exI, rule conjI, erule_tac sp="Some TSK_NS" in ttsplit_bang_inner_Cons)
   apply (simp add: ttsplit_bang_inner_def)
  apply simp
  done

lemma split_follow_typing_tree:
  "ttsplit K \<Gamma> sps' xs' \<Gamma>1 ys' \<Gamma>2 \<Longrightarrow> (\<Gamma>1, \<Gamma>2) = follow_typing_tree \<Gamma> \<and> new_tt_types \<Gamma> = ys'"
  "ttsplit_triv \<Gamma> xs' \<Gamma>1 ys' \<Gamma>2 \<Longrightarrow> (\<Gamma>1, \<Gamma>2) = follow_typing_tree_triv \<Gamma> \<and> new_tt_types \<Gamma> = ys'"
  "ttsplit_bang is sps' K \<Gamma> xs' \<Gamma>1 ys' \<Gamma>2 \<Longrightarrow> (\<Gamma>1, \<Gamma>2) = follow_typing_tree \<Gamma> \<and> new_tt_types \<Gamma> = ys'"
    apply (clarsimp simp: ttsplit_def ttsplit_inner_def ball_conj_distrib[symmetric])
    apply (case_tac a, simp_all)
    apply (case_tac aa, simp_all)
    apply (clarsimp elim!: in_set_zipE)
   apply (cases \<Gamma>, clarsimp simp: ttsplit_triv_def)
  apply (clarsimp simp: ttsplit_bang_def ttsplit_bang_inner_def ball_conj_distrib[symmetric])
  apply (case_tac a, simp_all)
  apply (case_tac aa, simp_all)
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
                   ; ttsplit_triv \<Gamma>2 [Some t] \<Gamma>3 [Some (TSum (tagged_list_update tag (t, Checked) ts))] \<Gamma>4
                   ; \<Xi>, K, \<Gamma>1 T\<turnstile> x : TSum ts
                   ; (tag, t, Unchecked) \<in> set ts
                   ; \<Xi>, K, \<Gamma>3 T\<turnstile> a : u
                   ; \<Xi>, K, \<Gamma>4 T\<turnstile> b : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Case x tag a b : u"

| ttyping_if     : "\<lbrakk> ttsplit K \<Gamma> ijs [] \<Gamma>1 [] \<Gamma>2
                   ; ttsplit_triv \<Gamma>2 [] \<Gamma>3 [] \<Gamma>4
                   ; \<Xi>, K, \<Gamma>1 T\<turnstile> x : TPrim Bool
                   ; \<Xi>, K, \<Gamma>3 T\<turnstile> a : t
                   ; \<Xi>, K, \<Gamma>4 T\<turnstile> b : t
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> If x a b : t"

| ttyping_take   : "\<lbrakk> ttsplit K \<Gamma> ijs [] \<Gamma>1 [Some t, Some (TRecord (ts [f := (n, t, taken)]) s)] \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 T\<turnstile> e : TRecord ts s
                   ; sigil_perm s \<noteq> Some ReadOnly
                   ; f < length ts
                   ; ts ! f = (n, t, Present)
                   ; K \<turnstile> t :\<kappa> k
                   ; S \<in> k \<or> taken = Taken
                   ; \<Xi>, K, \<Gamma>2 T\<turnstile> e' : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Take e f e' : u"

inductive_cases ttyping_splitE[elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Split x y : t'"
inductive_cases ttyping_letE[elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Let x y : u"
inductive_cases ttyping_letbE[elim]: "\<Xi>, K, \<Gamma> T\<turnstile> LetBang is x y : u"
inductive_cases ttyping_caseE[elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Case x tag a b : u"
inductive_cases ttyping_ifE[elim]: "\<Xi>, K, \<Gamma> T\<turnstile> If x a b : t"
inductive_cases ttyping_takeE[elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Take e f e' : u"

lemma ttyping_imp_typing:
assumes "\<Xi>, K, \<Gamma> T\<turnstile> e : u"
shows   "\<Xi>, K, (snd \<Gamma>) \<turnstile> e : u"
  using assms
proof (induct rule: ttyping.induct)
  case (ttyping_case K t\<Gamma> ijs t\<Gamma>1 t\<Gamma>2 t t\<Gamma>3 tag ts t\<Gamma>4 \<Xi> x a u b)
  then show ?case
  proof (intro typing_typing_all.intros)
    show "K \<turnstile> snd t\<Gamma> \<leadsto> snd t\<Gamma>1 | snd t\<Gamma>2"
      using ttsplit_imp_split ttyping_case.hyps(1) by fastforce
  next
    show "\<Xi>, K, Some t # snd t\<Gamma>2 \<turnstile> a : u"
      using ttsplit_triv_def ttyping_case.hyps(2,7) by auto
  next
    show "\<Xi>, K, Some (TSum (tagged_list_update tag (t, Checked) ts)) # snd t\<Gamma>2 \<turnstile> b : u"
      using ttsplit_triv_def ttyping_case.hyps(2,9) by auto
  qed simp+
qed (auto simp:  ttsplit_triv_def
         dest!: ttsplit_imp_split ttsplit_bang_imp_split_bang
         intro: typing_typing_all.intros)

lemma typing_imp_ttyping_induct:
shows " (\<Xi>, K, \<Gamma> \<turnstile> e : u \<Longrightarrow> (\<exists> tt. \<Xi>, K, (tt, \<Gamma>) T\<turnstile> e : u))"
and   " (\<Xi>, K, \<Gamma> \<turnstile>* es : us \<Longrightarrow> True)"
proof (induct rule: typing_typing_all.inducts)
  case (typing_case K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x ts tag t a u b)
  moreover then obtain sps tt1 tt2 tt  ijs tt2a tt2a'
    where "ttsplit K (tt, \<Gamma>) sps [] (tt1, \<Gamma>1) [] (tt2, \<Gamma>2)"
      and "tt = TyTrSplit sps [] tt1 [] tt2"
      and "\<Xi>, K, (tt1, \<Gamma>1) T\<turnstile> x : TSum ts"
      and "\<Xi>, K, (tt2a, Some t # \<Gamma>2) T\<turnstile> a : u"
      and "\<Xi>, K, (tt2a', Some (TSum (tagged_list_update tag (t, Checked) ts)) # \<Gamma>2) T\<turnstile> b : u"
      and tt2_is: "tt2 = TyTrSplit ijs [Some t] tt2a [Some (TSum (tagged_list_update tag (t, Checked) ts))] tt2a'"
    using split_imp_ttsplit[where xs="[]" and ys="[]"] by blast
  ultimately have "\<Xi>, K, (tt, \<Gamma>) T\<turnstile> Case x tag a b : u"
  proof (intro ttyping.ttyping_case)
    from tt2_is
    show "ttsplit_triv (tt2, \<Gamma>2)
            [Some t] (tt2a, Some t # \<Gamma>2)
            [Some (TSum (tagged_list_update tag (t, Checked) ts))] (tt2a', Some (TSum (tagged_list_update tag (t, Checked) ts)) # \<Gamma>2)"
      unfolding ttsplit_triv_def
      by simp
  qed blast+
  then show ?case
    by blast
qed (fastforce intro: ttyping_split[rotated] ttyping_let[rotated] ttyping_letb[rotated]
                      ttyping_case[rotated 2] ttyping_if[rotated 2] ttyping_take[rotated 2]
                      ttyping_default typing_typing_all.intros
            simp: composite_anormal_expr_def ttsplit_triv_def
            elim: split_imp_ttsplit
    | metis split_bang_imp_ttsplit ttyping_letb append.simps)+


lemma ttyping_eq_typing:
shows "\<Xi>, K, \<Gamma> \<turnstile> e : u = (\<exists> tt. \<Xi>, K, (tt, \<Gamma>) T\<turnstile> e : u)"
by (auto dest: ttyping_imp_typing typing_imp_ttyping_induct)

context update_sem begin

inductive u_tt_sem_pres :: "('f \<Rightarrow> poly_type)
                          \<Rightarrow> ('f,'a,'l) uabsfuns
                          \<Rightarrow> ('f,'a,'l) uval env
                          \<Rightarrow> kind env
                          \<Rightarrow> tree_ctx
                          \<Rightarrow> type
                          \<Rightarrow> ('f,'a,'l) store \<times> 'f expr
                          \<Rightarrow> ('f,'a,'l) store \<times> ('f,'a,'l) uval
                          \<Rightarrow> bool"  ("_, _, _, _, _, _ T\<turnstile> _ \<Down>! _" [30,0,0,0,0,20] 60)
where
  u_tt_sem_pres_default : "\<lbrakk> \<not> composite_anormal_expr x
                           ; \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! st
                           ; \<Xi>, K, snd \<Gamma> \<turnstile> x : \<tau>
                           ; \<exists>rs ws. matches_ptrs \<Xi> \<sigma> \<gamma> (snd \<Gamma>) rs ws
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, x) \<Down>! st"

| u_tt_sem_pres_let     : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [Some t] \<Gamma>2
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, t T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', a')
                           ; \<Xi>, \<xi> , (a' # \<gamma>), K, \<Gamma>2, \<tau> T\<turnstile> (\<sigma>', b) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Let a b) \<Down>! st"

| u_tt_sem_pres_letbang : "\<lbrakk> ttsplit_bang is sps K \<Gamma> [] \<Gamma>1 [Some t] \<Gamma>2
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, t T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', a')
                           ; \<Xi>, \<xi> , (a' # \<gamma>), K, \<Gamma>2, \<tau> T\<turnstile> (\<sigma>', b) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, LetBang vs a b) \<Down>! st"

| u_tt_sem_pres_case_m  : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [] \<Gamma>2
                           ; ttsplit_triv \<Gamma>2 [typ1] \<Gamma>3 [typ2] \<Gamma>4
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TSum ts T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', USum t v rs)
                           ; \<Xi>, \<xi> , (v # \<gamma>),K,  \<Gamma>3, \<tau> T\<turnstile> (\<sigma>', m) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Case x t m n) \<Down>! st"

| u_tt_sem_pres_case_nm : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [] \<Gamma>2
                           ; ttsplit_triv \<Gamma>2 [typ1] \<Gamma>3 [typ2] \<Gamma>4
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TSum ts T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', USum t' v rs)
                           ; t' \<noteq> t
                           ; \<Xi>, \<xi> , (USum t' v rs # \<gamma>), K, \<Gamma>4, \<tau> T\<turnstile> (\<sigma>', n) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Case x t m n) \<Down>! st"

| u_tt_sem_pres_if      : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [] \<Gamma>2
                           ; ttsplit_triv \<Gamma>2 [] \<Gamma>3 [] \<Gamma>4
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TPrim Bool T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', UPrim (LBool b))
                           ; \<Xi>, \<xi> , \<gamma>, K, (if b then \<Gamma>3 else \<Gamma>4), \<tau> T\<turnstile> (\<sigma>', if b then t else e) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, If x t e) \<Down>! st"

| u_tt_sem_pres_take    : "\<lbrakk> s = Boxed Writable l
                           ; ttsplit K \<Gamma> sps [] \<Gamma>1 [Some f_ty, Some (TRecord tak_fs s)] \<Gamma>2
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TRecord ts s T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', UPtr p rp)
                           ; \<sigma>' p = Some (URecord fs)
                           ; \<Xi>, \<xi> , (fst (fs ! f) # UPtr p rp # \<gamma>), K, \<Gamma>2, \<tau> T\<turnstile> (\<sigma>', e) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Take x f e) \<Down>! st"

| u_tt_sem_pres_take_ub : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [Some f_ty, Some (TRecord tak_ts Unboxed)] \<Gamma>2
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TRecord ts Unboxed T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', URecord fs)
                           ; \<Xi>, \<xi> , (fst (fs ! f) # URecord fs # \<gamma>), K, \<Gamma>2, \<tau> T\<turnstile> (\<sigma>', e) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Take x f e) \<Down>! st"

| u_tt_sem_pres_split   : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [Some t, Some u] \<Gamma>2
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TProduct t u T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', UProduct a b)
                           ; \<Xi>, \<xi> , (a # b # \<gamma>), K, \<Gamma>2, \<tau> T\<turnstile> (\<sigma>', e) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Split x e) \<Down>! st"


theorem intermediate_preservation:
assumes "proc_ctx_wellkinded \<Xi>"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (snd \<Gamma>) \<langle>r, w\<rangle>"
and     "\<xi> matches-u \<Xi>"
shows   "\<lbrakk> \<xi>, \<gamma> \<turnstile>  (\<sigma>, e) \<Down>! (\<sigma>', v)
         ; \<Xi>, [], \<Gamma> T\<turnstile> e : \<tau>
         \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, [], \<Gamma>, \<tau> T\<turnstile> (\<sigma>, e) \<Down>! (\<sigma>', v)"
and     "\<lbrakk> \<xi>, \<gamma> \<turnstile>* (\<sigma>, es) \<Down>! (\<sigma>', vs)
         ; \<Xi>, [], (snd \<Gamma>) \<turnstile>* es : \<tau>s'
         \<rbrakk> \<Longrightarrow> True"
using assms proof (induct "(\<sigma>, e)"        "(\<sigma>', v )"
                      and "(\<sigma>, es)" "(\<sigma>', vs)"
                      arbitrary:  e   \<tau>   \<Gamma> r w v  \<sigma>' \<sigma>
                             and  es  \<tau>s' \<Gamma> r w vs \<sigma>' \<sigma>
                      rule: u_sem_u_sem_all.inducts)

  case u_sem_let show ?case using u_sem_let.prems u_sem_let.hyps(1, 3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply (frule ttsplit_imp_split)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (frule(1) matches_ptrs_split', clarsimp)
    apply (erule u_tt_sem_pres_let)
     apply (rule u_sem_let.hyps(2), simp+)[1]
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_let.hyps(1)]
     , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply clarsimp
    apply (erule(1) u_sem_let.hyps(4))
     apply simp
     apply (erule matches_ptrs_some)
        apply (erule(2) matches_ptrs_frame)
        apply (drule(1) frame_noalias_matches_ptrs(2), blast, blast)
       apply (force dest: frame_noalias_matches_ptrs(1))
      apply (force dest!: frame_noalias_matches_ptrs(2))
     apply blast
    apply simp
    done

next

  case u_sem_letbang show ?case using u_sem_letbang.prems u_sem_letbang.hyps(1, 3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply (frule ttsplit_bang_imp_split_bang)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (frule(1) matches_ptrs_split_bang', clarsimp)
    apply (erule u_tt_sem_pres_letbang)
     apply (rule u_sem_letbang.hyps(2), simp+)[1]
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_letbang.hyps(1)]
     , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply clarsimp
    apply (frule(2) escapable_no_readers(1))
    apply (erule(1) u_sem_letbang.hyps(4))
     apply simp
     apply (erule matches_ptrs_some)
        apply (erule(1) matches_ptrs_frame, blast)
        apply (drule(1) frame_noalias_matches_ptrs(2), blast, blast)
       apply (rule frame_noalias_matches_ptrs(1), simp+, blast)
      apply (rule frame_noalias_matches_ptrs(2), simp+, blast)
     apply auto[1]
    apply assumption
    done

next

  case u_sem_split show ?case using u_sem_split.prems u_sem_split.hyps(1, 3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply (frule ttsplit_imp_split)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (frule(1) matches_ptrs_split', clarsimp)
    apply (erule u_tt_sem_pres_split)
     apply (rule u_sem_split.hyps(2), simp+)[1]
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_split.hyps(1)]
     , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply clarsimp
    apply (erule u_t_productE)
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (erule(1) u_sem_split.hyps(4))
     apply simp
      apply (rule matches_ptrs_some, simp, rule matches_ptrs_some, assumption)
           apply (erule(2) matches_ptrs_frame)
           apply fast
          apply blast
         apply fast
        apply blast
       apply blast
      apply fast
     apply blast
    apply blast
    done

next

  note if_splits[split del]
  case u_sem_if show ?case using u_sem_if.prems u_sem_if.hyps(1, 3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply (frule ttsplit_imp_split)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (frule(1) matches_ptrs_split', clarsimp)
    apply (erule(1) u_tt_sem_pres_if)
     apply (rule u_sem_if.hyps(2), simp+)[1]
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_if.hyps(1)]
     , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply (clarsimp simp: ttsplit_triv_def)
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (rule u_sem_if.hyps(4), simp split: if_splits, assumption)
     apply (simp split: if_splits, erule(2) matches_ptrs_frame)
      apply blast
    apply (meson matches_ptrs_frame subset_helper sup.cobounded1 sup.cobounded2)
    apply assumption
    done

next

  case u_sem_case_m show ?case using u_sem_case_m.prems u_sem_case_m.hyps(1, 3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply (frule ttsplit_imp_split)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (frule(1) matches_ptrs_split', clarsimp)
    apply (erule(1) u_tt_sem_pres_case_m)
     apply (rule u_sem_case_m.hyps(2), simp+)[1]
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_case_m.hyps(1)]
     , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply (clarsimp simp: ttsplit_triv_def)
    apply (erule u_t_sumE, clarsimp)
    apply (drule(1) distinct_fst[rotated 1], simp, simp)
    apply (erule(1) u_sem_case_m.hyps(4))
     apply simp
     apply (erule matches_ptrs_some)
        apply (erule(2) matches_ptrs_frame)
        apply (drule(1) frame_noalias_matches_ptrs(2), blast, blast)
       apply (force dest: frame_noalias_matches_ptrs(1))
      apply (force dest!: frame_noalias_matches_ptrs(2))
     apply blast
    apply simp
    done

next
  case (u_sem_case_nm \<xi> \<gamma> \<sigma> x \<sigma>'' t' v' rs t n m)

  from u_sem_case_nm.prems(1)
  show ?case
  proof (cases rule: ttyping.cases)
    case (ttyping_case ijs t\<Gamma>1 t\<Gamma>2 ta t\<Gamma>3 ts t\<Gamma>4)

    moreover have "[] \<turnstile> snd \<Gamma> \<leadsto> snd t\<Gamma>1 | snd t\<Gamma>2"
      using ttyping_case ttsplit_imp_split by fastforce
    moreover then obtain r1 w1 r2 w2
      where matches1: "\<Xi>, \<sigma> \<turnstile> \<gamma> matches snd t\<Gamma>1 \<langle>r1, w1\<rangle>"
        and matches2: "\<Xi>, \<sigma> \<turnstile> \<gamma> matches snd t\<Gamma>2 \<langle>r2, w2\<rangle>"
        and r_as_un: "r = r1 \<union> r2"
        and w_as_un: "w = w1 \<union> w2"
        and w1_2_disjoint: "w1 \<inter> w2 = {}"
      using matches_ptrs_split' u_sem_case_nm.prems(3)
      by blast
    moreover then have
      w1_r2_noalias: "w1 \<inter> r2 = {}"
      and w2_r1_noalias: "w2 \<inter> r1 = {}"
      using matches_ptrs_noalias u_sem_case_nm.prems(3) by blast+
    moreover obtain ijs \<Gamma>1a \<Gamma>2a
       where "fst t\<Gamma>2 = TyTrSplit ijs [Some ta] \<Gamma>1a [Some (TSum (tagged_list_update t (ta, Checked) ts))] \<Gamma>2a"
       and "t\<Gamma>3 = (\<Gamma>1a, [Some ta] @ snd t\<Gamma>2)"
       and t\<Gamma>4_is: "t\<Gamma>4 = (\<Gamma>2a, [Some (TSum (tagged_list_update t (ta, Checked) ts))] @ snd t\<Gamma>2)"
      using ttsplit_triv_def ttyping_case by blast
    ultimately show "\<Xi>, \<xi>, \<gamma>, [], \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Case x t m n) \<Down>! (\<sigma>', v)"
      using u_sem_case_nm.hyps
    proof (intro u_tt_sem_pres_case_nm)
      show "\<Xi>, \<xi>, \<gamma>, [], t\<Gamma>1, TSum ts T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>'', USum t' v' rs)"
        using u_sem_case_nm.hyps(2) matches1 u_sem_case_nm.prems ttyping_case by simp
    next
      have "\<Xi>, [], snd t\<Gamma>1 \<turnstile> x : TSum ts"
        by (simp add: ttyping_imp_typing ttyping_case)
      then obtain r1' w1'
        where usum_rs_under_\<sigma>'': "\<Xi>, \<sigma>'' \<turnstile> USum t' v' rs :u TSum ts \<langle>r1', w1'\<rangle>"
          and r1'_sub: "r1' \<subseteq> r1"
          and frame1: "frame \<sigma> w1 \<sigma>'' w1'"
        using preservation(1)[where \<tau>s=Nil, simplified] u_sem_case_nm.prems(2,4) matches1 u_sem_case_nm.hyps(1)
        by blast

      show "\<Xi>, \<xi>, USum t' v' rs # \<gamma>, [], t\<Gamma>4, \<tau> T\<turnstile> (\<sigma>'', n) \<Down>! (\<sigma>', v)"
        using u_sem_case_nm.prems ttyping_case
      proof (intro u_sem_case_nm.hyps(5))
        show "\<Xi>, \<sigma>'' \<turnstile> USum t' v' rs # \<gamma> matches snd t\<Gamma>4 \<langle>r1' \<union> r2, w1' \<union> w2\<rangle>"
          using frame1 frame_noalias_matches_ptrs matches2  w1_2_disjoint w1_r2_noalias
        proof (simp add: t\<Gamma>4_is, intro matches_ptrs_some)
          show "\<Xi>, \<sigma>'' \<turnstile> USum t' v' rs :u TSum (tagged_list_update t (ta, Checked) ts) \<langle>r1', w1'\<rangle>"
            by (simp add: sum_downcast_u ttyping_case u_sem_case_nm.hyps(3) usum_rs_under_\<sigma>'')
        next
          show "\<Xi>, \<sigma>'' \<turnstile> \<gamma> matches snd t\<Gamma>2 \<langle>r2, w2\<rangle>"
            using frame1 matches2 matches_ptrs_frame w1_2_disjoint w1_r2_noalias by blast
        next
          show "w2 \<inter> r1' = {}"
            using r1'_sub w2_r1_noalias by blast
        qed blast+
      qed simp+
    qed simp+
  qed (simp add: composite_anormal_expr_def)
next
  case (u_sem_take \<xi> \<gamma> \<sigma> x \<sigma>'' p r' fs f e)

  show ?case
    using u_sem_take.prems(1)
  proof (cases rule: ttyping.cases)
    case (ttyping_take ijs t\<Gamma>3 t ts n taken s t\<Gamma>4 k)

    obtain \<Gamma>1 \<Gamma>2
      where "[] \<turnstile> snd \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
        and snd_t\<Gamma>3_is: "snd t\<Gamma>3 = [] @ \<Gamma>1"
        and snd_t\<Gamma>4_is: "snd t\<Gamma>4 = [Some t, Some (TRecord (ts[f := (n, t, taken)]) s)] @ \<Gamma>2"
      using ttsplit_imp_split ttyping_take by blast
    moreover then obtain r1 w1 r2 w2
      where matches1: "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>1 \<langle>r1, w1\<rangle>"
        and matches2: "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>2 \<langle>r2, w2\<rangle>"
        and r_as_un: "r = r1 \<union> r2"
        and w_as_un: "w = w1 \<union> w2"
        and w1_w2_disjoint: "w1 \<inter> w2 = {}"
      using matches_ptrs_split' u_sem_take.prems(3) by blast
    moreover then have
      w1_r2_noalias: "w1 \<inter> r2 = {}"
      and w2_r1_noalias: "w2 \<inter> r1 = {}"
      using matches_ptrs_noalias u_sem_take.prems(3) by blast+

    have "\<Xi>, [], \<Gamma>1 \<turnstile> x : TRecord ts s"
      using snd_t\<Gamma>3_is ttyping_imp_typing ttyping_take by fastforce
    then obtain r1' w1'
      where uptr_p_under_\<sigma>'': "\<Xi>, \<sigma>'' \<turnstile> UPtr p r' :u TRecord ts s \<langle>r1', w1'\<rangle>"
        and r1'_sub: "r1' \<subseteq> r1"
        and frame1: "frame \<sigma> w1 \<sigma>'' w1'"
      using preservation(1)[where \<tau>s=Nil, simplified]
        u_sem_take.prems(2,4) matches1 u_sem_take.hyps(1)
      by blast

    have matches2_under_\<sigma>'': "\<Xi>, \<sigma>'' \<turnstile> \<gamma> matches \<Gamma>2 \<langle>r2, w2\<rangle>"
      using matches2 frame1 matches_ptrs_frame w1_w2_disjoint w1_r2_noalias
      by blast

    obtain w1'' ptrl
      where uptr_p_elim_lemmas:
        "w1' = insert p w1''"
        "\<Xi>, \<sigma>'' \<turnstile>* fs :ur ts \<langle>r1', w1''\<rangle>"
        "\<sigma>'' p = Some (URecord fs)"
        "r' = RRecord (map (type_repr \<circ> fst \<circ> snd) ts)"
        "distinct (map fst ts)"
        "s = Boxed Writable ptrl"
        "p \<notin> w1''"
        "p \<notin> r1'"
      using uptr_p_under_\<sigma>'' ttyping_take u_sem_take.hyps
      by auto

    then obtain rf wf r1a w1a
      where ut_fs_at_f: "\<Xi>, \<sigma>'' \<turnstile> fst (fs ! f) :u t \<langle>rf, wf\<rangle>"
        and ut_fs_taken_f: "\<Xi>, \<sigma>'' \<turnstile>* fs :ur ts[f := (n, t, Taken)] \<langle>r1a, w1a\<rangle>"
        and r1'_is: "r1' = rf \<union> r1a"
        and w1''_is: "w1'' = wf \<union> w1a"
        and "wf \<inter> w1a = {}"
      using uval_typing_record_take[simplified] u_t_p_rec_w ttyping_take
      by blast

    have disjointness_lemmas:
      "({p} \<union> wf \<union> w1a) \<inter> w2 = {}"
      "({p} \<union> wf \<union> w1a) \<inter> r2 = {}"
      "(rf \<union> r1a) \<inter> (wf \<union> w1a) = {}"
      "{p} \<inter> (wf \<union> w1a) = {}"
      "{p} \<inter> (rf \<union> r1a) = {}"
      "wf \<inter> w1a = {}"
      "w2 \<inter> (rf \<union> r1a) = {}"
      using frame_noalias_matches_ptrs(1)[OF frame1 matches2 w1_w2_disjoint]
        frame_noalias_matches_ptrs(2)[OF frame1 matches2 w1_r2_noalias]
        r1'_is  w1''_is uptr_p_elim_lemmas
            apply (force+)[2]
      using uptr_p_elim_lemmas uval_typing_pointers_noalias(2) r1'_is  w1''_is
          apply metis
      using uptr_p_elim_lemmas u_t_p_rec_w w1''_is r1'_is
         apply (blast+)[2]
      using \<open>wf \<inter> w1a = {}\<close>
       apply assumption
      using r1'_is r1'_sub w2_r1_noalias
      apply blast
      done

    have "\<Xi>, \<xi>, fst (fs ! f) # UPtr p r' # \<gamma>, [], t\<Gamma>4, \<tau> T\<turnstile> (\<sigma>'', e) \<Down>! (\<sigma>', v)"
    proof (cases taken)
      case Taken

      show ?thesis
        using u_sem_take.prems ttyping_take
      proof (intro u_sem_take.hyps(5))
        show "\<Xi>, \<sigma>'' \<turnstile> fst (fs ! f) # UPtr p r' # \<gamma> matches snd t\<Gamma>4 \<langle>rf \<union> (r1a \<union> r2), wf \<union> (insert p w1a \<union> w2)\<rangle>"
          using ut_fs_at_f matches2_under_\<sigma>'' disjointness_lemmas
        proof (simp only: snd_t\<Gamma>4_is append_Cons append.left_neutral, intro matches_ptrs_some[OF _ matches_ptrs_some])
          have "\<Xi>, \<sigma>'' \<turnstile>* fs :ur ts[f := (n, t, taken)] \<langle>r1a, w1a\<rangle>"
            by (simp add: ut_fs_taken_f Taken)
          moreover have "r' = RRecord (map (type_repr \<circ> fst \<circ> snd) (ts[f := (n, t, taken)]))"
              using Taken type_repr_uval_repr uptr_p_elim_lemmas ut_fs_taken_f
              by (metis (full_types))
          ultimately show "\<Xi>, \<sigma>'' \<turnstile> UPtr p r' :u TRecord (ts[f := (n, t, taken)]) s \<langle>r1a, insert p w1a\<rangle>"
            using uptr_p_elim_lemmas ut_fs_taken_f r1'_is w1''_is
            by (simp, intro u_t_p_rec_w';
                fastforce
                simp add: uptr_p_elim_lemmas ttyping_take map_update
                intro!: distinct_list_update)
        qed fast+
      qed simp+
    next
      case Present
      then have wf_empty: "wf = {}"
        using shareable_not_writable(1) ut_fs_at_f ttyping_take
        by blast

      show ?thesis
        using u_sem_take.prems ttyping_take
      proof (intro u_sem_take.hyps(5))
        show "\<Xi>, \<sigma>'' \<turnstile> fst (fs ! f) # UPtr p r' # \<gamma> matches snd t\<Gamma>4 \<langle>rf \<union> ((rf \<union> r1a) \<union> r2), {} \<union> (insert p w1a \<union> w2)\<rangle>"
          using ut_fs_at_f matches2_under_\<sigma>'' disjointness_lemmas wf_empty
        proof (simp only: snd_t\<Gamma>4_is append_Cons append.left_neutral, intro matches_ptrs_some[OF _ matches_ptrs_some])
          have "ts[f := (n, t, Present)] = ts"
            by (simp add: list_helper ttyping_take)
          thus "\<Xi>, \<sigma>'' \<turnstile> UPtr p r' :u TRecord (ts[f := (n, t, taken)]) s \<langle>rf \<union> r1a, insert p w1a\<rangle>"
            using uptr_p_elim_lemmas wf_empty r1'_is uptr_p_under_\<sigma>'' w1''_is Present by auto
        qed fast+
      qed simp+
    qed
    moreover have "\<Xi>, \<xi>, \<gamma>, [], t\<Gamma>3, TRecord ts s T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>'', UPtr p r')"
      using u_sem_take.hyps(2) u_sem_take.prems ttyping_take matches1 snd_t\<Gamma>3_is by auto
    ultimately show "\<Xi>, \<xi>, \<gamma>, [], \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Take x f e) \<Down>! (\<sigma>', v)"
      using ttyping_take uptr_p_elim_lemmas
      by (force intro!: u_tt_sem_pres_take)
  qed (simp add: composite_anormal_expr_def)
next
  case (u_sem_take_ub \<xi> \<gamma> \<sigma> x \<sigma>'' fs f e)
  show ?case using u_sem_take_ub.prems u_sem_take_ub.hyps(1,3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply clarsimp
    apply (rename_tac \<Gamma>a \<Gamma>b ijs \<Gamma>1a \<Gamma>1b t ts n taken s \<Gamma>2a TR\<Gamma>2b k)
    apply (frule ttsplit_imp_split)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (rename_tac \<Gamma>2b)
    apply (frule(1) matches_ptrs_split', clarsimp)
    apply (rename_tac r1 w1 r2 w2)
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_take_ub.hyps(1)]
        , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply clarsimp
    apply (rename_tac r1' w1')
    apply (erule u_t_recE, simp_all)
    apply (rename_tac tsa)
    apply (erule u_tt_sem_pres_take_ub)
     apply (rule u_sem_take_ub.hyps(2), simp+)[1]
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (frule(1) uval_typing_record_take, force, simp)
    apply (elim conjE exE)
    apply (rename_tac r1a w1a r1b w1b)
    apply (frule(2) matches_ptrs_frame, blast)
    apply (simp, erule disjE)
     apply (clarsimp)
     apply (frule(2) shareable_not_writable(1))
     apply simp
     apply (erule(1) u_sem_take_ub.hyps)
      apply simp
      apply (case_tac taken)
       apply (rule matches_ptrs_some [OF _ matches_ptrs_some])
               apply (simp)
              apply (fastforce intro!: u_t_struct simp add: map_update intro: distinct_list_update)
             apply fast
            apply (blast+)[6]
      apply (rule pointerset_helper_matches_ptrs)
        apply (rule matches_ptrs_some [OF _ matches_ptrs_some])
                apply (simp)
               apply (force intro!: u_t_struct simp: list_helper)
              apply (blast+)[10]
    apply (rule u_sem_take_ub.hyps(4))
       apply simp
      apply simp
     defer
     apply simp

    apply simp
    apply (rule pointerset_helper_matches_ptrs)
      apply (rule matches_ptrs_some [OF _ matches_ptrs_some])
              apply (simp+)[2]
             apply (fastforce intro!: u_t_struct simp add: map_update intro: distinct_list_update)
            apply auto[3]
         apply blast
        apply auto[1]
       apply (blast+)[2]
     apply (simp+)[2]
    done

next

  case u_sem_abs_app show ?case using u_sem_abs_app.prems u_sem_abs_app.hyps(5)
      UpdateSemantics.u_sem_abs_app[OF u_sem_abs_app.hyps(1, 3, 5)]
    apply -
    apply (rule u_tt_sem_pres_default, simp add: composite_anormal_expr_def)
      apply simp
     apply (auto dest: ttyping_imp_typing)
    done

next
  case u_sem_app show ?case using u_sem_app.prems u_sem_app.hyps(5)
      UpdateSemantics.u_sem_app[OF u_sem_app.hyps(1, 3, 5)]
    apply -
    apply (rule u_tt_sem_pres_default, simp add: composite_anormal_expr_def)
      apply simp
     apply (auto dest: ttyping_imp_typing)
    done
qed  (fastforce intro!: u_tt_sem_pres_default
               intro: u_sem_u_sem_all.intros ttyping_imp_typing
               simp: composite_anormal_expr_def
               )+ (* takes about 8s *)

lemma u_tt_sem_pres_imp_u_sem:
  "\<Xi>, \<xi>, \<gamma>, [], \<Gamma>, \<tau> T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', uv)
    \<Longrightarrow> \<xi>, \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', uv)"
  by (induct rule: u_tt_sem_pres.induct, auto intro: u_sem_u_sem_all.intros)

end

lemma split_type_wellkinded:
  "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2 \<Longrightarrow> Some t \<in> set \<Gamma> \<Longrightarrow> K \<turnstile> t wellkinded"
  by (fastforce simp add: split_def split_comp.simps in_set_conv_nth list_all3_conv_all_nth)

lemma split_bang_type_wellkinded:
  "split_bang K is \<Gamma> \<Gamma>1 \<Gamma>2 \<Longrightarrow> Some t \<in> set \<Gamma>
    \<Longrightarrow> Some t \<in> set \<Gamma>1 \<or> Some t \<in> set \<Gamma>2 \<or> K \<turnstile> t wellkinded"
  by (induct arbitrary: "is" rule: split_bang.induct,
    auto elim!: split_comp.cases)

lemma weakening_type_wellkinded:
  "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>' \<Longrightarrow> Some t \<in> set \<Gamma> \<Longrightarrow> K \<turnstile> t wellkinded"
  by (fastforce simp add: weakening_def weakening_comp.simps in_set_conv_nth list_all2_conv_all_nth)

lemma typing_to_kinding_env:
  "\<Xi>, K, \<Gamma> \<turnstile> e : u \<Longrightarrow> Some t \<in> set \<Gamma>
    \<Longrightarrow> K \<turnstile> t wellkinded"
  "\<Xi>, K, \<Gamma> \<turnstile>* es : us \<Longrightarrow> Some t \<in> set \<Gamma>
    \<Longrightarrow> K \<turnstile> t wellkinded"
  by (induct rule: typing_typing_all.inducts,
    auto simp add: Cogent.empty_def
      dest: split_bang_type_wellkinded weakening_type_wellkinded split_type_wellkinded)

lemma ttyping_type_wellkinded:
  "\<lbrakk> \<Xi>, K, \<Gamma> T\<turnstile> x : \<tau> \<rbrakk>
    \<Longrightarrow> \<forall>t. Some t \<in> set (snd \<Gamma>) \<longrightarrow> K \<turnstile> t wellkinded"
  by (induct rule: ttyping.induct,
    auto dest!: ttsplit_imp_split ttsplit_bang_imp_split_bang
      dest: split_bang_type_wellkinded split_type_wellkinded typing_to_kinding_env)

context update_sem begin

lemma matches_ptrs_replicate_None:
  "length \<gamma> = n \<Longrightarrow> \<Xi>, \<sigma>' \<turnstile> \<gamma> matches replicate n None \<langle>{}, {}\<rangle>"
  by (hypsubst_thin, induct \<gamma>, auto intro: matches_ptrs.intros)

lemma u_tt_sem_pres_type_wellkinded:
  "\<lbrakk> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', x) \<rbrakk>
    \<Longrightarrow> \<forall>t. Some t \<in> set (snd \<Gamma>) \<longrightarrow> K \<turnstile> t wellkinded"
  by (induct rule: u_tt_sem_pres.induct,
    auto dest!: ttsplit_imp_split ttsplit_bang_imp_split_bang
      dest: split_bang_type_wellkinded split_type_wellkinded typing_to_kinding_env)

lemma u_tt_sem_pres_type_wellkinded2:
  "\<lbrakk> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', x) \<rbrakk>
    \<Longrightarrow> K \<turnstile>  \<tau> wellkinded"
  by (induct rule: u_tt_sem_pres.induct,
    auto dest!: typing_to_kinding)

lemma u_tt_sem_pres_preservation:
  "\<Xi>, \<xi>, \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> st \<Down>! st' \<Longrightarrow> K = [] \<Longrightarrow>
    proc_ctx_wellkinded \<Xi> \<Longrightarrow> \<xi> matches-u \<Xi> \<Longrightarrow>
    \<exists>rs ws. \<Xi>, fst st' \<turnstile> snd st' :u \<tau> \<langle>rs, ws\<rangle>"
  apply (induct rule: u_tt_sem_pres.induct, simp_all)
  apply clarsimp
  apply (frule(4) preservation(1)[where \<tau>s=Nil and K=Nil, simplified])
  apply auto
  done

lemma u_tt_sem_pres_length:
  "\<Xi>, \<xi>, \<gamma>, [], \<Gamma>, \<tau> T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', x)
    \<Longrightarrow> length \<gamma> = length (snd \<Gamma>)"
  by (induct rule: u_tt_sem_pres.induct,
    auto simp: ttsplit_def ttsplit_inner_def
               ttsplit_bang_def ttsplit_bang_inner_def
         dest: matches_ptrs_length)

lemma let_elaborate_u_tt_sem_pres:
  "\<lbrakk> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', x); K = [];
        proc_ctx_wellkinded \<Xi>; \<xi> matches-u \<Xi> \<rbrakk>
    \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, (TyTrSplit (map (\<lambda>_. Some TSK_L) (snd \<Gamma>)) [] (fst \<Gamma>)
    [Some \<tau>] TyTrLeaf, snd \<Gamma>), \<tau> T\<turnstile> (\<sigma>, Let a (Var 0)) \<Down>! (\<sigma>', x)"
  apply (rule u_tt_sem_pres_let)
    apply (rule ttsplitI[OF _ refl refl])
    apply (simp only: ttsplit_inner_def zip_map1 map_map o_def Product_Type.split_def, simp)
    apply (fastforce dest: u_tt_sem_pres_type_wellkinded)
   apply simp
  apply (rule u_tt_sem_pres_default)
     apply (simp add: composite_anormal_expr_def)
    apply (rule u_sem_var[where \<gamma>="x # xs" and i=0 for x xs, simplified])
   apply simp
   apply (rule typing_var, simp_all add: weakening_def Cogent.empty_def
             zip_same_conv_map o_def map_replicate_const list_all2_same)
   apply (frule u_tt_sem_pres_type_wellkinded2)
   apply (clarsimp simp add: weakening_comp.intros)
  apply (frule u_tt_sem_pres_preservation, simp+)
  apply clarsimp
  apply (fastforce elim: matches_ptrs_some[OF _ matches_ptrs_replicate_None]
              dest: u_tt_sem_pres_length)
  done

end

end

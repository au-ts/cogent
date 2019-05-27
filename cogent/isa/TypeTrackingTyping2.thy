(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory TypeTrackingTyping2 imports
  Cogent
begin

datatype type_split_kind = TSK_L | TSK_R | TSK_S | TSK_NS | TSK_NONE

datatype ttctx =
  CtxSplit "type_split_kind list" ttctx ttctx
  | CtxSplitTriv ttctx ttctx
  | CtxLeaf
  | CtxFun string

fun apply_tsk :: "type_split_kind \<Rightarrow> type option \<Rightarrow> type option \<times> type option"
where
    "apply_tsk TSK_NONE None     = (None, None)"
  | "apply_tsk TSK_L    (Some t) = (Some t, None)"
  | "apply_tsk TSK_R    (Some t) = (None, Some t)"
  | "apply_tsk TSK_S    (Some t) = (Some t, Some t)"
  | "apply_tsk TSK_NS   (Some t) = (Some (bang t), Some t)"
  | "apply_tsk TSK_NONE (Some _) = undefined"
  | "apply_tsk _        None     = undefined"

definition apply_tsks :: "type_split_kind list \<Rightarrow> ctx \<Rightarrow> ctx \<times> ctx" where
  "apply_tsks sps \<Gamma> = unzip_fast (List.map2 apply_tsk sps \<Gamma>)"

lemma apply_tsks_Nil: "apply_tsks [] [] = ([], [])"
  by (simp add: apply_tsks_def unzip_fast_def)

lemma apply_tsks_Cons: "apply_tsks (sp # sps) (t # \<Gamma>) = (let (t1, t2) = apply_tsk sp t
                                                           ; (\<Gamma>1, \<Gamma>2) = apply_tsks sps \<Gamma>
                                                          in (t1 # \<Gamma>1, t2 # \<Gamma>2))"
  by (simp add: apply_tsks_def unzip_eq_unzip_fast[symmetric] split: prod.split)

lemma apply_tsks_preserves_length:
  assumes
    "length sps = length \<Gamma>"
    "apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)"
  shows
    "length \<Gamma>2 = length \<Gamma>1"
    "length \<Gamma>1 = length \<Gamma>"
proof -
  have
    "length (fst (unzip (List.map2 apply_tsk sps \<Gamma>))) = length (List.map2 apply_tsk sps \<Gamma>)"
    "length (snd (unzip (List.map2 apply_tsk sps \<Gamma>))) = length (List.map2 apply_tsk sps \<Gamma>)"
    using unzip_preserves_length
    by blast+
  then show
    "length \<Gamma>2 = length \<Gamma>1"
    "length \<Gamma>1 = length \<Gamma>"
    using assms
    by (simp add: apply_tsks_def unzip_eq_unzip_fast)+
qed


lemma apply_tsks_conv_all_nth_lemma1:
  assumes
    "length sps = length \<Gamma>"
    "apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)"
  shows
    "length \<Gamma>1 = length \<Gamma>2"
    "length \<Gamma>2 = length \<Gamma>"
    "\<forall>i<length sps. apply_tsk (sps ! i) (\<Gamma> ! i) = (\<Gamma>1 ! i, \<Gamma>2 ! i)"
  using assms
proof (induct sps \<Gamma> arbitrary: \<Gamma>1 \<Gamma>2 rule: list_induct2)
  case (Cons sp sps t \<Gamma>)
  case 1 then show ?case
    using Cons
    by (metis apply_tsks_preserves_length length_Cons)
  case 2 then show ?case
    using Cons
    by (metis apply_tsks_preserves_length length_Cons)
  case 3 then show ?case
    using Cons
    by (clarsimp simp add: apply_tsks_Cons less_Suc_eq_0_disj split: prod.splits)
qed (force simp add: apply_tsks_Nil)+

lemma apply_tsks_conv_all_nth_lemma2:
  assumes
    "length sps = length \<Gamma>"
    "length \<Gamma>1 = length \<Gamma>2"
    "length \<Gamma>2 = length \<Gamma>"
    "\<forall>i<length sps. apply_tsk (sps ! i) (\<Gamma> ! i) = (\<Gamma>1 ! i, \<Gamma>2 ! i)"
  shows
    "apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)"
  using assms
proof (induct sps \<Gamma> arbitrary: \<Gamma>1 \<Gamma>2 rule: list_induct2)
  case (Cons sp sps t \<Gamma>)
  then show ?case
    using Cons
    by (clarsimp simp add: All_less_Suc2 apply_tsks_Cons length_Suc_conv split: prod.splits)
qed (force simp add: apply_tsks_Nil)+

lemma apply_tsks_conv_all_nth:
  assumes
    "length sps = length \<Gamma>"
  shows
    "apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2) \<longleftrightarrow>
      length \<Gamma>1 = length \<Gamma>2 \<and> length \<Gamma>2 = length \<Gamma> \<and> (\<forall>i<length sps. apply_tsk (sps ! i) (\<Gamma> ! i) = (\<Gamma>1 ! i, \<Gamma>2 ! i))"
  using assms apply_tsks_conv_all_nth_lemma1 apply_tsks_conv_all_nth_lemma2
  by blast


fun verify_tsk :: "kind env \<Rightarrow> type_split_kind \<Rightarrow> type option \<Rightarrow> bool"
where
    "verify_tsk K TSK_NONE None     = True"
  | "verify_tsk K TSK_L    (Some t) = (\<exists>k. K \<turnstile> t :\<kappa> k)"
  | "verify_tsk K TSK_R    (Some t) = (\<exists>k. K \<turnstile> t :\<kappa> k)"
  | "verify_tsk K TSK_S    (Some t) = (\<exists>k. K \<turnstile> t :\<kappa> k \<and> S \<in> k)"
  | "verify_tsk K TSK_NS   (Some t) = (\<exists>k. K \<turnstile> t :\<kappa> k)"
  | "verify_tsk _ TSK_NONE (Some _) = False"
  | "verify_tsk _ _        None     = False"

definition verify_tsks :: "kind env \<Rightarrow> type_split_kind list \<Rightarrow> ctx \<Rightarrow> bool" where
  "verify_tsks K = list_all2 (verify_tsk K)"

lemmas verify_tsks_nil = list_all2_nil[where R=\<open>verify_tsk K\<close> for K, simplified verify_tsks_def[symmetric]]
lemmas verify_tsks_cons = list_all2_cons[where R=\<open>verify_tsk K\<close> for K, simplified verify_tsks_def[symmetric]]

lemmas verify_tsks_conv_all_nth = list_all2_conv_all_nth[where P=\<open>verify_tsk K\<close> for K, simplified verify_tsks_def[symmetric]]

lemmas verify_tsks_induct[consumes 1, case_names verify_tsks_nil verify_tsks_cons]
  = list_all2_induct[where P=\<open>verify_tsk K\<close> for K, simplified verify_tsks_def[symmetric]]

lemmas verify_tsks_Nil1 = list_all2_Nil[where P=\<open>verify_tsk K\<close> for K, simplified verify_tsks_def[symmetric]]
lemmas verify_tsks_Nil2 = list_all2_Nil2[where P=\<open>verify_tsk K\<close> for K, simplified verify_tsks_def[symmetric]]

lemmas verify_tsks_Cons = list_all2_Cons[where P=\<open>verify_tsk K\<close> for K, simplified verify_tsks_def[symmetric]]

definition verify_tsks_nobang :: "kind env \<Rightarrow> type_split_kind list \<Rightarrow> ctx \<Rightarrow> bool" where
  "verify_tsks_nobang K sps \<Gamma> \<equiv> verify_tsks K sps \<Gamma> \<and> list_all ((\<noteq>) TSK_NS) sps"

inductive syntactic_subtype :: "type \<Rightarrow> type \<Rightarrow> bool" where
  syn_subty_refl: "syntactic_subtype \<tau> \<tau>"
| syn_subty_tfun_in: "syntactic_subtype \<tau> \<tau>1 \<Longrightarrow> syntactic_subtype \<tau> (TFun \<tau>1 \<tau>2)"
| syn_subty_tfun_out: "syntactic_subtype \<tau> \<tau>2 \<Longrightarrow> syntactic_subtype \<tau> (TFun \<tau>1 \<tau>2)"
| syn_subty_tcon: "\<lbrakk> t \<in> set \<tau>s ; syntactic_subtype \<tau> t \<rbrakk> \<Longrightarrow> syntactic_subtype \<tau> (TCon n \<tau>s s)"
| syn_subty_tsum: "\<lbrakk> t \<in> set \<tau>s ; syntactic_subtype \<tau> (snd t) \<rbrakk> \<Longrightarrow> syntactic_subtype \<tau> (TSum \<tau>s)"
| syn_subty_tprod_l: "syntactic_subtype \<tau> \<tau>1 \<Longrightarrow> syntactic_subtype \<tau> (TProduct \<tau>1 \<tau>2)"
| syn_subty_tprod_r: "syntactic_subtype \<tau> \<tau>2 \<Longrightarrow> syntactic_subtype \<tau> (TProduct \<tau>1 \<tau>2)"
| syn_subty_trec: "\<lbrakk> t \<in> set \<tau>s ; syntactic_subtype \<tau> (fst t) \<rbrakk> \<Longrightarrow> syntactic_subtype \<tau> (TRecord \<tau>s s)"

fun syntactic_subtypes :: "type \<Rightarrow> type set" where
  "syntactic_subtypes (TVar i)       = {TVar i}"
| "syntactic_subtypes (TVarBang i)   = {TVarBang i}"
| "syntactic_subtypes (TCon n ts s)  = {TCon n ts s} \<union> (\<Union>(syntactic_subtypes ` set ts))"
| "syntactic_subtypes (TFun a b)     = {TFun a b} \<union> syntactic_subtypes a \<union> syntactic_subtypes b"
| "syntactic_subtypes (TPrim p)      = {TPrim p}"
| "syntactic_subtypes (TSum ts)      = {TSum ts} \<union> (\<Union>((syntactic_subtypes \<circ> snd) ` set ts))"
| "syntactic_subtypes (TProduct a b) = {TProduct a b} \<union> syntactic_subtypes a \<union> syntactic_subtypes b"
| "syntactic_subtypes (TRecord ts s) = {TRecord ts s} \<union> (\<Union>((syntactic_subtypes \<circ> fst) ` set ts))"
| "syntactic_subtypes (TUnit)        = {TUnit}"

lemma "t \<in> syntactic_subtypes \<tau> \<Longrightarrow> syntactic_subtype t \<tau>"
  by (induct \<tau> arbitrary: t rule: syntactic_subtypes.induct)
    (force intro: syntactic_subtype.intros)+

lemma syntactic_subtypes_refl: "\<tau> \<in> syntactic_subtypes \<tau>"
  by (induct \<tau>) simp+

lemma "syntactic_subtype t \<tau> \<Longrightarrow> t \<in> syntactic_subtypes \<tau>"
  by (induct rule: syntactic_subtype.inducts)
    (fastforce simp add: syntactic_subtypes_refl)+


section {* Fast Kinding *}

(* droppable+sharable, escapable *)
type_synonym kind' = "bool \<times> bool"

definition kind_isD :: "kind' \<Rightarrow> bool" where
  "kind_isD \<equiv> fst"

definition kind_isS :: "kind' \<Rightarrow> bool" where
  "kind_isS \<equiv> fst"

definition kind_isE :: "kind' \<Rightarrow> bool" where
  "kind_isE \<equiv> snd"

fun kind'_inter :: "kind' \<Rightarrow> kind' \<Rightarrow> kind'" where
  "kind'_inter (ds1, e1) (ds2, e2) = (ds1 \<and> ds2, e1 \<and> e2)"

fun sigil_kind' :: "sigil \<Rightarrow> kind'" where
  "sigil_kind' ReadOnly = (True, False)"
| "sigil_kind' Writable = (False, True)"
| "sigil_kind' Unboxed  = (True, True)"

fun wellformed' :: "nat \<Rightarrow> type \<Rightarrow> bool" where
  "wellformed' n (TVar i)       = (i < n)"
| "wellformed' n (TVarBang i)   = (i < n)"
| "wellformed' n (TCon _ ts s)  = foldl (\<and>) True (map (wellformed' n) ts)"
| "wellformed' n (TFun t u)     = (wellformed' n t \<and> wellformed' n u)"
| "wellformed' n (TPrim p)      = True"
| "wellformed' n (TSum ts)      = foldl (\<and>) True (map (wellformed' n \<circ> snd) ts)"
| "wellformed' n (TProduct t u) = (wellformed' n t \<and> wellformed' n u)"
| "wellformed' n (TRecord ts s) = foldl (\<and>) True (map (wellformed' n \<circ> fst) ts)"
| "wellformed' n (TUnit)        = True"

fun kinding' :: "kind' env \<Rightarrow> type \<Rightarrow> kind'" where
  "kinding' K (TVar i)       = (K ! i)"
| "kinding' K (TVarBang i)   = (True, snd (K ! i))"
| "kinding' K (TCon _ ts s)  = kind'_inter (foldl kind'_inter (True, True) (map (kinding' K) ts)) (sigil_kind' s)"
| "kinding' K (TFun t u)     = kind'_inter (kinding' K t) (kinding' K u)"
| "kinding' K (TPrim p)      = (True, True)"
| "kinding' K (TSum ts)      = foldl kind'_inter (True, True) (map (kinding' K \<circ> snd) ts)"
| "kinding' K (TProduct t u) = kind'_inter (kinding' K t) (kinding' K u)"
| "kinding' K (TRecord ts s) = foldl kind'_inter (True, True) (map (\<lambda>(t,b). if b then (True,True) else (kinding' K t)) ts)"
| "kinding' K (TUnit)        = (True, True)"


lemma foldl_kind'_inter_short_circuit:
  "foldl kind'_inter (False, False) ts = (False, False)"
  by (induct ts) (clarsimp+)

lemma foldl_map_evalsimps:
  "foldl f init (map g []) = init"
  "foldl f init (map g (x # xs)) = foldl f (f init (g x)) (map g xs)"
  by clarsimp+

lemmas kinding'_simps =
  kinding'.simps kind'_inter.simps foldl_map_evalsimps sigil_kind'.simps HOL.simp_thms(21-25)
  fst_conv snd_conv Product_Type.split if_True if_False

section {* Wellformed/Kinding as a function *}

fun wellformed_fn :: "nat \<Rightarrow> type \<Rightarrow> bool" where
  "wellformed_fn n (TVar i) = (i < n)"
| "wellformed_fn n (TVarBang i) = (i < n)"
| "wellformed_fn n (TCon _ ts _) = list_all (\<lambda>x. wellformed_fn n x) ts"
| "wellformed_fn n (TFun t1 t2) = (wellformed_fn n t1 \<and> wellformed_fn n t2)"
| "wellformed_fn n (TPrim _) = True"
| "wellformed_fn n (TSum ts) = (distinct (map fst ts) \<and> (list_all (\<lambda>x. wellformed_fn n (snd x)) ts))"
| "wellformed_fn n (TProduct t1 t2) = (wellformed_fn n t1 \<and> wellformed_fn n t2)"
| "wellformed_fn n (TRecord ts _) = (list_all (\<lambda>x. wellformed_fn n (fst x)) ts)"
| "wellformed_fn n TUnit = True"

definition ctx_wellformed_fn where
  "ctx_wellformed_fn n \<Gamma> \<equiv> list_all (\<lambda>t. \<forall>t'. t = Some t' \<longrightarrow> wellformed_fn n t') \<Gamma>"

lemmas ctx_wellformed_fn_nil =
  list_all_nil[where P=\<open>\<lambda>t. \<forall>t'. t = Some t' \<longrightarrow> wellformed_fn n t'\<close> for n, simplified ctx_wellformed_fn_def[symmetric]]
lemmas ctx_wellformed_fn_cons =
 list_all_cons[where P=\<open>\<lambda>t. \<forall>t'. t = Some t' \<longrightarrow> wellformed_fn n t'\<close> for n, simplified ctx_wellformed_fn_def[symmetric]]

lemmas ctx_wellformed_fn_Cons =
 list.pred_inject(2)[where P=\<open>\<lambda>t. \<forall>t'. t = Some t' \<longrightarrow> wellformed_fn n t'\<close> for n, simplified ctx_wellformed_fn_def[symmetric]]

fun kinding_fn :: "kind env \<Rightarrow> type \<Rightarrow> kind" where
  "kinding_fn K (TVar i)         = K ! i"
| "kinding_fn K (TVarBang i)     = {D,S}"
| "kinding_fn K (TCon n ts s)    = Inter (set (map (kinding_fn K) ts)) \<inter> (sigil_kind s)"
| "kinding_fn K (TFun ta tb)     = UNIV"
| "kinding_fn K (TPrim p)        = UNIV"
| "kinding_fn K (TSum ts)        = Inter (set (map (kinding_fn K \<circ> snd) ts))"
| "kinding_fn K (TProduct ta tb) = kinding_fn K ta \<inter> kinding_fn K tb"
| "kinding_fn K (TRecord ts s)   = Inter (set (map (\<lambda>(t,b). case b of False \<Rightarrow> kinding_fn K t | True \<Rightarrow> UNIV) ts)) \<inter> (sigil_kind s)"
| "kinding_fn K TUnit            = UNIV"

lemma kinding_imp_wellformedfn:
  "K \<turnstile> t :\<kappa> k \<Longrightarrow> wellformed_fn (length K) t"
  "K \<turnstile>* ts :\<kappa> k \<Longrightarrow> list_all (wellformed_fn (length K)) ts"
  "K \<turnstile>* tsr :\<kappa>r k \<Longrightarrow> list_all (wellformed_fn (length K) \<circ> fst) tsr"
  by (induct rule: kinding_kinding_all_kinding_record.inducts) (simp add: list_all_iff)+

lemma kinding_imp_kinding_fn:
  "K \<turnstile> t :\<kappa> k \<Longrightarrow> k \<subseteq> kinding_fn K t"
  "K \<turnstile>* ts :\<kappa> k \<Longrightarrow> k \<subseteq> Inter (set (map (kinding_fn K) ts))"
  "K \<turnstile>* tsr :\<kappa>r k \<Longrightarrow> k \<subseteq> Inter (set (map (\<lambda>(t,b). case b of False \<Rightarrow> kinding_fn K t | True \<Rightarrow> UNIV) tsr))"
  by (induct rule: kinding_kinding_all_kinding_record.inducts) (simp add: list_all_iff)+

lemma wellformedfn_and_kindingfn_imp_kinding:
  "\<lbrakk> wellformed_fn (length K) t; k \<subseteq> kinding_fn K t \<rbrakk> \<Longrightarrow> K \<turnstile> t :\<kappa> k"
proof (induct t arbitrary: k)
  case TCon then show ?case
    by (fastforce intro!: kinding_kinding_all_kinding_record.intros simp add: kinding_all_set INT_subset_iff list.pred_set)
next
  case TSum then show ?case
    by (fastforce intro!: kinding_kinding_all_kinding_record.intros simp add: kinding_all_set INT_subset_iff list.pred_set)
next
  case (TRecord x1a x2a)
  then show ?case
    apply (auto intro!: kinding_kinding_all_kinding_record.intros simp add: kinding_record_set kinding_all_set INT_subset_iff list.pred_set)
     apply (metis fst_conv order_refl)
    apply fastforce
    done
qed (auto intro!: kinding_kinding_all_kinding_record.intros)

lemma kinding_iff_wellformedfn_and_kindingfn:
  "K \<turnstile> t :\<kappa> k \<longleftrightarrow> wellformed_fn (length K) t \<and> k \<subseteq> kinding_fn K t"
  by (meson
      kinding_imp_kinding_fn kinding_imp_wellformedfn wellformedfn_and_kindingfn_imp_kinding)

lemma wellformed_iff_wellformedfn:
  "K \<turnstile> t wellformed \<longleftrightarrow> wellformed_fn (length K) t"
  by (force simp add: kinding_iff_wellformedfn_and_kindingfn)

lemma wellformed_all_iff_wellformedfn_all:
  "K \<turnstile>* ts wellformed \<longleftrightarrow> list_all (wellformed_fn (length K)) ts"
  by (clarsimp
      simp del: type_wellformed_all_def type_wellformed_def
      simp add: type_wellformed_all_subkind_weaken wellformed_iff_wellformedfn)

lemma wellformed_kindingfn_always_kinding:
  "\<lbrakk> wellformed_fn (length K) t; k = kinding_fn K t \<rbrakk> \<Longrightarrow> K \<turnstile> t :\<kappa> k"
  by (clarsimp simp add: kinding_iff_wellformedfn_and_kindingfn)

lemma wellformedfn_preserves_bang:
  assumes "wellformed_fn n t"
  shows "wellformed_fn n (bang t)"
  using assms
  by (induct t arbitrary: n) (force simp add: list_all_iff split: prod.split)+

lemma wellformedfn_preserves_instantiate:
  assumes
    "list_all (wellformed_fn n') \<delta>"
    "length \<delta> = n"
    "wellformed_fn n t"
  shows "wellformed_fn n' (instantiate \<delta> t)"
  using assms
  by (induct t arbitrary: n n') (force simp add: list_all_iff intro: wellformedfn_preserves_bang)+

lemma split_preserves_wellformed:
  assumes
    "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    "ctx_wellformed_fn (length K) \<Gamma>"
  shows
    "ctx_wellformed_fn (length K) \<Gamma>1"
    "ctx_wellformed_fn (length K) \<Gamma>2"
using assms
  by (induct rule: split_induct) (fastforce elim: split_comp.cases simp add: ctx_wellformed_fn_def)+

lemma split_bang_preserves_wellformed:
  assumes
    "K , is \<turnstile> \<Gamma> \<leadsto>b \<Gamma>1 | \<Gamma>2"
    "ctx_wellformed_fn (length K) \<Gamma>"
  shows
    "ctx_wellformed_fn (length K) \<Gamma>1"
    "ctx_wellformed_fn (length K) \<Gamma>2"
using assms
  by (induct rule: split_bang.inducts)
    (force intro: wellformedfn_preserves_bang simp: split_comp.simps split_bang_comp.simps ctx_wellformed_fn_def)+



lemma apply_tsk_some_preservation_left_nobang:
  assumes
    "apply_tsk sp t = (Some t1', t2)"
    "verify_tsk K sp t"
    "sp \<noteq> TSK_NS"
  shows "t = Some t1'"
  using assms
  by (cases sp; cases t; clarsimp)

lemma apply_tsk_some_preservation_left_bang:
  assumes
    "apply_tsk sp t = (Some t1', t2)"
    "verify_tsk K sp t"
    "sp = TSK_NS"
  shows "\<exists>t'. t1' = bang t' \<and> t = Some t'"
  using assms
  by (cases sp; cases t; clarsimp)

lemma apply_tsk_some_preservation_left_weak:
  assumes
    "apply_tsk sp t = (Some t1', t2)"
    "verify_tsk K sp t"
  shows "\<exists>t'. t = Some t'"
  using assms
  by (cases sp; cases t; clarsimp)

lemma apply_tsk_some_preservation_right:
  assumes
    "apply_tsk sp t = (t1, Some t2')"
    "verify_tsk K sp t"
  shows "t = Some t2'"
  using assms
  by (cases sp; cases t; clarsimp)

lemma apply_tsk_preserves_wellformedfn:
  assumes
    "verify_tsk K sp t"
    "apply_tsk sp t = (t1, t2)"
    "\<forall>t'. t = Some t' \<longrightarrow> wellformed_fn (length K) t'"
  shows
    "\<forall>t1'. t1 = Some t1' \<longrightarrow> wellformed_fn (length K) t1'"
    "\<forall>t2'. t2 = Some t2' \<longrightarrow> wellformed_fn (length K) t2'"
  using assms
  by (cases sp; cases t; clarsimp simp add: wellformedfn_preserves_bang)+

lemma apply_tsks_preserves_ctx_wellformedfn:
  assumes
    "verify_tsks K sps \<Gamma>"
    "apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)"
    "ctx_wellformed_fn (length K) \<Gamma>"
  shows
    "ctx_wellformed_fn (length K) \<Gamma>1"
    "ctx_wellformed_fn (length K) \<Gamma>2"
  using assms
  by (induct arbitrary: \<Gamma>1 \<Gamma>2 rule: verify_tsks_induct)
    (auto dest: apply_tsk_preserves_wellformedfn split: prod.splits
      simp add: apply_tsks_Cons apply_tsks_Nil ctx_wellformed_fn_Cons ctx_wellformed_fn_nil)

lemma apply_tsk_imp_split_comp:
  assumes
    "verify_tsk K sp t"
    "TSK_NS \<noteq> sp"
    "apply_tsk sp t = (t1, t2)"
  shows "K \<turnstile> t \<leadsto> t1 \<parallel> t2"
  using assms
  by (cases sp; cases t; clarsimp simp add: split_comp.simps)

lemma apply_tsks_imp_split:
  assumes
    "verify_tsks K sps \<Gamma>"
    "apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)"
    "list_all ((\<noteq>) TSK_NS) sps"
  shows
    "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
  using assms
  by (force intro!: apply_tsk_imp_split_comp
      simp add: verify_tsks_conv_all_nth split_conv_all_nth list_all_length apply_tsks_conv_all_nth)


lemma apply_tsk_imp_split_bang_comp:
  assumes
    "verify_tsk K sp t"
    "apply_tsk sp t = (t1, t2)"
  shows "K, (sp = TSK_NS) \<turnstile> t \<leadsto>b t1 \<parallel> t2"
  using assms
  by (cases sp; cases t; clarsimp simp add: split_bang_comp.simps split_comp.simps)

lemma apply_tsks_imp_split_bang:
  assumes
    "verify_tsks K sps \<Gamma>"
    "apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)"
  shows
    "K , {i. sps ! i = TSK_NS} \<turnstile> \<Gamma> \<leadsto>b \<Gamma>1 | \<Gamma>2"
  using assms
proof (induct arbitrary: \<Gamma>1 \<Gamma>2 rule: verify_tsks_induct)
  case (verify_tsks_cons x xs y ys)
  moreover have "pred ` Set.remove 0 {i. (x # xs) ! i = TSK_NS} = {i. xs ! i = TSK_NS}"
  proof -
    have "pred ` Set.remove 0 {i. (x # xs) ! i = TSK_NS} =
          pred ` {i. (\<forall>x2. i = Suc x2 \<longrightarrow> xs ! x2 = TSK_NS) \<and> i \<noteq> 0}"
      by fastforce
    also have "... = {y. \<exists>x. (\<exists>z. x = Suc z) \<and> (\<forall>x2. x = Suc x2 \<longrightarrow> xs ! x2 = TSK_NS \<and> y = x2)}"
      by (clarsimp simp add: gr0_conv_Suc pred_def image_def split: nat.split)
    also have "... = {i. xs ! i = TSK_NS}"
      by blast
    finally show ?thesis
      by blast
  qed
  ultimately show ?case
    by (auto elim: apply_tsk.elims intro!: split_bang.intros split: prod.splits
        simp add: apply_tsks_Cons split_bang_comp.simps split_comp.simps)
qed (clarsimp intro!: split_bang.intros simp add: apply_tsks_Nil)

fun split_comp_to_sps_comp where
  "split_comp_to_sps_comp None None None = TSK_NONE"
| "split_comp_to_sps_comp (Some t) (Some t1) None = TSK_L"
| "split_comp_to_sps_comp (Some t) None (Some t2) = TSK_R"
| "split_comp_to_sps_comp (Some t) (Some t1) (Some t2) = TSK_S"

(* TODO tailrec? *)
fun split_to_sps where
  "split_to_sps (t # \<Gamma>) (t1 # \<Gamma>1) (t2 # \<Gamma>2) =
    (let sp = split_comp_to_sps_comp t t1 t2
       ; sps = split_to_sps \<Gamma> \<Gamma>1 \<Gamma>2
    in sp # sps)"
| "split_to_sps [] [] [] = []"

lemma split_imp_apply_tsks:
  assumes
    "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
  shows
    "verify_tsks K (split_to_sps \<Gamma> \<Gamma>1 \<Gamma>2) \<Gamma> \<and> apply_tsks (split_to_sps \<Gamma> \<Gamma>1 \<Gamma>2) \<Gamma> = (\<Gamma>1, \<Gamma>2)"
  using assms
proof (induct rule: split_induct)
  case split_empty then show ?case
    by (clarsimp simp add: verify_tsks_Nil2 apply_tsks_Nil split: prod.splits)
next
  case (split_cons x xs y ys z zs)
  then show ?case
    by (cases x; cases y; cases z; clarsimp split: prod.splits
        simp add: verify_tsks_Cons apply_tsks_Cons list_all_cons split_comp.simps)
qed


fun split_bang_comp_to_sps_comp where
  "split_bang_comp_to_sps_comp False None None None = TSK_NONE"
| "split_bang_comp_to_sps_comp False (Some t) (Some t1) None = TSK_L"
| "split_bang_comp_to_sps_comp False (Some t) None (Some t2) = TSK_R"
| "split_bang_comp_to_sps_comp False (Some t) (Some t1) (Some t2) = TSK_S"
| "split_bang_comp_to_sps_comp True (Some t) (Some t1) (Some t2) = TSK_NS"

(* TODO tailrec? *)
fun split_bang_to_sps where
  "split_bang_to_sps is (t # \<Gamma>) (t1 # \<Gamma>1) (t2 # \<Gamma>2) =
    (let sp = split_bang_comp_to_sps_comp (0 \<in> is) t t1 t2
       ; sps = split_bang_to_sps (pred `(Set.remove 0 is)) \<Gamma> \<Gamma>1 \<Gamma>2
    in sp # sps)"
| "split_bang_to_sps _ [] [] [] = []"

lemma split_bang_imp_apply_tsks:
  assumes
    "K , is \<turnstile> \<Gamma> \<leadsto>b \<Gamma>1 | \<Gamma>2"
    "list_all (\<lambda>t. t = None \<or> type_wellformed K (the t)) \<Gamma>"
  shows
    "verify_tsks K (split_bang_to_sps is \<Gamma> \<Gamma>1 \<Gamma>2) \<Gamma> \<and> apply_tsks (split_bang_to_sps is \<Gamma> \<Gamma>1 \<Gamma>2) \<Gamma> = (\<Gamma>1, \<Gamma>2)"
  using assms
proof (induct rule: split_bang.induct)
  case split_bang_nil then show ?case
    by (clarsimp simp add: verify_tsks_Nil2 apply_tsks_Nil split: prod.splits)
next
  case (split_bang_cons K "is" x y z xs ys zs)
  then show ?case
    by (cases x; cases y; cases z; clarsimp split: prod.splits
        simp add: verify_tsks_Cons apply_tsks_Cons list_all_cons
        split_comp.simps split_bang_comp.simps;
        cases "0 \<in> is"; force)
qed


section {* Minimal Wellformed ttyping *}

inductive ttyping :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> ctx \<Rightarrow> ttctx \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> bool" 
          ("_, _, _, _ \<turnstile>2 _ : _" [55,0,0,0,0,55] 60)
      and ttyping_all :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> ctx \<Rightarrow> ttctx \<Rightarrow> 'f expr list \<Rightarrow> type list \<Rightarrow> bool"
          ("_, _, _, _ \<turnstile>2* _ : _" [55,0,0,0,0,55] 60) where

  ttyping_var    : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i t 
                   ; i < length \<Gamma>
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxLeaf \<turnstile>2 Var i : t"

| ttyping_afun   : "\<lbrakk> \<Xi> f = (K', t, u)
                   ; list_all2 (kinding K) ts K' 
                   ; wellformed_fn (length K') t
                   ; wellformed_fn (length K') u
                   ; K \<turnstile> \<Gamma> consumed
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxLeaf \<turnstile>2 AFun f ts : instantiate ts (TFun t u)"

| ttyping_fun    : "\<lbrakk> \<Xi>, K', [Some t], T \<turnstile>2 f : u 
                   ; K \<turnstile> \<Gamma> consumed
                   ; wellformed_fn (length K') t
                   ; wellformed_fn (length K') u
                   ; list_all2 (kinding K) ts K'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxFun n \<turnstile>2 Fun f ts : instantiate ts (TFun t u)"

| ttyping_app    : "\<lbrakk> verify_tsks_nobang K sps \<Gamma>
                   ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)
                   ; \<Xi>, K, \<Gamma>1, T1 \<turnstile>2 a : TFun x y
                   ; \<Xi>, K, \<Gamma>2, T2 \<turnstile>2 b : x
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 T2 \<turnstile>2 App a b : y"

| ttyping_con    : "\<lbrakk> \<Xi>, K, \<Gamma>, T \<turnstile>2 x : t
                   ; (tag,t) \<in> set ts
                   ; distinct (map fst ts)
                   ; list_all (wellformed_fn (length K) \<circ> snd) ts
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, T \<turnstile>2 Con ts tag x : TSum ts"

| ttyping_prom   : "\<lbrakk> \<Xi>, K, \<Gamma>, T \<turnstile>2 x : TSum ts
                   ; set ts \<subseteq> set ts'
                   ; distinct (map fst ts')
                   ; list_all (wellformed_fn (length K) \<circ> snd) ts'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, T \<turnstile>2 Promote ts' x : TSum ts'"

| ttyping_cast   : "\<lbrakk> \<Xi>, K, \<Gamma>, T \<turnstile>2 e : TPrim (Num \<tau>)
                   ; upcast_valid \<tau> \<tau>' 
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, T \<turnstile>2 Cast \<tau>' e : TPrim (Num \<tau>')"

| ttyping_tuple  : "\<lbrakk> verify_tsks_nobang K sps \<Gamma>
                   ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)
                   ; \<Xi>, K, \<Gamma>1, T1 \<turnstile>2 e1 : t
                   ; \<Xi>, K, \<Gamma>2, T2 \<turnstile>2 e2 : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 T2 \<turnstile>2 Tuple e1 e2 : TProduct t u"

| ttyping_split  : "\<lbrakk> verify_tsks_nobang K sps \<Gamma>
                   ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)
                   ; \<Xi>, K, \<Gamma>1, T1 \<turnstile>2 x : TProduct t u
                   ; \<Xi>, K, (Some t)#(Some u)#\<Gamma>2, T2 \<turnstile>2 y : t'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 T2 \<turnstile>2 Split x y : t'" 

| ttyping_let    : "\<lbrakk> verify_tsks_nobang K sps \<Gamma>
                   ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)
                   ; \<Xi>, K, \<Gamma>1, T1 \<turnstile>2 x : t
                   ; \<Xi>, K, (Some t # \<Gamma>2), T2 \<turnstile>2 y : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 T2 \<turnstile>2 Let x y : u"

| ttyping_letb   : "\<lbrakk> verify_tsks K sps \<Gamma>
                   ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)
                   ; \<Xi>, K, \<Gamma>1, T1 \<turnstile>2 x : t
                   ; \<Xi>, K, (Some t # \<Gamma>2), T2 \<turnstile>2 y : u
                   ; E \<in> kinding_fn K t
                   ; is = {i. sps ! i = TSK_NS}
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 T2 \<turnstile>2 LetBang is x y : u"

| ttyping_case   : "\<lbrakk> verify_tsks_nobang K sps \<Gamma>
                   ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)
                   ; \<Xi>, K, \<Gamma>1, T1 \<turnstile>2 x : TSum ts
                   ; (tag, t) \<in> set ts
                   ; \<Xi>, K, (Some t # \<Gamma>2), T21 \<turnstile>2 a : u
                   ; \<Xi>, K, (Some (TSum (filter (\<lambda> x. fst x \<noteq> tag) ts)) # \<Gamma>2), T22 \<turnstile>2 b : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 (CtxSplitTriv T21 T22) \<turnstile>2 Case x tag a b : u" 

| ttyping_esac   : "\<lbrakk> \<Xi>, K, \<Gamma>, T \<turnstile>2 x : TSum [(tag,t)]
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, T \<turnstile>2 Esac x : t"

| ttyping_if     : "\<lbrakk> verify_tsks_nobang K sps \<Gamma>
                   ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)
                   ; \<Xi>, K, \<Gamma>1, T \<turnstile>2 x : TPrim Bool
                   ; \<Xi>, K, \<Gamma>2, T21 \<turnstile>2 a : t
                   ; \<Xi>, K, \<Gamma>2, T22 \<turnstile>2 b : t
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 (CtxSplitTriv T21 T22) \<turnstile>2 If x a b : t"

| ttyping_prim   : "\<lbrakk> \<Xi>, K, \<Gamma>, T \<turnstile>2* args : map TPrim ts 
                   ; prim_op_type oper = (ts,t)
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, T \<turnstile>2 Prim oper args : TPrim t"

| ttyping_lit    : "\<lbrakk> K \<turnstile> \<Gamma> consumed
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxLeaf \<turnstile>2 Lit l : TPrim (lit_type l)" 

| ttyping_unit   : "\<lbrakk> K \<turnstile> \<Gamma> consumed
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxLeaf \<turnstile>2 Unit : TUnit"

| ttyping_struct : "\<lbrakk> \<Xi>, K, \<Gamma>, T \<turnstile>2* es : ts
                   ; ts' = zip ts (replicate (length ts) False)
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, T \<turnstile>2 Struct ts es : TRecord ts' Unboxed"

| ttyping_member : "\<lbrakk> \<Xi>, K, \<Gamma>, T \<turnstile>2 e : TRecord ts s
                   ; S \<in> kinding_fn K (TRecord ts s)
                   ; f < length ts
                   ; ts ! f = (t, False)
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, T \<turnstile>2 Member e f : t"

| ttyping_take   : "\<lbrakk> verify_tsks_nobang K sps \<Gamma>
                   ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)
                   ; \<Xi>, K, \<Gamma>1, T1 \<turnstile>2 e : TRecord ts s
                   ; s \<noteq> ReadOnly
                   ; f < length ts
                   ; ts ! f = (t, False)
                   ; S \<in> kinding_fn K t \<or> taken
                   ; \<Xi>, K, (Some t # Some (TRecord (ts [f := (t,taken)]) s) # \<Gamma>2), T2 \<turnstile>2 e' : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 T2 \<turnstile>2 Take e f e' : u"

| ttyping_put    : "\<lbrakk> verify_tsks_nobang K sps \<Gamma>
                   ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)
                   ; \<Xi>, K, \<Gamma>1, T1 \<turnstile>2 e : TRecord ts s
                   ; s \<noteq> ReadOnly
                   ; f < length ts
                   ; ts ! f = (t, taken)
                   ; K \<turnstile> t :\<kappa> k
                   ; D \<in> k \<or> taken
                   ; \<Xi>, K, \<Gamma>2, T2 \<turnstile>2 e' : t
                   ; ts' = ts[f := (t,False)]
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 T2 \<turnstile>2 Put e f e' : TRecord ts' s"

| ttyping_all_empty : "\<Xi>, K, empty n, CtxLeaf \<turnstile>2* [] : []"

| ttyping_all_cons  : "\<lbrakk> verify_tsks_nobang K sps \<Gamma>
                      ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)
                      ; \<Xi>, K, \<Gamma>1, T1 \<turnstile>2  e  : t
                      ; \<Xi>, K, \<Gamma>2, T2 \<turnstile>2* es : ts
                      \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 T2 \<turnstile>2* e # es : t # ts"

lemma ttyping_and_ctx_wellformed_impl_wellformed:
  assumes "ctx_wellformed_fn (length K) \<Gamma>"
  shows
    "\<Xi>, K, \<Gamma>, T \<turnstile>2 e : t \<Longrightarrow> wellformed_fn (length K) t"
    "\<Xi>, K, \<Gamma>, T \<turnstile>2* es : ts \<Longrightarrow> list_all (wellformed_fn (length K)) ts"
  using assms
proof (induct rule: ttyping_ttyping_all.inducts)
  case ttyping_var then show ?case
    by (force dest: weakening_preservation simp add: Cogent.empty_def list_all_length ctx_wellformed_fn_def)
next
  case ttyping_afun then show ?case
    by (auto intro!: wellformedfn_preserves_instantiate
        simp add: kinding_iff_wellformedfn_and_kindingfn list_all2_conv_all_nth list_all_length)
next
  case ttyping_fun then show ?case
    by (auto intro!: wellformedfn_preserves_instantiate
        simp add: kinding_iff_wellformedfn_and_kindingfn list_all2_conv_all_nth list_all_length)
next
  case ttyping_letb then show ?case
    by (force dest: apply_tsks_preserves_ctx_wellformedfn simp add: ctx_wellformed_fn_Cons)
next
  case (ttyping_case K sps \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> T1 x ts tag t T2 a u b)
  moreover then have "wellformed_fn (length K) t"
  proof -
    have "list_all (\<lambda>x. wellformed_fn (length K) (snd x)) ts"
      using ttyping_case
      by (force simp add: verify_tsks_nobang_def dest: apply_tsks_preserves_ctx_wellformedfn)
    then show ?thesis
      using ttyping_case
      by (force simp add: list_all_iff)
  qed
  ultimately show ?case
    by (force dest: apply_tsks_preserves_ctx_wellformedfn simp add: ctx_wellformed_fn_Cons verify_tsks_nobang_def)
next
  case ttyping_struct then show ?case
    by (simp add: list_all_length)
next
  case ttyping_member then show ?case
    by (force simp add: list_all_length)
next
  case (ttyping_take K sps \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> T1 e ts s f t taken T2 e' u)
  moreover have wellformed_t: "wellformed_fn (length K) t"
    using ttyping_take
    by (force dest: apply_tsks_preserves_ctx_wellformedfn simp add: list_all_length verify_tsks_nobang_def)
  moreover have "list_all (\<lambda>x. wellformed_fn (length K) (fst x)) (ts[f := (t, taken)])"
  proof -
    have "list_all (\<lambda>x. wellformed_fn (length K) (fst x)) ts"
      using ttyping_take
      by (force dest: apply_tsks_preserves_ctx_wellformedfn simp add: list_all_length verify_tsks_nobang_def)
    then show ?thesis
      using ttyping_take wellformed_t
      by (simp add: list_all_length nth_list_update)
  qed
  ultimately show ?case
    by (force dest: apply_tsks_preserves_ctx_wellformedfn simp add: ctx_wellformed_fn_Cons verify_tsks_nobang_def)
next
  case (ttyping_put K sps \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> T1 e ts s f t taken k T2 e')
  moreover have "list_all (\<lambda>x. wellformed_fn (length K) (fst x)) ts"
    using ttyping_put by (force dest: apply_tsks_preserves_ctx_wellformedfn simp add: verify_tsks_nobang_def)
  moreover have "wellformed_fn (length K) t"
    using ttyping_put by (force dest: kinding_imp_wellformedfn)
  ultimately show ?case
    by (clarsimp simp add: list_all_length nth_list_update)
qed (fastforce dest: apply_tsks_preserves_ctx_wellformedfn simp add: ctx_wellformed_fn_Cons comp_def verify_tsks_nobang_def)+

lemma ttyping2_imp_typing:
  assumes "ctx_wellformed_fn (length K) \<Gamma>"
  shows
    "\<Xi>, K, \<Gamma>, T \<turnstile>2 e : t \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> e : t"
    "\<Xi>, K, \<Gamma>, T \<turnstile>2* es : ts \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>* es : ts"
  using assms
proof (induct rule: ttyping_ttyping_all.inducts)
  case (ttyping_afun \<Xi> f K' t u K ts \<Gamma>)
  then show ?case sorry
next
  case (ttyping_fun \<Xi> K' t T f u K \<Gamma> ts n)
  then show ?case sorry
next
  case (ttyping_con \<Xi> K \<Gamma> T x t tag ts)
  then show ?case sorry
next
  case (ttyping_prom \<Xi> K \<Gamma> T x ts ts')
  then  show ?case
    by (fastforce simp del: type_wellformed_all_def
        simp add: type_wellformed_all_subkind_weaken list_all_length
        intro!: typing_typing_all.intros
        intro: wellformed_kindingfn_always_kinding)
next
  case (ttyping_split K sps \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> T1 x t u T2 y t')
  then show ?case sorry
next
  case (ttyping_let K sps \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> T1 x t T2 y u)
  then show ?case
  proof (intro typing_typing_all.intros)
    show split_gamma: "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
      using ttyping_let
      by (fastforce intro: apply_tsks_imp_split simp add: verify_tsks_nobang_def)
    show "\<Xi>, K, \<Gamma>1 \<turnstile> x : t"
      using ttyping_let split_gamma
      by (blast dest: split_preserves_wellformed)
    show "\<Xi>, K, Some t # \<Gamma>2 \<turnstile> y : u"
      using ttyping_let split_gamma
      by (auto simp add: ctx_wellformed_fn_Cons
          dest: split_preserves_wellformed ttyping_and_ctx_wellformed_impl_wellformed)
  qed
next
  case (ttyping_letb K sps \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> T1 x t T2 y u "is")
  then show ?case
  proof (intro typing_typing_all.intros)
    show split_gamma: "K , is \<turnstile> \<Gamma> \<leadsto>b \<Gamma>1 | \<Gamma>2"
      using ttyping_letb
      by (simp add: apply_tsks_imp_split_bang)
    show "\<Xi>, K, \<Gamma>1 \<turnstile> x : t"
      using ttyping_letb split_gamma
      by (blast dest: split_bang_preserves_wellformed)
    show "\<Xi>, K, Some t # \<Gamma>2 \<turnstile> y : u"
      using ttyping_letb split_gamma
      by (auto simp add: ctx_wellformed_fn_Cons
          dest: split_bang_preserves_wellformed ttyping_and_ctx_wellformed_impl_wellformed)
    show "K \<turnstile> t :\<kappa> kinding_fn K t"
      using ttyping_letb split_gamma
      by (blast dest: split_bang_preserves_wellformed ttyping_and_ctx_wellformed_impl_wellformed
          wellformed_kindingfn_always_kinding)
  qed auto
next
  case (ttyping_case K sps \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> T1 x ts tag t T21 a u T22 b)
  moreover have "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    using ttyping_case
    by (force simp add: verify_tsks_nobang_def intro!: apply_tsks_imp_split)
  moreover then have
    "ctx_wellformed_fn (length K) \<Gamma>1"
    "ctx_wellformed_fn (length K) \<Gamma>2"
    using ttyping_case
    by (blast dest: split_preserves_wellformed)+
  moreover then have wellformed_tsum: "wellformed_fn (length K) (TSum ts)"
    using ttyping_case
    by (auto dest: ttyping_and_ctx_wellformed_impl_wellformed)
  moreover then have
    "list_all (\<lambda>x. wellformed_fn (length K) (snd x)) (filter (\<lambda>x. fst x \<noteq> tag) ts)"
    "distinct (map fst (filter (\<lambda>x. fst x \<noteq> tag) ts))"
    by (auto dest: list_all_imp_list_all_filtered simp add: distinct_map_filter)
  moreover then have "wellformed_fn (length K) t"
    using ttyping_case.hyps wellformed_tsum
    by (auto simp add: in_set_conv_nth list_all_length)
  ultimately show ?case
    by (force intro: typing_typing_all.intros simp add: ctx_wellformed_fn_Cons)
next
  case (ttyping_if K sps \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> T x T21 a t T22 b T1)
  moreover have "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    using ttyping_if apply_tsks_imp_split verify_tsks_nobang_def by auto
  moreover then have
    "ctx_wellformed_fn (length K) \<Gamma>1"
    "ctx_wellformed_fn (length K) \<Gamma>2"
    using ttyping_if apply_tsks_preserves_ctx_wellformedfn
    by (auto simp add: verify_tsks_nobang_def)
  ultimately show ?case
    by (auto simp add: verify_tsks_nobang_def intro!: typing_typing_all.intros)
next
  case (ttyping_member \<Xi> K \<Gamma> T e ts s f t)
  then show ?case
  proof (intro typing_typing_all.intros)
    show "K \<turnstile> TRecord ts s :\<kappa> kinding_fn K (TRecord ts s)"
      using ttyping_member
      by (auto
          intro!: wellformed_kindingfn_always_kinding
          dest: ttyping_and_ctx_wellformed_impl_wellformed)
  qed auto
next
  case (ttyping_take K sps \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> T1 e ts s f t taken T2 e' u)
  moreover have "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    using ttyping_take apply_tsks_imp_split verify_tsks_nobang_def by auto
  moreover then have
    "ctx_wellformed_fn (length K) \<Gamma>1"
    "ctx_wellformed_fn (length K) \<Gamma>2"
    using ttyping_take apply_tsks_preserves_ctx_wellformedfn
    by (auto simp add: verify_tsks_nobang_def)
  moreover then have wellformed_rec: "wellformed_fn (length K) (TRecord ts s)"
    using ttyping_take by (blast dest: ttyping_and_ctx_wellformed_impl_wellformed)
  moreover then have "wellformed_fn (length K) t"
    using ttyping_take
    by (auto simp add: list_all_length)
  moreover then have
    "list_all (\<lambda>x. wellformed_fn (length K) (fst x)) (ts[f := (t, taken)])"
    "list_all (\<lambda>x. wellformed_fn (length K) (fst x)) (ts[f := (t, True)])"
    using ttyping_take wellformed_rec
    by (auto intro!: list_all_update_weak[where P=\<open>\<lambda>x. wellformed_fn (length K) (fst x)\<close>])
  ultimately show ?case
    by (auto simp add: kinding_iff_wellformedfn_and_kindingfn ctx_wellformed_fn_Cons
        intro!: typing_typing_all.intros)
qed (auto simp add: verify_tsks_nobang_def intro!: typing_typing_all.intros
        dest: apply_tsks_preserves_ctx_wellformedfn apply_tsks_imp_split)

end

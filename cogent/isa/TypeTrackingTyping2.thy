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

datatype ttctx = CtxSplit "type_split_kind list" ttctx ttctx | CtxSplitTriv ttctx ttctx | CtxLeaf

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
  "apply_tsks sps \<Gamma> = unzip (List.map2 apply_tsk sps \<Gamma>)"

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

section {* ttyping *}

inductive ttyping :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> ctx \<Rightarrow> ttctx \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> bool" 
          ("_, _, _, _ T\<turnstile> _ : _" [55,0,0,0,55] 60)
and ttyping_all :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> ctx \<Rightarrow> ttctx \<Rightarrow> 'f expr list \<Rightarrow> type list \<Rightarrow> bool" 
          ("_, _, _, _ T\<turnstile>* _ : _" [55,0,0,0,55] 60)
where

  typing_var    : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i t (* TODO *)
                   ; i < length \<Gamma>
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxLeaf T\<turnstile> Var i : t"

| typing_app    : "\<lbrakk> verify_tsks K sps \<Gamma>
                   ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)
                   ; \<Xi>, K, \<Gamma>1, t1 T\<turnstile> a : TFun x y
                   ; \<Xi>, K, \<Gamma>2, t2 T\<turnstile> b : x 
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 T2 T\<turnstile> App a b : y"

| typing_con    : "\<lbrakk> \<Xi>, K, \<Gamma>, T T\<turnstile> x : t
                   ; (tag,t) \<in> set ts
                   ; K \<turnstile>* (map snd ts) wellformed
                   ; distinct (map fst ts)
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, T T\<turnstile> Con ts tag x : TSum ts"

| ttyping_split  : "\<lbrakk> verify_tsks K sps \<Gamma>
                   ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2')
                   ; \<Xi>, K, \<Gamma>1, T1 T\<turnstile> x : TProduct t u
                   ; \<Gamma>2 = [Some t, Some u] @ \<Gamma>2'
                   ; \<Xi>, K, \<Gamma>2, T2 T\<turnstile> y : t'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 T2 T\<turnstile> Split x y : t'"

| ttyping_let    : "\<lbrakk> verify_tsks K sps \<Gamma>
                   ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2')
                   ; \<Xi>, K, \<Gamma>1, T1 T\<turnstile> x : t
                   ; \<Gamma>2 = [Some t] @ \<Gamma>2'
                   ; \<Xi>, K, \<Gamma>2, T2 T\<turnstile> y : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 T2 T\<turnstile> Let x y : u"

| ttyping_letb   : "\<lbrakk> verify_tsks K sps \<Gamma>
                   ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2')
                   ; \<Xi>, K, \<Gamma>1, T1 T\<turnstile> x : t
                   ; \<Gamma>2 = [Some t] @ \<Gamma>2'
                   ; \<Xi>, K, \<Gamma>2, T2 T\<turnstile> y : u
                   ; K \<turnstile> t :\<kappa> k
                   ; E \<in> k
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 T2 T\<turnstile> LetBang is x y : u"

| ttyping_case   : "\<lbrakk> verify_tsks K sps \<Gamma>
                   ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)
                   ; (tag, t) \<in> set ts
                   ; \<Xi>, K, \<Gamma>1, T1 T\<turnstile> x : TSum ts
                   ; \<Gamma>21 = [Some t] @ \<Gamma>2
                   ; \<Gamma>22 = [Some (TSum (filter (\<lambda> x. fst x \<noteq> tag) ts))] @ \<Gamma>2
                   ; \<Xi>, K, \<Gamma>21, T21 T\<turnstile> a : u
                   ; \<Xi>, K, \<Gamma>22, T22 T\<turnstile> b : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 (CtxSplitTriv T21 T22) T\<turnstile> Case x tag a b : u" 

| ttyping_if     : "\<lbrakk> verify_tsks K sps \<Gamma>
                   ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)
                   ; \<Xi>, K, \<Gamma>1, T1 T\<turnstile> x : TPrim Bool
                   ; \<Xi>, K, \<Gamma>2, T21 T\<turnstile> a : t
                   ; \<Xi>, K, \<Gamma>2, T22 T\<turnstile> b : t
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 (CtxSplitTriv T21 T22) T\<turnstile> If x a b : t"

| ttyping_take   : "\<lbrakk> verify_tsks K sps \<Gamma>
                   ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2')
                   ; s \<noteq> ReadOnly
                   ; f < length ts
                   ; ts ! f = (t, False)
                   ; K \<turnstile> t :\<kappa> k
                   ; S \<in> k \<or> taken
                   ; \<Xi>, K, \<Gamma>1, T1 T\<turnstile> e : TRecord ts s
                   ; \<Gamma>2 = [Some t, Some (TRecord (ts [f := (t, taken)]) s)] @ \<Gamma>2'
                   ; \<Xi>, K, \<Gamma>2, T2 T\<turnstile> e' : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 T2 T\<turnstile> Take e f e' : u"

| typing_put    : "\<lbrakk> verify_tsks K sps \<Gamma>
                   ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2')
                   ; \<Xi>, K, \<Gamma>1, T1 T\<turnstile> e : TRecord ts s
                   ; ts' = (ts [f := (t,False)])
                   ; s \<noteq> ReadOnly
                   ; f < length ts
                   ; ts ! f = (t, taken)
                   ; K \<turnstile> t :\<kappa> k
                   ; D \<in> k \<or> taken
                   ; \<Xi>, K, \<Gamma>2, T2 T\<turnstile> e' : t
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 T2 T\<turnstile> Put e f e' : TRecord ts' s"

| typing_all_empty : "\<Gamma> = empty n \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxLeaf T\<turnstile>* [] : []"

| typing_all_cons  : "\<lbrakk> verify_tsks K sps \<Gamma>
                      ; apply_tsks sps \<Gamma> = (\<Gamma>1, \<Gamma>2)
                      ; \<Xi>, K, \<Gamma>1, T1 T\<turnstile>  e  : t
                      ; \<Xi>, K, \<Gamma>2, T2 T\<turnstile>* es : ts
                      \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, CtxSplit sps T1 T2 T\<turnstile>* e # es : t # ts"


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
  by (induct rule: split_inducts) (fastforce elim: split_comp.cases simp add: ctx_wellformed_fn_def)+

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


section {* Minimal Wellformed typing *}

inductive typing2 :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> ctx \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> bool" 
          ("_, _, _ \<turnstile>2 _ : _" [55,0,0,0,55] 60)
      and typing2_all :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> ctx \<Rightarrow> 'f expr list \<Rightarrow> type list \<Rightarrow> bool"
          ("_, _, _ \<turnstile>2* _ : _" [55,0,0,0,55] 60) where

  typing_var    : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i t 
                   ; i < length \<Gamma>
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 Var i : t"

| typing_afun   : "\<lbrakk> \<Xi> f = (K', t, u)
                   ; list_all2 (kinding K) ts K' 
                   ; wellformed_fn (length K') t
                   ; wellformed_fn (length K') u
                   ; K \<turnstile> \<Gamma> consumed
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 AFun f ts : instantiate ts (TFun t u)"

| typing_fun    : "\<lbrakk> \<Xi>, K', [Some t] \<turnstile>2 f : u 
                   ; K \<turnstile> \<Gamma> consumed
                   ; wellformed_fn (length K') t
                   ; wellformed_fn (length K') u
                   ; list_all2 (kinding K) ts K'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 Fun f ts : instantiate ts (TFun t u)"

| typing_app    : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile>2 a : TFun x y
                   ; \<Xi>, K, \<Gamma>2 \<turnstile>2 b : x
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 App a b : y"

| typing_con    : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile>2 x : t
                   ; (tag,t) \<in> set ts
                   ; distinct (map fst ts)
                   ; list_all (wellformed_fn (length K) \<circ> snd) ts
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 Con ts tag x : TSum ts"

| typing_prom   : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile>2 x : TSum ts
                   ; set ts \<subseteq> set ts'
                   ; distinct (map fst ts')
                   ; list_all (wellformed_fn (length K) \<circ> snd) ts'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 Promote ts' x : TSum ts'"

| typing_cast   : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile>2 e : TPrim (Num \<tau>)
                   ; upcast_valid \<tau> \<tau>' 
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 Cast \<tau>' e : TPrim (Num \<tau>')"

| typing_tuple  : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile>2 t : T 
                   ; \<Xi>, K, \<Gamma>2 \<turnstile>2 u : U
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 Tuple t u : TProduct T U"

| typing_split  : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile>2 x : TProduct t u
                   ; \<Xi>, K, (Some t)#(Some u)#\<Gamma>2 \<turnstile>2 y : t'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 Split x y : t'" 

| typing_let    : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2 
                   ; \<Xi>, K, \<Gamma>1 \<turnstile>2 x : t
                   ; \<Xi>, K, (Some t # \<Gamma>2) \<turnstile>2 y : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 Let x y : u"

| typing_letb   : "\<lbrakk> split_bang K is \<Gamma> \<Gamma>1 \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile>2 x : t
                   ; \<Xi>, K, (Some t # \<Gamma>2) \<turnstile>2 y : u
                   ; E \<in> kinding_fn K t
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 LetBang is x y : u"

| typing_case   : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile>2 x : TSum ts
                   ; (tag, t) \<in> set ts
                   ; \<Xi>, K, (Some t # \<Gamma>2) \<turnstile>2 a : u
                   ; \<Xi>, K, (Some (TSum (filter (\<lambda> x. fst x \<noteq> tag) ts)) # \<Gamma>2) \<turnstile>2 b : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 Case x tag a b : u" 

| typing_esac   : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile>2 x : TSum [(tag,t)]
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 Esac x : t"

| typing_if     : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile>2 x : TPrim Bool
                   ; \<Xi>, K, \<Gamma>2 \<turnstile>2 a : t
                   ; \<Xi>, K, \<Gamma>2 \<turnstile>2 b : t
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 If x a b : t"

| typing_prim   : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile>2* args : map TPrim ts 
                   ; prim_op_type oper = (ts,t)
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 Prim oper args : TPrim t"

| typing_lit    : "\<lbrakk> K \<turnstile> \<Gamma> consumed
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 Lit l : TPrim (lit_type l)" 

| typing_unit   : "\<lbrakk> K \<turnstile> \<Gamma> consumed
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 Unit : TUnit"

| typing_struct : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile>2* es : ts
                   ; ts' = zip ts (replicate (length ts) False)
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 Struct ts es : TRecord ts' Unboxed"

| typing_member : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile>2 e : TRecord ts s
                   ; S \<in> kinding_fn K (TRecord ts s)
                   ; f < length ts
                   ; ts ! f = (t, False)
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 Member e f : t"

| typing_take   : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2 
                   ; \<Xi>, K, \<Gamma>1 \<turnstile>2 e : TRecord ts s
                   ; s \<noteq> ReadOnly
                   ; f < length ts
                   ; ts ! f = (t, False)
                   ; S \<in> kinding_fn K t \<or> taken
                   ; \<Xi>, K, (Some t # Some (TRecord (ts [f := (t,taken)]) s) # \<Gamma>2) \<turnstile>2 e' : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 Take e f e' : u"

| typing_put    : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile>2 e : TRecord ts s
                   ; s \<noteq> ReadOnly
                   ; f < length ts
                   ; ts ! f = (t, taken)
                   ; K \<turnstile> t :\<kappa> k
                   ; D \<in> k \<or> taken
                   ; \<Xi>, K, \<Gamma>2 \<turnstile>2 e' : t
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2 Put e f e' : TRecord (ts [f := (t,False)]) s"

| typing_all_empty : "\<Xi>, K, empty n \<turnstile>2* [] : []"

| typing_all_cons  : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                      ; \<Xi>, K, \<Gamma>1 \<turnstile>2  e  : t
                      ; \<Xi>, K, \<Gamma>2 \<turnstile>2* es : ts
                      \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>2* (e # es) : (t # ts)"

lemma typing2_and_ctx_wellformed_impl_wellformed:
  assumes "ctx_wellformed_fn (length K) \<Gamma>"
  shows
    "\<Xi>, K, \<Gamma> \<turnstile>2 e : t \<Longrightarrow> wellformed_fn (length K) t"
    "\<Xi>, K, \<Gamma> \<turnstile>2* es : ts \<Longrightarrow> list_all (wellformed_fn (length K)) ts"
  using assms
proof (induct rule: typing2_typing2_all.inducts)
  case typing_var then show ?case
    by (force dest: weakening_preservation simp add: Cogent.empty_def list_all_length ctx_wellformed_fn_def)
next
  case typing_afun then show ?case
    by (auto intro!: wellformedfn_preserves_instantiate
        simp add: kinding_iff_wellformedfn_and_kindingfn list_all2_conv_all_nth list_all_length)
next
  case typing_fun then show ?case
    by (auto intro!: wellformedfn_preserves_instantiate
        simp add: kinding_iff_wellformedfn_and_kindingfn list_all2_conv_all_nth list_all_length)
next
  case typing_letb then show ?case
    by (force dest: split_bang_preserves_wellformed simp add: ctx_wellformed_fn_Cons)
next
  case (typing_case K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x ts tag t a u b)
  moreover then have "wellformed_fn (length K) t"
  proof -
    have "list_all (\<lambda>x. wellformed_fn (length K) (snd x)) ts"
      using typing_case
      by (force dest: split_preserves_wellformed)
    then show ?thesis
      using typing_case
      by (force simp add: list_all_iff)
  qed
  ultimately show ?case
    by (force dest: split_preserves_wellformed simp add: ctx_wellformed_fn_Cons)
next
  case typing_struct then show ?case
    by (simp add: list_all_length)
next
  case typing_member then show ?case
    by (force simp add: list_all_length)
next
  case (typing_take K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f t taken e' u)
  moreover have wellformed_t: "wellformed_fn (length K) t"
    using typing_take
    by (force dest: split_preserves_wellformed simp add: list_all_length)
  moreover have "list_all (\<lambda>x. wellformed_fn (length K) (fst x)) (ts[f := (t, taken)])"
  proof -
    have "list_all (\<lambda>x. wellformed_fn (length K) (fst x)) ts"
      using typing_take
      by (force dest: split_preserves_wellformed simp add: list_all_length)
    then show ?thesis
      using typing_take wellformed_t
      by (simp add: list_all_length nth_list_update)
  qed
  ultimately show ?case
    by (force dest: split_preserves_wellformed simp add: ctx_wellformed_fn_Cons)
next
  case (typing_put K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f t taken k e')
  moreover have "list_all (\<lambda>x. wellformed_fn (length K) (fst x)) ts"
    using typing_put by (force dest: split_preserves_wellformed)
  moreover have "wellformed_fn (length K) t"
    using typing_put by (force dest: kinding_imp_wellformedfn)
  ultimately show ?case
    by (clarsimp simp add: list_all_length nth_list_update)
qed (fastforce dest: split_preserves_wellformed simp add: ctx_wellformed_fn_Cons comp_def)+

lemma typing2_imp_typing:
  assumes "ctx_wellformed_fn (length K) \<Gamma>"
  shows
    "\<Xi>, K, \<Gamma> \<turnstile>2 e : t \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> e : t"
    "\<Xi>, K, \<Gamma> \<turnstile>2* es : ts \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>* es : ts"
  using assms
proof (induct rule: typing2_typing2_all.inducts)
  case typing_afun then show ?case
    by (auto intro!: typing_typing_all.intros simp add: wellformed_iff_wellformedfn[simplified])
next
  case typing_fun then show ?case
    by (auto
        intro!: typing_typing_all.intros
        simp add: wellformed_iff_wellformedfn[simplified] ctx_wellformed_fn_Cons
        ctx_wellformed_fn_nil)
next
  case typing_con then show ?case
    by (auto intro!: typing_typing_all.intros
        simp add: wellformed_all_iff_wellformedfn_all[simplified] list.pred_map)
next
  case typing_prom then show ?case
    by (auto intro!: typing_typing_all.intros
        simp add: wellformed_all_iff_wellformedfn_all[simplified] list.pred_map)
next
  case (typing_split K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t u y t')
  moreover have
    "wellformed_fn (length K) t"
    "wellformed_fn (length K) u"
    using typing_split
    by (fastforce dest: typing2_and_ctx_wellformed_impl_wellformed split_preserves_wellformed)+
  ultimately show ?case
    by (auto intro!: typing_typing_all.intros dest: split_preserves_wellformed simp add: ctx_wellformed_fn_Cons)
next
  case typing_let then show ?case
    by (auto intro!: typing_typing_all.intros simp add: ctx_wellformed_fn_Cons
        dest: typing2_and_ctx_wellformed_impl_wellformed split_preserves_wellformed)
next
  case typing_letb then show ?case
    by (fastforce intro!: typing_typing_all.intros
        simp add: ctx_wellformed_fn_Cons kinding_iff_wellformedfn_and_kindingfn
        dest: typing2_and_ctx_wellformed_impl_wellformed split_bang_preserves_wellformed)
next
  case (typing_case K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x ts tag t a u b)
  moreover have wellformed_tsum: "wellformed_fn (length K) (TSum ts)"
    using typing_case
    by (blast dest: split_preserves_wellformed typing2_and_ctx_wellformed_impl_wellformed)
  moreover have "wellformed_fn (length K) t"
      using typing_case wellformed_tsum
      by (force simp add: list_all_iff)
  moreover have "distinct (map fst (filter (\<lambda>x. fst x \<noteq> tag) ts))"
    using wellformed_tsum distinct_map_filter by force
  moreover have "list_all (\<lambda>x. wellformed_fn (length K) (snd x)) (filter (\<lambda>x. fst x \<noteq> tag) ts)"
    using wellformed_tsum
    by (force intro: list_all_imp_list_all_filtered)
  ultimately show ?case
    by (auto intro!: typing_typing_all.intros dest: split_preserves_wellformed
        simp add: ctx_wellformed_fn_Cons)
next
  case (typing_member \<Xi> K \<Gamma> e ts s f t)
  then show ?case
  proof (intro typing_typing_all.intros)
    show "K \<turnstile> TRecord ts s :\<kappa> kinding_fn K (TRecord ts s)"
      using typing_member
      by (force dest: typing2_and_ctx_wellformed_impl_wellformed
          simp add: wellformedfn_and_kindingfn_imp_kinding)
  qed auto
next
  case (typing_take K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f t taken e' u)
  moreover have wellformed_rec: "wellformed_fn (length K) (TRecord ts s)"
    using typing_take
    by (blast dest: split_preserves_wellformed typing2_and_ctx_wellformed_impl_wellformed)
  moreover have wellformed_t: "wellformed_fn (length K) t"
    using wellformed_rec typing_take.hyps
    by (force simp add: list_all_length)
  moreover then have "ctx_wellformed_fn (length K) (Some t # Some (TRecord (ts[f := (t, taken)]) s) # \<Gamma>2)"
    using wellformed_t typing_take wellformed_rec wellformed_t
    by (auto dest: split_preserves_wellformed simp add: list_all_update_weak ctx_wellformed_fn_Cons)
  ultimately show ?case
  proof (intro typing_typing_all.intros)
    show "K \<turnstile> t :\<kappa> kinding_fn K t"
      using typing_member wellformed_t
      by (force simp add: wellformedfn_and_kindingfn_imp_kinding)
  qed (auto dest: split_preserves_wellformed)
qed (blast intro!: typing_typing_all.intros dest: split_preserves_wellformed)+

end

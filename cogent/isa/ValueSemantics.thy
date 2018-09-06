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

theory ValueSemantics
imports Cogent
begin


datatype ('f, 'a) vval = VPrim lit
                       | VProduct "('f, 'a) vval" "('f, 'a) vval"
                       | VSum name "('f, 'a) vval"
                       | VRecord "('f, 'a) vval list"
                       | VAbstract "'a"
                       | VFunction "'f expr" "type list"
                       | VAFunction "'f" "type list"
                       | VUnit

(* All polymorphic instantiations must have the _same_ value semantics. This means even if the C
implementations differ they must all refine the same specification *)
type_synonym ('f, 'a) vabsfuns = "'f \<Rightarrow> ('f, 'a) vval \<Rightarrow> ('f,'a) vval \<Rightarrow> bool"

definition eval_prim :: "prim_op \<Rightarrow> ('f, 'a) vval list \<Rightarrow> ('f, 'a) vval"
where
  "eval_prim pop xs = VPrim (eval_prim_op pop (map (\<lambda>vv. case vv of VPrim v \<Rightarrow> v | _ \<Rightarrow> LBool False) xs))"

(* NOTE: Termination is currently not provable with this approach. It's possible to show
   it for v_sem assuming all called functions are terminating, but proving
   this assumption would in turn require termination of v_sem.

   Fixing this problem is nontrivial, and will likely necessitate changes to the design.
*)


inductive v_sem :: "('f,'a) vabsfuns \<Rightarrow> ('f, 'a) vval env \<Rightarrow> 'f expr \<Rightarrow> ('f, 'a) vval \<Rightarrow> bool"
          ("_ , _ \<turnstile> _ \<Down> _" [30,0,0,20] 60)
and       v_sem_all  :: "('f,'a) vabsfuns \<Rightarrow> ('f, 'a) vval list \<Rightarrow> 'f expr list \<Rightarrow> ('f, 'a) vval list \<Rightarrow> bool"
          ("_ , _ \<turnstile>* _ \<Down> _" [30,0,0,20] 60)
where
  v_sem_var     : "\<xi> , \<gamma> \<turnstile> (Var i) \<Down> (\<gamma> ! i)"

| v_sem_lit     : "\<xi> , \<gamma> \<turnstile> (Lit l) \<Down> VPrim l"

| v_sem_prim    : "\<lbrakk> \<xi> , \<gamma> \<turnstile>* as \<Down> as'
                   \<rbrakk> \<Longrightarrow>  \<xi> , \<gamma> \<turnstile> (Prim p as) \<Down> eval_prim p as'"

| v_sem_fun     : "\<xi> , \<gamma> \<turnstile> Fun f ts \<Down> VFunction f ts"

| v_sem_afun     : "\<xi> , \<gamma> \<turnstile> AFun f ts \<Down> VAFunction f ts"

| v_sem_abs_app : "\<lbrakk> \<xi> , \<gamma> \<turnstile> x \<Down> VAFunction f ts
                   ; \<xi> , \<gamma> \<turnstile> y \<Down> a
                   ; \<xi> f a r
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (App x y) \<Down> r"

| v_sem_cast    : "\<lbrakk> \<xi> , \<gamma> \<turnstile> e \<Down> VPrim l
                   ; cast_to \<tau> l = Some l'
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> Cast \<tau> e \<Down> VPrim l'"

| v_sem_app     : "\<lbrakk> \<xi> , \<gamma> \<turnstile> x \<Down> VFunction e ts
                   ; \<xi> , \<gamma> \<turnstile> y \<Down> a
                   ; \<xi> , [ a ] \<turnstile> specialise ts e \<Down> r
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (App x y) \<Down> r"

| v_sem_con     : "\<lbrakk> \<xi> , \<gamma> \<turnstile> x \<Down> x'
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (Con _ t x) \<Down> VSum t x'"

| v_sem_member  : "\<lbrakk> \<xi> , \<gamma> \<turnstile> e \<Down> VRecord fs
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> Member e f \<Down> fs ! f"

| v_sem_unit    : "\<xi> , \<gamma> \<turnstile> Unit \<Down> VUnit"

| v_sem_tuple   : "\<lbrakk> \<xi> , \<gamma> \<turnstile> x \<Down> x'
                   ; \<xi> , \<gamma> \<turnstile> y \<Down> y'
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (Tuple x y) \<Down> VProduct x' y'"

| v_sem_esac    : "\<lbrakk> \<xi> , \<gamma> \<turnstile> t \<Down> VSum ts v
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> Esac t \<Down> v"

| v_sem_let     : "\<lbrakk> \<xi> , \<gamma> \<turnstile> a \<Down> a'
                   ; \<xi> , (a' # \<gamma>) \<turnstile> b \<Down> b'
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> Let a b \<Down> b'"

| v_sem_letbang : "\<lbrakk> \<xi> , \<gamma> \<turnstile> a \<Down> a'
                   ; \<xi> , (a' # \<gamma>) \<turnstile> b \<Down> b'
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> LetBang vs a b \<Down> b'"

| v_sem_case_m  : "\<lbrakk> \<xi> , \<gamma> \<turnstile> x \<Down> VSum t v
                   ; \<xi> , (v # \<gamma>) \<turnstile> m \<Down> m'
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> Case x t m n \<Down> m'"

| v_sem_case_nm : "\<lbrakk> \<xi> , \<gamma> \<turnstile> x \<Down> VSum t' v
                   ; t \<noteq> t'
                   ; \<xi> , (VSum t' v # \<gamma>) \<turnstile> n \<Down> n'
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> Case x t m n \<Down> n'"

| v_sem_if      : "\<lbrakk> \<xi> , \<gamma> \<turnstile> x \<Down> VPrim (LBool b)
                   ; \<xi> , \<gamma> \<turnstile> if b then t else e \<Down> r
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> If x t e \<Down> r"

| v_sem_struct  : "\<lbrakk> \<xi> , \<gamma> \<turnstile>* xs \<Down> vs
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> Struct ts xs \<Down> VRecord vs"

| v_sem_take    : "\<lbrakk> \<xi> , \<gamma> \<turnstile> x \<Down> VRecord fs
                   ; \<xi> , (fs ! f # VRecord fs # \<gamma>) \<turnstile> e \<Down> e'
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> Take x f e \<Down> e'"

| v_sem_put     : "\<lbrakk> \<xi> , \<gamma> \<turnstile> x \<Down> VRecord fs
                   ; \<xi> , \<gamma> \<turnstile> e \<Down> e'
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> Put x f e \<Down> VRecord (fs [ f := e' ])"

| v_sem_split   : "\<lbrakk> \<xi> , \<gamma> \<turnstile> x \<Down> VProduct a b
                   ; \<xi> , (a # b # \<gamma>) \<turnstile> e \<Down> e'
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> Split x e \<Down> e'"


| v_sem_all_empty : "\<xi> , \<gamma> \<turnstile>* [] \<Down> []"

| v_sem_all_cons  : "\<lbrakk> \<xi> , \<gamma> \<turnstile> x \<Down> v
                     ; \<xi> , \<gamma> \<turnstile>* xs \<Down> vs
                     \<rbrakk> \<Longrightarrow>  \<xi> , \<gamma> \<turnstile>* (x # xs) \<Down> (v # vs)"

inductive_cases v_sem_varE  [elim] : "\<xi> , \<gamma> \<turnstile> Var i \<Down> v"
inductive_cases v_sem_funE  [elim] : "\<xi> , \<gamma> \<turnstile> Fun f ts \<Down> v"
inductive_cases v_sem_afunE [elim] : "\<xi> , \<gamma> \<turnstile> AFun f ts \<Down> v"
inductive_cases v_sem_appE  [elim] : "\<xi> , \<gamma> \<turnstile> App a b \<Down> v"


locale value_sem =
  fixes abs_typing :: "'a \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> bool"
  assumes abs_typing_bang : "abs_typing av n \<tau>s \<Longrightarrow> abs_typing av n (map bang \<tau>s)"

context value_sem begin

inductive vval_typing  :: "('f \<Rightarrow> poly_type) \<Rightarrow> ('f, 'a) vval \<Rightarrow> type \<Rightarrow> bool"
          ("_ \<turnstile> _ :v _" [30,0,20] 80)
and vval_typing_record :: "('f \<Rightarrow> poly_type) \<Rightarrow> ('f, 'a) vval list \<Rightarrow> (type \<times> bool) list \<Rightarrow> bool"
          ("_ \<turnstile>* _ :vr _" [30,0,20] 80) where

  v_t_prim     : "\<Xi> \<turnstile> VPrim l :v TPrim (lit_type l)"

| v_t_product  : "\<lbrakk> \<Xi> \<turnstile> a :v t
                  ; \<Xi> \<turnstile> b :v u
                  \<rbrakk> \<Longrightarrow> \<Xi> \<turnstile> VProduct a b :v TProduct t u"

| v_t_sum      : "\<lbrakk> \<Xi> \<turnstile> a :v t
                  ; (g, t, False) \<in> set ts
                  ; distinct (map fst ts)
                  ; [] \<turnstile>* map (fst \<circ> snd) ts wellformed
                  \<rbrakk> \<Longrightarrow> \<Xi> \<turnstile> VSum g a :v TSum ts"

| v_t_record   : "\<lbrakk> \<Xi> \<turnstile>* fs :vr ts
                  \<rbrakk> \<Longrightarrow> \<Xi> \<turnstile> VRecord fs :v TRecord ts s"

| v_t_abstract : "\<lbrakk> abs_typing a n ts
                  ; [] \<turnstile>* ts wellformed
                  \<rbrakk> \<Longrightarrow> \<Xi> \<turnstile> VAbstract a :v TCon n ts s"

| v_t_afun     : "\<lbrakk> \<Xi> f = (ks, a, b)
                  ; list_all2 (kinding []) ts ks
                  ; ks \<turnstile> TFun a b wellformed
                  \<rbrakk> \<Longrightarrow> \<Xi> \<turnstile> VAFunction f ts :v TFun (instantiate ts a) (instantiate ts b)"

| v_t_function : "\<lbrakk> \<Xi> , K , [ Some t ] \<turnstile> f : u
                  ; K \<turnstile> t wellformed
                  ; list_all2 (kinding []) ts K
                  \<rbrakk> \<Longrightarrow> \<Xi> \<turnstile> VFunction f ts :v TFun (instantiate ts t) (instantiate ts u)"

| v_t_unit     : "\<Xi> \<turnstile> VUnit :v TUnit"

| v_t_r_empty  : "\<Xi> \<turnstile>* [] :vr []"

| v_t_r_cons1  : "\<lbrakk> \<Xi> \<turnstile> x :v t
                  ; \<Xi> \<turnstile>* xs :vr ts
                  \<rbrakk> \<Longrightarrow> \<Xi> \<turnstile>* (x # xs) :vr ((t, False) # ts)"

| v_t_r_cons2  : "\<lbrakk> \<Xi> \<turnstile>* xs :vr ts
                  ; [] \<turnstile> t wellformed
                  \<rbrakk> \<Longrightarrow> \<Xi> \<turnstile>* (x # xs) :vr ((t, True) # ts)"


lemma v_t_prim' [intro]:
assumes "lit_type l = \<tau>"
shows   "\<Xi> \<turnstile> VPrim l :v TPrim \<tau>"
using assms by (auto intro: v_t_prim)

inductive_cases v_t_funE      [elim]: "\<Xi> \<turnstile> VFunction f ts :v t"
inductive_cases v_t_afunE     [elim]: "\<Xi> \<turnstile> VAFunction f ts :v t"
inductive_cases v_t_recordE   [elim]: "\<Xi> \<turnstile> VRecord fs :v \<tau>"
inductive_cases v_t_productE  [elim]: "\<Xi> \<turnstile> VProduct a b :v \<tau>"
inductive_cases v_t_sumE'     [elim]: "\<Xi> \<turnstile> e :v TSum ts"
inductive_cases v_t_primE     [elim]: "\<Xi> \<turnstile> VPrim l :v TPrim (Num \<tau>)"


inductive_cases v_t_r_emptyE  [elim]: "\<Xi> \<turnstile>* [] :vr \<tau>s"
inductive_cases v_t_r_consE   [elim]: "\<Xi> \<turnstile>* (x # xs) :vr \<tau>s"


definition vval_typing_all :: "('f \<Rightarrow> poly_type) \<Rightarrow> ('f, 'a) vval list \<Rightarrow> type list \<Rightarrow> bool"
           ("_  \<turnstile>* _ :v _" [30,0,20] 80) where
   "(\<Xi> \<turnstile>* vs :v ts) \<equiv> list_all2 (vval_typing \<Xi>) vs ts"

definition matches :: "('f \<Rightarrow> poly_type) \<Rightarrow>  ('f, 'a) vval env \<Rightarrow> ctx \<Rightarrow> bool"
           ("_ \<turnstile> _ matches _" [30,0,20] 60) where
   "\<Xi> \<turnstile> \<gamma> matches \<Gamma> \<equiv> list_all2 (\<lambda> x m. \<forall> \<tau>. m = Some \<tau> \<longrightarrow> \<Xi> \<turnstile> x :v \<tau>) \<gamma> \<Gamma>"


definition proc_env_matches :: "('f \<Rightarrow> ('f, 'a) vval \<Rightarrow> ('f, 'a) vval \<Rightarrow> bool) \<Rightarrow> ('f \<Rightarrow> poly_type) \<Rightarrow> bool"
           ("_ matches _" [30,20] 60) where
  "\<xi> matches \<Xi> \<equiv> (\<forall> f. let (K, \<tau>i, \<tau>o) = \<Xi> f
                        in (\<forall> \<tau>s v v'. list_all2 (kinding []) \<tau>s K
                                  \<longrightarrow> (\<Xi> \<turnstile> v  :v instantiate \<tau>s \<tau>i)
                                  \<longrightarrow> \<xi> f v v'
                                  \<longrightarrow> (\<Xi> \<turnstile> v' :v instantiate \<tau>s \<tau>o)))"


section {* vval_typing lemmas *}

lemma vval_typing_to_kinding:
shows "\<Xi> \<turnstile> v :v \<tau>     \<Longrightarrow> [] \<turnstile> \<tau> wellformed"
and   "\<Xi> \<turnstile>* vs :vr fs \<Longrightarrow> [] \<turnstile>* map fst fs wellformed"
proof (induct rule: vval_typing_vval_typing_record.inducts)
     case v_t_function then show ?case by (force dest!: typing_to_kinding
                                                 intro: kinding_kinding_all_kinding_record.intros
                                                        substitutivity)
next case v_t_afun     then show ?case by (force dest: substitutivity)
qed (auto intro: kinding_kinding_all_kinding_record.intros supersumption kinding_all_record')

lemma vval_typing_bang:
shows  "\<Xi> \<turnstile> x :v \<tau> \<Longrightarrow> \<Xi> \<turnstile> x :v bang \<tau>"
and    "\<Xi> \<turnstile>* fs :vr \<tau>s \<Longrightarrow> \<Xi> \<turnstile>* fs :vr map (\<lambda> (x, y). (bang x, y)) \<tau>s"
proof (induct rule: vval_typing_vval_typing_record.inducts)
     case v_t_sum      then show ?case by (force intro: vval_typing_vval_typing_record.intros
                                                        bang_kind(2) [ where ts="map (fst \<circ> snd) ts"
                                                                       for ts, simplified])
next case v_t_abstract then show ?case by (force intro: vval_typing_vval_typing_record.intros
                                                        abs_typing_bang
                                                        bang_kind(2))
next case v_t_r_cons2  then show ?case by (force intro: vval_typing_vval_typing_record.intros
                                                        bang_kind)
qed (force intro: vval_typing_vval_typing_record.intros)+

subsection {* vval_typing_record *}

lemma vval_typing_record_length:
assumes "\<Xi> \<turnstile>* fs :vr \<tau>s"
shows   "length fs = length \<tau>s"
using assms proof (induct fs arbitrary: \<tau>s)
qed (auto)

lemma vval_typing_record_nth:
assumes "\<Xi> \<turnstile>* fs :vr \<tau>s"
and     "\<tau>s ! f = (\<tau>, False)"
and     "f < length \<tau>s"
shows   "\<Xi> \<turnstile> fs ! f :v \<tau>"
using assms proof (induct fs arbitrary: f \<tau>s)
     case Nil  then show ?case by (auto)
next case Cons then show ?case by (case_tac f, auto)
qed


lemma vval_typing_all_record:
assumes "\<Xi> \<turnstile>* vs :v ts"
shows "\<Xi> \<turnstile>* vs :vr zip ts (replicate (length ts) False)"
using assms[simplified vval_typing_all_def] proof (induct rule: list_all2_induct)
qed (auto intro: vval_typing_vval_typing_record.intros)

lemma vval_typing_record_take:
assumes "\<Xi> \<turnstile>* ts :vr \<tau>s"
and     "\<tau>s ! f = (t, False)"
and     "[] \<turnstile> t :\<kappa> k"
and     "S \<in> k \<or> taken"
shows   "\<Xi> \<turnstile>* ts :vr \<tau>s[ f := (t, taken) ]"
using assms proof (induct ts arbitrary: \<tau>s f)
     case Nil  then show ?case by ( force intro: vval_typing_vval_typing_record.intros)
next case Cons then show ?case by ( cases taken
                                  , (force split: nat.split
                                           intro: vval_typing_vval_typing_record.intros)+ )
qed

lemma vval_typing_record_put:
assumes "\<Xi> \<turnstile>* ts :vr \<tau>s"
and     "\<tau>s ! f = (t, taken)"
and     "[] \<turnstile> t :\<kappa> k"
and     "D \<in> k \<or> taken"
and     "\<Xi> \<turnstile> v :v t"
shows   "\<Xi> \<turnstile>* ts[ f := v ] :vr \<tau>s[ f := (t, False) ]"
using assms proof (induct ts arbitrary: \<tau>s f)
     case Nil  then show ?case by ( force intro: vval_typing_vval_typing_record.intros)
next case Cons then show ?case by ( cases taken
                                  , (fastforce split: nat.split
                                               intro: vval_typing_vval_typing_record.intros)+ )
qed

subsection {* Sums and subtyping *}

lemma width_subtyping:
assumes "set ts \<subseteq> set us"
and     "\<Xi> \<turnstile> v :v TSum ts"
and     "[] \<turnstile> TSum us wellformed"
shows   "\<Xi> \<turnstile> v :v TSum us"
using assms
by (force intro: vval_typing_vval_typing_record.intros)

lemma sum_downcast:
  assumes vval_tsum_ts: "\<Xi> \<turnstile> VSum tag v :v TSum ts"
    and   tag_neq_tag': "tag \<noteq> tag'"
    and   tag'_in_ts  : "(tag', \<tau>, False) \<in> set ts"
  shows   "\<Xi> \<turnstile> VSum tag v :v TSum (tagged_list_update tag' (\<tau>, True) ts)"
proof -
  from vval_tsum_ts
  obtain k \<tau>1
    where "\<Xi> \<turnstile> v :v \<tau>1"
    and tag_in_ts: "(tag, \<tau>1, False) \<in> set ts"
    and ts_distinct: "distinct (map fst ts)"
    and ts_wellformed: "[] \<turnstile>* map (fst \<circ> snd) ts :\<kappa> k"
    by force
  moreover have 1: "(\<lambda> x. x \<noteq> tag') \<circ> fst = (\<lambda> x. fst x \<noteq> tag')" by force
  moreover have 2: "map fst [x\<leftarrow>ts. fst x \<noteq> tag'] = [x\<leftarrow>map fst ts. x \<noteq> tag']" by (simp add: 1 filter_map)
  ultimately show ?thesis
    using assms
  proof (intro v_t_sum)
    show "(tag, \<tau>1, False) \<in> set (tagged_list_update tag' (\<tau>, True) ts)"
      using tag_in_ts tag_neq_tag' tagged_list_update_different_tag_preserves_values2
      by metis
  next
    obtain i where "ts ! i = (tag', \<tau> , False)"
               and "i < length ts"
      using tag'_in_ts in_set_conv_nth
      by metis
    moreover then have "[] \<turnstile>  \<tau> :\<kappa>  k"
      and "\<And>tag \<tau>' b. (tag, \<tau>', b) \<in> set ts \<Longrightarrow> [] \<turnstile>  \<tau>' :\<kappa>  k"
      using tag'_in_ts kinding_all_set ts_wellformed by auto
    moreover then have "\<And>tag \<tau>' b. (tag, \<tau>', b) \<in> set (ts[i := (tag', \<tau>, True)]) \<Longrightarrow> [] \<turnstile>  \<tau>' :\<kappa>  k"
      by (metis (no_types, lifting) fst_conv in_set_conv_nth length_list_update nth_list_update_eq nth_list_update_neq snd_conv)
    ultimately have "[] \<turnstile>* map (fst \<circ> snd) (tagged_list_update tag' (\<tau>, True) ts) :\<kappa> k"
      using kinding_all_set ts_distinct
      by (auto simp add: tagged_list_update_distinct)
    then show "[] \<turnstile>* map (fst \<circ> snd) (tagged_list_update tag' (\<tau>, True) ts) wellformed"
      using ts_distinct kinding_all_set
      by auto
  qed simp+
qed

subsection {* Introductions under instantiations *}

text {* An alternative introduction rule used for showing a value is a function under some type instantiation *}

lemma v_t_afun_instantiate:
assumes "list_all2 (kinding K') ts K"
and     "list_all2 (kinding []) \<delta> K'"
and     "K \<turnstile> t wellformed"
and     "K \<turnstile> u wellformed"
and     "\<Xi> f = (K, t, u)"
shows   "\<Xi> \<turnstile> VAFunction f (map (instantiate \<delta>) ts) :v TFun (instantiate \<delta> (instantiate ts t))
                                                           (instantiate \<delta> (instantiate ts u))"
proof -
from assms have "TFun (instantiate \<delta> (instantiate ts t))
                      (instantiate \<delta> (instantiate ts u))
               = TFun (instantiate (map (instantiate \<delta>) ts) t)
                      (instantiate (map (instantiate \<delta>) ts) u)"
           by (force intro: instantiate_instantiate dest: list_all2_lengthD)
with assms show ?thesis by (force intro: vval_typing_vval_typing_record.intros
                                         list_all2_substitutivity
                                         kinding_kinding_all_kinding_record.intros)
qed

lemma v_t_function_instantiate:
  assumes "\<Xi>, K, [Some t] \<turnstile> f : u"
  and     "K \<turnstile> t wellformed"
  and     "list_all2 (kinding []) \<delta> K'"
  assumes "list_all2 (kinding K') ts K"
  shows   "\<Xi> \<turnstile> VFunction f (map (instantiate \<delta>) ts) :v TFun (instantiate \<delta> (instantiate ts t))
                                                            (instantiate \<delta> (instantiate ts u))"
proof -
from assms have "TFun (instantiate \<delta> (instantiate ts t))
                      (instantiate \<delta> (instantiate ts u))
               = TFun (instantiate (map (instantiate \<delta>) ts) t)
                      (instantiate (map (instantiate \<delta>) ts) u)"
           by (force intro: instantiate_instantiate dest: list_all2_lengthD dest!: typing_to_kinding)
with assms show ?thesis by (force intro: vval_typing_vval_typing_record.intros
                                         list_all2_substitutivity
                                         kinding_kinding_all_kinding_record.intros)
qed

section {* matches lemmas *}

subsection {* matches + context manipulation *}
lemma matches_split':
assumes "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
and     "\<Xi> \<turnstile> \<gamma> matches \<Gamma>"
shows   "\<Xi> \<turnstile> \<gamma> matches \<Gamma>1"
and     "\<Xi> \<turnstile> \<gamma> matches \<Gamma>2"
using assms proof (induct arbitrary: \<gamma> rule: split.induct)
     case split_empty
       case 1 then show ?case by simp
       case 2 then show ?case by simp
next case split_cons note prems = this
       case 1 with prems show ?case by (force simp:  matches_def
                                              iff:   list_all2_Cons2
                                              elim!: split_comp.cases)
       case 2 with prems show ?case by (force simp:  matches_def
                                              iff:   list_all2_Cons2
                                              elim!: split_comp.cases)
qed

lemma matches_split:
assumes "\<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>)"
and     "list_all2 (kinding []) \<tau>s K"
and     "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
shows   "\<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>1)"
and     "\<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>2)"
using assms by (auto intro: matches_split' instantiate_ctx_split)


lemma matches_split2:
assumes "\<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>)"
and     "list_all2 (kinding []) \<tau>s K"
and     "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
shows   "(\<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>1)) \<and> (\<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>2))"
using assms by (auto dest: matches_split)


lemma matches_splitE:
assumes "\<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>)"
and     "list_all2 (kinding []) \<tau>s K"
and     "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
and     "\<lbrakk> \<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>1) ; \<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>2) \<rbrakk> \<Longrightarrow> P"
shows   "P"
using assms by (auto dest: matches_split2)


lemma matches_split_bang':
assumes "split_bang [] vs \<Gamma> \<Gamma>1 \<Gamma>2"
and     "\<Xi> \<turnstile> \<gamma> matches \<Gamma>"
shows   "\<Xi> \<turnstile> \<gamma> matches \<Gamma>1"
and     "\<Xi> \<turnstile> \<gamma> matches \<Gamma>2"
using assms proof (induct arbitrary: \<gamma> rule: split_bang.induct)
     case split_bang_empty
       case 1 then show ?case by simp
       case 2 then show ?case by simp
next case split_bang_cons note prems = this
       case 1 with prems show ?case by (force simp:  matches_def
                                              iff:   list_all2_Cons2
                                              elim!: split_comp.cases)
       case 2 with prems show ?case by (force simp:  matches_def
                                              iff:   list_all2_Cons2
                                              elim!: split_comp.cases)
next case split_bang_bang note prems = this
       case 1 with prems show ?case by (force simp: matches_def
                                              iff:  list_all2_Cons2
                                              dest: vval_typing_bang)
       case 2 with prems show ?case by (force simp: matches_def
                                              iff:  list_all2_Cons2
                                              dest: vval_typing_bang)
qed


lemma matches_split_bang:
assumes "\<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>)"
and     "list_all2 (kinding []) \<tau>s K"
and     "split_bang K vs \<Gamma> \<Gamma>1 \<Gamma>2"
shows   "\<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>1)"
and     "\<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>2)"
using assms by (auto intro: matches_split_bang' instantiate_ctx_split_bang)

lemma matches_weakening':
assumes "\<Xi> \<turnstile> \<gamma> matches \<Gamma>"
and     "[] \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
shows   "\<Xi> \<turnstile> \<gamma> matches \<Gamma>'"
using assms(2) [simplified weakening_def]
  and assms(1) proof(induct  arbitrary: \<gamma> rule: list_all2_induct)
     case Nil  then show ?case by simp
next case Cons then show ?case by (force simp:  matches_def
                                         iff:   list_all2_Cons2
                                         elim!: weakening_comp.cases)
qed

lemma matches_weakening:
assumes "\<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>)"
and     "list_all2 (kinding []) \<tau>s K"
and     "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
shows   "\<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>')"
using assms by (auto dest: instantiate_ctx_weaken intro: matches_weakening')

lemma matches_cons':
assumes "\<Xi> \<turnstile> \<gamma> matches \<Gamma>"
and     "\<Xi> \<turnstile> x :v \<tau>"
shows   "\<Xi> \<turnstile> (x # \<gamma>) matches (Some \<tau> # \<Gamma>)"
using assms by (simp add: matches_def)

lemma matches_cons:
assumes "list_all2 (kinding []) \<tau>s K"
and     "\<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>)"
and     "\<Xi> \<turnstile> x :v instantiate \<tau>s \<tau>"
shows   "\<Xi> \<turnstile> (x # \<gamma>) matches (instantiate_ctx \<tau>s (Some \<tau> # \<Gamma>))"
using assms by (auto intro: matches_cons')

lemma matches_empty':
shows "\<Xi> \<turnstile> [] matches []"
by (simp add: matches_def)

lemma matches_empty:
shows "\<Xi> \<turnstile> [] matches instantiate_ctx \<tau>s []"
by (simp add: matches_empty' instantiate_ctx_def)

subsection {* other matches properties *}

lemma matches_length:
assumes "\<Xi> \<turnstile> \<gamma> matches \<Gamma>"
shows   "length \<gamma> = length \<Gamma>"
using assms by (simp add: matches_def list_all2_lengthD)

lemma matches_proj':
assumes "\<Xi> \<turnstile> \<gamma> matches \<Gamma>"
and     "i < length \<Gamma>"
and     "\<Gamma> ! i = Some \<tau>"
shows   "\<Xi> \<turnstile> (\<gamma> ! i) :v \<tau>"
using assms by (auto dest: list_all2_nthD2
                     simp: matches_def
                     intro: vval_typing_vval_typing_record.intros)

lemma matches_proj:
assumes "list_all2 (kinding []) \<tau>s K"
and     "\<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>)"
and     "i < length \<Gamma>"
and     "\<Gamma> ! i = Some \<tau>"
shows   "\<Xi> \<turnstile> (\<gamma> ! i) :v instantiate \<tau>s \<tau>"
using assms by (auto intro: matches_proj' simp: instantiate_ctx_def)


section {* procedure environment matches *}
lemma proc_env_matches_abstract:
assumes "\<xi> matches \<Xi>"
and     "\<Xi> f = (K, \<tau>i, \<tau>o)"
and     "list_all2 (kinding []) \<tau>s K"
and     "\<Xi> \<turnstile> v    :v instantiate \<tau>s \<tau>i"
and     "\<xi> f v v'"
shows   "\<Xi> \<turnstile> v' :v instantiate \<tau>s \<tau>o"
using assms by ( clarsimp simp: proc_env_matches_def
               , drule_tac x = f in spec
               , auto)


section {* Type Safety *}

theorem progress:
assumes "\<Xi>, K, \<Gamma> \<turnstile> e : \<tau>"
and     "\<xi> matches \<Xi>"
and     "list_all2 (kinding []) \<tau>s K"
and     "\<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>)"
shows   "\<exists>! v. \<xi>, \<gamma> \<turnstile> specialise \<tau>s e \<Down> v"
oops

lemma v_t_map_TPrimD:
  "\<Xi> \<turnstile>* vs :v map TPrim \<tau>s
    \<Longrightarrow> \<exists>lits. vs = map VPrim lits \<and> map lit_type lits = \<tau>s"
  unfolding vval_typing_all_def list_all2_map2
  apply (induct rule: list_all2_induct, simp_all)
  apply clarsimp
  apply (erule vval_typing.cases, simp_all)
  apply (rule exI[where x="x # xs" for x xs], simp)
  done

lemma eval_prim_preservation:
assumes "prim_op_type p = (\<tau>s, \<tau>)"
and     "\<Xi> \<turnstile>* vs :v map TPrim \<tau>s"
shows   "\<Xi> \<turnstile>  eval_prim p vs :v TPrim \<tau>"
using assms v_t_prim[where \<Xi>=\<Xi> and l="case eval_prim p vs of VPrim v \<Rightarrow> v"]
by (clarsimp simp add: eval_prim_def o_def eval_prim_op_lit_type dest!: v_t_map_TPrimD)

theorem preservation:
assumes "list_all2 (kinding []) \<tau>s K"
and     "proc_ctx_wellformed \<Xi>"
and     "\<Xi> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>)"
and     "\<xi> matches \<Xi>"
shows   "\<lbrakk> \<xi>, \<gamma> \<turnstile>  specialise \<tau>s e \<Down> v  ; \<Xi>, K, \<Gamma> \<turnstile>  e  : \<tau>  \<rbrakk> \<Longrightarrow> \<Xi> \<turnstile>  v  :v instantiate \<tau>s \<tau>"
and     "\<lbrakk> \<xi>, \<gamma> \<turnstile>* map (specialise \<tau>s) es \<Down> vs ; \<Xi>, K, \<Gamma> \<turnstile>* es : \<tau>s' \<rbrakk> \<Longrightarrow> \<Xi> \<turnstile>* vs :v map (instantiate \<tau>s) \<tau>s'"
using assms proof (induct "specialise \<tau>s e"        v
                      and "map (specialise \<tau>s) es" vs
                      arbitrary: e  \<tau>s K \<tau>   \<Gamma>
                             and es \<tau>s K \<tau>s' \<Gamma>
                      rule: v_sem_v_sem_all.inducts)
     case v_sem_var     then show ?case by ( case_tac e, simp_all
                                           , fastforce dest:  matches_weakening
                                                       intro: matches_proj
                                                       simp:  empty_length empty_def)
next case v_sem_lit     then show ?case by ( case_tac e, simp_all
                                           , fastforce intro: vval_typing_vval_typing_record.intros)
next case v_sem_prim    then show ?case by ( case_tac e, simp_all
                                           , fastforce intro: eval_prim_preservation)
next case v_sem_cast    then show ?case by ( case_tac e, simp_all
                                           , fastforce elim!: upcast_valid_cast_to)
next case v_sem_afun    then show ?case by ( case_tac e, simp_all
                                           , fastforce intro: v_t_afun_instantiate)
next case v_sem_fun     then show ?case by ( case_tac e, simp_all
                                           , fastforce intro: v_t_function_instantiate)
next case (v_sem_con \<xi> \<gamma> x_spec x' ts_inst tag)
  then show ?case
  proof (cases e)
    case (Con ts tag' x)

    have tag'_is: "tag' = tag"
      and ts_inst_is: "ts_inst = map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts"
      and x_spec_is: "x_spec = specialise \<tau>s x"
      using v_sem_con.hyps(3) Con
      by clarsimp+
    moreover then obtain t k ts'
      where \<tau>_is: "\<tau> = TSum ts'"
        and typing_x: "\<Xi>, K, \<Gamma> \<turnstile> x : t"
        and tag_in_ts: "(tag, t, False) \<in> set ts"
        and distinct_ts: "distinct (map fst ts')"
        and tags_same: "map fst ts = map fst ts'"
        and types_same: "map (fst \<circ> snd) ts = map (fst \<circ> snd) ts'"
        and taken_subcond: "list_all2 (\<lambda>x y. snd (snd y) \<longrightarrow> snd (snd x)) ts ts'"
        and ts_wellformed: "K \<turnstile>* (map (fst \<circ> snd) ts') :\<kappa> k"
      using Con v_sem_con.prems by auto
    ultimately have "\<Xi> \<turnstile> VSum tag x' :v TSum (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts')"
    proof (intro v_t_sum)
      show "\<Xi> \<turnstile> x' :v instantiate \<tau>s t"
        using v_sem_con.hyps(2) v_sem_con.prems x_spec_is typing_x tag_in_ts
        by simp
    next
      obtain i
        where "ts ! i = (tag, t, False)"
          and i_in_bounds: " i < length ts"
        by (meson in_set_conv_nth tag_in_ts)
      moreover then have "snd (snd (ts' ! i)) \<longrightarrow> False"
        using list_all2_nthD taken_subcond by fastforce
      ultimately have
        "fst (ts' ! i) = tag"
        "fst (snd (ts' ! i)) = t"
        "snd (snd (ts' ! i)) = False"
        using tags_same types_same fst_conv length_map nth_map comp_def snd_conv
        by metis+
      then have "ts' ! i = (tag, t, False)"
        by (metis (full_types) prod.collapse)
      then show "(tag, instantiate \<tau>s t, False) \<in> set (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts')"
        using i_in_bounds in_set_conv_nth length_map nth_map old.prod.case tags_same
        by (metis (no_types, lifting))
    next
      have "[] \<turnstile>* map (instantiate \<tau>s \<circ> (fst \<circ> snd)) ts' :\<kappa>  k"
        using ts_wellformed substitutivity(2) v_sem_con.prems(2) by fastforce
      then show "[] \<turnstile>* map (fst \<circ> snd) (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts') wellformed"
        by auto
    qed simp+
    then show ?thesis
      using \<tau>_is by auto
  qed simp+
next case v_sem_member  then show ?case by ( case_tac e, simp_all
                                           , fastforce intro: vval_typing_record_nth)
next case v_sem_unit    then show ?case by ( case_tac e, simp_all
                                           , fastforce intro: vval_typing_vval_typing_record.intros)
next case v_sem_tuple   then show ?case by ( case_tac e, simp_all
                                           , fastforce intro: matches_split
                                                              vval_typing_vval_typing_record.intros)
next case v_sem_case_m  then show ?case by ( case_tac e, simp_all
                                           , fastforce intro: matches_split
                                                              matches_cons [simplified]
                                                       dest:  distinct_fst)
next case (v_sem_case_nm \<xi> \<gamma> x tag' v tag n n' m)
  from v_sem_case_nm.hyps(6)
  show ?case
  proof (case_tac e, simp_all, clarsimp)
    fix x1 x3 x4
    assume e_is: "e = Case x1 tag x3 x4"
      and x_is: "x = specialise \<tau>s x1"
      and m_is: "m = specialise \<tau>s x3"
      and n_is: "n = specialise \<tau>s x4"

    then obtain \<Gamma>1 \<Gamma>2 ts ta where split\<Gamma>: "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
      and typing_x1: "\<Xi>, K, \<Gamma>1 \<turnstile> x1 : TSum ts"
      and ta_in_ts: "(tag, ta, False) \<in> set ts"
      and typing_x3: "\<Xi>, K, Some ta # \<Gamma>2 \<turnstile> x3 : \<tau>"
      and typing_x4: "\<Xi>, K, Some (TSum (tagged_list_update tag (ta, True) ts)) # \<Gamma>2 \<turnstile> x4 : \<tau>"
      using v_sem_case_nm.prems
      by fastforce

    from split\<Gamma>
    have \<gamma>_matches_\<Gamma>1: "\<Xi> \<turnstile> \<gamma> matches instantiate_ctx \<tau>s \<Gamma>1"
      and \<gamma>_matches_\<Gamma>2: "\<Xi> \<turnstile> \<gamma> matches instantiate_ctx \<tau>s \<Gamma>2"
      using matches_split2 v_sem_case_nm.prems
      by fastforce+

    have "\<Xi> \<turnstile> VSum tag' v :v instantiate \<tau>s (TSum ts)"
      using x_is typing_x1 \<gamma>_matches_\<Gamma>1 v_sem_case_nm.hyps(2) v_sem_case_nm.prems
      by fastforce
    then have "\<Xi> \<turnstile> VSum tag' v :v TSum (tagged_list_update tag (instantiate \<tau>s ta, True) (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts))"
      using v_sem_case_nm.hyps(3) image_iff ta_in_ts
      by (fastforce intro!: sum_downcast)
    then have "\<Xi> \<turnstile> VSum tag' v :v instantiate \<tau>s (TSum (tagged_list_update tag (ta, True) ts))"
      by (simp add: tagged_list_update_map_over2[where f="\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)" and g="\<lambda>(t,b). (instantiate \<tau>s t, b)"] case_prod_beta)
    then show "\<Xi> \<turnstile> n' :v instantiate \<tau>s \<tau>"
      using v_sem_case_nm.prems v_sem_case_nm.hyps(5) \<gamma>_matches_\<Gamma>2 matches_cons
        n_is typing_x4
      by blast
  qed
next case (v_sem_esac \<xi> \<gamma> t tag v)
  from v_sem_esac.hyps(3)
  show ?case
  proof (case_tac e, simp_all)
    fix x
    assume e_is: "e = Esac x"
       and t_is: "t = specialise \<tau>s x"
    then have "\<Xi>, K, \<Gamma> \<turnstile> Esac x : \<tau>"
      using v_sem_esac.prems
      by simp
    then obtain ts' tag' where x_typing: "\<Xi>, K, \<Gamma> \<turnstile> x : TSum ts'"
                           and one_left: "[(tag', \<tau>, False)] = filter (HOL.Not \<circ> snd \<circ> snd) ts'"
      by blast

    have "\<Xi> \<turnstile> VSum tag v :v instantiate \<tau>s (TSum ts')"
      using t_is v_sem_esac.hyps(2) v_sem_esac.prems x_typing
      by blast
    then obtain \<tau>' k where v_vval_typing: "\<Xi> \<turnstile> v :v instantiate \<tau>s \<tau>'"
                       and instantiated_\<tau>'_in_ts': "(tag, instantiate \<tau>s \<tau>', False) \<in> set (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts')"
                       and distinct_fst_ts': "distinct (map fst ts')"
                       and instantiate_ts'_wellformed: "[] \<turnstile>* map (fst \<circ> snd) (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts') :\<kappa> k"
      by force

    have "\<And>tag \<tau>. (tag, \<tau>, False) \<in> set ts' \<Longrightarrow> tag = tag'"
      by (metis bex_empty filter_set list.set(1) member_filter o_apply one_left prod.inject set_ConsD snd_conv)
    then have "tag = tag'"
      using instantiated_\<tau>'_in_ts'
      by force
    then have "instantiate \<tau>s \<tau>' = instantiate \<tau>s \<tau>"
      using distinct_fst_ts' one_left instantiated_\<tau>'_in_ts' distinct_fst filtered_member
      by fastforce
    then show "\<Xi> \<turnstile> v :v instantiate \<tau>s \<tau>"
      using v_vval_typing
      by force
  qed
next case v_sem_let     then show ?case by ( case_tac e, simp_all
                                           , fastforce dest:   matches_split
                                                       intro!: matches_cons [simplified])
next case v_sem_letbang then show ?case by ( case_tac e, simp_all
                                           , fastforce dest:   matches_split_bang
                                                       intro!: matches_cons [simplified])
next case v_sem_if      then show ?case by ( case_tac e, simp_all
                                           , fastforce intro:  matches_split
                                                       split:  if_splits)
next case v_sem_struct  then show ?case by ( case_tac e, simp_all
                                           , fastforce intro: vval_typing_vval_typing_record.intros
                                                              vval_typing_all_record [ where ts = "map f ts" for f ts
                                                                                     , simplified])
next case v_sem_take    then show ?case apply (case_tac e, simp_all, clarsimp elim!: typing_takeE)
                                        apply (drule(2) matches_split2)
                                        apply (fastforce intro!: matches_cons
                                                                 vval_typing_vval_typing_record.intros
                                                                 vval_typing_record_take
                                                                 vval_typing_record_nth
                                                         simp:   map_update
                                                         intro:  substitutivity)
                                        done (* TODO automate properly *)
next case v_sem_put     then show ?case by ( case_tac e, simp_all
                                           , fastforce simp:  map_update
                                                       intro: vval_typing_vval_typing_record.intros
                                                              vval_typing_record_put
                                                              substitutivity
                                                              matches_split)
next case v_sem_split   then show ?case by ( case_tac e, simp_all
                                           , fastforce intro!: matches_cons
                                                       intro:  matches_split)
next case (v_sem_app \<xi> \<gamma> x ea ts y a r e \<tau>s K \<tau> \<Gamma>)
note IH1  = this(2)
and  IH2  = this(4)
and  IH3  = this(6)
and  rest = this(1,3,5,7-)
from rest show ?case
  apply (case_tac e, simp_all)
  apply (clarsimp)
  apply (fastforce elim!: typing_appE
                   dest!: IH1 [OF _ _ _ _ matches_split(1)]
                          IH2 [OF _ _ _ _ matches_split(2)]
                   intro: IH3
                   simp:  matches_def
                          instantiate_ctx_def).
next case v_sem_abs_app
note IH1  = this(2)
and  IH2  = this(4)
and  rest = this(1,3,5-)
from rest show ?case
  apply (case_tac e, simp_all)
  apply (clarsimp elim!: typing_appE)
  apply (frule(7) IH1 [OF _ _ _ _ matches_split(1)])
  apply (frule(7) IH2 [OF _ _ _ _ matches_split(2)])
  apply (fastforce intro: proc_env_matches_abstract).
next case v_sem_all_empty then show ?case by ( case_tac es, simp_all
                                             , fastforce simp: vval_typing_all_def)
next case v_sem_all_cons  then show ?case by ( case_tac es, simp_all
                                             , fastforce simp: vval_typing_all_def
                                                         dest: matches_split)
qed

(* TODO:
    - A-normal.
*)

lemma order_sum_list: "x \<in> set es \<Longrightarrow> x < Suc (sum_list es)"
  by (simp add: le_imp_less_Suc member_le_sum_list)

function monoexpr :: "'f expr \<Rightarrow> ('f \<times> type list) expr" where
  "monoexpr (AFun f ts)       = AFun (f, ts) []"
| "monoexpr (Fun f ts)        = Fun (monoexpr (specialise ts f)) []"
| "monoexpr (Var i)           = Var i"
| "monoexpr (Prim p es)       = Prim p (map (monoexpr) es)"
| "monoexpr (App a b)         = App (monoexpr a) (monoexpr b)"
| "monoexpr (Con as t e)      = Con as t (monoexpr e)"
| "monoexpr (Struct ts vs)    = Struct ts (map (monoexpr) vs)"
| "monoexpr (Member v f)      = Member (monoexpr v) f"
| "monoexpr (Unit)            = Unit"
| "monoexpr (Cast t e)        = Cast t (monoexpr e)"
| "monoexpr (Lit v)           = Lit v"
| "monoexpr (Tuple a b)       = Tuple (monoexpr a) (monoexpr b)"
| "monoexpr (Put e f e')      = Put (monoexpr e) f (monoexpr e')"
| "monoexpr (Let e e')        = Let (monoexpr e) (monoexpr e')"
| "monoexpr (LetBang vs e e') = LetBang vs (monoexpr e) (monoexpr e')"
| "monoexpr (Case e t a b)    = Case (monoexpr e) t (monoexpr a) (monoexpr b)"
| "monoexpr (Esac e)          = Esac (monoexpr e)"
| "monoexpr (If c t e)        = If (monoexpr c) (monoexpr t) (monoexpr e)"
| "monoexpr (Take e f e')     = Take (monoexpr e) f (monoexpr e')"
| "monoexpr (Split v va)      = Split (monoexpr v) (monoexpr va)"
             by (case_tac x, auto)
termination by (relation "measure expr_size", (simp add: order_sum_list)+)

fun monoval :: "('f, 'a) vval \<Rightarrow> ('f \<times> type list, 'a) vval"
where "monoval (VPrim lit) = VPrim lit"
    | "monoval (VProduct t u) = VProduct (monoval t) (monoval u)"
    | "monoval (VSum name v) = VSum name (monoval v)"
    | "monoval (VRecord vs) = VRecord (map monoval vs)"
    | "monoval (VAbstract t) = VAbstract t"
    | "monoval (VAFunction f ts) = VAFunction (f, ts) []"
    | "monoval (VFunction f ts) = VFunction (monoexpr (specialise ts f)) []"
    | "monoval VUnit = VUnit"


definition monoprog :: "('f, 'a) vabsfuns \<Rightarrow> (('f \<times> type list), 'a) vabsfuns \<Rightarrow> bool"
where "monoprog \<xi> \<xi>' \<equiv> \<forall>f \<tau>s. (\<forall>v v'. \<xi> f v v' \<longleftrightarrow> \<xi>' (f, \<tau>s) (monoval v) (monoval v'))"


lemma member_nth_map: "f < length fs \<Longrightarrow> \<xi>', map monoval \<gamma> \<turnstile> Member (monoexpr e) f \<Down> monoval (fs ! f) =  \<xi>' , map monoval \<gamma> \<turnstile> Member (monoexpr e) f \<Down> (map monoval fs) ! f"
by (subst nth_map, simp_all)
thm v_sem_prim

lemma v_sem_prim': "\<xi> , \<gamma> \<turnstile>* as \<Down> as' \<Longrightarrow> eval_prim p as' = r \<Longrightarrow> \<xi> , \<gamma> \<turnstile> Prim p as \<Down> r"
by (force dest: sym intro: v_sem_prim)

lemma monoval_vprim [simp]: "monoval \<circ> VPrim = VPrim" by (rule ext, simp)

lemma eval_prim_type_change:
assumes "(eval_prim :: prim_op \<Rightarrow> ('f1, 'a1) vval list \<Rightarrow> ('f1, 'a1) vval) p (map VPrim lits) = VPrim l"
shows "(eval_prim :: prim_op \<Rightarrow> ('f2, 'a2) vval list \<Rightarrow> ('f2, 'a2) vval) p (map VPrim lits) = VPrim l"
proof -
have helper: "(\<lambda>vv. case vv of VPrim v \<Rightarrow> v | _ \<Rightarrow> LBool False) \<circ> VPrim = id" by (rule ext, simp)
then show ?thesis using assms by (simp add: eval_prim_def helper)
qed

lemma mono_correct:
assumes "\<xi> matches \<Xi>"
and     "proc_ctx_wellformed \<Xi>"
and     "\<Xi> \<turnstile> \<gamma> matches \<Gamma>"
and     "monoprog \<xi> \<xi>'"
shows   "\<xi>, \<gamma> \<turnstile> e \<Down> e' \<Longrightarrow>  \<Xi>, [], \<Gamma> \<turnstile> e : \<tau>    \<Longrightarrow> \<xi>', map monoval \<gamma> \<turnstile> monoexpr e \<Down> monoval e'"
and     "\<xi>, \<gamma> \<turnstile>* es \<Down> es' \<Longrightarrow> \<Xi>, [], \<Gamma> \<turnstile>* es : \<tau>s \<Longrightarrow> \<xi>', map monoval \<gamma> \<turnstile>* map monoexpr es \<Down> map monoval es'"
using assms proof (induct \<xi> \<gamma> e e'
                      and \<xi> \<gamma> es es'
               arbitrary: \<tau> \<Gamma>
                      and \<tau>s \<Gamma>
                    rule: v_sem_v_sem_all.inducts)
case v_sem_app
note IH1 = this(2)
and  IH2 = this(4)
and  IH3 = this(6)
and  rest = this(1,3,5,7-)
then show ?case
  apply (clarsimp)
  apply (erule typing_appE)
  apply (rule, erule(5) IH1 [OF _ _ _ matches_split'(1), simplified], erule(5) IH2 [OF _ _ _ matches_split'(2), simplified])
  apply (simp)
  apply (frule(5) preservation(1) [where \<tau>s = "[]" and K = "[]", OF _ _ matches_split'(1), simplified])
  apply (frule(5) preservation(1) [where \<tau>s = "[]" and K = "[]", OF _ _ matches_split'(2), simplified])
  apply (auto elim!: v_t_funE
              intro: IH3 [simplified] specialisation
              simp:  matches_def instantiate_ctx_def)
done
next case v_sem_abs_app
note IH1  = this(2)
and  IH2  = this(4)
and  rest = this(1,3,5-)
then show ?case
  apply (clarsimp)
  apply (erule typing_appE)
  apply (rule v_sem_v_sem_all.v_sem_abs_app, erule(5) IH1 [OF _ _ _ matches_split'(1), simplified], erule(5) IH2 [OF _ _ _ matches_split'(2), simplified])
  apply (simp add: monoprog_def)
done
next case v_sem_var then show ?case by (simp, metis matches_length nth_map typing_varE v_sem_v_sem_all.v_sem_var)
next case v_sem_lit then show ?case by (fastforce intro!: v_sem_v_sem_all.v_sem_lit)
next case v_sem_fun then show ?case by (fastforce intro!: v_sem_v_sem_all.v_sem_fun)
next case v_sem_afun then show ?case by (fastforce intro!: v_sem_v_sem_all.v_sem_afun)
next case v_sem_cast then show ?case by (fastforce intro!: v_sem_v_sem_all.v_sem_cast)
next case v_sem_con then show ?case by (fastforce intro!: v_sem_v_sem_all.v_sem_con)
next case v_sem_unit then show ?case by (simp add: v_sem_v_sem_all.v_sem_unit)
next case v_sem_tuple then show ?case by (clarsimp elim!: typing_tupleE simp: matches_split' v_sem_v_sem_all.v_sem_tuple)
next case v_sem_esac then show ?case by (fastforce intro!: v_sem_v_sem_all.v_sem_esac)
next case v_sem_take
note IH1 = this(2)
and  IH2 = this(4)
and rest = this(1,3,5-)
from rest show ?case
  apply (clarsimp elim!: typing_takeE)
  apply (frule(1) matches_split'(1))
  apply (frule(1) matches_split'(2))
  apply (rule v_sem_v_sem_all.v_sem_take)
   apply (frule(5) IH1[simplified])
  apply (frule(4) preservation [where \<tau>s = "[]" and K = "[]", simplified, rotated -3])
  apply (erule v_t_recordE, simp)
  apply (frule(2) IH2[simplified])
    apply (rule matches_cons')
     apply (rule matches_cons')
      apply (simp)
     apply (frule(3) vval_typing_record_take)
     apply (rule)
     apply (simp)
    apply (frule(4) vval_typing_record_nth)
  apply (simp add: vval_typing_record_length)
done
next case v_sem_all_empty then show ?case by (simp add: v_sem_v_sem_all.v_sem_all_empty)
next case v_sem_all_cons then show ?case by (auto elim!: typing_all_consE dest: matches_split' intro!: v_sem_v_sem_all.intros)
next case v_sem_split
note IH1 = this(2)
and  IH2 = this(4)
and rest = this(1,3,5-)
from rest show ?case
  apply (clarsimp elim!: typing_splitE)
  apply (frule(1) matches_split'(1))
  apply (frule(1) matches_split'(2))
  apply (rule v_sem_v_sem_all.v_sem_split)
   apply (frule(5) IH1[simplified])
   apply (force dest: preservation [where \<tau>s = "[]" and K = "[]", simplified, rotated -3]
                      IH2
                simp: matches_def
                elim: v_t_productE)
done
next case v_sem_member then show ?case
  apply (clarsimp elim!: typing_memberE)
  apply (subst member_nth_map
        , (force dest:preservation [where \<tau>s = "[]" and K = "[]", simplified] elim!: v_t_recordE dest: vval_typing_record_length intro: v_sem_v_sem_all.intros)+
        )
done
next case v_sem_prim
note IH = this(2)
and rest = this(1,3-)
from rest show ?case
  apply (clarsimp elim!: typing_primE)
  apply (frule(4) preservation(2) [where \<tau>s = "[]" and K = "[]", simplified])
  apply (frule v_t_map_TPrimD)
  apply (clarsimp)
  apply (frule eval_prim_preservation)
  apply (simp)
  apply (erule vval_typing.cases, simp_all)
  apply (rule v_sem_prim')
  apply (clarsimp)
  apply (erule(4) IH)
  apply (force intro: eval_prim_type_change)
done
next case v_sem_struct then show ?case by (fastforce intro!: v_sem_v_sem_all.v_sem_struct)
next case v_sem_case_m then show ?case
    apply (clarsimp elim!: typing_caseE)
    apply (frule(1) matches_split'(1))
    apply (frule(1) matches_split'(2))
    apply (rule v_sem_v_sem_all.intros, fastforce)
    apply (frule(4) preservation [where \<tau>s = "[]" and K = "[]", simplified, rotated -3])
    apply (erule v_t_sumE', simp)
    apply (metis Pair_inject distinct_fst matches_cons')
    done
next case v_sem_case_nm
note IH1 = this(2)
and  IH2 = this(5)
and rest = this(1,3-4,6-)
from rest show ?case
  apply (clarsimp elim!: typing_caseE)
  apply (frule(1) matches_split'(1))
  apply (frule(1) matches_split'(2))
  apply (rule v_sem_v_sem_all.intros, frule(6) IH1[simplified])
  apply (frule(3) IH2[OF _ _ _ matches_cons', simplified])
  apply simp_all
  apply (force intro: sum_downcast dest: preservation[where \<tau>s = "[]" and K = "[]", simplified])
  done
next case v_sem_let
note IH1 = this(2)
and  IH2 = this(4)
and rest = this(1,3,5-)
from rest show ?case
  apply (clarsimp elim!: typing_letE)
  apply (frule(1) matches_split'(1))
  apply (frule(1) matches_split'(2))
  apply (frule(4) preservation [where \<tau>s = "[]" and K = "[]", simplified])
  apply (erule(4) v_sem_v_sem_all.v_sem_let [OF IH1])
  apply (frule(5) IH2 [OF _ _ _ matches_cons', simplified])
  apply simp
done
next case v_sem_letbang
note IH1 = this(2)
and  IH2 = this(4)
and rest = this(1,3,5-)
from rest show ?case
  apply (clarsimp elim!: typing_letbE)
  apply (frule(1) matches_split_bang'(1))
  apply (frule(1) matches_split_bang'(2))
  apply (frule(4) preservation [where \<tau>s = "[]" and K = "[]", simplified])
  apply (erule(4) v_sem_v_sem_all.v_sem_letbang [OF IH1])
  apply (frule(5) IH2 [OF _ _ _ matches_cons', simplified])
  apply simp
done
next case v_sem_if then show ?case by (fastforce elim!: typing_ifE dest: matches_split' intro!: v_sem_v_sem_all.v_sem_if)
next case v_sem_put then show ?case
  apply (clarsimp elim!: typing_putE)
  apply (frule(1) matches_split'(1))
  apply (frule(1) matches_split'(2))
  apply (fastforce simp: map_update intro: v_sem_v_sem_all.v_sem_put)
done
qed

end

end

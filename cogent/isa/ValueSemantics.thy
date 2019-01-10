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
and vval_typing_variant :: "('f \<Rightarrow> poly_type) \<Rightarrow> ('f, 'a) vval list \<Rightarrow> (name \<times> type \<times> variant_state) list \<Rightarrow> bool"
          ("_ \<turnstile>* _ :vv _" [30,0,20] 80)
and vval_typing_record :: "('f \<Rightarrow> poly_type) \<Rightarrow> ('f, 'a) vval list \<Rightarrow> (name \<times> type \<times> record_state) list \<Rightarrow> bool"
          ("_ \<turnstile>* _ :vr _" [30,0,20] 80) where

  v_t_prim     : "\<Xi> \<turnstile> VPrim l :v TPrim (lit_type l)"

| v_t_product  : "\<lbrakk> \<Xi> \<turnstile> a :v t
                  ; \<Xi> \<turnstile> b :v u
                  \<rbrakk> \<Longrightarrow> \<Xi> \<turnstile> VProduct a b :v TProduct t u"

| v_t_sum      : "\<lbrakk> \<Xi> \<turnstile> a :v t
                  ; (g, t, Unchecked) \<in> set ts
                  ; distinct (map fst ts)
                  ; [] \<turnstile> TSum ts wellformed
                  \<rbrakk> \<Longrightarrow> \<Xi> \<turnstile> VSum g a :v TSum ts"

| v_t_record   : "\<lbrakk> \<Xi> \<turnstile>* fs :vr ts
                  ; distinct (map fst ts)
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

| v_t_v_empty  : "\<Xi> \<turnstile>* [] :vr []"
| v_t_v_cons1  : "\<lbrakk> \<Xi> \<turnstile> x :v t
                  ; \<Xi> \<turnstile>* xs :vv ts
                  \<rbrakk> \<Longrightarrow> \<Xi> \<turnstile>* (x # xs) :vv ((n, t, Unchecked) # ts)"
| v_t_v_cons2  : "\<lbrakk> [] \<turnstile> t wellformed
                  ; \<Xi> \<turnstile>* xs :vv ts
                  \<rbrakk> \<Longrightarrow> \<Xi> \<turnstile>* (x # xs) :vv ((n, t, Checked) # ts)"

| v_t_r_empty  : "\<Xi> \<turnstile>* [] :vr []"
| v_t_r_cons1  : "\<lbrakk> \<Xi> \<turnstile> x :v t
                  ; \<Xi> \<turnstile>* xs :vr ts
                  \<rbrakk> \<Longrightarrow> \<Xi> \<turnstile>* (x # xs) :vr ((n, t, Present) # ts)"
| v_t_r_cons2  : "\<lbrakk> [] \<turnstile> t wellformed
                  ; \<Xi> \<turnstile>* xs :vr ts
                  \<rbrakk> \<Longrightarrow> \<Xi> \<turnstile>* (x # xs) :vr ((n, t, Taken) # ts)"


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

inductive_cases v_t_v_emptyE  [elim]: "\<Xi> \<turnstile>* [] :vv \<tau>s"
inductive_cases v_t_v_consE   [elim]: "\<Xi> \<turnstile>* (x # xs) :vv \<tau>s"

inductive_cases v_t_r_emptyE  [elim]: "\<Xi> \<turnstile>* [] :vr \<tau>s"
inductive_cases v_t_r_consE   [elim]: "\<Xi> \<turnstile>* (x # xs) :vr \<tau>s"


definition vval_typing_all :: "('f \<Rightarrow> poly_type) \<Rightarrow> ('f, 'a) vval list \<Rightarrow> type list \<Rightarrow> bool"
           ("_  \<turnstile>* _ :v _" [30,0,20] 80) where
   "(\<Xi> \<turnstile>* vs :v ts) \<equiv> list_all2 (vval_typing \<Xi>) vs ts"

definition matches :: "('f \<Rightarrow> poly_type) \<Rightarrow>  ('f, 'a) vval env \<Rightarrow> ctx \<Rightarrow> bool"
           ("_ \<turnstile> _ matches _" [30,0,20] 60) where
   "\<Xi> \<turnstile> \<gamma> matches \<Gamma> \<equiv> list_all2 (\<lambda> x m. \<forall> \<tau>. m = Some \<tau> \<longrightarrow> \<Xi> \<turnstile> x :v \<tau>) \<gamma> \<Gamma>"

lemmas matches_Cons = list_all2_Cons[where P="(\<lambda>x m. \<forall>\<tau>. m = Some \<tau> \<longrightarrow> \<Xi> \<turnstile> x :v \<tau>)" for \<Xi>, simplified matches_def[symmetric]]

definition proc_env_matches :: "('f \<Rightarrow> ('f, 'a) vval \<Rightarrow> ('f, 'a) vval \<Rightarrow> bool) \<Rightarrow> ('f \<Rightarrow> poly_type) \<Rightarrow> bool"
           ("_ matches _" [30,20] 60) where
  "\<xi> matches \<Xi> \<equiv> (\<forall> f. let (K, \<tau>i, \<tau>o) = \<Xi> f
                        in (\<forall> \<tau>s v v'. list_all2 (kinding []) \<tau>s K
                                  \<longrightarrow> (\<Xi> \<turnstile> v  :v instantiate \<tau>s \<tau>i)
                                  \<longrightarrow> \<xi> f v v'
                                  \<longrightarrow> (\<Xi> \<turnstile> v' :v instantiate \<tau>s \<tau>o)))"


section {* vval_typing lemmas *}

lemma vval_typing_to_wellformed:
  shows "\<Xi> \<turnstile> v :v \<tau>     \<Longrightarrow> [] \<turnstile> \<tau> wellformed"
    and "\<Xi> \<turnstile>* vs :vv cs \<Longrightarrow> [] \<turnstile>* map (fst \<circ> snd) cs wellformed"
    and "\<Xi> \<turnstile>* vs :vr fs \<Longrightarrow> [] \<turnstile>* map (fst \<circ> snd) fs wellformed"
proof (induct rule: vval_typing_vval_typing_variant_vval_typing_record.inducts)
  case v_t_function then show ?case
    by (auto intro!: instantiate_wellformed dest!: typing_to_wellformed
        dest: list_all2_kinding_wellformedD list_all2_lengthD)
next case v_t_afun  then show ?case
    by (auto intro!: instantiate_wellformed dest!: typing_to_wellformed
        dest: list_all2_kinding_wellformedD list_all2_lengthD)
qed (auto intro: supersumption simp add: kinding_simps dest: kinding_all_record'[simplified o_def])

lemma vval_typing_bang:
  shows "\<Xi> \<turnstile> x :v \<tau> \<Longrightarrow> \<Xi> \<turnstile> x :v bang \<tau>"
    and "\<Xi> \<turnstile>* cs :vv \<tau>vs \<Longrightarrow> \<Xi> \<turnstile>* cs :vv map (\<lambda>(n, x, y). (n, bang x, y)) \<tau>vs"
    and "\<Xi> \<turnstile>* fs :vr \<tau>rs \<Longrightarrow> \<Xi> \<turnstile>* fs :vr map (\<lambda>(n, x, y). (n, bang x, y)) \<tau>rs"
proof (induct rule: vval_typing_vval_typing_variant_vval_typing_record.inducts)
     case v_t_sum      then show ?case by (force intro: vval_typing_vval_typing_variant_vval_typing_record.intros
                                                        bang_wellformed rev_image_eqI)
next case v_t_abstract then show ?case by (force intro: vval_typing_vval_typing_variant_vval_typing_record.intros
                                                        abs_typing_bang bang_wellformed)
next case v_t_r_cons2  then show ?case by (force intro: vval_typing_vval_typing_variant_vval_typing_record.intros
                                                        bang_wellformed)
next case v_t_v_cons2  then show ?case by (force intro: vval_typing_vval_typing_variant_vval_typing_record.intros
                                                        bang_wellformed)
qed (force intro: vval_typing_vval_typing_variant_vval_typing_record.intros)+

subsection {* vval_typing_record *}

lemma vval_typing_record_length:
assumes "\<Xi> \<turnstile>* fs :vr \<tau>s"
shows   "length fs = length \<tau>s"
using assms proof (induct fs arbitrary: \<tau>s)
qed (auto)

lemma vval_typing_record_nth:
assumes "\<Xi> \<turnstile>* fs :vr \<tau>s"
and     "\<tau>s ! f = (n, \<tau>, Present)"
and     "f < length \<tau>s"
shows   "\<Xi> \<turnstile> fs ! f :v \<tau>"
using assms proof (induct fs arbitrary: f \<tau>s)
     case Nil  then show ?case by (auto)
next case Cons then show ?case by (case_tac f, auto)
qed


lemma vval_typing_all_record:
  assumes "\<Xi> \<turnstile>* vs :v ts"
  and "length ns = length ts"
shows "\<Xi> \<turnstile>* vs :vr zip ns (zip ts (replicate (length ts) Present))"
  using assms[simplified vval_typing_all_def]
  by (induct arbitrary: ns rule: list_all2_induct)
    (auto simp add: length_Suc_conv intro!: vval_typing_vval_typing_variant_vval_typing_record.intros)

lemma vval_typing_record_take:
  assumes "\<Xi> \<turnstile>* ts :vr \<tau>s"
    and "\<tau>s ! f = (n, t, Present)"
    and "[] \<turnstile> t :\<kappa> k"
    and "S \<in> k \<or> taken = Taken"
  shows "\<Xi> \<turnstile>* ts :vr \<tau>s[ f := (n, t, taken) ]"
  using assms
proof (induct ts arbitrary: \<tau>s n f)
  case (Cons a ts)
  moreover obtain \<tau> \<tau>s' where "\<tau>s = \<tau> # \<tau>s'"
    using Cons.prems by blast
  ultimately show ?case
    by (cases taken, auto dest: kinding_to_wellformedD split: nat.splits
        intro!: vval_typing_vval_typing_variant_vval_typing_record.intros)
qed (force intro: vval_typing_vval_typing_variant_vval_typing_record.intros)

lemma vval_typing_record_put:
assumes "\<Xi> \<turnstile>* ts :vr \<tau>s"
and     "\<tau>s ! f = (n, t, taken)"
and     "[] \<turnstile> t :\<kappa> k"
and     "D \<in> k \<or> taken = Taken"
and     "\<Xi> \<turnstile> v :v t"
shows   "\<Xi> \<turnstile>* ts[ f := v ] :vr \<tau>s[ f := (n, t, Present) ]"
using assms proof (induct ts arbitrary: \<tau>s f)
     case Nil  then show ?case by ( force intro: vval_typing_vval_typing_variant_vval_typing_record.intros)
next case Cons then show ?case by ( cases taken
                                  , (force split: nat.split
                                           intro!: vval_typing_vval_typing_variant_vval_typing_record.intros)+ )
qed

subsection {* Sums and subtyping *}

lemma width_subtyping:
assumes "set ts \<subseteq> set us"
and     "\<Xi> \<turnstile> v :v TSum ts"
and     "[] \<turnstile> TSum us wellformed"
shows   "\<Xi> \<turnstile> v :v TSum us"
using assms
by (force simp add: kinding_simps intro: vval_typing_vval_typing_variant_vval_typing_record.intros)

lemma sum_downcast:
  assumes vval_tsum_ts: "\<Xi> \<turnstile> VSum tag v :v TSum ts"
    and   tag_neq_tag': "tag \<noteq> tag'"
    and   tag'_in_ts  : "(tag', \<tau>, Unchecked) \<in> set ts"
  shows "\<Xi> \<turnstile> VSum tag v :v TSum (tagged_list_update tag' (\<tau>, Checked) ts)"
proof -
  from vval_tsum_ts
  obtain \<tau>1
    where vval_elim_lemmas:
      "\<Xi> \<turnstile> v :v \<tau>1"
      "(tag, \<tau>1, Unchecked) \<in> set ts"
      "distinct (map fst ts)"
      "[] \<turnstile> TSum ts wellformed"
    by force
  then show ?thesis
    using assms
  proof (intro v_t_sum)
    show "(tag, \<tau>1, Unchecked) \<in> set (tagged_list_update tag' (\<tau>, Checked) ts)"
      using vval_elim_lemmas tag_neq_tag' tagged_list_update_different_tag_preserves_values2
      by metis
  next
    show "[] \<turnstile> TSum (tagged_list_update tag' (\<tau>, Checked) ts) wellformed"
      using vval_elim_lemmas tag'_in_ts prod_in_set(1)
      by (fastforce intro!: variant_tagged_list_update_wellformedI)
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
  from assms
  have "TFun (instantiate \<delta> (instantiate ts t))
             (instantiate \<delta> (instantiate ts u))
      = TFun (instantiate (map (instantiate \<delta>) ts) t)
             (instantiate (map (instantiate \<delta>) ts) u)"
    by (force intro: instantiate_instantiate dest: list_all2_lengthD)
  with assms show ?thesis
    by (force simp add: kinding_simps
        intro: vval_typing_vval_typing_variant_vval_typing_record.intros list_all2_substitutivity)
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
           by (force intro: instantiate_instantiate dest: list_all2_lengthD dest!: typing_to_wellformed)
with assms show ?thesis by (force intro: vval_typing_vval_typing_variant_vval_typing_record.intros
                                         list_all2_substitutivity
                                  simp add: kinding_simps)
qed

section {* matches lemmas *}

subsection {* matches + context manipulation *}
lemma matches_split':
assumes "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
and     "\<Xi> \<turnstile> \<gamma> matches \<Gamma>"
shows   "\<Xi> \<turnstile> \<gamma> matches \<Gamma>1"
and     "\<Xi> \<turnstile> \<gamma> matches \<Gamma>2"
proof -
  have "\<And>a x y z. [] \<turnstile> x \<leadsto> y \<parallel> z \<Longrightarrow> \<forall>\<tau>. x = Some \<tau> \<longrightarrow> \<Xi> \<turnstile> a :v \<tau> \<Longrightarrow> (\<forall>\<tau>. y = Some \<tau> \<longrightarrow> \<Xi> \<turnstile> a :v \<tau>) \<and> (\<forall>\<tau>. z = Some \<tau> \<longrightarrow> \<Xi> \<turnstile> a :v \<tau>)"
    by (force simp add: split_comp.simps)
  then show "\<Xi> \<turnstile> \<gamma> matches \<Gamma>1" "\<Xi> \<turnstile> \<gamma> matches \<Gamma>2"
    using list_all3_product_over_list_all2
      [where A="\<lambda>x m. \<forall>\<tau>. m = Some \<tau> \<longrightarrow> \<Xi> \<turnstile> x :v \<tau>" and P="split_comp []",
              simplified matches_def[symmetric] split_def[symmetric]]
    using assms by blast+
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
  using assms
proof (induct arbitrary: \<gamma> rule: split_bang.induct)
  case split_bang_empty
  case 1 then show ?case by simp
  case 2 then show ?case by simp
next case split_bang_cons
  note prems = this
  case 1 with prems show ?case
    by (auto
        elim!: split_comp.cases split_bang_comp.cases
        intro: vval_typing_bang
        simp: matches_def list_all2_Cons2)
  case 2 with prems show ?case
    by (auto
        elim!: split_comp.cases split_bang_comp.cases
        simp: matches_def list_all2_Cons2)
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
                     intro: vval_typing_vval_typing_variant_vval_typing_record.intros)

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
                                           , fastforce intro: vval_typing_vval_typing_variant_vval_typing_record.intros)
next case v_sem_prim    then show ?case by ( case_tac e, simp_all
                                           , fastforce intro: eval_prim_preservation)
next case v_sem_cast    then show ?case by ( case_tac e, simp_all
                                           , fastforce elim!: upcast_valid_cast_to)
next case v_sem_afun    then show ?case by ( case_tac e, simp_all
                                           , fastforce intro: v_t_afun_instantiate simp add: kinding_simps)
next case v_sem_fun     then show ?case by ( case_tac e, simp_all
                                           , fastforce intro: v_t_function_instantiate)
next case (v_sem_con \<xi> \<gamma> x_spec x' ts_inst tag)
  then show ?case
  proof (cases e)
    case (Con ts tag' x)

    have typing_simps:
      "tag' = tag"
      "ts_inst = map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts"
      "x_spec = specialise \<tau>s x"
      using v_sem_con.hyps Con
      by clarsimp+
    moreover then obtain t t' ts'
      where con_elims:
        "\<tau> = TSum ts'"
        "\<Xi>, K, \<Gamma> \<turnstile> x : t"
        "K \<turnstile> t \<sqsubseteq> t'"
        "(tag, t', Unchecked) \<in> set ts"
        "distinct (map fst ts')"
        "map fst ts = map fst ts'"
        "map (fst \<circ> snd) ts = map (fst \<circ> snd) ts'"
        "list_all2 (\<lambda>x y. snd (snd x) \<le> snd (snd y)) ts ts'"
        "K \<turnstile> TSum ts' wellformed"
      using Con v_sem_con.prems by auto
    ultimately have "\<Xi> \<turnstile> VSum tag x' :v TSum (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts')"
      using v_sem_con.hyps(2) v_sem_con.prems con_elims typing_simps
    proof (intro v_t_sum)
      obtain i where tagelem_at:
        "ts ! i = (tag, t', Unchecked)"
        "i < length ts"
        by (meson con_elims in_set_conv_nth)
      then have
        "fst (ts' ! i) = tag"
        "fst (snd (ts' ! i)) = t'"
        "snd (snd (ts' ! i)) = Unchecked"
        using con_elims
        by (fastforce simp add: list_all2_eq list_all2_conv_all_nth order.antisym)+
      then have
        "ts' ! i = (tag, t', Unchecked)"
        "i < length ts'"
        using tagelem_at con_elims
        by (metis length_map prod.collapse)+
      then show "(tag, instantiate \<tau>s t', Unchecked) \<in> set (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts')"
        by (fastforce simp add: in_set_conv_nth simp del: set_map)
    next
      show "[] \<turnstile> TSum (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts') wellformed"
        using con_elims v_sem_con.prems
        by (fastforce dest: list_all2_kinding_wellformedD intro: instantiate_wellformed
            split: prod.splits variant_state.splits)
    next
      show "\<Xi> \<turnstile> x' :v instantiate \<tau>s t'"
        sorry
    qed auto
    then show ?thesis
      using con_elims by auto
  qed simp+
next case v_sem_member  then show ?case by ( case_tac e, simp_all
                                           , fastforce intro: vval_typing_record_nth)
next case v_sem_unit    then show ?case by ( case_tac e, simp_all
                                           , fastforce intro: vval_typing_vval_typing_variant_vval_typing_record.intros)
next case v_sem_tuple   then show ?case by ( case_tac e, simp_all
                                           , fastforce intro: matches_split
                                                              vval_typing_vval_typing_variant_vval_typing_record.intros)
next case v_sem_case_m  then show ?case by ( case_tac e, simp_all
                                           , fastforce intro: matches_split
                                                              matches_cons [simplified]
                                                       dest:  distinct_fst)
next case (v_sem_case_nm \<xi> \<gamma> x tag' v tag n n' m)
  from v_sem_case_nm.hyps(6)
  show ?case
  proof (case_tac e; clarsimp)
    fix x1 x3 x4
    assume e_is: "e = Case x1 tag x3 x4"
      and x_is: "x = specialise \<tau>s x1"
      and m_is: "m = specialise \<tau>s x3"
      and n_is: "n = specialise \<tau>s x4"

    then obtain \<Gamma>1 \<Gamma>2 ts ta
      where split\<Gamma>: "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
      and typing_x1: "\<Xi>, K, \<Gamma>1 \<turnstile> x1 : TSum ts"
      and ta_in_ts: "(tag, ta, Unchecked) \<in> set ts"
      and typing_x3: "\<Xi>, K, Some ta # \<Gamma>2 \<turnstile> x3 : \<tau>"
      and typing_x4: "\<Xi>, K, Some (TSum (tagged_list_update tag (ta, Checked) ts)) # \<Gamma>2 \<turnstile> x4 : \<tau>"
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
    then have "\<Xi> \<turnstile> VSum tag' v :v TSum (tagged_list_update tag (instantiate \<tau>s ta, Checked) (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts))"
      using v_sem_case_nm.hyps(3) image_iff ta_in_ts
      by (fastforce intro!: sum_downcast)
    then have "\<Xi> \<turnstile> VSum tag' v :v instantiate \<tau>s (TSum (tagged_list_update tag (ta, Checked) ts))"
      by (simp add: tagged_list_update_map_over2[where f="\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)" and g="\<lambda>(t,b). (instantiate \<tau>s t, b)"] case_prod_beta)
    then show "\<Xi> \<turnstile> n' :v instantiate \<tau>s \<tau>"
      using v_sem_case_nm.prems v_sem_case_nm.hyps(5) \<gamma>_matches_\<Gamma>2 matches_cons
        n_is typing_x4
      by blast
  qed
next
  case (v_sem_esac \<xi> \<gamma> spec_a tag v)
  then show ?case
  proof (cases e)
    case (Esac a)

    have esac_simps: "spec_a = specialise \<tau>s a"
      using v_sem_esac.hyps Esac
      by simp

    then obtain ts' tag'
      where esac_elims:
        "\<Xi>, K, \<Gamma> \<turnstile> a : TSum ts'"
        "[(tag', \<tau>, Unchecked)] = filter ((=) Unchecked \<circ> snd \<circ> snd) ts'"
      using v_sem_esac.prems Esac
      by blast

    have "\<Xi> \<turnstile> VSum tag v :v instantiate \<tau>s (TSum ts')"
      using v_sem_esac.hyps(2) v_sem_esac.prems esac_simps esac_elims
      by blast
    then obtain \<tau>' k
      where ih_elims:
        "\<Xi> \<turnstile> v :v instantiate \<tau>s \<tau>'"
        "(tag, instantiate \<tau>s \<tau>', Unchecked) \<in> set (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts')"
        "distinct (map fst ts')"
        "[] \<turnstile> instantiate \<tau>s (TSum ts') wellformed"
      by (force simp add: kinding_simps)
    then have "(tag, instantiate \<tau>s \<tau>', Unchecked) = (tag', instantiate \<tau>s \<tau>, Unchecked)"
      using esac_elims ih_elims by (fastforce simp add: filter_eq_singleton_iff2)
    then show "\<Xi> \<turnstile> v :v instantiate \<tau>s \<tau>"
      using ih_elims by simp
  qed clarsimp+
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
                                           , fastforce intro: vval_typing_vval_typing_variant_vval_typing_record.intros
                                                              vval_typing_all_record [ where ts = "map f ts" for f ts
                                                                                     , simplified])
next
  case (v_sem_take \<xi> \<gamma> spec_x fs f' spec_y e')
  then show ?case
  proof (cases e)
    case (Take x f y)
    then have spec_simps:
      "spec_x = specialise \<tau>s x"
      "f' = f"
      "spec_y = specialise \<tau>s y"
      using v_sem_take(5) Take by simp+
    
    obtain \<Gamma>1 \<Gamma>2 ts s n t k taken
      where typing_elims:
        "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
        "\<Xi>, K, \<Gamma>1 \<turnstile> x : TRecord ts s"
        "sigil_perm s \<noteq> Some ReadOnly"
        "f < length ts"
        "ts ! f = (n, t, Present)"
        "K \<turnstile> t :\<kappa> k"
        "S \<in> k \<or> taken = Taken"
        "\<Xi>, K, Some t # Some (TRecord (ts[f := (n, t, taken)]) s) # \<Gamma>2 \<turnstile> y : \<tau>"
      using v_sem_take.prems(1) spec_simps Take
      by blast
    then have matchsplit_lemmas:
      "\<Xi> \<turnstile> \<gamma> matches instantiate_ctx \<tau>s \<Gamma>1"
      "\<Xi> \<turnstile> \<gamma> matches instantiate_ctx \<tau>s \<Gamma>2"
      using matches_split2 v_sem_take.prems
      by blast+
    
    have "\<Xi> \<turnstile> VRecord fs :v instantiate \<tau>s (TRecord ts s)"
      using v_sem_take.prems spec_simps typing_elims matchsplit_lemmas
      by (fastforce intro!: v_sem_take.hyps(2))
    moreover then have all_inst_ts:
      "\<Xi> \<turnstile>* fs :vr map (\<lambda>(n, t, b). (n, instantiate \<tau>s t, b)) ts"
      "distinct (map fst ts)"
      by (fastforce elim!: v_t_recordE)+
    moreover then have "\<And>t' b'. distinct (map fst (ts[f := (n, t', b')]))"
      by (simp add: map_fst_update typing_elims)
    ultimately have "\<Xi> \<turnstile> VRecord fs :v TRecord (map (\<lambda>(n, t, b). (n, instantiate \<tau>s t, b)) (ts[f := (n, t, taken)])) s"
      using typing_elims v_sem_take.prems
      by (fastforce simp add: map_update intro: substitutivity vval_typing_vval_typing_variant_vval_typing_record.intros vval_typing_record_take)
    then show ?thesis
      using v_sem_take.prems matchsplit_lemmas typing_elims spec_simps all_inst_ts
      by (fastforce intro!: v_sem_take.hyps(4) simp add: matches_Cons vval_typing_record_nth)
  qed simp+
next
  case (v_sem_put \<xi> \<gamma> x_spec fs ea_spec ea' f)
  
  then show ?case
  proof (case_tac e; clarsimp)
    fix x ea
    assume assms1:
      "e = Put x f ea"
      "x_spec = specialise \<tau>s x"
      "ea_spec = specialise \<tau>s ea"
    then obtain \<Gamma>1 \<Gamma>2 ts s n t taken k
      where typingelims:
        "\<tau> = TRecord (ts[f := (n, t, Present)]) s"
        "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
        "\<Xi>, K, \<Gamma>1 \<turnstile> x : TRecord ts s"
        "sigil_perm s \<noteq> Some ReadOnly"
        "f < length ts"
        "ts ! f = (n, t, taken)"
        "K \<turnstile> t :\<kappa> k"
        "D \<in> k \<or> taken = Taken"
        "\<Xi>, K, \<Gamma>2 \<turnstile> ea : t"
      using v_sem_put by blast
    
    have IHresults:
      "\<Xi> \<turnstile> VRecord fs :v instantiate \<tau>s (TRecord ts s)"
      "\<Xi> \<turnstile> ea' :v instantiate \<tau>s t"
      using v_sem_put.prems assms1 typingelims matches_split
      by (fast intro: v_sem_put.hyps(2,4))+
    then obtain ts' s'
      where instvrecordelims:
        "instantiate \<tau>s (TRecord ts s) = TRecord ts' s'"
        "\<Xi> \<turnstile>* fs :vr ts'"
        "distinct (map fst ts')"
      by blast

    show "\<Xi> \<turnstile> VRecord (fs[f := ea']) :v instantiate \<tau>s \<tau>"
      using v_sem_put assms1 typingelims IHresults instvrecordelims
    proof (simp add: map_update, intro vval_typing_vval_typing_variant_vval_typing_record.intros vval_typing_record_put)
      show "[] \<turnstile> instantiate \<tau>s t :\<kappa> k"
        using v_sem_put.prems typingelims
        by (blast intro: substitutivity)
    next
      show "ts' ! f = (n, instantiate \<tau>s t, taken)"
        using instvrecordelims typingelims by fastforce
      then show "distinct (map fst (ts'[f := (n, instantiate \<tau>s t, Present)]))"
        using instvrecordelims typingelims
        by (fastforce simp add: map_fst_update)
    qed simp+
  qed
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
| "monoexpr (Promote t x)     = Promote t (monoexpr x)"
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
next case (v_sem_take \<xi> \<gamma> x fs f e e')
  obtain \<Gamma>1 \<Gamma>2 ts s n t k taken
    where takeelims:
      "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
      "\<Xi>, [], \<Gamma>1 \<turnstile> x : TRecord ts s"
      "sigil_perm s \<noteq> Some ReadOnly"
      "f < length ts"
      "ts ! f = (n, t, Present)"
      "[] \<turnstile> t :\<kappa> k"
      "S \<in> k \<or> taken = Taken"
      "\<Xi>, [], Some t # Some (TRecord (ts[f := (n, t, taken)]) s) # \<Gamma>2 \<turnstile> e : \<tau>"
    using v_sem_take.prems typing_takeE
    by blast

  have submatches:
    "\<Xi> \<turnstile> \<gamma> matches \<Gamma>1"
    "\<Xi> \<turnstile> \<gamma> matches \<Gamma>2"
    using matches_split' takeelims v_sem_take.prems
    by blast+

  have ts_v_sem_lemmas:
    "\<Xi> \<turnstile>* fs :vr ts"
    "distinct (map fst ts)"
    using preservation[where \<tau>s="[]" and K="[]", simplified] submatches takeelims v_sem_take
    by blast+

  have "\<Xi> \<turnstile> VRecord fs :v TRecord (ts[f := (n, t, taken)]) s"
    using takeelims ts_v_sem_lemmas
    by (fastforce intro: vval_typing_vval_typing_variant_vval_typing_record.intros vval_typing_record_take simp add: map_fst_update)
  moreover have "\<Xi> \<turnstile> fs ! f :v t"
    using takeelims ts_v_sem_lemmas vval_typing_record_nth by blast
  ultimately have "\<xi>' , map monoval fs ! f # VRecord (map monoval fs) # map monoval \<gamma> \<turnstile> monoexpr e \<Down> monoval e'"
    using v_sem_take.prems takeelims submatches ts_v_sem_lemmas vval_typing_record_take
    by (force dest!: v_sem_take.hyps(4) intro!: matches_cons' simp add: vval_typing_record_length)
  then show ?case
    using v_sem_take takeelims submatches
    by (auto intro!: v_sem_v_sem_all.intros)
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

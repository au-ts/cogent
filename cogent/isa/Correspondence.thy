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

theory Correspondence
imports UpdateSemantics
begin

locale correspondence =
val: value_sem  "val_abs_typing :: 'av \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> bool" +
upd: update_sem "upd_abs_typing :: 'au \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> sigil \<Rightarrow> 'l set \<Rightarrow> 'l set \<Rightarrow> bool"
for val_abs_typing and upd_abs_typing
+
fixes abs_upd_val :: "'au \<Rightarrow> 'av \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> sigil \<Rightarrow> 'l set \<Rightarrow> 'l set \<Rightarrow> bool"
assumes abs_upd_val_to_vval_typing: "abs_upd_val u v n \<tau>s s l r \<Longrightarrow> val_abs_typing v n \<tau>s"
and     abs_upd_val_to_uval_typing: "abs_upd_val u v n \<tau>s s l r \<Longrightarrow> upd_abs_typing u n \<tau>s s l r"
and     abs_upd_val_bang : "\<lbrakk> abs_upd_val au av n \<tau>s s r w
                            \<rbrakk> \<Longrightarrow> abs_upd_val au av n (map bang \<tau>s) (bang_sigil s) (r \<union> w) {}"

context correspondence
begin

inductive upd_val_rel :: "('f \<Rightarrow> poly_type)
                        \<Rightarrow> ('f, 'au, 'l) store
                        \<Rightarrow> ('f, 'au, 'l) uval
                        \<Rightarrow> ('f, 'av) vval
                        \<Rightarrow> type
                        \<Rightarrow> 'l set
                        \<Rightarrow> 'l set
                        \<Rightarrow> bool"  ("_, _ \<turnstile> _ \<sim> _ : _ \<langle>_, _\<rangle>" [30,0,0,0,0,20] 80)
and upd_val_rel_record :: "('f \<Rightarrow> poly_type)
                         \<Rightarrow> ('f, 'au, 'l) store
                         \<Rightarrow> (('f, 'au, 'l) uval \<times> repr) list
                         \<Rightarrow> ('f, 'av) vval list
                         \<Rightarrow> (type \<times> bool) list
                         \<Rightarrow> 'l set
                         \<Rightarrow> 'l set
                         \<Rightarrow> bool" ("_, _ \<turnstile>* _ \<sim> _ :r _ \<langle>_, _\<rangle>" [30,0,0,0,0,20] 80) where

  u_v_prim     : "\<Xi>, \<sigma> \<turnstile> UPrim l \<sim> VPrim l : TPrim (lit_type l) \<langle>{}, {}\<rangle>"

| u_v_product  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile> a \<sim> a' : t \<langle>r , w \<rangle>
                  ; \<Xi>, \<sigma> \<turnstile> b \<sim> b' : u \<langle>r', w'\<rangle>
                  ; w  \<inter> w' = {}
                  ; w  \<inter> r' = {}
                  ; w' \<inter> r  = {}
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UProduct a b \<sim> VProduct a' b' : TProduct t u \<langle>r \<union> r', w \<union> w'\<rangle>"

| u_v_sum      : "\<lbrakk> \<Xi>, \<sigma> \<turnstile> a \<sim> a' : t \<langle>r, w\<rangle>
                  ; (g, t, False) \<in> set ts
                  ; distinct (map fst ts)
                  ; [] \<turnstile>* map (fst \<circ> snd) ts wellformed
                  ; rs = map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) ts
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> USum g a rs \<sim> VSum g a' : TSum ts \<langle>r, w\<rangle>"


| u_v_struct   : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs \<sim> fs' :r ts \<langle>r, w\<rangle>
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> URecord fs \<sim> VRecord fs' : TRecord ts Unboxed \<langle>r, w\<rangle>"

| u_v_abstract : "\<lbrakk> abs_upd_val a a' n ts Unboxed r w
                  ; [] \<turnstile>* ts wellformed
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UAbstract a \<sim> VAbstract a' : TCon n ts Unboxed \<langle>r, w\<rangle>"

| u_v_function : "\<lbrakk> \<Xi> , ks , [ Some a ] \<turnstile> f : b
                  ; list_all2 (kinding []) ts ks
                  ; ks \<turnstile> a wellformed
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UFunction f ts \<sim> VFunction f ts : TFun (instantiate ts a) (instantiate ts b) \<langle>{}, {}\<rangle>"

| u_v_afun     : "\<lbrakk> \<Xi> f = (ks, a, b)
                  ; list_all2 (kinding []) ts ks
                  ; ks \<turnstile> TFun a b wellformed
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UAFunction f ts \<sim> VAFunction f ts : TFun (instantiate ts a) (instantiate ts b) \<langle>{}, {}\<rangle>"

| u_v_unit     : "\<Xi>, \<sigma> \<turnstile> UUnit \<sim> VUnit : TUnit \<langle>{}, {}\<rangle>"

| u_v_p_rec_ro : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs \<sim> fs' :r ts \<langle>r, {}\<rangle>
                  ; \<sigma> l = Some (URecord fs)
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UPtr l (RRecord (map (\<lambda>(a,b). type_repr a) ts)) \<sim> VRecord fs' : TRecord ts ReadOnly \<langle>insert l r, {}\<rangle>"

| u_v_p_rec_w  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs \<sim> fs' :r ts \<langle>r, w\<rangle>
                  ; \<sigma> l = Some (URecord fs)
                  ; l \<notin> (w \<union> r)
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UPtr l (RRecord (map (\<lambda>(a,b). type_repr a) ts)) \<sim> VRecord fs' : TRecord ts Writable \<langle>r, insert l w\<rangle>"

| u_v_p_abs_ro : "\<lbrakk> abs_upd_val a a' n ts ReadOnly r w
                  ; [] \<turnstile>* ts wellformed
                  ; \<sigma> l = Some (UAbstract a)
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UPtr l (RCon n (map type_repr ts)) \<sim> VAbstract a' : TCon n ts ReadOnly \<langle>insert l r, {}\<rangle>"


| u_v_p_abs_w  : "\<lbrakk> abs_upd_val a a' n ts Writable r w
                  ; [] \<turnstile>* ts wellformed
                  ; \<sigma> l = Some (UAbstract a)
                  ; l \<notin> (w \<union> r)
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UPtr l (RCon n (map type_repr ts)) \<sim> VAbstract a' : TCon n ts Writable \<langle>r, insert l w\<rangle>"

| u_v_r_empty  : "\<Xi>, \<sigma> \<turnstile>* [] \<sim> [] :r [] \<langle>{}, {}\<rangle>"

| u_v_r_cons1  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>  x  \<sim> x'  :  t  \<langle>r , w \<rangle>
                  ; \<Xi>, \<sigma> \<turnstile>* xs \<sim> xs' :r ts \<langle>r', w'\<rangle>
                  ; w  \<inter> w' = {}
                  ; w  \<inter> r' = {}
                  ; w' \<inter> r  = {}
                  ; type_repr t = rp
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile>* ((x,rp) # xs) \<sim> (x' # xs') :r ((t, False) # ts) \<langle>r \<union> r', w \<union> w'\<rangle>"

| u_v_r_cons2  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* xs \<sim> xs' :r ts \<langle>r, w\<rangle>
                  ; [] \<turnstile> t wellformed
                  ; type_repr t = rp
                  ; upd.uval_repr x = rp
                  ; upd.uval_repr_deep x = rp
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile>* ((x,rp) # xs) \<sim> (x' # xs') :r ((t, True) # ts) \<langle>r, w\<rangle>"

lemma upd_val_rel_to_vval_typing:
shows "\<Xi>, \<sigma> \<turnstile>  u  \<sim> v  :  \<tau>  \<langle>r, w\<rangle> \<Longrightarrow> val.vval_typing \<Xi> v \<tau>"
and   "\<Xi>, \<sigma> \<turnstile>* us \<sim> vs :r \<tau>s \<langle>r, w\<rangle> \<Longrightarrow> val.vval_typing_record \<Xi> vs \<tau>s"
proof (induct rule: upd_val_rel_upd_val_rel_record.inducts)
     case u_v_abstract then show ?case by (auto intro!: val.vval_typing_vval_typing_record.intros
                                                        abs_upd_val_to_vval_typing)
next case u_v_p_abs_ro then show ?case by (auto intro!: val.vval_typing_vval_typing_record.intros
                                                        abs_upd_val_to_vval_typing)
next case u_v_p_abs_w  then show ?case by (auto intro!: val.vval_typing_vval_typing_record.intros
                                                        abs_upd_val_to_vval_typing)
qed (auto intro!: val.vval_typing_vval_typing_record.intros)


lemma upd_val_rel_to_uval_typing:
shows "\<Xi>, \<sigma> \<turnstile>  u  \<sim> v  :  \<tau>  \<langle>r, w\<rangle> \<Longrightarrow> upd.uval_typing \<Xi> \<sigma> u \<tau> r w"
and   "\<Xi>, \<sigma> \<turnstile>* us \<sim> vs :r \<tau>s \<langle>r, w\<rangle> \<Longrightarrow> upd.uval_typing_record \<Xi> \<sigma> us \<tau>s r w"
proof (induct rule: upd_val_rel_upd_val_rel_record.inducts)
     case u_v_abstract then show ?case by (auto intro!: upd.uval_typing_uval_typing_record.intros
                                                        abs_upd_val_to_uval_typing)
next case u_v_p_abs_ro then show ?case by (auto dest:   upd.abs_typing_readonly [rotated 1]
                                                        abs_upd_val_to_uval_typing
                                                intro!: upd.uval_typing_uval_typing_record.intros)
next case u_v_p_abs_w  then show ?case by (auto dest:   upd.abs_typing_readonly [rotated 1]
                                                        abs_upd_val_to_uval_typing
                                                intro!: upd.uval_typing_uval_typing_record.intros)
qed (auto intro!: upd.uval_typing_uval_typing_record.intros)


lemma u_v_prim' : "\<tau> = lit_type l \<Longrightarrow> l = l' \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UPrim l \<sim> VPrim l' : TPrim \<tau> \<langle>{}, {}\<rangle>"
   by (simp add: u_v_prim)

inductive_cases u_v_primE     [elim] : "\<Xi>, \<sigma> \<turnstile> UPrim l \<sim> VPrim l' : TPrim \<tau> \<langle>r, w\<rangle>"
inductive_cases u_v_functionE [elim] : "\<Xi>, \<sigma> \<turnstile> UFunction f ts \<sim> VFunction f' ts' : TFun \<tau> \<rho> \<langle>r, w\<rangle>"
inductive_cases u_v_afunE     [elim] : "\<Xi>, \<sigma> \<turnstile> UAFunction f ts \<sim> VAFunction f' ts' : TFun \<tau> \<rho> \<langle>r, w\<rangle>"
inductive_cases u_v_sumE      [elim] : "\<Xi>, \<sigma> \<turnstile> u \<sim> v : TSum \<tau>s \<langle>r, w\<rangle>"
inductive_cases u_v_productE  [elim] : "\<Xi>, \<sigma> \<turnstile> UProduct a b \<sim> VProduct a' b' : TProduct \<tau> \<rho> \<langle>r, w\<rangle>"
inductive_cases u_v_recE      [elim] : "\<Xi>, \<sigma> \<turnstile> URecord fs \<sim> VRecord fs' : \<tau> \<langle>r, w\<rangle>"
inductive_cases u_v_p_recE    [elim] : "\<Xi>, \<sigma> \<turnstile> UPtr p rp \<sim> VRecord fs' : TRecord fs s \<langle>r, w\<rangle>"
inductive_cases u_v_r_emptyE  [elim] : "\<Xi>, \<sigma> \<turnstile>* [] \<sim> [] :r \<tau>s \<langle>r, w\<rangle>"
inductive_cases u_v_r_consE   [elim] : "\<Xi>, \<sigma> \<turnstile>* (a # b) \<sim> (a' # b') :r \<tau>s \<langle>r, w\<rangle>"
inductive_cases u_v_r_consE'  [elim] : "\<Xi>, \<sigma> \<turnstile>* (a # b) \<sim> xx :r \<tau>s \<langle>r, w\<rangle>"

inductive upd_val_rel_all :: "('f \<Rightarrow> poly_type)
                            \<Rightarrow> ('f, 'au, 'l) store
                            \<Rightarrow> ('f, 'au, 'l) uval list
                            \<Rightarrow> ('f, 'av) vval list
                            \<Rightarrow> type list
                            \<Rightarrow> 'l set
                            \<Rightarrow> 'l set
                            \<Rightarrow> bool" ("_, _ \<turnstile>* _ \<sim> _ : _ \<langle>_, _\<rangle>" [30,0,0,0,0,0,20] 80) where
  u_v_all_empty  : "\<Xi>, \<sigma> \<turnstile>* [] \<sim> [] : [] \<langle>{}, {}\<rangle>"

| u_v_all_cons   : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>  x  \<sim> x'  : t  \<langle>r , w \<rangle>
                    ; \<Xi>, \<sigma> \<turnstile>* xs \<sim> xs' : ts \<langle>r', w'\<rangle>
                    ; w  \<inter> w' = {}
                    ; w  \<inter> r' = {}
                    ; w' \<inter> r  = {}
                    \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile>* (x # xs) \<sim> (x' # xs') : (t # ts) \<langle>r \<union> r', w \<union> w'\<rangle>"

lemma upd_val_rel_all_to_vval_typing_all:
shows "\<Xi>, \<sigma> \<turnstile>* us \<sim> vs : \<tau>s  \<langle>r, w\<rangle> \<Longrightarrow> val.vval_typing_all \<Xi> vs \<tau>s"
proof (induct rule: upd_val_rel_all.inducts)
case u_v_all_empty then show ?case by (simp add: val.vval_typing_all_def)
case u_v_all_cons  then show ?case by (simp add: val.vval_typing_all_def upd_val_rel_to_vval_typing)
qed


lemma upd_val_rel_all_to_uval_typing_all:
shows "\<Xi>, \<sigma> \<turnstile>* us \<sim> vs : \<tau>s \<langle>r, w\<rangle> \<Longrightarrow> upd.uval_typing_all \<Xi> \<sigma> us \<tau>s r w"
proof (induct rule: upd_val_rel_all.inducts )
case u_v_all_empty then show ?case by (rule upd.u_t_all_empty)
case u_v_all_cons  then show ?case by (auto intro: upd.uval_typing_all.intros
                                            simp:  upd_val_rel_to_uval_typing)
qed

inductive u_v_matches :: "('f \<Rightarrow> poly_type)
                        \<Rightarrow> ('f, 'au, 'l) store
                        \<Rightarrow> ('f, 'au, 'l) uval env
                        \<Rightarrow> ('f, 'av) vval env
                        \<Rightarrow> ctx
                        \<Rightarrow> 'l set
                        \<Rightarrow> 'l set
                        \<Rightarrow> bool" ("_, _ \<turnstile> _ \<sim> _ matches _ \<langle>_, _\<rangle>" [30,0,0,0,0,0,20] 60) where

  u_v_matches_empty : "\<Xi>, \<sigma> \<turnstile> [] \<sim> [] matches [] \<langle>{}, {}\<rangle>"

| u_v_matches_none  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile> xs \<sim> xs' matches \<Gamma> \<langle>r, w\<rangle>
                       \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> (x # xs) \<sim> (x' # xs') matches (None # \<Gamma>) \<langle>r, w\<rangle>"

| u_v_matches_some  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile> x \<sim> x' : t  \<langle>r , w \<rangle>
                       ; \<Xi>, \<sigma> \<turnstile> xs \<sim> xs' matches ts \<langle>r', w'\<rangle>
                       ; w  \<inter> w' = {}
                       ; w  \<inter> r' = {}
                       ; w' \<inter> r  = {}
                       \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> (x # xs) \<sim> (x' # xs') matches (Some t # ts) \<langle>r \<union> r', w \<union> w'\<rangle>"

inductive_cases u_v_matches_consE: "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches (\<tau> # \<tau>s) \<langle> r , w \<rangle>"

lemma u_v_matches_to_matches:
assumes "\<Xi>, \<sigma> \<turnstile> us \<sim> vs matches \<Gamma> \<langle>r, w\<rangle>"
shows   "val.matches \<Xi> vs \<Gamma>"
using assms proof (induct rule: u_v_matches.inducts)
case u_v_matches_empty then show ?case by (simp add: val.matches_def)
case u_v_matches_none  then show ?case by (simp add: val.matches_def)
case u_v_matches_some  then show ?case by (simp add: val.matches_def upd_val_rel_to_vval_typing)
qed

lemma u_v_matches_to_matches_ptrs:
assumes "\<Xi>, \<sigma> \<turnstile> us \<sim> vs matches \<Gamma> \<langle>r, w\<rangle>"
shows   "upd.matches_ptrs \<Xi> \<sigma> us \<Gamma> r w"
using assms proof (induct rule: u_v_matches.inducts)
case u_v_matches_empty then show ?case by rule
case u_v_matches_none  then show ?case by (auto intro: upd.matches_ptrs_none)
case u_v_matches_some  then show ?case by (auto intro: upd.matches_ptrs_some
                                                simp: upd_val_rel_to_uval_typing)
qed

definition proc_env_u_v_matches :: "(('f, 'au, 'l) uabsfuns)

                                  \<Rightarrow> (('f, 'av)    vabsfuns)
                                  \<Rightarrow> ('f \<Rightarrow> poly_type)
                                  \<Rightarrow> bool"
           ("_ \<sim> _ matches-u-v _" [30,20] 60) where
  "\<xi> \<sim> \<xi>' matches-u-v \<Xi>
          \<equiv> (\<forall> f. let (K, \<tau>i, \<tau>o) = \<Xi> f
                  in (\<forall> \<sigma> \<sigma>' \<tau>s a a' v v' r w.
                         list_all2 (kinding []) \<tau>s K
                      \<longrightarrow> (\<Xi> , \<sigma> \<turnstile> a \<sim> a' : instantiate \<tau>s \<tau>i \<langle>r, w\<rangle>)
                      \<longrightarrow> \<xi> f (\<sigma>, a) (\<sigma>', v)
                      \<longrightarrow> (\<xi>' f a' v'
                           \<longrightarrow> (\<exists>r' w'. (\<Xi> , \<sigma>' \<turnstile> v \<sim> v' : instantiate \<tau>s \<tau>o \<langle>r', w'\<rangle>)
                                    \<and> r' \<subseteq> r \<and> upd.frame \<sigma> w \<sigma>' w'))
                       \<and> (\<exists> v'. \<xi>' f a' v')))"

lemma upd_val_rel_record:
assumes "\<Xi>, \<sigma> \<turnstile>* vs \<sim> vs' : ts \<langle>r, w\<rangle>"
shows   "\<Xi>, \<sigma> \<turnstile>* (zip vs (map (type_repr) ts)) \<sim> vs' :r zip ts (replicate (length ts) False) \<langle>r, w\<rangle>"
using assms proof (induct rule: upd_val_rel_all.induct)
case u_v_all_empty  then show ?case by (auto intro: upd_val_rel_upd_val_rel_record.intros)
case u_v_all_cons   then show ?case by (auto intro: upd_val_rel_upd_val_rel_record.intros)
qed


lemma upd_val_rel_pointers_noalias:
shows "\<lbrakk> \<Xi>, \<sigma> \<turnstile>  v  \<sim> v'  :  \<tau>  \<langle> r , w \<rangle> \<rbrakk> \<Longrightarrow> r \<inter> w = {}"
and   "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* vs \<sim> vs' :r \<tau>s \<langle> r , w \<rangle> \<rbrakk> \<Longrightarrow> r \<inter> w = {}"
by (auto dest!: upd_val_rel_to_uval_typing  upd.uval_typing_pointers_noalias)

lemma u_v_shareable_not_writable:
assumes "S \<in> k"
shows "\<lbrakk> \<Xi>, \<sigma> \<turnstile>  v  \<sim> v'  :  \<tau>  \<langle> r , w \<rangle>; K \<turnstile>  \<tau>  :\<kappa>  k \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs \<sim> fs' :r \<tau>s \<langle> r , w \<rangle>; K \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> w = {}"
using assms by (fastforce dest: upd_val_rel_to_uval_typing upd.shareable_not_writable)+

lemma u_v_discardable_not_writable:
assumes "D \<in> k"
shows "\<lbrakk> \<Xi>, \<sigma> \<turnstile>  v  \<sim> v'  :  \<tau>  \<langle> r , w \<rangle>; K \<turnstile>  \<tau>  :\<kappa>  k \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs \<sim> fs' :r \<tau>s \<langle> r , w \<rangle>; K \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> w = {}"
using assms by (fastforce dest: upd_val_rel_to_uval_typing upd.discardable_not_writable)+


lemma u_v_discardable_not_writable_all:
assumes "D \<in> k"
shows   "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs \<sim> fs' : \<tau>s \<langle> r , w \<rangle>; K \<turnstile>* \<tau>s :\<kappa> k \<rbrakk> \<Longrightarrow> w = {}"
using assms by (fastforce dest: upd_val_rel_all_to_uval_typing_all upd.discardable_not_writable_all)

lemma u_v_escapable_no_readers:
shows   "\<lbrakk> \<Xi> , \<sigma> \<turnstile>  x  \<sim> x'  :  \<tau>  \<langle>r, w\<rangle> ; E \<in> k; [] \<turnstile>  \<tau>  :\<kappa>  k \<rbrakk> \<Longrightarrow> r = {}"
and     "\<lbrakk> \<Xi> , \<sigma> \<turnstile>* xs \<sim> xs' :r \<tau>s \<langle>r, w\<rangle> ; E \<in> k; [] \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> r = {}"
by (auto dest: upd_val_rel_to_uval_typing upd.escapable_no_readers)

lemma u_v_tprim_no_pointers:
assumes "\<Xi> , \<sigma> \<turnstile> u \<sim> v : TPrim \<tau> \<langle>r, w\<rangle>"
shows   "r = {}"
and     "w = {}"
using assms by (auto dest: upd_val_rel_to_uval_typing upd.tprim_no_pointers)

lemma u_v_tfun_no_pointers:
assumes "\<Xi> , \<sigma> \<turnstile> u \<sim> v : TFun \<tau> \<rho> \<langle>r, w\<rangle>"
shows   "r = {}"
and     "w = {}"
using assms by (auto dest: upd_val_rel_to_uval_typing upd.tfun_no_pointers)

lemma u_v_map_tprim_no_pointers:
assumes "\<Xi> , \<sigma> \<turnstile>* us \<sim> vs : map TPrim \<tau>s \<langle>r, w\<rangle>"
shows   "r = {}"
and     "w = {}"
using assms by (auto dest: upd_val_rel_all_to_uval_typing_all upd.map_tprim_no_pointers)

lemma u_v_map_tprim_no_pointers':
assumes "\<Xi> , \<sigma> \<turnstile>* us \<sim> vs : map TPrim \<tau>s \<langle>r, w\<rangle>"
shows   "\<Xi> , \<sigma> \<turnstile>* us \<sim> vs : map TPrim \<tau>s \<langle>{}, {}\<rangle>"
using assms by (auto dest: u_v_map_tprim_no_pointers)

lemma u_v_matches_none [simp]:
shows "(\<Xi>, \<sigma> \<turnstile> (x # xs) \<sim> (x' # xs') matches (None # ts) \<langle>r , w\<rangle>)
     = (\<Xi>, \<sigma> \<turnstile> xs       \<sim> xs'        matches ts          \<langle>r , w\<rangle>)"
proof (rule iffI)
     assume "\<Xi>, \<sigma> \<turnstile> (x # xs) \<sim> (x' # xs') matches (None # ts) \<langle>r, w\<rangle>"
then show   "\<Xi>, \<sigma> \<turnstile> xs       \<sim> xs'        matches ts          \<langle>r, w\<rangle>"
     by (auto elim: u_v_matches.cases)

next assume "\<Xi>, \<sigma> \<turnstile> xs       \<sim> xs'        matches ts          \<langle>r, w\<rangle>"
then show   "\<Xi>, \<sigma> \<turnstile> (x # xs) \<sim> (x' # xs') matches (None # ts) \<langle>r, w\<rangle>"
     by (auto intro: u_v_matches.intros)
qed

lemma u_v_pointerset_helper:
assumes "\<Xi>, \<sigma> \<turnstile> u \<sim> v : \<tau> \<langle>r, w\<rangle>"
and     "r = r'"
and     "w = w'"
shows   "\<Xi>, \<sigma> \<turnstile> u \<sim> v : \<tau> \<langle>r', w'\<rangle>"
using assms by auto

lemma u_v_pointerset_helper_record:
assumes "\<Xi>, \<sigma> \<turnstile>* us \<sim> vs :r \<tau>s \<langle>r, w\<rangle>"
and     "r = r'"
and     "w = w'"
shows   "\<Xi>, \<sigma> \<turnstile>* us \<sim> vs :r \<tau>s \<langle>r', w'\<rangle>"
using assms by auto

lemma u_v_pointerset_helper_matches:
assumes "\<Xi>, \<sigma> \<turnstile> us \<sim> vs matches \<tau>s \<langle>r, w\<rangle>"
and     "r = r'"
and     "w = w'"
shows   "\<Xi>, \<sigma> \<turnstile> us \<sim> vs matches \<tau>s \<langle>r', w'\<rangle>"
using assms by auto

lemma upd_val_rel_bang:
shows" \<Xi>, \<sigma> \<turnstile>  u  \<sim> v  :  \<tau>  \<langle>r, w\<rangle> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile>  u  \<sim> v  :  bang \<tau> \<langle>r \<union> w, {}\<rangle>"
and   "\<Xi>, \<sigma> \<turnstile>* us \<sim> vs :r \<tau>s \<langle>r, w\<rangle> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile>* us \<sim> vs :r (map (\<lambda> (t, b). (bang t, b)) \<tau>s) \<langle>r \<union> w, {}\<rangle>"
proof (induct rule: upd_val_rel_upd_val_rel_record.inducts)
     case u_v_prim     then show ?case by (auto  intro: upd_val_rel_upd_val_rel_record.intros)
next case u_v_product  then show ?case by (auto  dest:  upd_val_rel_upd_val_rel_record.u_v_product
                                                 intro: u_v_pointerset_helper)
next case (u_v_sum \<Xi> \<sigma> a a' t r w g ts rs)
  then show ?case
  proof (simp, intro upd_val_rel_upd_val_rel_record.intros)
    show "[] \<turnstile>* map (fst \<circ> snd) (map (\<lambda>(c, t, b). (c, bang t, b)) ts) wellformed"
      using bang_kind(2) u_v_sum.hyps
      unfolding type_wellformed_all_def
      by fastforce
  next
    obtain k where "\<And>tag \<tau> b. (tag, \<tau>, b) \<in> set ts \<Longrightarrow> [] \<turnstile> \<tau> :\<kappa> k"
      using u_v_sum.hyps(5)  kinding_all_set by fastforce
    then show "map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) ts = map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) (map (\<lambda>(c, t, b). (c, bang t, b)) ts)"
      using bang_type_repr by fastforce
  qed force+
next case u_v_struct   then show ?case by (auto  intro: upd_val_rel_upd_val_rel_record.intros)
next case u_v_abstract then show ?case by (force intro: upd_val_rel_upd_val_rel_record.intros
                                                        abs_upd_val_bang [where s = Unboxed, simplified]
                                                        bang_kind)
next case u_v_function then show ?case by (force intro: upd_val_rel_upd_val_rel_record.intros)
next case u_v_afun     then show ?case by (force intro: upd_val_rel_upd_val_rel_record.intros)
next case u_v_unit     then show ?case by (force intro: upd_val_rel_upd_val_rel_record.intros)
next case u_v_p_rec_ro
  then show ?case
    apply clarsimp
    apply (drule upd_val_rel_to_uval_typing)
    apply (drule upd.uval_typing_to_kinding(2))
    apply (frule upd_val_rel_upd_val_rel_record.u_v_p_rec_ro)
    apply (auto dest!: kinding_all_record' upd.bang_type_repr')
  done
next case u_v_p_rec_w
  then show ?case
    apply clarsimp
    apply (drule upd_val_rel_to_uval_typing)
    apply (drule upd.uval_typing_to_kinding(2))
    apply (frule upd_val_rel_upd_val_rel_record.u_v_p_rec_ro)
    apply (auto dest!: kinding_all_record' upd.bang_type_repr')
  done
next case u_v_p_abs_ro
  then show ?case
    apply (clarsimp)
    apply (frule abs_upd_val_to_uval_typing)
    apply (drule upd.abs_typing_readonly [rotated 1],simp,clarsimp)
    apply (drule abs_upd_val_bang [where s = ReadOnly and w = "{}", simplified])
    apply (frule bang_kind)
    apply (force dest:upd_val_rel_upd_val_rel_record.u_v_p_abs_ro)
  done
next case u_v_p_abs_w
  then show ?case
    apply (clarsimp)
    apply (frule abs_upd_val_to_uval_typing)
    apply (drule abs_upd_val_bang [where s = Writable, simplified])
    apply (frule bang_kind)
    apply (force dest:upd_val_rel_upd_val_rel_record.u_v_p_abs_ro)
  done
next case u_v_r_empty  then show ?case by (force intro: upd_val_rel_upd_val_rel_record.intros)
next case u_v_r_cons1
  then show ?case
    apply (clarsimp)
    apply ( drule(1) upd_val_rel_upd_val_rel_record.u_v_r_cons1
                     [ where t = "bang t"
                       and   ts = " map (\<lambda>(a,b).(bang a, b)) ts"
                       for t ts]
          , blast, blast, blast, simp)
    apply ( rule u_v_pointerset_helper_record)
    apply (force dest: upd_val_rel_to_uval_typing upd.uval_typing_to_kinding)+ (* takes ~5.0s *)
  done
next case u_v_r_cons2  then show ?case by (force intro: upd_val_rel_upd_val_rel_record.intros bang_kind)
qed


lemma u_v_function_instantiate:
assumes "list_all2 (kinding K') ts K"
and     "list_all2 (kinding []) \<delta> K'"
and     "K \<turnstile> t wellformed"
and     "K \<turnstile> u wellformed"
and     "\<Xi>, K, [Some t] \<turnstile> f : u"
shows   "\<Xi>, \<sigma> \<turnstile> UFunction f (map (instantiate \<delta>) ts)
              \<sim> VFunction f (map (instantiate \<delta>) ts) : TFun (instantiate \<delta> (instantiate ts t))
                                                            (instantiate \<delta> (instantiate ts u)) \<langle>{}, {}\<rangle>"
proof -
from assms have "TFun (instantiate \<delta> (instantiate ts t))
                      (instantiate \<delta> (instantiate ts u))
               = TFun (instantiate (map (instantiate \<delta>) ts) t)
                      (instantiate (map (instantiate \<delta>) ts) u)"
           by (force intro: instantiate_instantiate dest: list_all2_lengthD)
with assms show ?thesis by (force intro: upd_val_rel_upd_val_rel_record.intros
                                         list_all2_substitutivity
                                         kinding_kinding_all_kinding_record.intros)
qed

lemma u_v_afun_instantiate:
assumes "list_all2 (kinding K') ts K"
and     "list_all2 (kinding []) \<delta> K'"
and     "K \<turnstile> t wellformed"
and     "K \<turnstile> u wellformed"
and     "\<Xi> f = (K, t, u)"
shows   "\<Xi>, \<sigma> \<turnstile> UAFunction f (map (instantiate \<delta>) ts)
              \<sim> VAFunction f (map (instantiate \<delta>) ts) : TFun (instantiate \<delta> (instantiate ts t))
                                                            (instantiate \<delta> (instantiate ts u)) \<langle>{}, {}\<rangle>"
proof -
from assms have "TFun (instantiate \<delta> (instantiate ts t))
                      (instantiate \<delta> (instantiate ts u))
               = TFun (instantiate (map (instantiate \<delta>) ts) t)
                      (instantiate (map (instantiate \<delta>) ts) u)"
           by (force intro: instantiate_instantiate dest: list_all2_lengthD)
with assms show ?thesis by (force intro: upd_val_rel_upd_val_rel_record.intros
                                         list_all2_substitutivity
                                         kinding_kinding_all_kinding_record.intros)
qed

lemma u_v_matches_noalias:
assumes "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma> \<langle>r, w\<rangle>"
shows   "w \<inter> r = {}"
using assms by (auto dest: u_v_matches_to_matches_ptrs upd.matches_ptrs_noalias)


lemma u_v_matches_some_bang:
assumes "\<Xi>, \<sigma> \<turnstile> x \<sim> x' : t \<langle>r, w\<rangle>"
and     "\<Xi>, \<sigma> \<turnstile> xs \<sim> xs' matches ts \<langle>r' \<union> b, w'\<rangle>"
and     "w \<inter> w' = {}"
and     "w \<inter> r' = {}"
and     "w' \<inter> r = {}"
shows   "\<Xi>, \<sigma> \<turnstile> (x # xs) \<sim> (x' # xs') matches Some (bang t) # ts \<langle>r \<union> (r' \<union> (b \<union> w)), w'\<rangle>"
proof -
have SetLemma : "r \<union> (r' \<union> (b \<union> w)) = (r \<union> w) \<union> (r' \<union> b)" by auto
from assms show ?thesis by (auto simp:  SetLemma
                                 intro: u_v_matches_some
                                          [where w = "{}", simplified]
                                        upd_val_rel_bang)
qed

lemma u_v_matches_split':
assumes "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma> \<langle>r, w\<rangle>"
shows   "\<exists>r' w' r'' w''. r = r' \<union> r''
                       \<and> w = w' \<union> w''
                       \<and> w' \<inter> w'' = {}
                       \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma>1 \<langle>r' , w' \<rangle>)
                       \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma>2 \<langle>r'', w''\<rangle>)"
using assms proof (induct arbitrary: \<gamma> \<gamma>' r w rule: split.induct)
     case split_empty then show ?case by (fastforce elim:  u_v_matches.cases
                                                    intro: u_v_matches.intros)
next case (split_cons K x a b xs as bs \<gamma> \<gamma>' r w)
  then show ?case
  proof (cases \<Xi> \<sigma> \<gamma> \<gamma>' x xs r w rule: u_v_matches_consE)
       case 1 with split_cons show ?case   by simp
  next case 2 with split_cons show ?thesis by (auto elim: split_comp.cases)
  next case (3 _ _ _ rx wx _ _ rs ws)
    with split_cons show ?thesis
    proof (cases rule: split_comp.cases)
         case none  with 3 show ?thesis by simp
    next case left  with 3 show ?thesis
      apply (clarsimp dest!: split_cons(3))
      apply (rule_tac x = "rx \<union> r'" in exI)
      apply (rule_tac x = "wx \<union> w'" in exI)
      apply (rule_tac x = "r''"     in exI, rule,blast)
      apply (rule_tac x = "w''"     in exI)
      apply (force intro!: u_v_matches.intros)
    done
    next case right with 3 show ?thesis
      apply (clarsimp dest!: split_cons(3))
      apply (rule_tac x = "r'"       in exI)
      apply (rule_tac x = "w'"       in exI)
      apply (rule_tac x = "rx \<union> r''" in exI, rule, blast)
      apply (rule_tac x = "wx \<union> w''" in exI)
      apply (force intro!: u_v_matches.intros)
    done
    next case share with 3 show ?thesis
      apply (clarsimp dest!: split_cons(3))
      apply (drule(2) u_v_shareable_not_writable)
      apply (clarsimp)
      apply (rule_tac x = "rx \<union> r'"  in exI)
      apply (rule_tac x = "w'"       in exI)
      apply (rule_tac x = "rx \<union> r''" in exI, rule, blast)
      apply (rule_tac x = "w''"      in exI)
      apply (force intro: u_v_matches_some [where w = "{}", simplified])
    done
    qed
  qed
qed

lemma u_v_matches_split:
assumes "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "list_all2 (kinding []) \<tau>s K"
shows   "\<exists>r' w' r'' w''. r = r' \<union> r''
                       \<and> w = w' \<union> w''
                       \<and> w' \<inter> w'' = {}
                       \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches (instantiate_ctx \<tau>s \<Gamma>1) \<langle>r' , w' \<rangle>)
                       \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches (instantiate_ctx \<tau>s \<Gamma>2) \<langle>r'', w''\<rangle>)"
using assms by (auto dest:  instantiate_ctx_split
                     intro: u_v_matches_split' [simplified])


lemma u_v_matches_split_bang':
assumes "split_bang [] vs \<Gamma> \<Gamma>1 \<Gamma>2"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma> \<langle>r, w\<rangle>"
shows   "\<exists>r' w' r'' w'' b. r = r' \<union> r''
                         \<and> w' \<inter> w'' = {}
                         \<and> w = w' \<union> w'' \<union> b
                         \<and> b \<inter> (w' \<union> w'') = {}
                         \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma>1 \<langle>r' \<union> b, w'     \<rangle>)
                         \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma>2 \<langle>r''   , w'' \<union> b\<rangle>)"
using assms proof (induct arbitrary: \<gamma> \<gamma>' r w rule: split_bang.induct)
     case split_bang_empty then show ?case by (fastforce elim:  u_v_matches.cases
                                                         intro: u_v_matches.intros)
next case (split_bang_cons iss K x a b xs as bs \<gamma> \<gamma>' r w)
  then show ?case
  proof (cases \<Xi> \<sigma> \<gamma> \<gamma>' x xs r w rule: u_v_matches_consE)
       case 1 with split_bang_cons show ?case   by simp
  next case 2 with split_bang_cons show ?thesis by (auto elim: split_comp.cases)
  next case (3 _ _ _ rx wx _ _ rs ws)
    with split_bang_cons(2,1,3-) show ?thesis
    proof (cases rule: split_comp.cases)
         case none  with 3 show ?thesis by simp
    next case left  with 3 show ?thesis
      apply (clarsimp dest!: split_bang_cons(4))
      apply (rule_tac x = "rx \<union> r'" in exI)
      apply (rule_tac x = "wx \<union> w'" in exI)
      apply (rule_tac x = "r''"     in exI, rule, blast)
      apply (rule_tac x = "w''"     in exI, rule, blast)
      apply (rule_tac x = "ba"      in exI)
      apply (auto simp: Un_assoc intro!: u_v_matches.intros)
    done
    next case right with 3 show ?thesis
      apply (clarsimp dest!: split_bang_cons(4))
      apply (rule_tac x = "r'"       in exI)
      apply (rule_tac x = "w'"       in exI)
      apply (rule_tac x = "rx \<union> r''" in exI, rule, blast)
      apply (rule_tac x = "wx \<union> w''" in exI, rule, blast)
      apply (rule_tac x = "ba"       in exI)
      apply (auto simp: Un_assoc intro!: u_v_matches.intros)
    done
    next case share with 3 show ?thesis
      apply (clarsimp dest!: split_bang_cons(4))
      apply (drule(2) u_v_shareable_not_writable)
      apply (clarsimp)
      apply (rule_tac x = "rx \<union> r'"  in exI)
      apply (rule_tac x = "w'"       in exI)
      apply (rule_tac x = "rx \<union> r''" in exI, rule, blast)
      apply (rule_tac x = "w''"      in exI, rule, blast)
      apply (rule_tac x = "ba"       in exI)
      apply (auto simp: Un_assoc intro: u_v_matches_some [where w = "{}", simplified])
    done
    qed
  qed
next case (split_bang_bang iss iss' K xs as bs x \<gamma> \<gamma>' r w)
  then show ?case
  proof (cases \<Xi> \<sigma> \<gamma> \<gamma>' "Some x" xs r w rule: u_v_matches_consE)
       case 1 with split_bang_bang show ?case by simp
  next case 2 with split_bang_bang show ?thesis by simp
  next case (3 _ _ _ rx wx _ _ rs ws) with split_bang_bang show ?thesis
    apply (clarsimp dest!: split_bang_bang(4))
    apply (rule_tac x = "rx \<union> r'"  in exI)
    apply (rule_tac x = "w'"       in exI)
    apply (rule_tac x = "rx \<union> r''" in exI, rule, blast)
    apply (rule_tac x = "w''"      in exI, rule, blast)
    apply (rule_tac x = "b \<union> wx"   in exI)
    apply (auto simp:   Un_assoc
                dest:   u_v_matches_some
                intro!: u_v_matches_some_bang
                intro:  u_v_pointerset_helper_matches)
  done
  qed
qed


lemma u_v_matches_split_bang:
assumes "split_bang K vs \<Gamma> \<Gamma>1 \<Gamma>2"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "list_all2 (kinding []) \<tau>s K"
shows   "\<exists>r' w' r'' w'' b. r = r' \<union> r''
                         \<and> w' \<inter> w'' = {}
                         \<and> w = w' \<union> w'' \<union> b
                         \<and> b \<inter> (w' \<union> w'') = {}
                         \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches (instantiate_ctx \<tau>s \<Gamma>1) \<langle>r'  \<union> b , w'     \<rangle>)
                         \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches (instantiate_ctx \<tau>s \<Gamma>2) \<langle>r''     , w'' \<union> b\<rangle>)"
using assms by (auto dest:  instantiate_ctx_split_bang
                     intro: u_v_matches_split_bang' [simplified])

lemma u_v_matches_weaken':
assumes "[] \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma>  \<langle>r, w\<rangle>"
shows   "\<exists> r'. (r' \<subseteq> r) \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma>' \<langle>r', w\<rangle>)"
using assms(1) [simplified weakening_def] and assms(2-)
proof (induct arbitrary: \<gamma> \<gamma>' r w rule: list_all2_induct )
     case Nil  then show ?case by auto
next case Cons then show ?case
  proof (cases rule: weakening_comp.cases)
       case none with Cons show ?thesis by (force elim!: u_v_matches_consE)
  next case keep with Cons show ?thesis
    apply (safe elim!: u_v_matches_consE dest!: Cons(3))
    apply (rule_tac x = "r \<union> r'a" in exI)
    apply (force intro!: u_v_matches.intros)
  done
  next case drop with Cons show ?thesis
    apply (safe elim!: u_v_matches_consE weakening_comp.cases dest!: Cons(3))
    apply (frule(2) u_v_discardable_not_writable)
    apply (clarsimp)
    apply (rule_tac x = "r'a" in exI)
    apply (force)
  done
  qed
qed

lemma u_v_matches_weaken:
assumes "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "list_all2 (kinding []) \<tau>s K"
shows   "\<exists>r'. (r' \<subseteq> r) \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches (instantiate_ctx \<tau>s \<Gamma>') \<langle>r', w\<rangle>) "
using assms by (auto dest:  instantiate_ctx_weaken
                     intro: u_v_matches_weaken' [simplified])



lemma u_v_matches_cons:
assumes "list_all2 (kinding []) \<tau>s K"
and     "\<Xi> , \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r', w'\<rangle>"
and     "\<Xi> , \<sigma> \<turnstile> x \<sim> x' : instantiate \<tau>s \<tau> \<langle>r, w\<rangle>"
and     "w  \<inter> w' = {}"
and     "w  \<inter> r' = {}"
and     "w' \<inter> r  = {}"
shows   "\<Xi> , \<sigma> \<turnstile> (x # \<gamma>) \<sim> (x' # \<gamma>') matches (instantiate_ctx \<tau>s (Some \<tau> # \<Gamma>)) \<langle>r \<union> r', w \<union> w'\<rangle>"
using assms by (auto intro: u_v_matches_some)

lemma u_v_matches_empty:
shows "\<Xi> , \<sigma> \<turnstile> [] \<sim> [] matches instantiate_ctx \<tau>s [] \<langle>{}, {}\<rangle>"
by (simp add: u_v_matches_empty instantiate_ctx_def)

lemma u_v_matches_length:
assumes "\<Xi> , \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma> \<langle>r, w\<rangle>"
shows   "length \<gamma> = length \<Gamma>"
using assms by (auto elim: u_v_matches.induct)

lemma u_v_matches_empty_env:
assumes "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches empty n \<langle>r, w\<rangle>"
shows   "r = {}"
and     "w = {}"
using assms by (auto dest: u_v_matches_to_matches_ptrs upd.matches_ptrs_empty_env)

lemma u_v_matches_proj':
assumes "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma> \<langle>r, w\<rangle>"
and     "[] \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i \<tau>"
and     "i < length \<Gamma>"
shows   "\<exists> r' \<subseteq> r. \<Xi>, \<sigma> \<turnstile> (\<gamma> ! i) \<sim> (\<gamma>' ! i) : \<tau> \<langle>r', w\<rangle>"
proof -
  from assms obtain r' where S: "r' \<subseteq> r"
                       and   I: "\<Xi> , \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches (singleton (length \<Gamma>) i \<tau>) \<langle>r', w\<rangle>"
       by (auto dest: u_v_matches_weaken')
  from assms obtain env where "singleton (length \<Gamma>) i \<tau> = env" by simp
  from I [simplified this] S assms(3-) this
  show ?thesis proof (induct arbitrary: i \<Gamma> rule: u_v_matches.inducts )
       case u_v_matches_empty then moreover   have "\<Gamma> = []" by (simp add: empty_def)
                                    ultimately show ?case    by simp
  next case (u_v_matches_none  \<Xi> \<sigma> xs xs' \<Gamma>' r w x x' i \<Gamma>)
       show ?case proof (cases i)
            case 0       with u_v_matches_none show ?thesis by ( cases "length \<Gamma>"
                                                               , simp_all add: empty_def )
       next case (Suc n)
         moreover with u_v_matches_none have "\<Gamma>' = empty (length \<Gamma> - 1) [n := Some \<tau>]"
                                         by (cases "length \<Gamma>", simp_all add: empty_def)
         moreover with u_v_matches_none have "length \<Gamma> = Suc (length \<Gamma>')"
                                         by (simp add: empty_def)
         ultimately show ?thesis apply -
                                 apply (insert u_v_matches_none)
                                 apply (auto).
       qed
  next case (u_v_matches_some)
       show ?case proof (cases i)
            case 0 with u_v_matches_some show ?thesis
              apply (cases "length \<Gamma>", simp_all add: empty_def)
              apply (clarsimp dest!:u_v_matches_empty_env(2) [simplified empty_def])
              apply (blast).
       next case (Suc n) with u_v_matches_some show ?thesis by ( cases "length \<Gamma>"
                                                                , simp_all add: empty_def )
       qed
  qed
qed



lemma u_v_matches_proj:
assumes "list_all2 (kinding []) \<tau>s K"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "K \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i \<tau>"
and     "i < length \<Gamma>"
shows   "\<exists> r' \<subseteq> r. \<Xi>, \<sigma> \<turnstile> (\<gamma> ! i) \<sim> (\<gamma>' ! i) : (instantiate \<tau>s \<tau>) \<langle>r', w\<rangle>"
using assms by (fastforce dest:   instantiate_ctx_weaken
                          intro!: u_v_matches_proj' [simplified])

lemma u_v_matches_proj_single':
assumes "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma> \<langle>r, w\<rangle>"
and     "i < length \<Gamma>"
and     "\<Gamma> ! i = Some \<tau>"
shows   "\<exists>r' w'. (r' \<subseteq> r) \<and> (w' \<subseteq> w) \<and> (\<Xi>, \<sigma> \<turnstile> (\<gamma> ! i) \<sim> (\<gamma>' ! i) : \<tau> \<langle>r', w'\<rangle>)"
using assms proof (induct arbitrary: i rule: u_v_matches.induct)
     case u_v_matches_empty then show ?case by simp
next case u_v_matches_none  then show ?case
  proof (cases i)
       case 0   with u_v_matches_none show ?thesis by simp
  next case Suc with u_v_matches_none show ?thesis by simp
  qed
next case u_v_matches_some then show ?case
  proof (cases i)
       case 0   with u_v_matches_some show ?thesis by auto
  next case Suc with u_v_matches_some show ?thesis
    apply (clarsimp dest!: u_v_matches_some(3))
    apply (rule_tac x = r'a in exI, rule, blast)
    apply (rule_tac x = w'a in exI, rule, blast)
    apply (simp)
  done
  qed
qed


lemma u_v_matches_proj_consumed':
assumes "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma> \<langle>r, w\<rangle>"
and     "[] \<turnstile> \<Gamma> consumed"
shows   "w = {}"
using assms proof(induction rule: u_v_matches.induct)
     case u_v_matches_empty then show ?case by auto
next case u_v_matches_none  then show ?case by (simp add: empty_def weakening_def)
next case u_v_matches_some  then show ?case by (auto simp: weakening_def empty_def
                                                     elim: weakening_comp.cases
                                                     dest: u_v_discardable_not_writable)
qed


lemma u_v_matches_proj_consumed:
assumes "list_all2 (kinding []) \<tau>s K"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "K \<turnstile> \<Gamma> consumed"
shows   "w = {}"
using assms by (auto dest:   instantiate_ctx_weaken
                     intro!: u_v_matches_proj_consumed')

lemma u_v_matches_proj_single:
assumes "list_all2 (kinding []) \<tau>s K"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "i < length \<Gamma>"
and     "\<Gamma> ! i = Some \<tau>"
shows   "\<exists> r' w'. (r' \<subseteq> r) \<and> (w' \<subseteq> w) \<and> (\<Xi>, \<sigma> \<turnstile> (\<gamma> ! i) \<sim> (\<gamma>' ! i) : instantiate \<tau>s \<tau> \<langle>r', w'\<rangle>)"
using assms by (auto intro!: u_v_matches_proj_single' [simplified]
                     simp:   instantiate_ctx_def)


section {* procedure environment matches *}

lemma proc_env_u_v_matches_abstract:
assumes "\<xi> \<sim> \<xi>' matches-u-v \<Xi>"
and     "\<Xi> f = (K, \<tau>i, \<tau>o)"
and     "list_all2 (kinding []) \<tau>s K"
and     "\<Xi> , \<sigma> \<turnstile> a \<sim> a'   : instantiate \<tau>s \<tau>i \<langle>r, w\<rangle>"
and     "\<xi> f (\<sigma>, a) (\<sigma>', v)"
and     "\<xi>' f a' v'"
shows   "\<exists>r' w'.
             \<Xi> , \<sigma>' \<turnstile> v \<sim> v' : instantiate \<tau>s \<tau>o \<langle>r', w'\<rangle>
            \<and> r' \<subseteq> r \<and> upd.frame \<sigma> w \<sigma>' w'"
  using assms by (clarsimp simp: proc_env_u_v_matches_def, drule_tac x = f in spec, fastforce)

section {* frame *}

lemma helper_one:
assumes "\<Xi>, \<sigma> \<turnstile>* vs \<sim> vs' : map TPrim \<tau>s \<langle>{}, {}\<rangle>"
shows "(map (\<lambda>vv. case vv of UPrim v \<Rightarrow> v | _ \<Rightarrow> LBool False) vs) =
       (map (\<lambda>vv. case vv of VPrim v \<Rightarrow> v | _ \<Rightarrow> LBool False) vs')"
using assms proof (induct rule: upd_val_rel_all.inducts)
     case u_v_all_empty then show ?case by simp
next case u_v_all_cons  then show ?case by (force elim: upd_val_rel.cases)
qed

lemma helper_two:
assumes "\<Xi>, \<sigma> \<turnstile>* vs \<sim> vs' : \<tau>s \<langle>{}, {}\<rangle>"
and     "\<tau>s = map TPrim \<tau>s'"
shows   "map lit_type (map (\<lambda>vv. case vv of UPrim v \<Rightarrow> v | _ \<Rightarrow> LBool False) vs) = \<tau>s'"
using assms proof (induct arbitrary: \<tau>s' rule: upd_val_rel_all.inducts)
case u_v_all_empty then show ?case by clarsimp
next case u_v_all_cons  then show ?case by (fastforce elim: upd_val_rel.cases)
qed

lemma eval_prim_u_v_corres:
assumes "prim_op_type p = (\<tau>s, \<tau>)"
and     "\<Xi> , \<sigma> \<turnstile>* vs \<sim> vs' : map TPrim \<tau>s \<langle>{}, {}\<rangle>"
shows   "\<Xi> , \<sigma> \<turnstile>  eval_prim_u p vs \<sim> eval_prim p vs' : TPrim \<tau> \<langle>{}, {}\<rangle>"
using assms
  apply (simp add: eval_prim_def)
  apply (simp add: eval_prim_u_def)
  apply (rule u_v_prim')
  apply (frule eval_prim_op_lit_type)
  apply (frule helper_two, rule refl)
  apply (assumption)
  apply (rule sym, assumption)
  apply (frule helper_one)
  apply (simp)
done

lemma upd_val_rel_valid:
assumes "p \<in> (r \<union> w)"
shows   "\<Xi> , \<sigma> \<turnstile>  u  \<sim> v  :  t  \<langle> r , w \<rangle> \<Longrightarrow> \<sigma> p \<noteq> None"
and     "\<Xi> , \<sigma> \<turnstile>* us \<sim> vs :r ts \<langle> r , w \<rangle> \<Longrightarrow> \<sigma> p \<noteq> None"
using assms by (auto dest: upd_val_rel_to_uval_typing intro: upd.uval_typing_valid [simplified])

lemma u_v_matches_valid:
assumes "\<Xi> , \<sigma> \<turnstile> u \<sim> u' matches t \<langle> r , w \<rangle>"
and     "p \<in> (r \<union> w)"
shows   "\<sigma> p \<noteq> None"
using assms by (auto dest: u_v_matches_to_matches_ptrs upd.matches_ptrs_valid)

lemma upd_val_rel_frame:
assumes "upd.frame \<sigma> w1 \<sigma>' w2"
and     "w \<inter> w1 = {}"
and     "r \<inter> w1 = {}"
shows   "\<Xi> , \<sigma> \<turnstile>  u  \<sim> v  :  t  \<langle> r , w \<rangle> \<Longrightarrow> \<Xi> , \<sigma>' \<turnstile>  u  \<sim> v  : t   \<langle> r , w \<rangle>"
and     "\<Xi> , \<sigma> \<turnstile>* us \<sim> vs :r ts \<langle> r , w \<rangle> \<Longrightarrow> \<Xi> , \<sigma>' \<turnstile>* us \<sim> vs :r ts \<langle> r , w \<rangle>"
using assms proof (induct rule:upd_val_rel_upd_val_rel_record.inducts)
     case u_v_prim     then show ?case by (auto simp add: upd_val_rel_upd_val_rel_record.u_v_prim)
next case u_v_product  then show ?case by (fastforce intro!: upd_val_rel_upd_val_rel_record.u_v_product)
next case u_v_sum      then show ?case by (fastforce intro!: upd_val_rel_upd_val_rel_record.u_v_sum)
next case u_v_struct   then show ?case by (fastforce intro!: upd_val_rel_upd_val_rel_record.u_v_struct)
next case u_v_abstract then show ?case by (simp add: upd_val_rel_upd_val_rel_record.u_v_abstract)
next case u_v_function then show ?case by (simp add: upd_val_rel_upd_val_rel_record.u_v_function)
next case u_v_afun     then show ?case by (simp add: upd_val_rel_upd_val_rel_record.u_v_afun)
next case u_v_unit     then show ?case by (simp add: upd_val_rel_upd_val_rel_record.u_v_unit)
next case u_v_p_rec_ro then show ?case by (auto intro!: upd_val_rel_upd_val_rel_record.u_v_p_rec_ro
                                                simp:   upd.frame_def)
next case u_v_p_rec_w  then show ?case by (auto intro!: upd_val_rel_upd_val_rel_record.u_v_p_rec_w
                                                simp:   upd.frame_def)
next case u_v_p_abs_ro then show ?case by (auto intro!: upd_val_rel_upd_val_rel_record.u_v_p_abs_ro
                                                simp:   upd.frame_def)
next case u_v_p_abs_w  then show ?case by (auto intro!: upd_val_rel_upd_val_rel_record.u_v_p_abs_w
                                                simp:   upd.frame_def)
next case u_v_r_empty  then show ?case by (simp add: upd_val_rel_upd_val_rel_record.u_v_r_empty)
next case u_v_r_cons1  then show ?case by (force intro!: upd_val_rel_upd_val_rel_record.u_v_r_cons1
                                                 simp: upd.frame_def)
next case u_v_r_cons2  then show ?case by (simp add: upd_val_rel_upd_val_rel_record.u_v_r_cons2)
qed

lemma u_v_matches_frame:
assumes "\<Xi> , \<sigma> \<turnstile> u \<sim> v matches t \<langle> r , w \<rangle>"
and     "upd.frame \<sigma> w1 \<sigma>' w2"
and     "w1 \<inter> w = {}"
and     "w1 \<inter> r = {}"
shows   "\<Xi> , \<sigma>' \<turnstile> u \<sim> v matches t \<langle> r , w \<rangle>"
using assms proof (induct rule: u_v_matches.induct)
     case u_v_matches_empty then show ?case by (simp add: u_v_matches.intros)
next case u_v_matches_none  then show ?case by (auto)
next case u_v_matches_some  then show ?case by (fast dest:   upd_val_rel_frame(1) [rotated -1]
                                                     intro!: u_v_matches.u_v_matches_some)
qed

lemma frame_noalias_upd_val_rel :
assumes "upd.frame \<sigma> u \<sigma>' u'"
and     "\<Xi>, \<sigma> \<turnstile> v \<sim> v' : \<tau> \<langle>r, w\<rangle>"
shows   "u  \<inter> w = {} \<Longrightarrow> u' \<inter> w = {}"
and     "u  \<inter> r = {} \<Longrightarrow> u' \<inter> r = {}"
  using assms by (auto dest: upd_val_rel_to_uval_typing upd.frame_noalias_uval_typing)

lemma frame_noalias_u_v_matches :
assumes "upd.frame \<sigma> u \<sigma>' u'"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma> \<langle>r, w\<rangle>"
shows   "u  \<inter> w = {} \<Longrightarrow> u' \<inter> w = {}"
and     "u  \<inter> r = {} \<Longrightarrow> u' \<inter> r = {}"
  using assms by (auto dest: u_v_matches_to_matches_ptrs upd.frame_noalias_matches_ptrs)

lemma frame_noalias_upd_val_rel' :
assumes "upd.frame \<sigma> u \<sigma>' u'"
and     "\<Xi>, \<sigma> \<turnstile> v \<sim> v' : \<tau> \<langle>r, w\<rangle>"
shows   "w \<inter> u = {} \<Longrightarrow> w \<inter> u' = {}"
and     "r \<inter> u = {} \<Longrightarrow> r \<inter> u' = {}"
using assms by (auto dest: upd_val_rel_to_uval_typing upd.frame_noalias_uval_typing)


lemma frame_noalias_2_uv :
assumes "upd.frame \<sigma>  u \<sigma>'  u'"
and     "upd.frame \<sigma>' w \<sigma>'' w'"
and     "\<Xi>, \<sigma>  \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma>  \<langle>r , w\<rangle>"
and     "\<Xi>, \<sigma>' \<turnstile> v \<sim> v' : \<tau> \<langle>r', u'\<rangle>"
and     "u \<inter> w = {}"
shows   "u' \<inter> w' = {}"
proof -
from assms(1,3,5) have "u' \<inter> w = {}"by (rule frame_noalias_u_v_matches)
with assms(2,4)   show ?thesis      by (rule frame_noalias_upd_val_rel')
qed


lemma upd_val_rel_record_nth:
assumes "\<Xi>, \<sigma> \<turnstile>* fs \<sim> fs' :r \<tau>s \<langle>r, {}\<rangle>"
and     "\<tau>s ! f = (\<tau>, False)"
and     "f < length \<tau>s"
shows "\<exists>r' \<subseteq> r. \<Xi>, \<sigma> \<turnstile> fst (fs ! f) \<sim> fs' ! f : \<tau> \<langle>r', {}\<rangle>"
using assms proof (induct fs arbitrary: fs' f r \<tau>s)
     case Nil  then show ?case by (fastforce elim!: upd_val_rel_record.cases)
next case Cons then show ?case
  proof (cases f)
       case 0   with Cons(2-) show ?thesis by (force elim!: u_v_r_consE')
  next case Suc with Cons(2-) show ?thesis by (elim u_v_r_consE', auto dest!: Cons(1))
  qed
qed


lemma sum_downcast_u_v:
  assumes u_v_sum_before: "\<Xi>, \<sigma> \<turnstile> USum t v xs \<sim> VSum t v' : TSum ts \<langle>r, w\<rangle>"
    and t_not_t': "t \<noteq> t'"
    and t'_in_ts: "(t', \<tau>', False) \<in> set ts"
  shows "\<Xi>, \<sigma> \<turnstile> USum t v xs \<sim> VSum t v' : TSum (tagged_list_update t' (\<tau>', True) ts) \<langle>r, w\<rangle>"
proof -
  obtain \<tau> k
    where "USum t v xs = USum t v (map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) ts)"
      and "VSum t v' = VSum t v'"
      and val_rel_v_v': "\<Xi>, \<sigma> \<turnstile> v \<sim> v' : \<tau> \<langle>r, w\<rangle>"
      and t_in_ts: "(t, \<tau>, False) \<in> set ts"
      and distinct_fst_ts: "distinct (map fst ts)"
      and wellformed_ts: "[] \<turnstile>* map (fst \<circ> snd) ts :\<kappa>  k"
      and xs_is: "xs = map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) ts"
    using u_v_sum_before by auto

  obtain i
    where list_update_i: "tagged_list_update t' (\<tau>', True) ts = ts[i := (t', \<tau>', True)]"
      and original_i: "ts ! i = (t', \<tau>', False)"
      and i_in_bounds: "i < length ts"
    using tagged_list_update_distinct distinct_fst_ts t'_in_ts
    by (metis fst_conv in_set_conv_nth)

  show ?thesis
    using val_rel_v_v' distinct_fst_ts t_in_ts t_not_t' tagged_list_update_different_tag_preserves_values2
  proof (intro u_v_sum)
    have "[] \<turnstile>* map (fst \<circ> snd) (tagged_list_update t' (\<tau>', True) ts) :\<kappa> k"
    proof (clarsimp simp add: kinding_all_set)
      fix tag \<tau>'' b
      assume tag_in_updated_ts: "(tag, \<tau>'', b) \<in> set (tagged_list_update t' (\<tau>', True) ts)"
      show "[] \<turnstile>  \<tau>'' :\<kappa>  k"
      proof (cases "tag = t'")
        case True

        have "(t', \<tau>', True) \<in> set (tagged_list_update t' (\<tau>', True) ts)"
          by (simp add: list_update_i i_in_bounds set_update_memI)
        then have \<tau>''_is: "\<tau>'' = \<tau>'"
          using True distinct_fst distinct_fst_ts tag_in_updated_ts
            tagged_list_update_preserves_tags
          by (metis Pair_inject)
        then show ?thesis
          using kinding_all_set t'_in_ts wellformed_ts by auto
      next
        case False
        moreover have "(tag, \<tau>'', b) \<in> set ts \<Longrightarrow> [] \<turnstile>  \<tau>'' :\<kappa>  k"
          using wellformed_ts kinding_all_set by auto
        ultimately show "[] \<turnstile>  \<tau>'' :\<kappa>  k"
          using tagged_list_update_different_tag_preserves_values2 tag_in_updated_ts by metis
      qed
    qed
    then show "[] \<turnstile>* map (fst \<circ> snd) (tagged_list_update t' (\<tau>', True) ts) wellformed"
      by auto
  next
    have "(\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) (t', \<tau>', False) = (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) (t', \<tau>', True)"
      by simp
    then show "xs = map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) (tagged_list_update t' (\<tau>', True) ts)"
      by (metis (no_types, lifting) xs_is list_update_i list_update_id map_update original_i)
  qed fastforce+
qed


lemma upd_val_rel_record_take:
assumes "\<Xi>, \<sigma> \<turnstile>* fs \<sim> fs' :r \<tau>s \<langle>r, w\<rangle>"
and     "\<tau>s ! f = (\<tau>, False)"
and     "[] \<turnstile> \<tau> wellformed"
and     "f < length \<tau>s"
shows   "\<exists>r' w' r'' w''. (\<Xi>, \<sigma> \<turnstile>  fst (fs ! f) \<sim> fs' ! f :  \<tau>                     \<langle>r' , w' \<rangle>)
                       \<and> (\<Xi>, \<sigma> \<turnstile>* fs           \<sim> fs'     :r (\<tau>s [f := (\<tau>, True)]) \<langle>r'', w''\<rangle>)
                       \<and> r = r' \<union> r''
                       \<and> w = w' \<union> w''
                       \<and> w' \<inter> w'' = {}"
using assms proof (induct fs arbitrary: fs' f r w \<tau>s)
     case Nil  then show ?case by (fastforce elim: upd_val_rel_record.cases)
next case Cons then show ?case
  proof (cases f)
       case 0   with Cons(2-) show ?thesis by ( clarsimp, elim u_v_r_consE'
                                              , auto intro!: exI
                                                             upd_val_rel_upd_val_rel_record.intros
                                                       simp: upd.type_repr_uval_repr_deep(1)[OF upd_val_rel_to_uval_typing(1)]
                                                             upd.type_repr_uval_repr(1)[OF upd_val_rel_to_uval_typing(1)])
  next case Suc with Cons(2-) show ?thesis
    apply (clarsimp)
    apply (erule u_v_r_consE')
     apply (clarsimp, frule(2) Cons(1) [OF _ _ assms(3)])
     apply (blast intro: upd_val_rel_upd_val_rel_record.intros)
    apply (clarsimp, frule(2) Cons(1) [OF _ _ assms(3)])
    apply (fastforce intro!: upd_val_rel_upd_val_rel_record.intros)
  done
  qed
qed

lemma upd_val_rel_record_put_taken:
assumes "\<Xi>, \<sigma> \<turnstile>  v  \<sim> v'  :  t  \<langle>r'b, w'b\<rangle>"
and     "\<Xi>, \<sigma> \<turnstile>* fs \<sim> fs' :r ts \<langle>r'a, w'a\<rangle>"
and     "ts ! f = (t, True)"
and     "w'b \<inter> r'a = {}"
and     "w'a \<inter> r'b = {}"
and     "w'a \<inter> w'b = {}"
and     "f < length ts"
shows   "\<Xi>, \<sigma> \<turnstile>* fs[f := (v, snd(fs!f))] \<sim> fs'[f := v'] :r (ts[f := (t, False)]) \<langle>r'a \<union> r'b, w'a \<union> w'b\<rangle>"
using assms proof (induct fs arbitrary: fs' f r'a w'a ts)
case Nil then show ?case by (auto elim!: upd_val_rel_record.cases)
next case Cons then show ?case
  proof (cases f)
       case 0   with Cons(2-) show ?thesis
         apply (clarsimp)
         apply (elim u_v_r_consE', simp)
         apply (rule u_v_pointerset_helper_record, (fastforce intro!: u_v_r_cons2 u_v_r_cons1)+)
       done
  next case Suc with Cons(2-) show ?thesis
         apply (clarsimp)
         apply (elim u_v_r_consE')
          apply (frule(1) Cons(1), simp, blast,blast,blast ,simp)
          apply (clarsimp, rule u_v_pointerset_helper_record, force intro!: u_v_r_cons1, blast, blast)
         apply (frule(1) Cons(1), simp, blast,blast,blast ,simp)
         apply (clarsimp, rule u_v_pointerset_helper_record, force intro!: u_v_r_cons2, blast, blast)
       done
  qed
qed

lemma upd_val_rel_record_put_discardable:
assumes "\<Xi>, \<sigma> \<turnstile>  v  \<sim> v'  :  t  \<langle>r'b, w'b\<rangle>"
and     "\<Xi>, \<sigma> \<turnstile>* fs \<sim> fs' :r ts \<langle>r'a, w'a\<rangle>"
and     "ts ! f = (t, False)"
and     "[] \<turnstile> t :\<kappa> k"
and     "D \<in> k"
and     "w'b \<inter> r'a = {}"
and     "w'a \<inter> r'b = {}"
and     "w'a \<inter> w'b = {}"
and     "f < length ts"
shows   "\<exists>r''a\<subseteq> r'a. \<Xi>, \<sigma> \<turnstile>* fs[f := (v, snd(fs!f))] \<sim> fs'[f := v'] :r (ts[f := (t, False)]) \<langle>r''a \<union> r'b, w'a \<union> w'b\<rangle>"
using assms proof (induct fs arbitrary: fs' f r'a w'a ts)
case Nil then show ?case by (auto elim!: upd_val_rel_record.cases)
next case Cons then show ?case
  proof (cases f)
       case 0   with Cons(2-) show ?thesis
         apply (clarsimp)
         apply (frule(2) u_v_discardable_not_writable)
         apply (elim u_v_r_consE', simp)
         apply (rotate_tac 3, frule(2) u_v_discardable_not_writable)
         apply (rule_tac x = r' in exI)
         apply (rule, blast)
         apply (rule u_v_pointerset_helper_record,(fastforce intro!:  u_v_r_cons2 u_v_r_cons1)+)
       done
  next case Suc with Cons(2-) show ?thesis
         apply (clarsimp)
         apply (elim u_v_r_consE')
          apply (frule(1) Cons(1), simp,blast,blast,blast,blast,blast, simp)
          apply (clarsimp, rule_tac x = "r \<union> r''a" in exI, rule, blast)
          apply (rule u_v_pointerset_helper_record,(force intro!: u_v_r_cons2 u_v_r_cons1), blast,blast)
         apply (frule(1) Cons(1), simp,blast,blast,blast,blast,blast, simp)
         apply (clarsimp, rule_tac x = "r''a" in exI, rule, blast)
         apply (rule u_v_pointerset_helper_record,(fastforce intro!:  u_v_r_cons2 u_v_r_cons1)+)
    done
  qed
qed


lemma upd_val_rel_record_put:
assumes "\<Xi>, \<sigma> \<turnstile>  v \<sim> v' :  t  \<langle>r'b, w'b\<rangle>"
and     "\<Xi>, \<sigma> \<turnstile>* fs \<sim> fs' :r ts \<langle>r'a, w'a\<rangle>"
and     "ts ! f = (t, taken)"
and     "D \<in> k \<or> taken"
and     "w'b \<inter> r'a = {}"
and     "w'a \<inter> r'b = {}"
and     "w'a \<inter> w'b = {}"
and     "f < length ts"
and     "[] \<turnstile> t :\<kappa> k"
shows   "\<exists>r''a\<subseteq> r'a. \<Xi>, \<sigma> \<turnstile>* fs[f := (v, snd(fs!f))] \<sim> fs'[f := v'] :r (ts[f := (t, False)]) \<langle>r''a \<union> r'b, w'a \<union> w'b\<rangle>"
using assms proof (cases taken)
     case False with assms show ?thesis by (fastforce intro!: upd_val_rel_record_put_discardable)
next case True  with assms show ?thesis by (fastforce intro!: upd_val_rel_record_put_taken)
qed

inductive_cases v_sem_primE   [elim!] : " \<xi> , \<gamma> \<turnstile> (Prim p as) \<Down> v"
inductive_cases v_sem_litE    [elim!] : " \<xi> , \<gamma> \<turnstile> Lit l \<Down> v"
inductive_cases v_sem_funE    [elim!] : " \<xi> , \<gamma> \<turnstile> Fun e ts \<Down> v"
inductive_cases v_sem_unitE   [elim!] : " \<xi> , \<gamma> \<turnstile> Unit \<Down> v"
inductive_cases v_sem_castE   [elim!] : " \<xi> , \<gamma> \<turnstile> Cast a b \<Down> v"
inductive_cases v_sem_esacE   [elim!] : " \<xi> , \<gamma> \<turnstile> Esac e \<Down> v"
inductive_cases v_sem_splitE  [elim!] : " \<xi> , \<gamma> \<turnstile> Split e e' \<Down> v"
inductive_cases v_sem_letE    [elim!] : " \<xi> , \<gamma> \<turnstile> Let e1 e2 \<Down> v"
inductive_cases v_sem_letbE   [elim!] : " \<xi> , \<gamma> \<turnstile> LetBang is e1 e2 \<Down> v"
inductive_cases v_sem_takeE   [elim!] : " \<xi> , \<gamma> \<turnstile> Take e f e' \<Down> v"
inductive_cases v_sem_conE    [elim!] : " \<xi> , \<gamma> \<turnstile> Con ts t e \<Down> v"
inductive_cases v_sem_appE    [elim!] : " \<xi> , \<gamma> \<turnstile> App e e' \<Down> v"
inductive_cases v_sem_caseE   [elim]  : " \<xi> , \<gamma> \<turnstile> Case e t m nm \<Down> v"
inductive_cases v_sem_ifE     [elim!] : " \<xi> , \<gamma> \<turnstile> If c t e \<Down> v"
inductive_cases v_sem_memberE [elim!] : " \<xi> , \<gamma> \<turnstile> Member e f \<Down> v"
inductive_cases v_sem_putE    [elim!] : " \<xi> , \<gamma> \<turnstile> Put e f e' \<Down> v"
inductive_cases v_sem_structE [elim!] : " \<xi> , \<gamma> \<turnstile> Struct fs ts \<Down> v"
inductive_cases v_sem_tupleE  [elim!] : " \<xi> , \<gamma> \<turnstile> Tuple a b \<Down> v"
inductive_cases v_sem_all_emptyE [elim!] : " \<xi> , \<gamma> \<turnstile>* [] \<Down> v"
inductive_cases v_sem_all_consE  [elim!] : " \<xi> , \<gamma> \<turnstile>* x # xs \<Down> v"

lemma u_v_p_rec_w':
assumes "\<Xi>, \<sigma> \<turnstile>* fs \<sim> fs' :r ts \<langle>r, w\<rangle>"
and     "\<sigma> l = Some (URecord fs)"
and     "l \<notin> w \<union> r"
and     "rp = (RRecord (map (\<lambda>(a,b). type_repr a) ts)) "
shows   "\<Xi>, \<sigma> \<turnstile> UPtr l rp \<sim> VRecord fs' : TRecord ts Writable \<langle> r, insert l w \<rangle>"
using assms by (auto intro: u_v_p_rec_w)

theorem correspondence:
assumes "list_all2 (kinding []) \<tau>s K"
and     "proc_ctx_wellformed \<Xi>"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "\<xi> \<sim> \<xi>' matches-u-v \<Xi>"
shows   "\<lbrakk> \<xi> , \<gamma>  \<turnstile> (\<sigma>, specialise \<tau>s e) \<Down>! (\<sigma>', v)
         ; \<xi>', \<gamma>' \<turnstile>     specialise \<tau>s e  \<Down>       v'
         ; \<Xi>, K, \<Gamma> \<turnstile> e : \<tau>
         \<rbrakk> \<Longrightarrow> \<exists>r' w'. (\<Xi> , \<sigma>' \<turnstile> v \<sim> v' : instantiate \<tau>s \<tau> \<langle>r', w'\<rangle>)
                     \<and> r' \<subseteq> r
                     \<and> upd.frame \<sigma> w \<sigma>' w'"
and     "\<lbrakk> \<xi> , \<gamma>  \<turnstile>* (\<sigma>, map (specialise \<tau>s) es) \<Down>! (\<sigma>', vs)
         ; \<xi>', \<gamma>' \<turnstile>*     map (specialise \<tau>s) es  \<Down>       vs'
         ; \<Xi>, K, \<Gamma> \<turnstile>* es : \<tau>s'
         \<rbrakk> \<Longrightarrow> \<exists>r' w'. (\<Xi>, \<sigma>' \<turnstile>* vs \<sim> vs' : map (instantiate \<tau>s) \<tau>s' \<langle>r', w'\<rangle>)
                     \<and> r' \<subseteq> r
                     \<and> upd.frame \<sigma> w \<sigma>' w'"
using assms proof (induct "(\<sigma>, specialise \<tau>s e)"        "(\<sigma>', v )"
                      and "(\<sigma>, map (specialise \<tau>s) es)" "(\<sigma>', vs)"
                      arbitrary:  e  \<tau>s K \<tau>   \<Gamma> r w v  \<sigma>' \<sigma> \<gamma>' v'
                             and  es \<tau>s K \<tau>s' \<Gamma> r w vs \<sigma>' \<sigma> \<gamma>' vs'
                      rule: u_sem_u_sem_all.inducts)
     case u_sem_var       then show ?case by ( cases e, simp_all
                                             , fastforce elim!:  typing_varE
                                                         dest!:  u_v_matches_proj
                                                         intro:  upd.frame_id)
next case u_sem_prim      then show ?case by ( cases e, simp_all
                                             , auto      elim!:  typing_primE
                                                         dest!:  u_sem_prim(2)
                                                         intro!: exI u_v_map_tprim_no_pointers'
                                                         intro:  eval_prim_u_v_corres
                                                         dest:   u_v_map_tprim_no_pointers)
next case u_sem_lit       then show ?case by ( cases e, simp_all
                                             , fastforce dest:   u_v_matches_proj_consumed
                                                         intro!: upd_val_rel_upd_val_rel_record.intros
                                                                 upd.frame_id)
next case u_sem_fun       then show ?case by ( cases e, simp_all
                                             , force elim!:  typing_funE
                                                     dest:   typing_to_kinding u_v_matches_proj_consumed
                                                     intro!: exI u_v_function_instantiate upd.frame_id)
next case u_sem_afun      then show ?case apply (cases e, simp_all)
                                          apply (fastforce elim!:  typing_afunE v_sem_afunE
                                                           intro!: u_v_afun_instantiate upd.frame_id
                                                           dest:   u_v_matches_proj_consumed).
next case u_sem_app
  note IH1  = this(2)
  and  IH2  = this(4)
  and  IH3  = this(6)
  and  rest = this(1,3,5,7-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (clarsimp elim!: typing_appE)
    apply (frule u_v_matches_noalias)
    apply (frule(2) u_v_matches_split, clarsimp)
    apply (erule v_sem_appE)

    apply (frule(6) IH1, clarsimp)
    apply (erule upd_val_rel.cases, simp_all)

    apply (frule(6) IH1, clarsimp)

    apply (erule u_v_functionE)
    apply (clarsimp)
    apply (frule(8) IH2 [OF _ _ _ _ _  u_v_matches_frame, rotated -1])
     apply (fastforce intro!: upd.subset_helper dest: upd.subset_helper2 upd.subset_helper2')
    apply (clarsimp elim!: u_v_functionE)
    apply (frule(4) IH3 [OF refl, rotated -1])
     apply (force intro!: u_v_matches.intros simp: instantiate_ctx_def)
    apply (clarsimp, auto intro!: exI
                          intro:  upd.frame_trans upd.subset_helper2'
                          dest:   upd.frame_app [where w' = "{}", simplified])
  done
next case u_sem_abs_app
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (clarsimp elim!: typing_appE)
    apply (frule u_v_matches_noalias)
    apply (frule(2) u_v_matches_split, clarsimp)
    apply (erule v_sem_appE)
     apply (frule(6) IH1, clarsimp)
     apply (frule(8) IH2 [OF _ _ _ _ _ u_v_matches_frame, rotated -1])
      apply (fastforce intro!: upd.subset_helper dest: upd.subset_helper2 upd.subset_helper2')
     apply (clarsimp elim!: u_v_afunE)
     apply (frule(5) proc_env_u_v_matches_abstract)
     apply (clarsimp)
     apply (intro exI conjI, force, blast)
     apply (force intro: upd.frame_trans upd.subset_helper2' dest: upd.frame_app [where w'="{}",simplified])
    apply (frule(6) IH1, clarsimp)
    apply (erule upd_val_rel.cases,simp_all)
  done
next
  case (u_sem_con \<xi> \<gamma> \<sigma> x_spec \<sigma>' x'' ts_inst tag')
  then show ?case
  proof (cases e)
  next
    case (Con ts tag x)

    have ts_inst_is: "ts_inst = map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts"
      and tag'_is: "tag' = tag"
      and x_spec_is: "x_spec = specialise \<tau>s x"
      using u_sem_con.hyps(3) Con
      by simp+

    obtain xa
      where v'_is: "v' = VSum tag xa"
        and vsem_specialised_x: "\<xi>' , \<gamma>' \<turnstile> specialise \<tau>s x \<Down> xa"
      using u_sem_con.prems(1) Con by auto

    obtain t k
      where \<tau>_is: "\<tau> = TSum ts"
        and typing_x: "\<Xi>, K, \<Gamma> \<turnstile> x : t"
        and tag_in_ts: "(tag, t, False) \<in> set ts"
        and distinct_fst_ts: "distinct (map fst ts)"
        and ts_wellformed: "K \<turnstile>* map (fst \<circ> snd) ts :\<kappa>  k"
      using typing_conE u_sem_con.prems(2) Con
      by auto

    obtain r' w'
      where "\<Xi>, \<sigma>' \<turnstile> x'' \<sim> xa : instantiate \<tau>s t \<langle>r', w'\<rangle>"
        and r'_sub_r: "r' \<subseteq> r"
        and frame_w_w': "upd.frame \<sigma> w \<sigma>' w'"
      using u_sem_con.hyps(2) x_spec_is vsem_specialised_x typing_x u_sem_con.prems
      by blast
    then have "\<Xi>, \<sigma>' \<turnstile> USum tag x'' (map ((\<lambda>(n, t, _). (n, type_repr t)) \<circ> (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b))) ts)
                        \<sim> VSum tag xa : TSum (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts) \<langle>r', w'\<rangle>"
      using tag_in_ts  distinct_fst_ts
    proof (intro upd_val_rel_upd_val_rel_record.u_v_sum)
      have "[] \<turnstile>* map (instantiate \<tau>s \<circ> (fst \<circ> snd)) ts :\<kappa>  k"
        using substitutivity(2) u_sem_con.prems(3) ts_wellformed
        by fastforce
      then show "[] \<turnstile>* map (fst \<circ> snd) (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts) wellformed"
        by force
    qed force+
    then show ?thesis
      using r'_sub_r frame_w_w' v'_is \<tau>_is tag'_is ts_inst_is
      by auto
  qed simp+
next case u_sem_let
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (clarsimp elim!: typing_letE)
    apply (frule u_v_matches_noalias)
    apply (frule(2) u_v_matches_split, clarsimp)
    apply (frule(6) IH1, clarsimp)
    apply (frule(5) IH2 [rotated -1], clarsimp)
    apply (rule,force)
        apply (force intro: u_v_matches_frame)
       apply (force dest: frame_noalias_u_v_matches(1))
      apply (force dest!: frame_noalias_u_v_matches(2))
     apply (blast)
    apply (fastforce intro: upd.frame_let simp: Un_commute)
  done

next case u_sem_letbang
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (clarsimp elim!: typing_letbE)
    apply (frule u_v_matches_noalias)
    apply (frule(2) u_v_matches_split_bang, clarsimp)
    apply (frule(6) IH1, clarsimp)
    apply (frule(3) u_v_escapable_no_readers(1) [OF _ _ substitutivity(1)], clarsimp)
    apply (frule(5) IH2 [rotated -1], clarsimp)
     apply (rule, force)
        apply (force intro: u_v_matches_frame)
       apply (rule frame_noalias_u_v_matches(1), simp+, blast)
      apply (rule frame_noalias_u_v_matches(2), simp+, blast)
     apply (simp)
    apply (clarsimp)
    apply (auto intro!: exI
                simp:   Un_assoc
                intro:  upd.frame_let
                intro:  upd.pointerset_helper_frame [OF _ _ refl])
  done

next case u_sem_unit      then show ?case by ( cases e, simp_all
                                             , auto elim!:  typing_unitE
                                                    intro!: exI
                                                    dest!:  u_v_matches_proj_consumed
                                                    intro:  upd.frame_id
                                                            upd_val_rel_upd_val_rel_record.intros)

next case u_sem_cast      then show ?case apply ( cases e, simp_all)
                                          apply ( slowsimp intro!: u_v_prim'
                                                           elim!:  typing_castE
                                                                   upd_val_rel.cases
                                                                   upcast_valid_cast_to).

next case u_sem_tuple
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (clarsimp elim!: typing_tupleE)
    apply (frule u_v_matches_noalias)
    apply (frule(2) u_v_matches_split, clarsimp)
    apply (frule(6) IH1, clarsimp)
    apply (frule(2) u_v_matches_frame, blast)
    apply (frule(6) IH2, clarsimp)
    apply (frule(1) upd.frame_app)

    apply (frule(2) frame_noalias_u_v_matches(2) [where u = "w \<union> w'" for w and w'])
    apply (frule(4) upd_val_rel_frame [rotated -1, OF _ _ frame_noalias_u_v_matches(1)], blast)
    apply (frule(4) frame_noalias_2_uv)
    apply (blast intro!: upd_val_rel_upd_val_rel_record.intros)
  done
next
  case (u_sem_esac \<xi> \<gamma> \<sigma> t \<sigma>' tagu v tsu')
  then show ?case
  proof (cases e)
    case (Esac x1)

    have t_is: "t = specialise \<tau>s x1"
      using u_sem_esac.hyps(3) Esac by simp

    obtain tag
      where v_sem_specialise_x1: "\<xi>' , \<gamma>' \<turnstile> specialise \<tau>s x1 \<Down> VSum tag v'"
      using u_sem_esac.prems(1) Esac by auto

    obtain tsty tag'
      where typing_x1: "\<Xi>, K, \<Gamma> \<turnstile> x1 : TSum tsty"
        and "[(tag', \<tau>, False)] = filter (HOL.Not \<circ> snd \<circ> snd) tsty"
      using typing_esacE u_sem_esac.prems(2) Esac
      by auto
    then have "set [(tag', \<tau>, False)] = set (filter (HOL.Not \<circ> snd \<circ> snd) tsty)"
      by presburger
    then have tag'_last_case: "{(tag', \<tau>, False)} = {(c, t, b) \<in> set tsty. \<not> b}"
      by force

    obtain r' w'
      where "\<Xi>, \<sigma>' \<turnstile> USum tagu v tsu' \<sim> VSum tag v' : instantiate \<tau>s (TSum tsty) \<langle>r', w'\<rangle>"
        and r'_sub_r: "r' \<subseteq> r"
        and frame_w_w': "upd.frame \<sigma> w \<sigma>' w'"
      using u_sem_esac.hyps(2) u_sem_esac.prems t_is v_sem_specialise_x1 typing_x1
      by blast
    then obtain ta k
      where tagu_is: "tagu = tag"
        and tsu'_is: "tsu' = map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) tsty)"
        and u_v_sem_v_v'_ta: "\<Xi>, \<sigma>' \<turnstile> v \<sim> v' : ta \<langle>r', w'\<rangle>"
        and "(tag, ta, False) \<in> (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ` set tsty"
        and "distinct (map fst tsty)"
        and "[] \<turnstile>* map (fst \<circ> snd) (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) tsty) :\<kappa>  k"
      by auto
    then obtain t''
      where ta_is: "ta = instantiate \<tau>s t''"
        and "(tag, t'', False) \<in> set tsty"
      by fast
    moreover have "\<And>c t. (c, t, False) \<in> set tsty \<Longrightarrow> c = tag' \<and> t = \<tau>"
      using tag'_last_case
      by (metis (no_types, lifting) mem_Collect_eq prod.simps(1) singletonD split_conv)
    ultimately have tag_is: "tag = tag'"
      and t''_Is: "t'' = \<tau>"
      by blast+
    then have " \<Xi>, \<sigma>' \<turnstile> v \<sim> v' : instantiate \<tau>s \<tau> \<langle>r', w'\<rangle>"
      using u_v_sem_v_v'_ta ta_is by simp
    then show ?thesis
      using r'_sub_r frame_w_w' by blast
  qed simp+

next
  case (u_sem_case_nm \<xi> \<gamma> \<sigma>a x \<sigma>a' tag va rs tag'' n m)
  then show ?case
  proof (cases e)
    case (Case x' tag' m' n')

    have x_is: "x = specialise \<tau>s x'"
      and tag''_is: "tag'' = tag'"
      and m_is: "m = specialise \<tau>s m'"
      and n_is: "n = specialise \<tau>s n'"
      using Case u_sem_case_nm.hyps(6)
      by simp+
    then have vsem_case: "\<xi>' , \<gamma>' \<turnstile> Case (specialise \<tau>s x') tag' (specialise \<tau>s m') (specialise \<tau>s n') \<Down> v'"
      using u_sem_case_nm.prems(1) u_sem_case_nm.hyps(6) by simp

    have "\<Xi>, K, \<Gamma> \<turnstile> Case x' tag' m' n' : \<tau>"
      using Case u_sem_case_nm.prems
      by simp
    then obtain \<Gamma>1 \<Gamma>2 ts t
      where split_\<Gamma>: "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
        and typing_x': "\<Xi>, K, \<Gamma>1 \<turnstile> x' : TSum ts"
        and tag'_in_ts: "(tag', t, False) \<in> set ts"
        and "\<Xi>, K, Some t # \<Gamma>2 \<turnstile> m' : \<tau>"
        and typing_n': "\<Xi>, K, Some (TSum (tagged_list_update tag' (t, True) ts)) # \<Gamma>2 \<turnstile> n' : \<tau>"
      by auto
    then obtain r1 w1 r2 w2
      where matches1: "\<Xi>, \<sigma>a \<turnstile> \<gamma> \<sim> \<gamma>' matches instantiate_ctx \<tau>s \<Gamma>1 \<langle>r1, w1\<rangle>"
        and matches2: "\<Xi>, \<sigma>a \<turnstile> \<gamma> \<sim> \<gamma>' matches instantiate_ctx \<tau>s \<Gamma>2 \<langle>r2, w2\<rangle>"
        and r_as_un: "r = r1 \<union> r2"
        and w_as_un: "w = w1 \<union> w2"
        and w1_w2_disjoint: "w1 \<inter> w2 = {}"
      using u_sem_case_nm.prems(3,5) u_v_matches_split by blast
    then have w1_r2_disjoint: "w1 \<inter> r2 = {}"
      and w2_r1_disjoint: "w2 \<inter> r1 = {}"
      using u_sem_case_nm.prems(5) u_v_matches_noalias
      by blast+

    obtain vx
      where vsem_specialise_x': "\<xi>' , \<gamma>' \<turnstile> specialise \<tau>s x' \<Down> VSum tag vx"
        and vsem_specialise_n': "\<xi>' , VSum tag vx # \<gamma>' \<turnstile> specialise \<tau>s n' \<Down> v'"
      using vsem_case
    proof (cases rule: v_sem.cases)
      case (v_sem_case_m v)
      then obtain r' w'
        where "\<Xi>, \<sigma>a' \<turnstile> USum tag va rs \<sim> VSum tag' v : instantiate \<tau>s (TSum ts) \<langle>r', w'\<rangle>"
        using u_sem_case_nm.hyps(2) u_sem_case_nm.prems x_is typing_x' matches1
        by blast
      then have "tag = tag'"
        by auto
      then show ?thesis
        using u_sem_case_nm.hyps(3) tag''_is
        by simp
    next
      case (v_sem_case_nm taga v)
      moreover then have taga_is: "taga = tag"
        using u_sem_case_nm.hyps(2) u_sem_case_nm.prems x_is v_sem_case_nm typing_x' matches1
        by fastforce
      moreover assume "\<And>v. \<lbrakk> \<xi>' , \<gamma>' \<turnstile> specialise \<tau>s x' \<Down> VSum tag v; \<xi>' , VSum tag v # \<gamma>' \<turnstile> specialise \<tau>s n' \<Down> v' \<rbrakk> \<Longrightarrow> thesis"
      ultimately show ?thesis
        by blast
    qed
    then obtain w1' r1'
      where u_v_rel_sum_tag: "\<Xi>, \<sigma>a' \<turnstile> USum tag va rs \<sim> VSum tag vx : instantiate \<tau>s (TSum ts) \<langle>r1', w1'\<rangle>"
        and r_sub1: "r1' \<subseteq> r1"
        and frame1: "upd.frame \<sigma>a w1 \<sigma>a' w1'"
      using u_sem_case_nm.hyps(2) u_sem_case_nm.prems x_is v_sem_case_nm typing_x' matches1
      by blast


    have "\<Xi>, \<sigma>a' \<turnstile> USum tag va rs # \<gamma> \<sim> VSum tag vx # \<gamma>' matches instantiate_ctx \<tau>s (Some (TSum (tagged_list_update tag' (t, True) ts)) # \<Gamma>2) \<langle>r1' \<union> r2, w1' \<union> w2 \<rangle>"
      using frame1 frame_noalias_u_v_matches matches2 w1_w2_disjoint w1_r2_disjoint r_sub1 w2_r1_disjoint
    proof (simp add: r_as_un w_as_un, intro u_v_matches_some)
      obtain t' k
        where rs_is: "rs = (map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts))"
          and u_v_rel_va_vx: "\<Xi>, \<sigma>a' \<turnstile> va \<sim> vx : t' \<langle>r1', w1'\<rangle>"
          and tag_in_instantiated_ts: "(tag, t', False) \<in> set (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts)"
          and distinct_fst_ts: "distinct (map fst ts)"
          and wellformed_instantiated_ts: "[] \<turnstile>* map (fst \<circ> snd) (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts) :\<kappa>  k"
        using u_v_rel_sum_tag
        by auto

      obtain i
        where updated_ts_is: "tagged_list_update tag' (t, True) ts = ts[i := (tag', t, True)]"
          and ts_at_i: "ts ! i = (tag', t, False)"
          and inst_ts_at_i: "(map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts) ! i = (tag', instantiate \<tau>s t, False)"
        using tag'_in_ts distinct_fst_ts tagged_list_update_distinct
        by (force simp add: in_set_conv_nth)

      show "\<Xi>, \<sigma>a' \<turnstile> USum tag va rs \<sim> VSum tag vx : TSum (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) (tagged_list_update tag' (t, True) ts)) \<langle>r1', w1'\<rangle>"
        using u_v_rel_va_vx
      proof (intro u_v_sum)
        obtain j
          where inst_ts_at_j: "(map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) ts) ! j = (tag, t', False)"
            and j_bounded_len_ts: "j < length ts"
          using tag_in_instantiated_ts
          by (metis (no_types, lifting) in_set_conv_nth length_map)

        have i_neq_j: "i \<noteq> j"
          using inst_ts_at_i inst_ts_at_j tag''_is u_sem_case_nm.hyps(3)
          by auto

        show "(tag, t', False) \<in> set (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) (tagged_list_update tag' (t, True) ts))"
          using i_neq_j j_bounded_len_ts inst_ts_at_j
          by (simp add: updated_ts_is,
              metis (no_types, lifting) length_list_update list_update_id list_update_swap
              rev_image_eqI set_update_memI)
      next
        have "distinct (map fst (tagged_list_update tag' (t, True) ts))"
          by (metis distinct_fst_ts tagged_list_update_preserves_tags)
        then show "distinct (map fst (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) (tagged_list_update tag' (t, True) ts)))"
          by simp
      next
        have wellformed_ignores_taken: "(instantiate \<tau>s \<circ> (fst \<circ> snd)) (tag', t, False) = (instantiate \<tau>s \<circ> (fst \<circ> snd)) (tag', t, True)"
          by auto

        have "[] \<turnstile>* map (instantiate \<tau>s \<circ> (fst \<circ> snd)) ts :\<kappa>  k"
          using wellformed_instantiated_ts
          by simp
        then have "[] \<turnstile>* map (instantiate \<tau>s \<circ> (fst \<circ> snd)) (tagged_list_update tag' (t, True) ts) :\<kappa>  k"
          by (metis (no_types, lifting) wellformed_ignores_taken list_update_id map_update ts_at_i updated_ts_is)
        then show "[] \<turnstile>* map (fst \<circ> snd) (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) (tagged_list_update tag' (t, True) ts)) wellformed"
          by auto
      next
        have "map ((\<lambda>(cs, t, b). (cs, type_repr t)) \<circ> (\<lambda>(cs, t, b). (cs, instantiate \<tau>s t, b))) ts
            = map ((\<lambda>(cs, t, b). (cs, type_repr t)) \<circ> (\<lambda>(cs, t, b). (cs, instantiate \<tau>s t, b))) ts [i := ((\<lambda>(cs, t, b). (cs, type_repr t)) \<circ> (\<lambda>(cs, t, b). (cs, instantiate \<tau>s t, b))) (tag', t, False)]"
          by (metis (no_types) list_update_id map_update ts_at_i)
        then have "map ((\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) \<circ> (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b))) ts
                  = map ((\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) \<circ> (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b))) (tagged_list_update tag' (t, True) ts)"
          by (simp add: map_update updated_ts_is)
        then show "rs = map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) (map (\<lambda>(c, t, b). (c, instantiate \<tau>s t, b)) (tagged_list_update tag' (t, True) ts))"
          using rs_is by simp
      qed
    next
      show "\<Xi>, \<sigma>a' \<turnstile> \<gamma> \<sim> \<gamma>' matches instantiate_ctx \<tau>s \<Gamma>2 \<langle>r2, w2\<rangle>"
        using u_sem_case_nm.prems(5) frame1 matches2 r_as_un
          u_v_matches_frame u_v_matches_noalias
          w1_w2_disjoint w_as_un
        by blast
    qed fast+
    then obtain r12' w12'
      where "\<Xi>, \<sigma>' \<turnstile> v \<sim> v' : instantiate \<tau>s \<tau> \<langle>r12', w12'\<rangle>"
        and r_sub12: "r12' \<subseteq> r1' \<union> r2"
        and frame12: "upd.frame \<sigma>a' (w1' \<union> w2) \<sigma>' w12'"
      using u_sem_case_nm.hyps(5) n_is vsem_specialise_n' typing_n' u_sem_case_nm.prems
      by blast
    moreover have "upd.frame \<sigma>a w \<sigma>' w12'"
      by (metis upd.frame_let w_as_un frame1 frame12 inf_sup_aci(5))
    ultimately show ?thesis
      using r_as_un r_sub1 by auto
  qed simp+

next case u_sem_case_m
  note IH1 = this(2)
  and  IH2 = this(4)
  and rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (erule typing_caseE)
    apply (frule u_v_matches_noalias)
    apply (frule(2) u_v_matches_split, clarsimp)
    apply (erule v_sem_caseE)
     apply (frule(6) IH1,clarsimp)
     apply (frule(2) frame_noalias_u_v_matches)
     apply (frule(1) frame_noalias_u_v_matches(2), blast)
     apply (frule(2) u_v_matches_frame, blast)
     apply (erule u_v_sumE, clarsimp)
      apply (drule(1) distinct_fst [rotated 1],simp,simp)
     apply (frule(5) IH2 [rotated -1])
      apply (force intro!: u_v_matches_some)
     apply (clarsimp, force intro!: exI simp: Un_commute intro: upd.frame_let)
    apply (force dest!: IH1 elim: upd_val_rel.cases)
  done
next case (u_sem_if _ _ _ _ _ b)
  note IH1 = this(2)
  and  IH2 = this(4)
  and rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (frule u_v_matches_noalias)
    apply (erule typing_ifE)
    apply (frule(2) u_v_matches_split, clarsimp)
    apply (frule(6) IH1, clarsimp)
    apply (erule u_v_primE)
    apply (clarsimp)
    apply (frule(4) IH2 [ rotated 3
                        , where e23 (* FIXME: unstable name *) = "if b then e2 else e3" for e2 and e3
                        , OF _ _ u_v_matches_frame ])
         apply (blast, simp)
       apply (cases b, simp, simp)+
    apply (fastforce intro: upd.frame_let)
  done
next case u_sem_struct    then show ?case by ( cases e, simp_all
                                             , fastforce intro!: upd_val_rel_upd_val_rel_record.intros
                                                         intro:  upd_val_rel_record
                                                                 [where ts = "map (instantiate \<tau>s) ts"
                                                                    for ts, simplified])
next case u_sem_member
 then show ?case
   apply ( cases e
         , simp_all )
   apply ( clarsimp elim!: typing_memberE)
   apply ( frule(6) u_sem_member(2)
         , clarsimp )
   apply ( frule(1) u_v_shareable_not_writable
         , fastforce elim!:  kind_trecE
                     intro!: kind_trec
                             substitutivity
         , clarsimp elim!: u_v_recE)
   apply ( auto dest!: upd_val_rel_record_nth
         , fastforce )
 done
next case u_sem_memb_b
 then show ?case
   apply ( cases e
         , simp_all )
   apply ( clarsimp elim!: typing_memberE)
   apply ( frule(6) u_sem_memb_b(2)
         , clarsimp )
   apply ( frule(1) u_v_shareable_not_writable
         , fastforce elim!:  kind_trecE
                     intro!: kind_trec
                             substitutivity
         , clarsimp)
   apply ( erule u_v_p_recE)
   apply ( auto dest!: upd_val_rel_record_nth
         , fastforce )
 done
next case (u_sem_take _ _ _ _ _ p)
  note IH1  = this(2)
  and  IH2  = this(5)
  and  rest = this(1,3-4,6-)
  have HELP: "\<forall> ts f \<tau>. (f < length ts \<and> (ts ! f = (\<tau>, False))
          \<longrightarrow> (map (\<lambda>(t, y). (instantiate \<tau>s t, y)) ts ! f = (instantiate \<tau>s \<tau>, False)))"
    apply (rule allI, induct_tac ts, simp)
    apply (simp split: prod.split)
    apply (clarsimp)
    apply (case_tac f, simp, simp)
  done
  have HELP2: "\<forall> \<tau>s. ((\<lambda>(a, b). type_repr a) \<circ> (\<lambda>(t, y). (instantiate \<tau>s t, y)))
                   = (\<lambda>(t,y). type_repr (instantiate \<tau>s t))"
  by (force split: prod.split)
  from rest show ?case
    apply (cases e, simp_all)
    apply (erule typing_takeE)
    apply (frule u_v_matches_noalias)
    apply (frule(2) u_v_matches_split,clarsimp)
    apply (frule(6) IH1, clarsimp)
    apply (erule u_v_p_recE, simp_all)
    apply (frule(2) frame_noalias_u_v_matches)
    apply (frule(1) frame_noalias_u_v_matches(2), blast)
    apply (frule upd_val_rel_record_take [ where \<tau>s = "map (\<lambda>(t, y). (instantiate \<tau>s t, y)) ts" for ts
                                         , simplified
                                         , OF _ HELP [rule_format]],
           force, force intro: substitutivity, force)
    apply (elim exE conjE)
    apply (frule(2) u_v_matches_frame, blast)
    apply (simp, erule disjE)
     apply (clarsimp)
     apply (frule(3) u_v_shareable_not_writable(1) [OF _ _ substitutivity(1)], clarsimp)
     apply (frule(5) IH2 [rotated -1], simp)
      apply (case_tac taken)
       apply (rule u_v_matches_some [OF _ u_v_matches_some])
               apply (simp)
              apply (force intro!: u_v_p_rec_w' simp: HELP2 map_update intro: upd.list_helper [symmetric])
             apply (simp)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (clarsimp)
      apply (rule u_v_pointerset_helper_matches)
        apply (rule u_v_matches_some [OF _ u_v_matches_some])
                apply (simp)
               apply (force intro!: u_v_p_rec_w' simp: upd.list_helper HELP2 map_update intro: upd.list_helper [symmetric])
              apply (simp)
             apply (blast)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (blast)
     apply (clarsimp, intro exI conjI, simp, blast, force simp: Un_commute intro: upd.frame_let)
    apply (clarsimp)
    apply (frule(5) IH2 [rotated -1], simp)
     apply (rule u_v_matches_some [OF _ u_v_matches_some])
             apply (simp)
            apply (force intro!: u_v_p_rec_w' simp: upd.list_helper HELP2 map_update intro: upd.list_helper [symmetric])
           apply (simp)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (blast)
     apply (blast)
    apply (clarsimp, auto intro!: exI intro: upd.frame_let upd.pointerset_helper_frame)
  done
next case u_sem_take_ub
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  have HELP: "\<forall> ts f \<tau>. (f < length ts \<and> (ts ! f = (\<tau>, False))
          \<longrightarrow> (map (\<lambda>(t, y). (instantiate \<tau>s t, y)) ts ! f = (instantiate \<tau>s \<tau>, False)))"
    apply (rule allI, induct_tac ts, simp)
    apply (simp split: prod.split)
    apply (clarsimp)
    apply (case_tac f, simp, simp)
  done
  from rest show ?case
    apply (cases e, simp_all)
    apply (erule typing_takeE)
    apply (frule u_v_matches_noalias)
    apply (frule(2) u_v_matches_split,clarsimp)
    apply (frule(6) IH1, clarsimp)
    apply (erule u_v_recE, simp_all)
    apply (frule(2) frame_noalias_u_v_matches)
    apply (frule(1) frame_noalias_u_v_matches(2), blast)
    apply (clarsimp)
    apply (frule upd_val_rel_record_take [ where \<tau>s = "map (\<lambda>(t, y). (instantiate \<tau>s t, y)) ts" for ts
                                         , simplified
                                         , OF _ HELP [rule_format]], force, force intro: substitutivity, force)
    apply (elim exE conjE)
    apply (frule(2) u_v_matches_frame, blast)
    apply (simp, erule disjE)
     apply (clarsimp)
     apply (frule(3) u_v_shareable_not_writable(1) [OF _ _ substitutivity(1)], clarsimp)
     apply (frule(5) IH2 [rotated -1], simp)
      apply (case_tac taken)
       apply (rule u_v_matches_some [OF _ u_v_matches_some])
               apply (simp)
              apply (force intro!: u_v_struct simp: map_update)
             apply (simp)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (clarsimp)
      apply (rule u_v_pointerset_helper_matches)
        apply (rule u_v_matches_some [OF _ u_v_matches_some])
                apply (simp)
               apply (force intro!: u_v_struct simp: upd.list_helper)
              apply (simp)
             apply (blast)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (blast)
     apply (clarsimp, intro exI conjI, simp, blast, force simp: Un_commute intro: upd.frame_let)
    apply (clarsimp)
    apply (frule(5) IH2 [rotated -1], simp)
     apply (rule u_v_matches_some [OF _ u_v_matches_some])
             apply (simp)
            apply (fastforce intro!: u_v_struct simp: map_update)
           apply (simp)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (blast)
     apply (blast)
    apply (clarsimp, auto intro!: exI intro: upd.frame_let upd.pointerset_helper_frame)
  done

next case u_sem_put
  note IH1  = this(2)
  and  IH2  = this(5)
  and  rest = this(1,3-4,6-)
  have HELP: "\<forall> ts f \<tau> taken. (f < length ts \<longrightarrow> (ts ! f = (\<tau>, taken)
              \<longrightarrow> (map (\<lambda>(t, y). (instantiate \<tau>s t, y)) ts ! f = (instantiate \<tau>s \<tau>, taken))))"
    apply (rule allI, induct_tac ts, simp)
    apply (simp split: prod.split)
    apply (clarsimp)
    apply (case_tac f, simp, simp)
  done
  have HELP2: "\<forall> \<tau>s. ((\<lambda>(a, b). type_repr a) \<circ> (\<lambda>(t, y). (instantiate \<tau>s t, y)))
                   = (\<lambda>(t,y). type_repr (instantiate \<tau>s t))"
  by (force split: prod.split)
  from rest show ?case
    apply (cases e, simp_all)
    apply (erule typing_putE)
    apply (frule u_v_matches_noalias)
    apply (clarsimp)
    apply (frule(2) u_v_matches_split,clarsimp)
    apply (frule(6) IH1, clarsimp)
    apply (frule(2) u_v_matches_frame,blast )
    apply (frule(2) frame_noalias_u_v_matches)
    apply (frule(1) frame_noalias_u_v_matches(2), blast)
    apply (frule(6) IH2, clarsimp)
    apply (frule(1) frame_noalias_upd_val_rel, blast)
    apply (frule(1) frame_noalias_upd_val_rel(2), blast)
    apply (erule u_v_p_recE, simp,clarsimp)
    apply (drule(1) upd.frame_app)
    apply (drule(2) upd_val_rel_frame(2) [rotated -1], blast)
    apply (drule(1) upd_val_rel_frame(1) [OF upd.frame_single_update, simplified, rotated -1], blast)
    apply (drule(2) upd_val_rel_frame(2) [OF upd.frame_single_update, simplified, rotated -1])

    apply (frule(5) upd_val_rel_record_put [ where ts = "map (\<lambda>(t, y). (instantiate \<tau>s t, y)) ts" for ts
                                           , OF _ _ HELP [rule_format]
                                           , simplified
                                           ])
        apply (fast)
       apply (fast)
      apply (fast)
     apply (fastforce intro: substitutivity)
    apply (clarsimp, intro conjI exI, rule u_v_p_rec_w')
    apply (simp add: map_update)
    apply (auto intro!: upd.list_helper[symmetric] simp: HELP2 map_update upd.frame_def)
  done
next case u_sem_put_ub
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  have HELP: "\<forall> ts f \<tau> taken. (f < length ts \<longrightarrow> (ts ! f = (\<tau>, taken)
              \<longrightarrow> (map (\<lambda>(t, y). (instantiate \<tau>s t, y)) ts ! f = (instantiate \<tau>s \<tau>, taken))))"
    apply (rule allI, induct_tac ts, simp)
    apply (simp split: prod.split)
    apply (clarsimp)
    apply (case_tac f, simp, simp)
  done
  from rest show ?case
    apply (cases e, simp_all)
    apply (erule typing_putE)
    apply (frule u_v_matches_noalias)
    apply (clarsimp)
    apply (frule(2) u_v_matches_split,clarsimp)
    apply (frule(6) IH1, clarsimp)
    apply (frule(2) u_v_matches_frame,blast )
    apply (frule(2) frame_noalias_u_v_matches)
    apply (frule(1) frame_noalias_u_v_matches(2), blast)
    apply (frule(6) IH2, clarsimp)
    apply (frule(1) frame_noalias_upd_val_rel, blast)
    apply (frule(1) frame_noalias_upd_val_rel(2), blast)
    apply (erule u_v_recE, simp,clarsimp)
    apply (drule(1) upd.frame_app)
    apply (drule(2) upd_val_rel_frame(2) [rotated -1], blast)

    apply (frule(5) upd_val_rel_record_put [ where ts = "map (\<lambda>(t, y). (instantiate \<tau>s t, y)) ts" for ts
                                           , OF _ _ HELP [rule_format]
                                           , simplified
                                           ])
        apply (fast)
       apply (fast)
      apply (fast)
     apply (fastforce intro: substitutivity)
    apply (clarsimp, auto intro!: exI u_v_struct simp: map_update upd.frame_def)
  done
next case u_sem_split
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (erule typing_splitE)
    apply (frule u_v_matches_noalias)
    apply (frule(2) u_v_matches_split,clarsimp)
    apply (frule(6) IH1, clarsimp)
    apply (erule u_v_productE)
    apply (frule(2) frame_noalias_u_v_matches)
    apply (frule(1) frame_noalias_u_v_matches(2), blast)
    apply (frule(4) IH2)
      apply (simp)
      apply (rule u_v_matches_some, simp, rule u_v_matches_some, simp)
            apply (rule u_v_matches_frame, simp, simp)
             apply (blast)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (blast)
     apply (blast)
    apply (clarsimp, auto intro!: exI intro: upd.frame_let upd.pointerset_helper_frame)
  done
next case u_sem_all_empty then show ?case by ( cases es, simp_all
                                             , fastforce intro!: upd.frame_id
                                                                 upd_val_rel_all.intros
                                                         dest: u_v_matches_empty_env(2))
next case u_sem_all_cons
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (cases es, simp_all)
    apply (erule typing_all_consE, clarsimp)
    apply (frule(2) u_v_matches_split, clarsimp)
    apply (frule(6) IH1, clarsimp)
    apply (frule u_v_matches_noalias)
    apply (frule(8) IH2 [OF _ _ _ _ _ u_v_matches_frame, rotated -1], blast, clarsimp)
    apply (frule(1) upd.frame_app)
    apply (frule(2) frame_noalias_u_v_matches(2) [where u = "w \<union> w'" for w and w'])
    apply (frule(4) upd_val_rel_frame [rotated -1, OF _ _ frame_noalias_u_v_matches(1)], blast)
    apply (frule(4) frame_noalias_2_uv)
    apply (blast intro!: upd_val_rel_all.intros)
  done


qed
lemmas mono_correspondence = correspondence [where \<tau>s = "[]" and K = "[]", simplified]

lemma val_executes_from_upd_executes:
assumes "proc_ctx_wellformed \<Xi>"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma> \<langle>r, w\<rangle>"
and     "\<xi> \<sim> \<xi>' matches-u-v \<Xi>"
shows   "\<lbrakk> \<xi> , \<gamma>  \<turnstile> (\<sigma>, e) \<Down>! (\<sigma>', v)
         ; \<Xi>, [], \<Gamma> \<turnstile> e : \<tau>
         \<rbrakk> \<Longrightarrow> \<exists>v'. \<xi>', \<gamma>' \<turnstile> e \<Down> v'"
and     "\<lbrakk> \<xi> , \<gamma>  \<turnstile>* (\<sigma>, es) \<Down>! (\<sigma>', vs)
         ; \<Xi>, [], \<Gamma> \<turnstile>* es : \<tau>s'
         \<rbrakk> \<Longrightarrow> \<exists>vs'. \<xi>', \<gamma>' \<turnstile>* es \<Down> vs' "
  using assms proof (induct "(\<sigma>,e)" "(\<sigma>',v)"
    and "(\<sigma>,es)" "(\<sigma>', vs)" arbitrary: \<Gamma> r w \<sigma> e v \<tau> \<sigma>' \<gamma>' and \<Gamma> r w  \<sigma> es vs \<tau>s' \<sigma>'  \<gamma>'
    rule: u_sem_u_sem_all.inducts)
     case u_sem_cast
  note IH   = this(2)
  and  rest = this(1,3-)
  from rest show ?case
    apply (clarsimp elim!: typing_castE)
    apply (frule(3) IH, clarsimp)
    apply (frule(2) mono_correspondence)
    apply (auto elim: upd_val_rel.cases intro!: v_sem_v_sem_all.intros)
  done
next case u_sem_app
  note IH1 = this(2)
   and IH2 = this(4)
   and IH3 = this(6)
   and rest = this(1,3,5,7-)
  from rest show ?case
    apply (clarsimp elim!: typing_appE)
    apply (frule u_v_matches_noalias)
    apply (frule(1) u_v_matches_split', clarsimp)
    apply (frule(3) IH1, clarsimp)
    apply (drule(5) mono_correspondence [rotated -1], clarsimp)
    apply (frule(5) IH2 [OF _ _ u_v_matches_frame, rotated -1], blast, clarsimp)
    apply (drule(4) mono_correspondence [rotated -1, OF _ _ u_v_matches_frame],blast,simp,simp,simp)
    apply (clarsimp)
    apply (erule upd_val_rel.cases [where ?a5.0="TFun xa \<tau>" for xa \<tau>], simp_all)
    apply (clarsimp)
    apply (drule(1) specialisation)
    apply (frule(1) IH3 [OF _ _ u_v_matches_frame])
    apply (simp,rule u_v_matches_some)
    apply (simp)
    apply (auto simp: instantiate_ctx_def intro!: u_v_matches.intros upd.frame_id v_sem_v_sem_all.intros)
    done
next case (u_sem_abs_app _ _ _ _ _ f)
  note IH1 = this(2)
   and IH2 = this(4)
   and rest = this(1,3,5-)
  from rest show ?case
    apply (clarsimp elim!: typing_appE)
    apply (frule u_v_matches_noalias)
    apply (frule(1) u_v_matches_split', clarsimp)
    apply (frule(3) IH1, clarsimp)
    apply (drule(5) mono_correspondence [rotated -1], clarsimp)
    apply (frule(5) IH2 [OF _ _ u_v_matches_frame, rotated -1], blast, clarsimp)
    apply (drule(4) mono_correspondence [rotated -1, OF _ _ u_v_matches_frame],blast,simp,simp,simp)
    apply (clarsimp)
    apply (erule upd_val_rel.cases [where ?a5.0="TFun xa \<tau>" for xa \<tau>], simp_all)
    apply (clarsimp)
    apply (simp add: proc_env_u_v_matches_def)
    apply (drule_tac x = f in spec)
    apply (clarsimp)
    apply (elim allE impE, simp+)
    apply (clarsimp)
    apply (rule,erule(2) v_sem_abs_app)
  done
next case u_sem_con then show ?case by (force intro!: v_sem_v_sem_all.intros)
next case u_sem_member
  note IH = this(2)
  and rest = this(1,3-)
  from rest show ?case
    apply (clarsimp elim!: typing_memberE)
    apply (frule(3) IH, clarsimp)
    apply (frule(5) mono_correspondence, clarsimp)
    apply (force elim: upd_val_rel.cases intro!: v_sem_v_sem_all.intros)
  done
next case u_sem_memb_b
  note IH = this(2)
  and rest = this(1,3-)
  from rest show ?case
    apply (clarsimp elim!: typing_memberE)
    apply (frule(3) IH, clarsimp)
    apply (frule(5) mono_correspondence, clarsimp)
    apply (force elim: upd_val_rel.cases intro!: v_sem_v_sem_all.intros)
  done
next case u_sem_esac
  note IH = this(2)
  and rest = this(1,3-)
  from rest show ?case
    apply (clarsimp elim!: typing_esacE)
    apply (frule(3) IH, clarsimp)
    apply (frule(5) mono_correspondence, clarsimp)
    apply (force elim: upd_val_rel.cases intro!: v_sem_v_sem_all.intros)
  done
next case u_sem_let
  note IH1 = this(2)
  and  IH2 = this(4)
  and rest = this(1,3,5-)
  from rest show ?case
    apply (clarsimp elim!: typing_letE)
    apply (frule u_v_matches_noalias)
    apply (frule(1) u_v_matches_split', clarsimp)
    apply (frule(3) IH1, clarsimp)
    apply (drule(5) mono_correspondence [rotated -1], clarsimp)
    apply (frule(1) IH2)
    apply (rule)
    apply (simp)
    apply (erule(2) u_v_matches_frame,blast)
    apply (erule(2) frame_noalias_u_v_matches)
    apply (erule(1) frame_noalias_u_v_matches(2),blast)
    apply (auto simp: instantiate_ctx_def intro!: u_v_matches.intros upd.frame_id v_sem_v_sem_all.intros)
  done
next case u_sem_letbang
  note IH1 = this(2)
  and  IH2 = this(4)
  and rest = this(1,3,5-)
  from rest show ?case
    apply (clarsimp elim!: typing_letbE)
    apply (frule u_v_matches_noalias)
    apply (frule(1) u_v_matches_split_bang', clarsimp)
    apply (frule(3) IH1, clarsimp)
    apply (drule(5) mono_correspondence [rotated -1], clarsimp)
    apply (frule(2) u_v_escapable_no_readers(1), clarsimp)
    apply (frule(1) IH2)
    apply (rule)
    apply (simp)
    apply (erule(1) u_v_matches_frame,blast, blast)
    apply (erule(1) frame_noalias_u_v_matches,blast)
    apply (erule(1) frame_noalias_u_v_matches(2),blast)
    apply (auto simp: instantiate_ctx_def intro!: u_v_matches.intros upd.frame_id v_sem_v_sem_all.intros)
  done

next case u_sem_tuple
  note IH1 = this(2)
  and  IH2 = this(4)
  and rest = this(1,3,5-)
  from rest show ?case
    apply (clarsimp elim!: typing_tupleE)
    apply (frule(1) u_v_matches_split',clarsimp)
    apply (frule(3) IH1, clarsimp)
    apply (drule(5) mono_correspondence [rotated -1], clarsimp)
    apply (frule(5) IH2 [OF _ _ u_v_matches_frame,rotated -1],force dest!: u_v_matches_noalias)
    apply (force intro: v_sem_v_sem_all.intros)
  done
next case u_sem_if
  note IH1 = this(2)
  and  IH2 = this(4)
  and rest = this(1,3,5-)
  from rest show ?case
    apply (clarsimp elim!: typing_ifE)
    apply (frule u_v_matches_noalias)
    apply (frule(1) u_v_matches_split',clarsimp)
    apply (frule(3) IH1, clarsimp)
    apply (frule(5) mono_correspondence [rotated -1], clarsimp)
    apply (frule(2) u_v_matches_frame, blast)
    apply (erule upd_val_rel.cases, simp_all)
    apply (drule_tac t = "l" in sym)
    apply (clarsimp)
    apply (frule(2) IH2 [rotated 1], force simp add: if_splits)
    apply (force intro: v_sem_v_sem_all.intros)
  done
next case u_sem_split
  note IH1 = this(2)
  and  IH2 = this(4)
  and rest = this(1,3,5-)
  from rest show ?case
    apply (clarsimp elim!: typing_splitE)
    apply (frule u_v_matches_noalias)
    apply (frule(1) u_v_matches_split', clarsimp)
    apply (frule(3) IH1, clarsimp)
    apply (frule(5) mono_correspondence [rotated -1], clarsimp)
    apply (frule(2) u_v_matches_frame,blast)
    apply (erule upd_val_rel.cases, simp_all)
    apply (clarsimp)
    apply (frule(2) IH2 [rotated -1])
    apply (erule(2) u_v_matches_some [OF _ u_v_matches_some])
    apply (frule(2) frame_noalias_u_v_matches,blast)
    apply (frule(1) frame_noalias_u_v_matches(2),blast,blast)
    apply (blast)
    apply (frule(2) frame_noalias_u_v_matches,blast)
    apply (frule(1) frame_noalias_u_v_matches(2),blast,blast)
    apply (blast)
    apply (force intro: v_sem_v_sem_all.intros)
  done
next case u_sem_case_m
  note IH1 = this(2)
  and  IH2 = this(4)
  and rest = this(1,3,5-)
  from rest show ?case
    apply (clarsimp elim!: typing_caseE)
    apply (frule u_v_matches_noalias)
    apply (frule(1) u_v_matches_split',clarsimp)
    apply (frule(3) IH1, clarsimp)
    apply (frule(5) mono_correspondence [rotated -1], clarsimp)
    apply (frule(2) u_v_matches_frame, blast)
    apply (erule upd_val_rel.cases, simp_all)
    apply (clarsimp)
    apply (frule(2) IH2 [rotated -1])
    apply (drule(1) distinct_fst [rotated 1],simp)
    apply (simp)
    apply (erule(1) u_v_matches_some)
    apply (erule(2) frame_noalias_u_v_matches)
    apply (erule(1) frame_noalias_u_v_matches(2),blast)
    apply (blast)
    apply (force intro: v_sem_v_sem_all.intros)
  done
next
  case (u_sem_case_nm \<xi> \<gamma> \<sigma> x \<sigma>'' tag' va rs tag n m)

  obtain \<Gamma>1 \<Gamma>2 ts ta
    where split\<Gamma>: "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
      and typing_x: "\<Xi>, [], \<Gamma>1 \<turnstile> x : TSum ts"
      and tag_in_ts: "(tag, ta, False) \<in> set ts"
      and typing_m: "\<Xi>, [], Some ta # \<Gamma>2 \<turnstile> m : \<tau>"
      and typing_n: "\<Xi>, [], Some (TSum (tagged_list_update tag (ta, True) ts)) # \<Gamma>2 \<turnstile> n : \<tau>"
    using u_sem_case_nm.prems by auto

  have w_r_disjoint: "w \<inter> r = {}"
    using u_v_matches_noalias u_sem_case_nm.prems
    by blast

  obtain r1 w1 r2 w2
    where r_as_un: "r = r1 \<union> r2"
      and w_as_un: "w = w1 \<union> w2"
      and w1_w2_disjoint: "w1 \<inter> w2 = {}"
      and matches1: "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma>1 \<langle>r1, w1\<rangle>"
      and matches2: "\<Xi>, \<sigma> \<turnstile> \<gamma> \<sim> \<gamma>' matches \<Gamma>2 \<langle>r2, w2\<rangle>"
    using u_v_matches_split'[OF split\<Gamma> u_sem_case_nm.prems(3)]
    by force

  obtain vxsum
    where vsem_x: "\<xi>', \<gamma>' \<turnstile> x \<Down> vxsum"
    using u_sem_case_nm.hyps(2) u_sem_case_nm.prems typing_x matches1
    by blast

 obtain r1' w1'
    where "\<Xi>, \<sigma>'' \<turnstile> USum tag' va rs \<sim> vxsum : TSum ts \<langle>r1', w1'\<rangle>"
      and r1'_sub_r1: "r1' \<subseteq> r1"
      and frame1: "upd.frame \<sigma> w1 \<sigma>'' w1'"
   using mono_correspondence(1) u_sem_case_nm.hyps(1) u_sem_case_nm.prems matches1 vsem_x typing_x
   by blast
  then obtain vv t k
    where rs_is: "rs = (map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) ts)"
      and vxsum_is: "vxsum = VSum tag' vv"
      and u_v_rel_va_vv: "\<Xi>, \<sigma>'' \<turnstile> va \<sim> vv : t \<langle>r1', w1'\<rangle>"
      and tag'_in_ts: "(tag', t, False) \<in> set ts"
      and distinct_fst_ts: "distinct (map fst ts)"
      and wellformed_ts: "[] \<turnstile>* map (fst \<circ> snd) ts :\<kappa>  k"
    by auto

  have "\<Xi>, \<sigma>'' \<turnstile> USum tag' va rs \<sim> VSum tag' vv : TSum (tagged_list_update tag (ta, True) ts) \<langle>r1', w1'\<rangle>"
    using u_v_rel_va_vv distinct_fst_ts
  proof (intro u_v_sum)
    show "(tag', t, False) \<in> set (tagged_list_update tag (ta, True) ts)"
      by (meson tag'_in_ts tagged_list_update_different_tag_preserves_values2 u_sem_case_nm.hyps(3))
  next
    have "map (fst \<circ> snd) ts = map (fst \<circ> snd) (tagged_list_update tag (ta, True) ts)"
      using tagged_list_update_map_over_indistinguishable tagged_list_update_same_distinct_is_equal
        tag_in_ts distinct_fst_ts
      by (metis (no_types, lifting) fst_conv in_set_conv_nth)
    then have "[] \<turnstile>* map (fst \<circ> snd) (tagged_list_update tag (ta, True) ts) :\<kappa>  k"
      using wellformed_ts
      by (clarsimp simp add: kinding_all_list_all)
    then show "[] \<turnstile>* map (fst \<circ> snd) (tagged_list_update tag (ta, True) ts) wellformed"
      by auto
  next
    obtain i
      where ts_upd_is: "tagged_list_update tag (ta, True) ts = ts[i := (tag, ta, True)]"
        and i_in_bounds: "i < length ts"
        and "ts ! i = (tag, ta, False)"
      using tagged_list_update_distinct distinct_fst_ts
      by (metis fst_conv in_set_conv_nth tag_in_ts)
    then have "(tag, type_repr ta) = map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) ts ! i"
      by simp
    then show "rs = map (\<lambda>(c, \<tau>, _). (c, type_repr \<tau>)) (tagged_list_update tag (ta, True) ts)"
      by (simp add: rs_is ts_upd_is map_update)
  qed simp+
  then have "\<Xi>, \<sigma>'' \<turnstile> USum tag' va rs # \<gamma> \<sim> VSum tag' vv # \<gamma>' matches Some (TSum (tagged_list_update tag (ta, True) ts)) # \<Gamma>2 \<langle>r1' \<union> r2, w1' \<union> w2\<rangle>"
    using w_r_disjoint[simplified r_as_un w_as_un] w1_w2_disjoint
      matches2 frame1 frame_noalias_u_v_matches r1'_sub_r1 u_v_matches_frame
    by (fast intro!: u_v_matches_some)
  then obtain nvv
    where "\<xi>', VSum tag' vv # \<gamma>' \<turnstile> n \<Down> nvv"
    using u_sem_case_nm.hyps(5)  u_sem_case_nm.prems typing_n by blast
  then
  have "\<xi>', \<gamma>' \<turnstile> (Case x tag m n) \<Down> nvv"
    using vsem_x vxsum_is u_sem_case_nm.hyps(3) v_sem_case_nm
    by fastforce
  then show ?case
    by blast

next case u_sem_take
  note IH1 = this(2)
  and  IH2 = this(5)
  and rest = this(1,3-4,6-)
  have HELP [rule_format] :
    "\<forall> tsa f t x y. tsa ! f = (t,y) \<longrightarrow> map (\<lambda>(a, b). type_repr a) tsa = map (\<lambda>(a, b). type_repr a) (tsa[f := (t, x)])"
    apply (rule allI)
    apply (induct_tac tsa)
    apply (auto split: nat.split)
  done
  from rest show ?case
    apply (clarsimp elim!: typing_takeE)
    apply (frule u_v_matches_noalias)
    apply (frule(1) u_v_matches_split', clarsimp)
    apply (frule(3) IH1, clarsimp)
    apply (frule(5) mono_correspondence [rotated -1], clarsimp)
    apply (frule(2) u_v_matches_frame, blast)
    apply (frule(2) frame_noalias_u_v_matches)
    apply (frule(1) frame_noalias_u_v_matches(2),blast)
    apply (erule upd_val_rel.cases, simp_all, clarsimp)
    apply (frule(1) upd_val_rel_record_take, force, force)
    apply (elim exE conjE)
    apply (frule(2) IH2 [rotated -1])
     apply (case_tac "taken")
      apply (clarsimp)
      apply (rule u_v_pointerset_helper_matches)
        apply (rule u_v_matches_some, simp, rule u_v_matches_some)
               apply (fastforce intro!: u_v_p_rec_w' simp:HELP)
              apply (simp)
             apply (blast) (* go get a cup of tea *)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (fastforce)
        apply (fastforce)
       apply (simp)
      apply (simp)
     apply (clarsimp)
     apply (frule(2) u_v_shareable_not_writable, clarsimp)
     apply (rule u_v_pointerset_helper_matches)
       apply (rule u_v_matches_some, simp, rule u_v_matches_some)
              apply (force intro!: u_v_p_rec_w' simp: upd.list_helper simp: HELP)
             apply (simp)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (blast)
     apply (blast)
    apply (force intro: v_sem_v_sem_all.intros)
  done
next case u_sem_take_ub
  note IH1 = this(2)
  and  IH2 = this(4)
  and rest = this(1,3,5-)
  have HELP [rule_format] :
    "\<forall> tsa f t x y. tsa ! f = (t,y) \<longrightarrow> map (\<lambda>(a, b). type_repr a) tsa = map (\<lambda>(a, b). type_repr a) (tsa[f := (t, x)])"
    apply (rule allI)
    apply (induct_tac tsa)
    apply (auto split: nat.split)
  done
  from rest show ?case
    apply (clarsimp elim!: typing_takeE)
    apply (frule u_v_matches_noalias)
    apply (frule(1) u_v_matches_split', clarsimp)
    apply (frule(3) IH1, clarsimp)
    apply (frule(5) mono_correspondence [rotated -1], clarsimp)
    apply (frule(2) u_v_matches_frame, blast)
    apply (frule(2) frame_noalias_u_v_matches)
    apply (frule(1) frame_noalias_u_v_matches(2),blast)
    apply (erule upd_val_rel.cases, simp_all, clarsimp)
    apply (frule(1) upd_val_rel_record_take, force, force)
    apply (elim exE conjE)
    apply (frule(2) IH2 [rotated -1])
     apply (case_tac "taken")
      apply (clarsimp)
      apply (rule u_v_pointerset_helper_matches)
        apply (rule u_v_matches_some, simp, rule u_v_matches_some)
               apply (fastforce intro!: u_v_struct simp:HELP)
              apply (simp)
             apply (blast) (* go get a cup of tea *)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (fastforce)
        apply (fastforce)
       apply (simp)
      apply (simp)
     apply (clarsimp)
     apply (frule(2) u_v_shareable_not_writable, clarsimp)
     apply (rule u_v_pointerset_helper_matches)
       apply (rule u_v_matches_some, simp, rule u_v_matches_some)
              apply (force intro!: u_v_struct simp: upd.list_helper simp: HELP)
             apply (simp)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (blast)
     apply (blast)
    apply (force intro: v_sem_v_sem_all.intros)
  done
next case u_sem_put
  note IH1 = this(2)
  and  IH2 = this(5)
  and rest = this(1,3-4,6-)
  from rest show ?case
    apply (clarsimp elim!: typing_putE)
    apply (frule u_v_matches_noalias)
    apply (frule(1) u_v_matches_split',clarsimp)
    apply (frule(3) IH1, clarsimp)
    apply (drule(5) mono_correspondence [rotated -1], clarsimp)
    apply (frule(5) IH2 [OF _ _ u_v_matches_frame,rotated -1],force)
    apply (erule upd_val_rel.cases,simp_all)
    apply (force intro: v_sem_v_sem_all.intros)
  done
next case u_sem_put_ub
  note IH1 = this(2)
  and  IH2 = this(4)
  and rest = this(1,3,5-)
  from rest show ?case
    apply (clarsimp elim!: typing_putE)
    apply (frule u_v_matches_noalias)
    apply (frule(1) u_v_matches_split',clarsimp)
    apply (frule(3) IH1, clarsimp)
    apply (drule(5) mono_correspondence [rotated -1], clarsimp)
    apply (frule(5) IH2 [OF _ _ u_v_matches_frame,rotated -1],force)
    apply (erule upd_val_rel.cases,simp_all)
    apply (force intro: v_sem_v_sem_all.intros)
  done
next case u_sem_all_cons
  note IH1 = this(2)
  and  IH2 = this(4)
  and rest = this(1,3,5-)
  from rest show ?case
    apply (clarsimp elim!: typing_all_consE)
    apply (frule(1) u_v_matches_split',clarsimp)
    apply (frule(3) IH1, clarsimp)
    apply (drule(5) mono_correspondence [rotated -1], clarsimp)
    apply (frule(5) IH2 [OF _ _ u_v_matches_frame,rotated -1],force dest!: u_v_matches_noalias)
    apply (force intro: v_sem_v_sem_all.intros)
  done
qed (force intro!: v_sem_v_sem_all.intros)+

end

end


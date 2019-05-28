(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory UpdateSemantics
  imports Cogent
begin



datatype ('f, 'a, 'l) uval = UPrim lit
                           | UProduct "('f,'a,'l) uval" "('f,'a,'l) uval"
                           | USum name "('f,'a,'l) uval" "(name \<times> repr) list"
                           | URecord "(('f,'a,'l) uval \<times> repr) list" 
                           | UAbstract "'a"
                           | UFunction "'f expr" "type list"
                           | UAFunction "'f" "type list"
                           | UUnit
                           | UPtr "'l" repr

(* NB: The "type" in the store is just a tag used for the C proofs.
 *     The u_sem rules simply carry this tag along into the updated store. *)
type_synonym ('f, 'a, 'l) store = "'l \<Rightarrow> ('f, 'a, 'l) uval option"


type_synonym ('f,'a,'l) ufundef = "('f,'a,'l) store \<times> ('f,'a,'l) uval
                                 \<Rightarrow> ('f,'a,'l) store \<times> ('f,'a,'l) uval
                                 \<Rightarrow> bool"

type_synonym ('f, 'a, 'l) uabsfuns = "'f \<Rightarrow> ('f, 'a, 'l) ufundef"

definition eval_prim_u :: "prim_op \<Rightarrow> ('f, 'a, 'l) uval list \<Rightarrow> ('f, 'a, 'l) uval"
where
  "eval_prim_u pop xs = UPrim (eval_prim_op pop (map (\<lambda>vv. case vv of UPrim v \<Rightarrow> v | _ \<Rightarrow> LBool False) xs))"




inductive u_sem :: "('f,'a,'l) uabsfuns
                  \<Rightarrow> ('f,'a,'l) uval env 
                  \<Rightarrow> ('f,'a,'l) store \<times> 'f expr 
                  \<Rightarrow> ('f,'a,'l) store \<times> ('f,'a,'l) uval
                  \<Rightarrow> bool" 
          ("_, _ \<turnstile> _ \<Down>! _" [30,0,0,20] 60)
and       u_sem_all :: "('f,'a,'l) uabsfuns 
                      \<Rightarrow> ('f,'a,'l) uval env
                      \<Rightarrow> ('f,'a,'l) store \<times> 'f expr list 
                      \<Rightarrow> ('f,'a,'l) store \<times> ('f,'a,'l) uval list 
                      \<Rightarrow> bool" 
          ("_, _ \<turnstile>* _ \<Down>! _" [30,0,0,20] 60) 
where 
  u_sem_var     : "\<xi> , \<gamma> \<turnstile> (\<sigma>, Var i) \<Down>! (\<sigma>, \<gamma> ! i)"

| u_sem_lit     : "\<xi> , \<gamma> \<turnstile> (\<sigma>, Lit l) \<Down>! (\<sigma>, UPrim l)"

| u_sem_prim    : "\<lbrakk> \<xi> , \<gamma> \<turnstile>* (\<sigma>, as) \<Down>! (\<sigma>', as') 
                   \<rbrakk> \<Longrightarrow>  \<xi> , \<gamma> \<turnstile> (\<sigma>, Prim p as) \<Down>! (\<sigma>', eval_prim_u p as')"

| u_sem_cast    : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, e) \<Down>! (\<sigma>', UPrim l)
                   ; cast_to \<tau> l = Some l' 
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Cast \<tau> e) \<Down>! (\<sigma>', UPrim l')"

| u_sem_fun     : "\<xi> , \<gamma> \<turnstile> (\<sigma>, Fun f ts) \<Down>! (\<sigma>, UFunction f ts)"

| u_sem_afun    : "\<xi> , \<gamma> \<turnstile> (\<sigma>, AFun f ts) \<Down>! (\<sigma>, UAFunction f ts)"

| u_sem_abs_app : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma> , x) \<Down>! (\<sigma>' , UAFunction f ts)
                   ; \<xi> , \<gamma> \<turnstile> (\<sigma>', y) \<Down>! (\<sigma>'', a)
                   ; \<xi> f (\<sigma>'', a) (\<sigma>''', r)
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, App x y) \<Down>! (\<sigma>''', r)"

| u_sem_app     : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma> , x) \<Down>! (\<sigma>' , UFunction f ts)
                   ; \<xi> , \<gamma> \<turnstile> (\<sigma>', y) \<Down>! (\<sigma>'', a)
                   ; \<xi> , [ a ] \<turnstile> (\<sigma>'', specialise ts f) \<Down>! st
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, App x y) \<Down>! st"

| u_sem_con     : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', x') 
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Con ts t x) \<Down>! (\<sigma>', USum t x' (map (\<lambda>(n,t).(n,type_repr t)) ts))"

| u_sem_promote : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', USum c p ts)  
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Promote ts' x) \<Down>! (\<sigma>', USum c p (map (\<lambda>(n,t).(n,type_repr t)) ts'))"

| u_sem_member  : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, e) \<Down>! (\<sigma>', URecord fs)
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Member e f) \<Down>! (\<sigma>', fst (fs ! f))"

| u_sem_memb_b  : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, e) \<Down>! (\<sigma>', UPtr p r)
                   ; \<sigma>' p = Some (URecord fs)
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Member e f) \<Down>! (\<sigma>', fst (fs ! f))"

| u_sem_unit    : "\<xi> , \<gamma> \<turnstile> (\<sigma>, Unit) \<Down>! (\<sigma>, UUnit)"

| u_sem_tuple   : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma> , x) \<Down>! (\<sigma>' , x') 
                   ; \<xi> , \<gamma> \<turnstile> (\<sigma>', y) \<Down>! (\<sigma>'', y') 
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Tuple x y) \<Down>! (\<sigma>'', UProduct x' y')"
            
| u_sem_esac    : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, t) \<Down>! (\<sigma>', USum ts v ts') 
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Esac t) \<Down>! (\<sigma>', v)" 

| u_sem_let     : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', a')
                   ; \<xi> , (a' # \<gamma>) \<turnstile> (\<sigma>', b) \<Down>! st 
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Let a b) \<Down>! st" 

| u_sem_letbang : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', a') 
                   ; \<xi> , (a' # \<gamma>) \<turnstile> (\<sigma>', b) \<Down>! st 
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, LetBang vs a b) \<Down>! st"

| u_sem_case_m  : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', USum t v ts)
                   ; \<xi> , (v # \<gamma>) \<turnstile> (\<sigma>', m) \<Down>! st
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Case x t m n) \<Down>! st"

| u_sem_case_nm : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', USum t' v ts)
                   ; t' \<noteq> t
                   ; \<xi> , (USum t' v (filter (\<lambda> x. fst x \<noteq> t) ts) # \<gamma>) \<turnstile> (\<sigma>', n) \<Down>! st
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Case x t m n) \<Down>! st"

| u_sem_if      : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', UPrim (LBool b))
                   ; \<xi> , \<gamma> \<turnstile> (\<sigma>', if b then t else e) \<Down>! st
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, If x t e) \<Down>! st" 

| u_sem_struct  : "\<lbrakk> \<xi> , \<gamma> \<turnstile>* (\<sigma>, xs) \<Down>! (\<sigma>', vs)
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Struct ts xs) \<Down>! (\<sigma>', URecord (zip vs (map type_repr ts)))" 

| u_sem_take    : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', UPtr p r)
                   ; \<sigma>' p = Some (URecord fs)
                   ; \<xi> , (fst (fs ! f) # UPtr p r # \<gamma>) \<turnstile> (\<sigma>', e) \<Down>! st 
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Take x f e) \<Down>! st"

| u_sem_take_ub : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', URecord fs)
                   ; \<xi> , (fst (fs ! f) # URecord fs # \<gamma>) \<turnstile> (\<sigma>', e) \<Down>! st 
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Take x f e) \<Down>! st"

| u_sem_put     : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', UPtr p r)
                   ; \<sigma>' p = Some (URecord fs)
                   ; \<xi> , \<gamma> \<turnstile> (\<sigma>', e) \<Down>! (\<sigma>'', e') 
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Put x f e) 
                      \<Down>! (\<sigma>'' (p := Some (URecord (fs [ f := (e', snd (fs ! f) )]))), UPtr p r)"

| u_sem_put_ub  : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', URecord fs)
                   ; \<xi> , \<gamma> \<turnstile> (\<sigma>', e) \<Down>! (\<sigma>'', e') 
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Put x f e) \<Down>! (\<sigma>'', URecord (fs [ f := (e', snd (fs ! f)) ]))"


| u_sem_split   : "\<lbrakk> \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', UProduct a b)
                   ; \<xi> , (a # b # \<gamma>) \<turnstile> (\<sigma>', e) \<Down>! st 
                   \<rbrakk> \<Longrightarrow> \<xi> , \<gamma> \<turnstile> (\<sigma>, Split x e) \<Down>! st"

| u_sem_all_empty : "\<xi> , \<gamma> \<turnstile>* (\<sigma>, []) \<Down>! (\<sigma>, [])"

| u_sem_all_cons  : "\<lbrakk> \<xi> , \<gamma> \<turnstile>  (\<sigma> , x ) \<Down>! (\<sigma>' , v ) 
                     ; \<xi> , \<gamma> \<turnstile>* (\<sigma>', xs) \<Down>! (\<sigma>'', vs)
                     \<rbrakk> \<Longrightarrow>  \<xi> , \<gamma> \<turnstile>* (\<sigma>, x # xs) \<Down>! (\<sigma>'', v # vs)" 



locale update_sem =
  fixes abs_typing :: "'a \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> sigil \<Rightarrow> 'l set \<Rightarrow> 'l set \<Rightarrow> bool"
  and   abs_repr   :: "'a \<Rightarrow> name \<times> repr list"
  assumes abs_typing_bang : "abs_typing av n \<tau>s s r w \<Longrightarrow> abs_typing av n (map bang \<tau>s) (bang_sigil s) (r \<union> w) {}"
  and     abs_typing_noalias : "abs_typing av n \<tau>s s r w \<Longrightarrow> r \<inter> w = {}"
  and     abs_typing_readonly : "s \<noteq> Writable \<Longrightarrow> abs_typing av n \<tau>s s r w \<Longrightarrow> w = {}"
  and     abs_typing_escape   : "s \<noteq> ReadOnly \<Longrightarrow> [] \<turnstile>* \<tau>s :\<kappa> k \<Longrightarrow> E \<in> k \<Longrightarrow> abs_typing av n \<tau>s s r w \<Longrightarrow> r = {}"
  and     abs_typing_valid : "abs_typing av n \<tau>s s r w \<Longrightarrow> p \<in> r \<union> w \<Longrightarrow> \<sigma> p \<noteq> None"
  and     abs_typing_unique_repr   : "abs_typing av n \<tau>s s r w \<Longrightarrow> abs_typing av n' \<tau>s' s' r' w'
                                    \<Longrightarrow> type_repr (TCon n \<tau>s s) = type_repr (TCon n' \<tau>s' s')"
  and     abs_typing_repr : "abs_typing av n \<tau>s s r w \<Longrightarrow> abs_repr av = (n, map type_repr \<tau>s)"

context update_sem begin

fun uval_repr :: "('f, 'a,'l) uval \<Rightarrow> repr" where
  "uval_repr (UPrim lit) = RPrim (lit_type lit)"
| "uval_repr (UProduct a b) = RProduct (uval_repr a) (uval_repr b)"
| "uval_repr (USum a b reprs) = RSum reprs"
| "uval_repr (URecord fs) = RRecord (map snd fs)"
| "uval_repr (UAbstract a) = (let (x,y) = abs_repr a in RCon x y)"
| "uval_repr (UFunction _ _) = RFun"
| "uval_repr (UAFunction _ _) = RFun"
| "uval_repr (UUnit) = RUnit"
| "uval_repr (UPtr p r) = RPtr r"

fun uval_repr_deep :: "('f, 'a,'l) uval \<Rightarrow> repr" where
  "uval_repr_deep (UPrim lit) = RPrim (lit_type lit)"
| "uval_repr_deep (UProduct a b) = RProduct (uval_repr_deep a) (uval_repr_deep b)"
| "uval_repr_deep (USum a b reprs) = RSum reprs"
| "uval_repr_deep (URecord fs) = RRecord (map uval_repr_deep (map fst fs))"
| "uval_repr_deep (UAbstract a) = (let (x,y) = abs_repr a in RCon x y)"
| "uval_repr_deep (UFunction _ _) = RFun"
| "uval_repr_deep (UAFunction _ _) = RFun"
| "uval_repr_deep (UUnit) = RUnit"
| "uval_repr_deep (UPtr p r) = RPtr r"

inductive uval_typing :: "('f \<Rightarrow> poly_type) 
                       \<Rightarrow> ('f, 'a, 'l) store
                       \<Rightarrow> ('f, 'a, 'l) uval
                       \<Rightarrow> type 
                       \<Rightarrow> 'l set
                       \<Rightarrow> 'l set
                       \<Rightarrow> bool"  ("_, _ \<turnstile> _ :u _ \<langle>_, _\<rangle>" [30,0,0,0,20] 80)
and uval_typing_record :: "('f \<Rightarrow> poly_type) 
                        \<Rightarrow> ('f, 'a, 'l) store 
                        \<Rightarrow> (('f, 'a, 'l) uval \<times> repr) list
                        \<Rightarrow> (type \<times> bool) list
                        \<Rightarrow> 'l set
                        \<Rightarrow> 'l set
                        \<Rightarrow> bool" ("_, _ \<turnstile>* _ :ur _ \<langle>_, _\<rangle>" [30,0,0,0,20] 80) where


  u_t_prim     : "\<Xi>, \<sigma> \<turnstile> UPrim l :u TPrim (lit_type l) \<langle>{}, {}\<rangle>"

| u_t_product  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile> a :u t \<langle>r , w \<rangle> 
                  ; \<Xi>, \<sigma> \<turnstile> b :u u \<langle>r', w'\<rangle>
                  ; w  \<inter> w' = {}
                  ; w  \<inter> r' = {}
                  ; w' \<inter> r  = {}
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UProduct a b :u TProduct t u \<langle>r \<union> r', w \<union> w'\<rangle>"

| u_t_sum      : "\<lbrakk> \<Xi>, \<sigma> \<turnstile> a :u t \<langle>r, w\<rangle>
                  ; (g, t) \<in> set ts 
                  ; distinct (map fst ts)
                  ; [] \<turnstile>* map snd ts wellformed
                  ; map fst ts = map fst rs
                  ; list_all2 (\<lambda> t r. type_repr t = r) (map snd ts) (map snd rs)
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> USum g a rs :u TSum ts \<langle>r, w\<rangle>"

| u_t_struct   : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r, w\<rangle> 
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> URecord fs :u TRecord ts Unboxed \<langle>r, w\<rangle>"  

| u_t_abstract : "\<lbrakk> abs_typing a n ts Unboxed r w
                  ; [] \<turnstile>* ts wellformed
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UAbstract a :u TCon n ts Unboxed \<langle>r, w\<rangle>"

| u_t_afun     : "\<lbrakk> \<Xi> f = (ks, a, b)
                  ; list_all2 (kinding []) ts ks
                  ; ks \<turnstile> TFun a b wellformed
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UAFunction f ts :u TFun (instantiate ts a) (instantiate ts b) \<langle>{}, {}\<rangle>" 

| u_t_function : "\<lbrakk> \<Xi> , K , [ Some t ] \<turnstile> f : u
                  ; K \<turnstile> t wellformed
                  ; list_all2 (kinding []) ts K
                  \<rbrakk> \<Longrightarrow> \<Xi> , \<sigma> \<turnstile> UFunction f ts :u TFun (instantiate ts t) (instantiate ts u) \<langle>{}, {}\<rangle>"

| u_t_unit     : "\<Xi>, \<sigma> \<turnstile> UUnit :u TUnit \<langle>{}, {}\<rangle>"

| u_t_p_rec_ro : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r, {}\<rangle>
                  ; \<sigma> l = Some (URecord fs) 
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UPtr l (RRecord (map (\<lambda>(a,b). type_repr a) ts)) :u TRecord ts ReadOnly \<langle>insert l r, {}\<rangle>"  

| u_t_p_rec_w  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r, w\<rangle> 
                  ; \<sigma> l = Some (URecord fs)
                  ; l \<notin> (w \<union> r)
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UPtr l (RRecord (map (\<lambda>(a,b). type_repr a) ts)) :u TRecord ts Writable \<langle>r, insert l w\<rangle>"  

| u_t_p_abs_ro : "\<lbrakk> abs_typing a n ts ReadOnly r {}
                  ; [] \<turnstile>* ts wellformed
                  ; \<sigma> l = Some (UAbstract a)
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UPtr l (RCon n (map (type_repr) ts)) :u TCon n ts ReadOnly \<langle>insert l r, {}\<rangle>"

| u_t_p_abs_w  : "\<lbrakk> abs_typing a n ts Writable r w
                  ; [] \<turnstile>* ts wellformed
                  ; \<sigma> l = Some (UAbstract a)
                  ; l \<notin> (w \<union> r)
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UPtr l (RCon n (map (type_repr) ts)) :u TCon n ts Writable \<langle>r, insert l w\<rangle>"

| u_t_r_empty  : "\<Xi>, \<sigma> \<turnstile>* [] :ur [] \<langle>{}, {}\<rangle>"
| u_t_r_cons1  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>  x  :u  t  \<langle>r , w \<rangle>
                  ; \<Xi>, \<sigma> \<turnstile>* xs :ur ts \<langle>r', w'\<rangle>  
                  ; w  \<inter> w' = {}
                  ; w  \<inter> r' = {}
                  ; w' \<inter> r  = {}
                  ; type_repr t = rp
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile>* ((x,rp) # xs) :ur ((t, False) # ts) \<langle>r \<union> r', w \<union> w'\<rangle>"

| u_t_r_cons2  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* xs :ur ts \<langle>r, w\<rangle>
                  ; [] \<turnstile> t wellformed
                  ; type_repr t = rp
                  ; uval_repr x = rp
                  ; uval_repr_deep x = rp
                  \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile>* ((x,rp) # xs) :ur ((t, True) # ts) \<langle>r, w\<rangle>"

lemma u_t_prim' : "\<tau> = lit_type l \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> UPrim l :u TPrim \<tau> \<langle>{}, {}\<rangle>"
   by (simp add: u_t_prim)

inductive_cases u_t_primE     [elim] : "\<Xi>, \<sigma> \<turnstile> UPrim l :u TPrim \<tau> \<langle>r, w\<rangle>"
inductive_cases u_t_functionE [elim] : "\<Xi>, \<sigma> \<turnstile> UFunction f ts :u TFun \<tau> \<rho> \<langle>r, w\<rangle>"
inductive_cases u_t_afunE     [elim] : "\<Xi>, \<sigma> \<turnstile> UAFunction f ts :u TFun \<tau> \<rho> \<langle>r, w\<rangle>"
inductive_cases u_t_sumE      [elim] : "\<Xi>, \<sigma> \<turnstile> v :u TSum \<tau>s \<langle>r, w\<rangle>"
inductive_cases u_t_productE  [elim] : "\<Xi>, \<sigma> \<turnstile> UProduct a b :u TProduct \<tau> \<rho> \<langle>r, w\<rangle>"
inductive_cases u_t_recE      [elim] : "\<Xi>, \<sigma> \<turnstile> URecord fs :u \<tau> \<langle>r, w\<rangle>"
inductive_cases u_t_p_recE    [elim] : "\<Xi>, \<sigma> \<turnstile> UPtr p rp :u TRecord fs s \<langle>r, w\<rangle>"
inductive_cases u_t_r_emptyE  [elim] : "\<Xi>, \<sigma> \<turnstile>* [] :ur \<tau>s \<langle>r, w\<rangle>"
inductive_cases u_t_r_consE   [elim] : "\<Xi>, \<sigma> \<turnstile>* (a # b) :ur \<tau>s \<langle>r, w\<rangle>"

inductive uval_typing_all :: "('f \<Rightarrow> poly_type) 
                            \<Rightarrow> ('f, 'a, 'l) store 
                            \<Rightarrow> ('f, 'a, 'l) uval list 
                            \<Rightarrow> type list 
                            \<Rightarrow> 'l set 
                            \<Rightarrow> 'l set 
                            \<Rightarrow> bool" ("_, _ \<turnstile>* _ :u _ \<langle>_, _\<rangle>" [30,0,0,0,0,20] 80) where
  u_t_all_empty  : "\<Xi>, \<sigma> \<turnstile>* [] :u [] \<langle>{}, {}\<rangle>"

| u_t_all_cons   : "\<lbrakk> \<Xi>, \<sigma> \<turnstile>  x  :u t  \<langle>r , w \<rangle>
                    ; \<Xi>, \<sigma> \<turnstile>* xs :u ts \<langle>r', w'\<rangle>  
                    ; w  \<inter> w' = {}
                    ; w  \<inter> r' = {}
                    ; w' \<inter> r  = {}
                    \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile>* (x # xs) :u (t # ts) \<langle>r \<union> r', w \<union> w'\<rangle>"

inductive matches_ptrs :: "('f \<Rightarrow> poly_type) 
                         \<Rightarrow> ('f, 'a, 'l) store 
                         \<Rightarrow> ('f, 'a, 'l) uval env 
                         \<Rightarrow> ctx
                         \<Rightarrow> 'l set 
                         \<Rightarrow> 'l set 
                         \<Rightarrow> bool" ("_, _ \<turnstile> _ matches _ \<langle>_, _\<rangle>" [30,0,0,0,0,20] 60) where 

  matches_ptrs_empty : "\<Xi>, \<sigma> \<turnstile> [] matches [] \<langle>{}, {}\<rangle>"

| matches_ptrs_none  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile> xs matches \<Gamma> \<langle>r, w\<rangle> 
                        \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> (x # xs) matches (None # \<Gamma>) \<langle>r, w\<rangle>"

| matches_ptrs_some  : "\<lbrakk> \<Xi>, \<sigma> \<turnstile> x  :u      t  \<langle>r , w \<rangle>
                        ; \<Xi>, \<sigma> \<turnstile> xs matches ts \<langle>r', w'\<rangle>  
                        ; w  \<inter> w' = {}
                        ; w  \<inter> r' = {}
                        ; w' \<inter> r  = {}
                        \<rbrakk> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> (x # xs) matches (Some t # ts) \<langle>r \<union> r', w \<union> w'\<rangle>"

inductive_cases matches_ptrs_consE: "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (\<tau> # \<tau>s) \<langle> r , w \<rangle>"


definition frame :: "('f, 'a, 'l) store \<Rightarrow> 'l set \<Rightarrow> ('f, 'a, 'l) store \<Rightarrow> 'l set \<Rightarrow> bool"
           where
  "frame \<sigma> pi \<sigma>' po \<equiv> \<forall>p. (p \<in> pi \<and> p \<notin> po \<longrightarrow> \<sigma>' p = None)
                       \<and>  (p \<notin> pi \<and> p \<in> po \<longrightarrow> \<sigma>  p = None)
                       \<and>  (p \<notin> pi \<and> p \<notin> po \<longrightarrow> \<sigma>  p = \<sigma>' p)"

definition proc_env_matches_ptrs :: "(('f,'a,'l) uabsfuns) \<Rightarrow> ('f \<Rightarrow> poly_type) \<Rightarrow> bool" 
           ("_ matches-u _" [30,20] 60) where 
  "\<xi> matches-u \<Xi> \<equiv> (\<forall> f. let (K, \<tau>i, \<tau>o) = \<Xi> f 
                          in (\<forall> \<sigma> \<sigma>' \<tau>s v v' r w. list_all2 (kinding []) \<tau>s K 
                                             \<longrightarrow> (\<Xi> , \<sigma> \<turnstile> v   :u instantiate \<tau>s \<tau>i \<langle>r, w\<rangle>)
                                             \<longrightarrow> \<xi> f (\<sigma>, v) (\<sigma>', v')
                                             \<longrightarrow> (\<exists>r' w'. (\<Xi> , \<sigma>' \<turnstile> v' :u instantiate \<tau>s \<tau>o \<langle>r', w'\<rangle>)
                                              \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w')))"

lemma uval_typing_to_kinding:
shows "\<Xi>, \<sigma> \<turnstile> v :u t \<langle>r, w\<rangle> \<Longrightarrow> [] \<turnstile> t wellformed"
and   "\<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r, w\<rangle> \<Longrightarrow> [] \<turnstile>* (map fst ts) wellformed"
proof (induct  arbitrary: k rule: uval_typing_uval_typing_record.inducts)
next case u_t_sum      then show ?case by (force intro: kinding_kinding_all_kinding_record.intros)
next case u_t_struct   then show ?case by ( clarsimp
                                          , intro exI kinding_kinding_all_kinding_record.intros
                                          , auto intro: kinding_all_record' simp: kind_top)
next case u_t_abstract then show ?case by ( clarsimp
                                          , intro exI kinding_kinding_all_kinding_record.intros
                                          , auto simp: kind_top)
next case u_t_function then show ?case by (force dest!: typing_to_kinding
                                                 intro: substitutivity kinding_kinding_all_kinding_record.intros)
next case u_t_afun     then show ?case by (force intro: substitutivity kinding_kinding_all_kinding_record.intros)
qed (auto intro: kinding_kinding_all_kinding_record.intros
                 kind_tcon [OF supersumption(2) [where k' ="{}"]]
                 kinding_all_record' [OF supersumption(2) [where k' = "{}"]]
                 supersumption)



lemma uval_typing_all_record:
assumes "\<Xi>, \<sigma> \<turnstile>* vs :u ts \<langle>r, w\<rangle>"
shows "\<Xi>, \<sigma> \<turnstile>* (zip vs (map (type_repr) ts)) :ur zip ts (replicate (length ts) False) \<langle>r, w\<rangle>"
using assms proof (induct rule: uval_typing_all.induct)
qed (auto intro: uval_typing_uval_typing_record.intros)


lemma uval_typing_pointers_noalias:
shows "\<lbrakk> \<Xi>, \<sigma> \<turnstile>  v  :u  \<tau>  \<langle> r , w \<rangle> \<rbrakk> \<Longrightarrow> r \<inter> w = {}"
and   "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* vs :ur \<tau>s \<langle> r , w \<rangle> \<rbrakk> \<Longrightarrow> r \<inter> w = {}"
proof (induct rule: uval_typing_uval_typing_record.inducts)
qed (auto simp: abs_typing_noalias [where s = Unboxed] abs_typing_noalias [where s = Writable])

lemma shareable_not_writable:
assumes "S \<in> k"
shows "\<lbrakk> \<Xi>, \<sigma> \<turnstile>  v  :u  \<tau>  \<langle> r , w \<rangle>; K \<turnstile>  \<tau>  :\<kappa>  k \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s \<langle> r , w \<rangle>; K \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> w = {}"
using assms proof (induct rule: uval_typing_uval_typing_record.inducts)
qed (force simp: kinding_all_set abs_typing_readonly [where s = Unboxed])+

lemma discardable_not_writable:
assumes "D \<in> k"
shows "\<lbrakk> \<Xi>, \<sigma> \<turnstile>  v  :u  \<tau>  \<langle> r , w \<rangle>; K \<turnstile>  \<tau>  :\<kappa>  k \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s \<langle> r , w \<rangle>; K \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> w = {}"
using assms proof (induct rule: uval_typing_uval_typing_record.inducts)
qed (force simp: kinding_all_set abs_typing_readonly [where s = Unboxed])+


lemma discardable_not_writable_all:
assumes "D \<in> k"
shows   "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs :u \<tau>s \<langle> r , w \<rangle>; K \<turnstile>* \<tau>s :\<kappa> k \<rbrakk> \<Longrightarrow> w = {}"
proof (induct rule: uval_typing_all.induct)
qed (auto elim: kinding_all.cases
          dest: discardable_not_writable [OF assms])

lemma escapable_no_readers:
shows   "\<lbrakk> \<Xi> , \<sigma> \<turnstile>  x  :u  \<tau>  \<langle>r, w\<rangle> ; E \<in> k; [] \<turnstile>  \<tau>  :\<kappa>  k \<rbrakk> \<Longrightarrow> r = {}"
and     "\<lbrakk> \<Xi> , \<sigma> \<turnstile>* xs :ur \<tau>s \<langle>r, w\<rangle> ; E \<in> k; [] \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> r = {}"
proof (induct arbitrary: k and k rule: uval_typing_uval_typing_record.inducts)
qed (fastforce dest!: abs_typing_escape [where s = Unboxed , simplified, rotated -1]
                      abs_typing_escape [where s = Writable, simplified, rotated -1]
               simp:  kinding_all_set)+


lemma map_tprim_kinding:
shows "[] \<turnstile>* map (TPrim) \<tau>s :\<kappa> {D,S,E}"
proof (induct \<tau>s) qed (auto intro: kinding_kinding_all_kinding_record.intros)

lemma tprim_no_pointers:
assumes "\<Xi> , \<sigma> \<turnstile> v :u TPrim \<tau> \<langle>r, w\<rangle>"
shows   "r = {}"
and     "w = {}"
proof -
  from assms show "w = {}"by (auto intro!: discardable_not_writable(1) [OF _ assms, where k = "{D}"]
                                           kinding_kinding_all_kinding_record.intros)
  from assms show "r = {}"by (auto elim!:  uval_typing.cases)
qed

lemma tfun_no_pointers:
assumes "\<Xi> , \<sigma> \<turnstile> v :u TFun \<tau> \<rho> \<langle>r, w\<rangle>"
shows   "r = {}"
and     "w = {}"
proof -
  from assms show "w = {}" by (auto elim!:  uval_typing.cases)
  from assms show "r = {}" by (auto elim!:  uval_typing.cases)
qed

lemma map_tprim_no_pointers:
assumes "\<Xi> , \<sigma> \<turnstile>* vs :u map TPrim \<tau>s \<langle>r, w\<rangle>"
shows   "r = {}"
and     "w = {}"
using assms proof -
obtain ys where X: "map TPrim \<tau>s = ys" by (clarsimp)
show "r = {}" using assms [simplified X] X
  proof (induct arbitrary: \<tau>s rule: uval_typing_all.induct )
       case u_t_all_empty then show ?case by (simp)
  next case u_t_all_cons  with X show ?case apply (clarsimp)
                                            apply (rule tprim_no_pointers, simp).
  qed

show "w = {}" using assms apply -
                          apply (rule discardable_not_writable_all [where k = "{D, S, E}"])
                          apply (auto intro: map_tprim_kinding).
qed

lemma map_tprim_no_pointers':
assumes "\<Xi> , \<sigma> \<turnstile>* vs :u map TPrim \<tau>s \<langle>r, w\<rangle>"
shows   "\<Xi> , \<sigma> \<turnstile>* vs :u map TPrim \<tau>s \<langle>{}, {}\<rangle>"
using assms by (auto dest: map_tprim_no_pointers)
 

lemma matches_ptrs_none [simp]:
shows "(\<Xi>, \<sigma> \<turnstile> (x # xs) matches (None # ts) \<langle>r , w\<rangle>)
     = (\<Xi>, \<sigma> \<turnstile> xs       matches ts \<langle>r , w\<rangle>)"
proof (rule iffI) 
     assume "\<Xi>, \<sigma> \<turnstile> (x # xs) matches (None # ts) \<langle>r, w\<rangle>" 
then show   "\<Xi>, \<sigma> \<turnstile> xs       matches ts          \<langle>r, w\<rangle>"
     by (auto elim: matches_ptrs.cases)

next assume "\<Xi>, \<sigma> \<turnstile> xs       matches ts          \<langle>r, w\<rangle>"
then show   "\<Xi>, \<sigma> \<turnstile> (x # xs) matches (None # ts) \<langle>r, w\<rangle>"
     by (auto intro: matches_ptrs.intros)
qed



lemma pointerset_helper:
assumes "\<Xi>, \<sigma> \<turnstile> v :u \<tau> \<langle>r, w\<rangle>"
and     "r = r'"
and     "w = w'"
shows   "\<Xi>, \<sigma> \<turnstile> v :u \<tau> \<langle>r', w'\<rangle>"
using assms by auto

lemma pointerset_helper_record:
assumes "\<Xi>, \<sigma> \<turnstile>* vs :ur \<tau>s \<langle>r, w\<rangle>"
and     "r = r'"
and     "w = w'"
shows   "\<Xi>, \<sigma> \<turnstile>* vs :ur \<tau>s \<langle>r', w'\<rangle>"
using assms by auto


lemma pointerset_helper_matches_ptrs:
assumes "\<Xi>, \<sigma> \<turnstile> vs matches \<tau>s \<langle>r, w\<rangle>"
and     "r = r'"
and     "w = w'"
shows   "\<Xi>, \<sigma> \<turnstile> vs matches \<tau>s \<langle>r', w'\<rangle>"
using assms by auto

lemma pointerset_helper_frame:
assumes "frame \<sigma> w \<sigma>' w'"
and     "w  = u "
and     "w' = u'"
shows   "frame \<sigma> u \<sigma>' u'"
using assms by auto

lemma bang_idempotent':
shows "((\<lambda>(c, t). (c, bang t)) \<circ> (\<lambda>(a, b). (a, bang b))) = (\<lambda>(c,t).(c,bang t))"
by (rule ext, clarsimp simp: bang_idempotent)

lemma list_all2_bang_type_helper:
 "\<lbrakk> list_all2 (\<lambda>t. (=) (type_repr t)) ts rs ; [] \<turnstile>* ts :\<kappa>  k\<rbrakk>
        \<Longrightarrow> list_all2 (\<lambda>t. (=) (type_repr t)) (map (bang) ts) rs"
by (induct rule: list_all2_induct, auto dest: bang_type_repr)


lemma bang_type_repr':
assumes "[] \<turnstile>* ts :\<kappa>r k"
shows   "(map ((\<lambda>(a, b). type_repr a) \<circ> (\<lambda>(t, y). (bang t, y))) ts) = (map (\<lambda>(a,b). type_repr a) ts)"
using assms by (force dest: kinding_record_wellformed intro: bang_type_repr)

  
lemma uval_typing_bang:
shows   "\<Xi>, \<sigma> \<turnstile> v :u \<tau> \<langle>r, w\<rangle> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> v :u bang \<tau> \<langle>r \<union> w, {}\<rangle>"
and     "\<Xi>, \<sigma> \<turnstile>* vs :ur \<tau>s \<langle>r, w\<rangle> \<Longrightarrow> \<Xi>, \<sigma> \<turnstile>* vs :ur  (map (\<lambda> (t, b). (bang t, b)) \<tau>s) \<langle>r \<union> w, {}\<rangle>"
proof (induct rule: uval_typing_uval_typing_record.inducts)
next case u_t_product  then show ?case by (auto  dest:  uval_typing_uval_typing_record.u_t_product 
                                                 intro: pointerset_helper)
next case u_t_sum      then show ?case by (auto  intro!: uval_typing_uval_typing_record.intros exI
                                                 dest:  bang_kind
                                                        list_all2_bang_type_helper
                                                          [ where ts = "map snd ts"
                                                            and   rs = "map snd rs"
                                                            for ts rs
                                                          , simplified])
next case u_t_p_rec_ro
  then show ?case
    apply clarsimp
    apply (drule uval_typing_to_kinding(2))
    apply (frule uval_typing_uval_typing_record.u_t_p_rec_ro)
    apply (auto dest!: kinding_all_record' bang_type_repr')
  done
next case u_t_p_rec_w
  then show ?case
    apply (clarsimp)
    apply (drule uval_typing_to_kinding(2))
    apply (frule uval_typing_uval_typing_record.u_t_p_rec_ro)
    apply (auto dest!: kinding_all_record' bang_type_repr')
  done  
next case u_t_p_abs_ro
  then show ?case
    apply (clarsimp)
    apply (drule abs_typing_bang [where s = ReadOnly and w = "{}", simplified])
    apply (frule bang_kind)
    apply (force dest: uval_typing_uval_typing_record.u_t_p_abs_ro) 
  done
next case u_t_p_abs_w 
  then show ?case
    apply (clarsimp)
    apply (drule abs_typing_bang [where s = Writable, simplified])
    apply (frule bang_kind)
    apply (force dest:uval_typing_uval_typing_record.u_t_p_abs_ro) 
  done
next case u_t_r_cons1
  then show ?case
    apply (clarsimp)
    apply ( drule(1) uval_typing_uval_typing_record.u_t_r_cons1
                     [ where t = "bang t"
                       and   ts = " map (\<lambda>(a,b).(bang a, b)) ts"
                       for t ts]
          , blast, blast, blast, simp)
    apply ( rule pointerset_helper_record
          , (force dest: uval_typing_to_kinding)+)
  done
qed (force intro: uval_typing_uval_typing_record.intros bang_kind abs_typing_bang [where s = Unboxed, simplified])+


lemma u_t_afun_instantiate:
assumes "list_all2 (kinding K') ts K"
and     "list_all2 (kinding []) \<delta> K'"
and     "K \<turnstile> t wellformed"
and     "K \<turnstile> u wellformed"
and     "\<Xi> f = (K, t, u)"
shows   "\<Xi> , \<sigma> \<turnstile> UAFunction f (map (instantiate \<delta>) ts) :u TFun (instantiate \<delta> (instantiate ts t))
                                                               (instantiate \<delta> (instantiate ts u)) \<langle>{}, {}\<rangle>" 
proof -
from assms have "TFun (instantiate \<delta> (instantiate ts t))
                      (instantiate \<delta> (instantiate ts u))
               = TFun (instantiate (map (instantiate \<delta>) ts) t)
                      (instantiate (map (instantiate \<delta>) ts) u)"
           by (force intro: instantiate_instantiate dest: list_all2_lengthD)
with assms show ?thesis by (force intro: uval_typing_uval_typing_record.intros 
                                         list_all2_substitutivity
                                         kinding_kinding_all_kinding_record.intros)
qed

lemma u_t_function_instantiate:
  assumes "\<Xi>, K, [Some t] \<turnstile> f : u"
  and     "K \<turnstile> t wellformed"
  and     "list_all2 (kinding []) \<delta> K'"
  assumes "list_all2 (kinding K') ts K"
  shows   "\<Xi> , \<sigma> \<turnstile> UFunction f (map (instantiate \<delta>) ts) :u TFun (instantiate \<delta> (instantiate ts t))
                                                                (instantiate \<delta> (instantiate ts u)) \<langle>{}, {}\<rangle>"
proof -
from assms have "TFun (instantiate \<delta> (instantiate ts t))
                      (instantiate \<delta> (instantiate ts u))
               = TFun (instantiate (map (instantiate \<delta>) ts) t)
                      (instantiate (map (instantiate \<delta>) ts) u)"
           by (force intro: instantiate_instantiate dest: list_all2_lengthD dest!: typing_to_kinding)
with assms show ?thesis by (force intro: uval_typing_uval_typing_record.intros 
                                         list_all2_substitutivity
                                         kinding_kinding_all_kinding_record.intros)
qed

lemma matches_ptrs_noalias:
assumes "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>"
shows   "w \<inter> r = {}"
using assms proof (induct rule: matches_ptrs.induct)
qed (auto dest!: uval_typing_pointers_noalias)

lemma matches_ptrs_some_bang:
assumes "\<Xi>, \<sigma> \<turnstile> x :u t \<langle>r, w\<rangle>"
and     "\<Xi>, \<sigma> \<turnstile> xs matches ts \<langle>r' \<union> b, w'\<rangle>"
and     "w \<inter> w' = {}"
and     "w \<inter> r' = {}"
and     "w' \<inter> r = {}"
shows   "\<Xi>, \<sigma> \<turnstile> x # xs matches Some (bang t) # ts \<langle>r \<union> (r' \<union> (b \<union> w)), w'\<rangle>"
proof - 
have SetLemma : "r \<union> (r' \<union> (b \<union> w)) = (r \<union> w) \<union> (r' \<union> b)" by auto
from assms show ?thesis by (auto simp:  SetLemma
                                 intro: matches_ptrs_some [where w = "{}", simplified]
                                        uval_typing_bang)
qed

lemma matches_ptrs_split':
assumes "[] \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2" 
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>" 
shows   "\<exists>r' w' r'' w''. r = r' \<union> r'' 
                       \<and> w = w' \<union> w'' 
                       \<and> w' \<inter> w'' = {} 
                       \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>1 \<langle>r' , w' \<rangle>) 
                       \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>2 \<langle>r'', w''\<rangle>)" 
using assms proof (induct arbitrary: \<gamma> r w rule: split_induct)
     case split_empty then show ?case by (fastforce elim:  matches_ptrs.cases
                                                    intro: matches_ptrs.intros)
next case (split_cons x xs a as b bs \<gamma> r w) 
  then show ?case 
  proof (cases \<Xi> \<sigma> \<gamma> x xs r w rule: matches_ptrs_consE)
       case 1 with split_cons show ?case   by simp
  next case 2 with split_cons show ?thesis by (auto elim: split_comp.cases)
  next case (3 _ _ rx wx _ rs ws)
    with split_cons show ?thesis
    proof (cases rule: split_comp.cases)
         case none  with 3 show ?thesis by simp
    next case left  with 3 show ?thesis
      apply (clarsimp dest!: split_cons(3))
      apply (rule_tac x = "rx \<union> r'" in exI)
      apply (rule_tac x = "wx \<union> w'" in exI)
      apply (rule_tac x = "r''"     in exI, rule,blast)
      apply (rule_tac x = "w''"     in exI)
      apply (force intro!: matches_ptrs.intros)
    done
    next case right with 3 show ?thesis
      apply (clarsimp dest!: split_cons(3))
      apply (rule_tac x = "r'"       in exI)
      apply (rule_tac x = "w'"       in exI)
      apply (rule_tac x = "rx \<union> r''" in exI, rule, blast)
      apply (rule_tac x = "wx \<union> w''" in exI)
      apply (force intro!: matches_ptrs.intros)
    done
    next case share with 3 show ?thesis
      apply (clarsimp dest!: split_cons(3))
      apply (drule(2) shareable_not_writable)
      apply (clarsimp)
      apply (rule_tac x = "rx \<union> r'"  in exI)
      apply (rule_tac x = "w'"       in exI)
      apply (rule_tac x = "rx \<union> r''" in exI, rule, blast)
      apply (rule_tac x = "w''"      in exI)
      apply (force intro: matches_ptrs_some [where w = "{}", simplified])
    done
    qed
  qed 
qed

lemma matches_ptrs_split:
assumes "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2" 
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>" 
and     "list_all2 (kinding []) \<tau>s K" 
shows   "\<exists>r' w' r'' w''. r = r' \<union> r'' 
                       \<and> w = w' \<union> w'' 
                       \<and> w' \<inter> w'' = {} 
                       \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>1) \<langle>r' , w' \<rangle>) 
                       \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>2) \<langle>r'', w''\<rangle>)" 
using assms by (auto dest:  instantiate_ctx_split 
                     intro: matches_ptrs_split' [simplified])



lemma matches_ptrs_split_bang':
assumes "split_bang [] vs \<Gamma> \<Gamma>1 \<Gamma>2" 
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>" 
shows   "\<exists>r' w' r'' w'' b. r = r' \<union> r'' 
                         \<and> w' \<inter> w'' = {} 
                         \<and> w = w' \<union> w'' \<union> b
                         \<and> b \<inter> (w' \<union> w'') = {}
                         \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>1 \<langle>r' \<union> b, w'     \<rangle>) 
                         \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>2 \<langle>r''   , w'' \<union> b\<rangle>)" 
using assms proof (induct arbitrary: \<gamma> r w rule: split_bang.induct)
     case split_bang_nil then show ?case by (fastforce elim:  matches_ptrs.cases
                                                         intro: matches_ptrs.intros)
   next case (split_bang_cons iss K x xa xb xs as bs \<gamma> r w)
     note IH = split_bang_cons(3)

     show ?case
     proof (cases \<Xi> \<sigma> \<gamma> x xs r w rule: matches_ptrs_consE)
       case 1 with split_bang_cons show ?case   by simp
     next case 2 with split_bang_cons show ?thesis
         by (auto simp add: split_bang_comp.simps split_comp.simps)
     next case (3 g ta rx wx gs rs ws)
       with split_bang_cons(1) show ?thesis
       proof (cases rule: split_bang_comp.cases)
         case nobang
         from nobang(2) show ?thesis
         proof (cases rule: split_comp.cases)
           case none with 3 show ?thesis by simp
         next
           case left with 3 show ?thesis
             apply -
             apply (clarsimp dest!: IH)
             apply (rule_tac x = "rx \<union> r'" in exI)
             apply (rule_tac x = "wx \<union> w'" in exI)
             apply (rule_tac x = "r''"     in exI, rule, blast)
             apply (rule_tac x = "w''"     in exI, rule, blast)
             apply (rule_tac x = "b"      in exI)
             apply (auto simp: Un_assoc intro!: matches_ptrs.intros)
             done
         next
           case right with 3 show ?thesis
             apply (clarsimp dest!: IH)
             apply (rule_tac x = "r'"       in exI)
             apply (rule_tac x = "w'"       in exI)
             apply (rule_tac x = "rx \<union> r''" in exI, rule, blast)
             apply (rule_tac x = "wx \<union> w''" in exI, rule, blast)
             apply (rule_tac x = "b"       in exI)
             apply (auto simp: Un_assoc intro!: matches_ptrs.intros)
             done
         next
           case share with 3 show ?thesis
             apply (clarsimp dest!: IH)
             apply (drule(2) shareable_not_writable)
             apply (clarsimp)
             apply (rule_tac x = "rx \<union> r'"  in exI)
             apply (rule_tac x = "w'"       in exI)
             apply (rule_tac x = "rx \<union> r''" in exI, rule, blast)
             apply (rule_tac x = "w''"      in exI, rule, blast)
             apply (rule_tac x = "b"       in exI)
             apply (auto simp: Un_assoc intro: matches_ptrs_some [where w = "{}", simplified])
             done
         qed
    next
      case dobang with 3 show ?thesis
        apply (clarsimp dest!: IH)
        apply (rule_tac x = "rx \<union> r'"  in exI)
        apply (rule_tac x = "w'"       in exI)
        apply (rule_tac x = "rx \<union> r''" in exI, rule conjI, blast)
        apply (rule_tac x = "w''"      in exI, rule conjI, blast)
        apply (rule_tac x = "b \<union> wx"   in exI, rule conjI, blast)
        apply (auto
            simp:   Un_assoc
            dest:   matches_ptrs_some
            intro!: matches_ptrs_some_bang
            intro:  pointerset_helper_matches_ptrs)
        done
    qed
  qed
qed


lemma matches_ptrs_split_bang:
assumes "split_bang K vs \<Gamma> \<Gamma>1 \<Gamma>2" 
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>" 
and     "list_all2 (kinding []) \<tau>s K" 
shows   "\<exists>r' w' r'' w'' b. r = r' \<union> r'' 
                         \<and> w' \<inter> w'' = {} 
                         \<and> w = w' \<union> w'' \<union> b
                         \<and> b \<inter> (w' \<union> w'') = {}
                         \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>1) \<langle>r'  \<union> b , w'     \<rangle>) 
                         \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>2) \<langle>r''     , w'' \<union> b\<rangle>)" 
using assms by (auto dest:  instantiate_ctx_split_bang
                     intro: matches_ptrs_split_bang' [simplified])

lemma matches_ptrs_weaken':
assumes "[] \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>  \<langle>r, w\<rangle>"
shows   "\<exists> r'. (r' \<subseteq> r) \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>' \<langle>r', w\<rangle>)"
using assms(1) [simplified weakening_def] and assms(2-) 
proof (induct arbitrary: \<gamma> r w rule: list_all2_induct )
     case Nil  then show ?case by auto
next case Cons then show ?case 
  proof (cases rule: weakening_comp.cases)
       case none with Cons show ?thesis by (force elim!: matches_ptrs_consE) 
  next case keep with Cons show ?thesis
    apply (safe elim!: matches_ptrs_consE dest!: Cons(3))
    apply (rule_tac x = "r \<union> r'a" in exI)
    apply (force intro!: matches_ptrs.intros)
  done
  next case drop with Cons show ?thesis
    apply (safe elim!: matches_ptrs_consE weakening_comp.cases dest!: Cons(3))
    apply (frule(2) discardable_not_writable)
    apply (clarsimp)
    apply (rule_tac x = "r'a" in exI)
    apply (force)
  done
  qed
qed

lemma matches_ptrs_weaken:
assumes "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'" 
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>" 
and     "list_all2 (kinding []) \<tau>s K" 
shows   "\<exists>r'. (r' \<subseteq> r) \<and> (\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>') \<langle>r', w\<rangle>) " 
using assms by (auto dest:  instantiate_ctx_weaken
                     intro: matches_ptrs_weaken' [simplified])



lemma matches_ptrs_cons:
assumes "list_all2 (kinding []) \<tau>s K"
and     "\<Xi> , \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r', w'\<rangle>"
and     "\<Xi> , \<sigma> \<turnstile> x :u instantiate \<tau>s \<tau> \<langle>r, w\<rangle>"
and     "w  \<inter> w' = {}"
and     "w  \<inter> r' = {}"
and     "w' \<inter> r  = {}"
shows   "\<Xi> , \<sigma> \<turnstile> (x # \<gamma>) matches (instantiate_ctx \<tau>s (Some \<tau> # \<Gamma>)) \<langle>r \<union> r', w \<union> w'\<rangle>"  
using assms by (auto intro: matches_ptrs_some)

lemma matches_ptrs_empty:
shows "\<Xi> , \<sigma> \<turnstile> [] matches instantiate_ctx \<tau>s [] \<langle>{}, {}\<rangle>" 
by (simp add: matches_ptrs_empty instantiate_ctx_def)

lemma matches_ptrs_length:
assumes "\<Xi> , \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>"
shows   "length \<gamma> = length \<Gamma>"
using assms by (auto elim: matches_ptrs.induct) 

lemma matches_ptrs_empty_env:
assumes "\<Xi>, \<sigma> \<turnstile> \<gamma> matches empty n \<langle>r, w\<rangle>"
shows   "r = {}"
and     "w = {}"
using assms [simplified empty_def] proof (induct n arbitrary: \<gamma> r w)
case 0
  case 1 then show ?case by (auto elim: matches_ptrs.cases)
  case 2 then show ?case by (auto elim: matches_ptrs.cases)
next case (Suc n) 
  case 1 with Suc show ?case by (fastforce elim!: matches_ptrs_consE)
  case 2 with Suc show ?case by (fastforce elim!: matches_ptrs_consE)
qed

lemma matches_ptrs_proj':
assumes "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>"
and     "[] \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i \<tau>" 
and     "i < length \<Gamma>"
shows   "\<exists> r' \<subseteq> r. \<Xi>, \<sigma> \<turnstile> (\<gamma> ! i) :u \<tau> \<langle>r', w\<rangle>"
proof -
  from assms obtain r' where S: "r' \<subseteq> r" 
                       and   I: "\<Xi> , \<sigma> \<turnstile> \<gamma> matches (singleton (length \<Gamma>) i \<tau>) \<langle>r', w\<rangle>"
       by (auto dest: matches_ptrs_weaken')
  from assms obtain env where "singleton (length \<Gamma>) i \<tau> = env" by simp  
  from I [simplified this] S assms(3-) this
  show ?thesis proof (induct arbitrary: i \<Gamma> rule: matches_ptrs.inducts )
       case matches_ptrs_empty then moreover   have "\<Gamma> = []" by (simp add: empty_def)
                                    ultimately show ?case    by simp
  next case (matches_ptrs_none  \<Xi> \<sigma> xs \<Gamma>' r w x i \<Gamma>)
       show ?case proof (cases i)
            case 0       with matches_ptrs_none show ?thesis by ( cases "length \<Gamma>"
                                                                , simp_all add: empty_def )
       next case (Suc n)
         moreover with matches_ptrs_none have "\<Gamma>' = empty (length \<Gamma> - 1) [n := Some \<tau>]"
                                         by (cases "length \<Gamma>", simp_all add: empty_def)
         moreover with matches_ptrs_none have "length \<Gamma> = Suc (length \<Gamma>')"
                                         by (simp add: empty_def)
         ultimately show ?thesis apply -
                                 apply (insert matches_ptrs_none)
                                 apply (auto).
       qed
  next case (matches_ptrs_some)
       show ?case proof (cases i)
            case 0 with matches_ptrs_some show ?thesis
              apply (cases "length \<Gamma>", simp_all add: empty_def)
              apply (clarsimp dest!:matches_ptrs_empty_env(2) [simplified empty_def])
              apply (blast).
       next case (Suc n) with matches_ptrs_some show ?thesis by ( cases "length \<Gamma>"
                                                                , simp_all add: empty_def )
       qed
  qed
qed



lemma matches_ptrs_proj:
assumes "list_all2 (kinding []) \<tau>s K"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "K \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i \<tau>" 
and     "i < length \<Gamma>"
shows   "\<exists> r' \<subseteq> r. \<Xi>, \<sigma> \<turnstile> (\<gamma> ! i) :u (instantiate \<tau>s \<tau>) \<langle>r', w\<rangle>"
using assms by (fastforce dest:   instantiate_ctx_weaken
                          intro!: matches_ptrs_proj' [simplified])

lemma matches_ptrs_proj_single':
assumes "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>"
and     "i < length \<Gamma>"
and     "\<Gamma> ! i = Some \<tau>"
shows   "\<exists>r' w'. (r' \<subseteq> r) \<and> (w' \<subseteq> w) \<and> (\<Xi>, \<sigma> \<turnstile> (\<gamma> ! i) :u \<tau> \<langle>r', w'\<rangle>)"
using assms proof (induct arbitrary: i rule: matches_ptrs.induct)
     case matches_ptrs_empty then show ?case by simp
next case matches_ptrs_none  then show ?case
  proof (cases i)
       case 0   with matches_ptrs_none show ?thesis by simp
  next case Suc with matches_ptrs_none show ?thesis by simp
  qed
next case matches_ptrs_some then show ?case
  proof (cases i)
       case 0   with matches_ptrs_some show ?thesis by auto
  next case Suc with matches_ptrs_some show ?thesis 
    apply (clarsimp dest!: matches_ptrs_some(3))
    apply (rule_tac x = r'a in exI, rule, blast)
    apply (rule_tac x = w'a in exI, rule, blast)
    apply (simp)
  done
  qed
qed


lemma matches_ptrs_proj_consumed':
assumes "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>"
and     "[] \<turnstile> \<Gamma> consumed"
shows   "w = {}"
using assms proof(induction rule: matches_ptrs.induct)         
qed (auto simp: weakening_def empty_def
          elim: weakening_comp.cases
          dest: discardable_not_writable)


lemma matches_ptrs_proj_consumed:
assumes "list_all2 (kinding []) \<tau>s K"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "K \<turnstile> \<Gamma> consumed"
shows   "w = {}"
using assms by (auto dest:   instantiate_ctx_weaken
                     intro!: matches_ptrs_proj_consumed')

lemma matches_ptrs_proj_single:
assumes "list_all2 (kinding []) \<tau>s K"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "i < length \<Gamma>"
and     "\<Gamma> ! i = Some \<tau>"
shows   "\<exists> r' w'. (r' \<subseteq> r) \<and> (w' \<subseteq> w) \<and> (\<Xi>, \<sigma> \<turnstile> (\<gamma> ! i) :u instantiate \<tau>s \<tau> \<langle>r', w'\<rangle>)"
using assms by (auto intro!: matches_ptrs_proj_single' [simplified]
                     simp:   instantiate_ctx_def)


section {* procedure environment matches *}
lemma proc_env_matches_ptrs_abstract:
assumes "\<xi> matches-u \<Xi>"
and     "\<Xi> f = (K, \<tau>i, \<tau>o)"
and     "list_all2 (kinding []) \<tau>s K"
and     "\<Xi> , \<sigma> \<turnstile> v   :u instantiate \<tau>s \<tau>i \<langle>r, w\<rangle>"
and     "\<xi> f (\<sigma>, v) (\<sigma>', v')"
shows   "(\<exists>r' w'. (\<Xi> , \<sigma>' \<turnstile> v' :u instantiate \<tau>s \<tau>o \<langle>r', w'\<rangle>)
                \<and> r' \<subseteq> r
                \<and> frame \<sigma> w \<sigma>' w')"
using assms by ( clarsimp simp: proc_env_matches_ptrs_def
               , drule_tac x = f in spec
               , auto)


section {* frame *}

theorem frame_id:
shows "frame \<sigma> w \<sigma> w"
by (simp add: frame_def)

section {* Type Safety *}

theorem u_progress: 
assumes "\<Xi>, K, \<Gamma> \<turnstile> c : \<tau>" 
and     "\<xi> matches-u \<Xi>"
and     "list_all2 (kinding []) \<tau>s K"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>" 
shows   "\<exists>! st. (\<xi>, \<gamma> \<turnstile> (\<sigma>,c) \<Down>! st)" 
oops (* NOT ACTUALLY EVEN TRUE IN THE CURRENT SETUP *)

lemma u_t_map_UPrimD:
  "\<Xi> , \<sigma> \<turnstile>* vs :u map TPrim \<tau>s \<langle>rs, ws\<rangle>
    \<Longrightarrow> \<exists>lits. vs = map UPrim lits \<and> map lit_type lits = \<tau>s"
  apply (induct \<Xi> \<sigma> vs \<tau>s'\<equiv>"map TPrim \<tau>s" rs ws
        arbitrary: \<tau>s rule: uval_typing_all.induct, simp_all)
  apply (clarsimp simp: Cons_eq_map_conv)
  apply (erule uval_typing.cases, simp_all)
  apply (erule meta_allE, drule meta_mp, rule refl, clarsimp)
  apply (rule exI[where x="x # xs" for x xs], simp)
  done

lemma eval_prim_u_preservation:
assumes "prim_op_type p = (\<tau>s, \<tau>)"
and     "\<Xi> , \<sigma> \<turnstile>* vs :u map TPrim \<tau>s \<langle>{}, {}\<rangle>"
shows   "\<Xi> , \<sigma> \<turnstile>  eval_prim_u p vs :u TPrim \<tau> \<langle>{}, {}\<rangle>"
using assms u_t_prim[where \<Xi>=\<Xi> and l="case eval_prim_u p vs of UPrim v \<Rightarrow> v"]
by (clarsimp simp add: eval_prim_u_def o_def eval_prim_op_lit_type dest!: u_t_map_UPrimD)

lemma uval_typing_valid:
assumes "p \<in> (r \<union> w)"
shows   "\<Xi> , \<sigma> \<turnstile> u :u t \<langle> r , w \<rangle> \<Longrightarrow> \<sigma> p \<noteq> None"
and     "\<Xi> , \<sigma> \<turnstile>* us :ur ts \<langle> r , w \<rangle> \<Longrightarrow> \<sigma> p \<noteq> None"
using assms proof(induct  rule: uval_typing_uval_typing_record.inducts)
qed (auto dest: abs_typing_readonly [ where s = Unboxed, simplified]
                abs_typing_valid)

lemma matches_ptrs_valid:
assumes "\<Xi> , \<sigma> \<turnstile> u matches t \<langle> r , w \<rangle>"
and     "p \<in> (r \<union> w)"
shows   "\<sigma> p \<noteq> None"
using assms proof (induct arbitrary: p rule: matches_ptrs.induct)
case matches_ptrs_some then show ?case using uval_typing_valid by blast
qed auto

lemma uval_typing_frame:
assumes "frame \<sigma> w1 \<sigma>' w2"
and     "w \<inter> w1 = {}"
and     "r \<inter> w1 = {}"
shows   "\<Xi> , \<sigma> \<turnstile>  u  :u  t  \<langle> r , w \<rangle> \<Longrightarrow> \<Xi> , \<sigma>' \<turnstile>  u  :u t   \<langle> r , w \<rangle>"
and     "\<Xi> , \<sigma> \<turnstile>* us :ur ts \<langle> r , w \<rangle> \<Longrightarrow> \<Xi> , \<sigma>' \<turnstile>* us :ur ts \<langle> r , w \<rangle>"
using assms  proof(induct  rule:uval_typing_uval_typing_record.inducts)
     case u_t_prim     then show ?case by (auto simp add: uval_typing_uval_typing_record.u_t_prim)
next case u_t_product  then show ?case by (fastforce intro!: uval_typing_uval_typing_record.intros)
next case u_t_sum      then show ?case by (fastforce intro!: uval_typing_uval_typing_record.intros)
next case u_t_struct   then show ?case by (fastforce intro!: uval_typing_uval_typing_record.intros)
next case u_t_abstract then show ?case by (simp add: uval_typing_uval_typing_record.u_t_abstract)
next case u_t_function then show ?case by (simp add: uval_typing_uval_typing_record.u_t_function)
next case u_t_unit     then show ?case by (simp add: uval_typing_uval_typing_record.u_t_unit)
next case u_t_r_empty  then show ?case by (simp add: uval_typing_uval_typing_record.u_t_r_empty)
next case u_t_r_cons1  then show ?case by (force simp: frame_def
                                                 intro!: uval_typing_uval_typing_record.u_t_r_cons1)
next case u_t_r_cons2  then show ?case by (simp add: uval_typing_uval_typing_record.u_t_r_cons2)
qed (fastforce simp:   frame_def
               intro!: uval_typing_uval_typing_record.intros)+

lemma matches_ptrs_frame:
assumes "\<Xi> , \<sigma> \<turnstile> u matches t \<langle> r , w \<rangle>"
and     "frame \<sigma> w1 \<sigma>' w2"
and     "w1 \<inter> w = {}"
and     "w1 \<inter> r = {}"
shows   "\<Xi> , \<sigma>' \<turnstile> u matches t \<langle> r , w \<rangle>"
using assms proof (induct rule: matches_ptrs.induct)
     case matches_ptrs_empty then show ?case by (simp add: matches_ptrs.matches_ptrs_empty)
next case matches_ptrs_none  then show ?case by (auto)
next case matches_ptrs_some  then show ?case by (fast dest:   uval_typing_frame(1) [rotated -1]
                                                      intro!: matches_ptrs.intros)
qed

lemma frame_single_update:
shows  "frame \<sigma> {l} (\<sigma>(l \<mapsto> v)) {l}"
by (simp add: frame_def)

lemma frame_noalias_uval_typing :
assumes "frame \<sigma> u \<sigma>' u'"
and     "\<Xi>, \<sigma> \<turnstile> v :u \<tau> \<langle>r, w\<rangle>"
shows   "u  \<inter> w = {} \<Longrightarrow> u' \<inter> w = {}"
and     "u  \<inter> r = {} \<Longrightarrow> u' \<inter> r = {}"
using assms by (auto iff:  set_eq_iff
                     simp: frame_def
                     dest: uval_typing_valid [rotated 1])

lemma frame_noalias_matches_ptrs :
assumes "frame \<sigma> u \<sigma>' u'"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>"
shows   "u  \<inter> w = {} \<Longrightarrow> u' \<inter> w = {}"
and     "u  \<inter> r = {} \<Longrightarrow> u' \<inter> r = {}"
using assms by (auto simp: frame_def
                     dest: matches_ptrs_valid
                     iff:  set_eq_iff)

lemma frame_noalias_uval_typing' :
assumes "frame \<sigma> u \<sigma>' u'"
and     "\<Xi>, \<sigma> \<turnstile> v :u \<tau> \<langle>r, w\<rangle>"
shows   "w \<inter> u = {} \<Longrightarrow> w \<inter> u' = {}"
and     "r \<inter> u = {} \<Longrightarrow> r \<inter> u' = {}"
using assms by (auto simp: frame_def
                     dest: uval_typing_valid [rotated 1]
                     iff:  set_eq_iff)


lemma frame_noalias_2 :
assumes "frame \<sigma>  u \<sigma>'  u'"
and     "frame \<sigma>' w \<sigma>'' w'"
and     "\<Xi>, \<sigma>  \<turnstile> \<gamma>  matches \<Gamma>  \<langle>r , w\<rangle>"
and     "\<Xi>, \<sigma>' \<turnstile> v :u \<tau> \<langle>r', u'\<rangle>"
and     "u \<inter> w = {}"
shows   "u' \<inter> w' = {}"
proof -
from assms(1,3,5) have "u' \<inter> w = {}"by (rule frame_noalias_matches_ptrs)
with assms(2,4)   show ?thesis      by (rule frame_noalias_uval_typing')
qed
                                                       
lemma frame_let:
assumes "frame \<sigma> w \<sigma>' w'"
and     "frame \<sigma>' (u \<union> w') \<sigma>'' u''"
shows   "frame \<sigma> (w \<union> u) \<sigma>'' u''"
using assms apply -
  apply (simp add: frame_def)
  apply (clarsimp)
  apply (drule_tac x = p in spec)
  apply (drule_tac x = p in spec)
  apply (clarsimp)
  apply (auto)
done

lemma frame_app:
assumes "frame \<sigma> w \<sigma>' w'"
and     "frame \<sigma>' u \<sigma>'' u'"
shows   "frame \<sigma> (w \<union> u) \<sigma>'' (w' \<union> u')"
using assms apply -
  apply (simp add: frame_def)
  apply (clarsimp)
  apply (drule_tac x = p in spec)
  apply (drule_tac x = p in spec)
  apply (clarsimp)
  apply (auto)
done


lemma frame_trans:
assumes "frame \<sigma>  w  \<sigma>'  w'"
and     "frame \<sigma>' w' \<sigma>'' w''"
shows   "frame \<sigma>  w  \<sigma>'' w''"
using assms by (rule frame_let [where u = "{}", simplified])

lemma subset_helper:
assumes "x \<inter> y = {}"
and     "x' \<subseteq> x"
and     "y' \<subseteq> y"
shows   "x' \<inter> y' = {}"
using assms by (blast)

lemma subset_helper2:
assumes "x \<union> y = z"
shows   "x \<subseteq> z"
using assms by blast

lemma subset_helper2':
assumes "x \<union> y = z"
shows   "y \<subseteq> z"
using assms by blast


lemma uval_typing_record_nth:
assumes "\<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s \<langle>r, {}\<rangle>"
and     "\<tau>s ! f = (\<tau>, False)"
and     "f < length \<tau>s"
shows "\<exists>r' \<subseteq> r. \<Xi>, \<sigma> \<turnstile> fst (fs ! f) :u \<tau> \<langle>r', {}\<rangle>"
using assms proof (induct fs arbitrary: f r \<tau>s)
     case Nil  then show ?case by force
next case Cons then show ?case
  proof (cases f)
       case 0   with Cons(2-) show ?thesis by (force elim!: u_t_r_consE)
  next case Suc with Cons(2-) show ?thesis by (elim u_t_r_consE, auto dest!: Cons(1))
  qed
qed


lemma sum_downcast_u:
assumes "\<Xi>, \<sigma> \<turnstile> USum t v xs :u TSum ts \<langle>r, w\<rangle>"
and     "t \<noteq> t'"
shows   "\<Xi>, \<sigma> \<turnstile> USum t v (filter (\<lambda> x. fst x \<noteq> t') xs) :u TSum (filter (\<lambda> x. fst x \<noteq> t') ts) \<langle>r, w\<rangle>"
proof -
have 1: "(\<lambda> x. x \<noteq> t') \<circ> fst = (\<lambda> x. fst x \<noteq> t')" by (auto)
have 2: "map fst [ x \<leftarrow> ts. fst x \<noteq> t' ] = [ x \<leftarrow> map fst ts. x \<noteq> t' ]"by (simp add: 1 filter_map)
have 3: "[x\<leftarrow>map fst xs . x \<noteq> t'] = map fst [x\<leftarrow>xs . fst x \<noteq> t']" by (induct xs,simp,simp)
have 4: "\<lbrakk> list_all2 (\<lambda>t. (=) (type_repr t)) (map snd ts) (map snd xs)
         ; map fst ts = map fst xs
         \<rbrakk> \<Longrightarrow> list_all2 (\<lambda>t. (=) (type_repr t)) 
                 (map snd [x\<leftarrow>ts . fst x \<noteq> t']) 
                 (map snd [x\<leftarrow>xs . fst x \<noteq> t'])"
by ( induct "map snd ts" "map snd xs"
     arbitrary: ts xs
     rule: list_all2_induct
   , auto)

from 1 2 assms show ?thesis apply -
  apply (erule uval_typing.cases,simp_all)
  apply (clarsimp)
  apply (rule, simp,simp,simp)
     apply (clarsimp, rule)
    apply (force intro: kinding_all_subset)
   apply (simp add: 3)
  apply (simp add: 4)
done
qed

lemma list_all2_helper2:
assumes "map fst tsa = map fst rs"
and     "list_all2 (\<lambda>t. (=) (type_repr t)) (map snd tsa) (map snd rs)"
shows   "map (\<lambda>(a,b). (a,type_repr b)) tsa = rs"
using assms(2,1) by ( induct "map snd tsa" "map snd rs"
                      arbitrary: tsa rs
                      rule: list_all2_induct
                    , auto)

lemma type_repr_uval_repr:
shows"\<Xi>, \<sigma> \<turnstile> v :u t \<langle>r, w\<rangle> \<Longrightarrow> uval_repr v = type_repr t"
and  "\<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r, w\<rangle> \<Longrightarrow> map snd fs = map (\<lambda> a. (type_repr (fst a))) ts"
by ( induct rule: uval_typing_uval_typing_record.inducts
   , auto dest: abs_typing_repr intro: list_all2_helper2 [symmetric])

lemma type_repr_uval_repr_deep:
shows"\<Xi>, \<sigma> \<turnstile> v :u t \<langle>r, w\<rangle> \<Longrightarrow> uval_repr_deep v = type_repr t"
and  "\<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r, w\<rangle> \<Longrightarrow> map uval_repr_deep (map fst fs) = map (\<lambda> a. (type_repr (fst a))) ts"
by ( induct rule: uval_typing_uval_typing_record.inducts
   , auto dest: abs_typing_repr intro: list_all2_helper2 [symmetric])


lemma uval_typing_record_take:
assumes "\<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s \<langle>r, w\<rangle>"
and     "\<tau>s ! f = (\<tau>, False)"
and     "[] \<turnstile> \<tau> wellformed"
and     "f < length \<tau>s"
shows   "\<exists>r' w' r'' w''. (\<Xi>, \<sigma> \<turnstile> fst (fs ! f) :u  \<tau>                     \<langle>r' , w' \<rangle>) 
                       \<and> (\<Xi>, \<sigma> \<turnstile>* fs          :ur (\<tau>s [f := (\<tau>, True)]) \<langle>r'', w''\<rangle>)
                       \<and> r = r' \<union> r'' 
                       \<and> w = w' \<union> w'' 
                       \<and> w' \<inter> w'' = {}"
using assms proof (induct fs arbitrary: f r w \<tau>s)
     case Nil  then show ?case by force
next case Cons then show ?case
  proof (cases f)
       case 0   with Cons(2-) show ?thesis by ( clarsimp, elim u_t_r_consE
                                              , auto intro!: exI
                                                             uval_typing_uval_typing_record.intros
                                                       elim: type_repr_uval_repr type_repr_uval_repr_deep)
  next case Suc with Cons(2-) show ?thesis
    apply (clarsimp)
    apply (erule u_t_r_consE)
     apply (clarsimp, frule(2) Cons(1) [OF _ _ assms(3)])
     apply (blast intro: uval_typing_uval_typing_record.intros)
    apply (clarsimp, frule(2) Cons(1) [OF _ _ assms(3)])
    apply (fastforce intro!: uval_typing_uval_typing_record.intros)
  done
  qed
qed

lemma uval_typing_record_put_taken:
assumes "\<Xi>, \<sigma> \<turnstile>  e' :u  t  \<langle>r'b, w'b\<rangle>"
and     "\<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r'a, w'a\<rangle>"
and     "ts ! f = (t, True)"
and     "w'b \<inter> r'a = {}"
and     "w'a \<inter> r'b = {}"
and     "w'a \<inter> w'b = {}"
and     "f < length ts"
shows   "\<Xi>, \<sigma> \<turnstile>* fs[f := (e', snd (fs ! f))] :ur (ts[f := (t, False)]) \<langle>r'a \<union> r'b, w'a \<union> w'b\<rangle>"
using assms proof (induct fs arbitrary: f r'a w'a ts)
case Nil then show ?case by auto
next case Cons then show ?case
  proof (cases f)
       case 0   with Cons(2-) show ?thesis
         apply (clarsimp)
         apply (elim u_t_r_consE, simp)
         apply (rule pointerset_helper_record, (fastforce intro!: u_t_r_cons2 u_t_r_cons1)+)
       done
  next case Suc with Cons(2-) show ?thesis
         apply (clarsimp)
         apply (elim u_t_r_consE)
          apply (frule(1) Cons(1), simp, blast,blast,blast ,simp)
          apply (clarsimp, rule pointerset_helper_record, force intro!: u_t_r_cons1, blast, blast) 
         apply (frule(1) Cons(1), simp, blast,blast,blast ,simp)
         apply (clarsimp, rule pointerset_helper_record, force intro!: u_t_r_cons2, blast, blast)
       done
  qed
qed

lemma uval_typing_record_put_discardable:
assumes "\<Xi>, \<sigma> \<turnstile>  e' :u  t  \<langle>r'b, w'b\<rangle>"
and     "\<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r'a, w'a\<rangle>"
and     "ts ! f = (t, False)"
and     "[] \<turnstile> t :\<kappa> k"
and     "D \<in> k"
and     "w'b \<inter> r'a = {}"
and     "w'a \<inter> r'b = {}"
and     "w'a \<inter> w'b = {}"
and     "f < length ts"
shows   "\<exists>r''a\<subseteq> r'a. \<Xi>, \<sigma> \<turnstile>* fs[f := (e', snd (fs ! f))] :ur (ts[f := (t, False)]) \<langle>r''a \<union> r'b, w'a \<union> w'b\<rangle>"
using assms proof (induct fs arbitrary: f r'a w'a ts)
  case Nil then show ?case by fastforce
next case Cons then show ?case
  proof (cases f)
       case 0   with Cons(2-) show ?thesis
         apply (clarsimp)
         apply (frule(2) discardable_not_writable)
         apply (elim u_t_r_consE, simp)
         apply (rotate_tac 3, frule(2) discardable_not_writable)
         apply (rule_tac x = r' in exI)
         apply (rule, blast)
         apply (rule pointerset_helper_record,(fastforce intro!:  u_t_r_cons2 u_t_r_cons1)+)
       done
  next case Suc with Cons(2-) show ?thesis
         apply (clarsimp)
         apply (elim u_t_r_consE)
          apply (frule(1) Cons(1), simp,blast,blast,blast,blast,blast, simp)
          apply (clarsimp, rule_tac x = "r \<union> r''a" in exI, rule, blast)
          apply (rule pointerset_helper_record,(force intro!:  u_t_r_cons2 u_t_r_cons1), blast,blast)
         apply (frule(1) Cons(1), simp,blast,blast,blast,blast,blast, simp)
         apply (clarsimp, rule_tac x = "r''a" in exI, rule, blast)
         apply (rule pointerset_helper_record,(fastforce intro!:  u_t_r_cons2 u_t_r_cons1)+)
    done
  qed
qed


lemma uval_typing_record_put:
assumes "\<Xi>, \<sigma> \<turnstile>  e' :u  t  \<langle>r'b, w'b\<rangle>"
and     "\<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r'a, w'a\<rangle>"
and     "ts ! f = (t, taken)"
and     "D \<in> k \<or> taken"
and     "w'b \<inter> r'a = {}"
and     "w'a \<inter> r'b = {}"
and     "w'a \<inter> w'b = {}"
and     "f < length ts"
and     "[] \<turnstile> t :\<kappa> k"
shows   "\<exists>r''a\<subseteq> r'a. \<Xi>, \<sigma> \<turnstile>* fs[f := (e', snd (fs ! f))] :ur (ts[f := (t, False)]) \<langle>r''a \<union> r'b, w'a \<union> w'b\<rangle>"
using assms proof (cases taken)
     case False with assms show ?thesis by (fastforce intro!: uval_typing_record_put_discardable)
next case True  with assms show ?thesis by (fastforce intro!: uval_typing_record_put_taken)
qed

lemma list_helper:
assumes "ls ! x = y"
shows   "ls[x := y] = ls"
using assms by auto


lemma list_all2_helper:
shows "list_all2 (\<lambda>t. (=) (type_repr t)) 
                 (map (instantiate \<tau>s \<circ> snd) list)
                 (map (snd \<circ> ((\<lambda>(n, t). (n, type_repr t)) \<circ> (\<lambda>(c, t). (c, instantiate \<tau>s t)))) list)"
by (induct list, (simp+, (case_tac a)?)+)

lemma u_t_p_rec_w':
assumes "\<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r, w\<rangle>"
and     "\<sigma> l = Some (URecord fs)"
and     "l \<notin> w \<union> r"
and     "rp = (RRecord (map (\<lambda>(a,b). type_repr a) ts)) "
shows   "\<Xi>, \<sigma> \<turnstile> UPtr l rp :u TRecord ts Writable \<langle> r, insert l w \<rangle>"
using assms by (auto intro: u_t_p_rec_w)

theorem preservation: 
assumes "list_all2 (kinding []) \<tau>s K"
and     "proc_ctx_wellformed \<Xi>"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (instantiate_ctx \<tau>s \<Gamma>) \<langle>r, w\<rangle>"
and     "\<xi> matches-u \<Xi>"
shows   "\<lbrakk> \<xi>, \<gamma> \<turnstile>  (\<sigma>, specialise \<tau>s e) \<Down>! (\<sigma>', v)
         ; \<Xi>, K, \<Gamma> \<turnstile> e : \<tau> 
         \<rbrakk> \<Longrightarrow> \<exists>r' w'. (\<Xi> , \<sigma>' \<turnstile> v :u instantiate \<tau>s \<tau> \<langle>r', w'\<rangle>) 
                     \<and> r' \<subseteq> r 
                     \<and> frame \<sigma> w \<sigma>' w'"
and     "\<lbrakk> \<xi>, \<gamma> \<turnstile>* (\<sigma>, map (specialise \<tau>s) es) \<Down>! (\<sigma>', vs)
         ; \<Xi>, K, \<Gamma> \<turnstile>* es : \<tau>s'
         \<rbrakk> \<Longrightarrow> \<exists>r' w'. (\<Xi>, \<sigma>' \<turnstile>* vs :u map (instantiate \<tau>s) \<tau>s' \<langle>r', w'\<rangle>)
                     \<and> r' \<subseteq> r
                     \<and> frame \<sigma> w \<sigma>' w'"
using assms proof (induct "(\<sigma>, specialise \<tau>s e)"        "(\<sigma>', v )" 
                      and "(\<sigma>, map (specialise \<tau>s) es)" "(\<sigma>', vs)" 
                      arbitrary:  e  \<tau>s K \<tau>   \<Gamma> r w v  \<sigma>' \<sigma>
                             and  es \<tau>s K \<tau>s' \<Gamma> r w vs \<sigma>' \<sigma>
                      rule: u_sem_u_sem_all.inducts) 
     case u_sem_var       then show ?case by ( cases e, simp_all
                                             , fastforce elim!:  typing_varE
                                                         dest!:  matches_ptrs_proj
                                                         intro:  frame_id)
next case u_sem_prim      then show ?case by ( cases e, simp_all
                                             , auto      elim!:  typing_primE
                                                         dest!:  u_sem_prim(2)
                                                         intro!: exI map_tprim_no_pointers' 
                                                         intro:  eval_prim_u_preservation
                                                         dest:   map_tprim_no_pointers)
next case u_sem_lit       then show ?case by ( cases e, simp_all
                                             , fastforce dest:   matches_ptrs_proj_consumed
                                                         intro!: uval_typing_uval_typing_record.intros
                                                                 frame_id)
next case u_sem_afun      then show ?case by ( cases e, simp_all
                                             , fastforce intro: u_t_afun_instantiate
                                                                frame_id
                                                         dest:  matches_ptrs_proj_consumed)
next case u_sem_fun       then show ?case by ( cases e, simp_all
                                             , fastforce intro: u_t_function_instantiate
                                                                frame_id
                                                         dest:  matches_ptrs_proj_consumed)
next case u_sem_promote   then show ?case by ( cases e, simp_all
                                             , fastforce elim:   u_t_sumE typing_promE
                                                         intro!: u_t_sum
                                                         dest:   u_sem_promote(2)
                                                         intro:  substitutivity(2)
                                                                  [ where ts = "map snd ls" for ls
                                                                  , simplified]
                                                         simp:   list_all2_helper)
next case u_sem_app
  note IH1  = this(2)
  and  IH2  = this(4)
  and  IH3  = this(6)
  and  rest = this(1,3,5,7-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (clarsimp elim!: typing_appE)
    apply (frule matches_ptrs_noalias)
    apply (frule(2) matches_ptrs_split, clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (frule(7) IH2 [OF _ _ _ _ matches_ptrs_frame, rotated -1])
     apply (fastforce intro!: subset_helper dest: subset_helper2 subset_helper2')
    apply (clarsimp elim!: u_t_functionE)
    apply (frule(3) IH3 [OF refl, rotated -1])
     apply (force intro!: matches_ptrs.intros simp: instantiate_ctx_def)
    apply (clarsimp, auto intro!: exI
                          intro:  frame_trans subset_helper2'
                          dest:   frame_app [where w' = "{}", simplified])
  done
next case u_sem_abs_app
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (clarsimp elim!: typing_appE)
    apply (frule matches_ptrs_noalias)
    apply (frule(2) matches_ptrs_split, clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (frule(7) IH2 [OF _ _ _ _ matches_ptrs_frame, rotated -1])
     apply (fastforce intro!: subset_helper dest: subset_helper2 subset_helper2')
    apply (clarsimp elim!: u_t_afunE)
    apply (frule(4) proc_env_matches_ptrs_abstract)
    apply (clarsimp, auto intro!: exI
                          intro:  frame_trans subset_helper2'
                          dest:   frame_app [where w' = "{}", simplified])
  done

next case u_sem_con
  note IH   = this(2)
  and  rest = this(1,3-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (clarsimp elim!: typing_conE)
    apply (frule(5) IH,clarsimp)
    apply (auto dest: imageI [where f = "\<lambda>(c, t). (c, instantiate \<tau>s t)"]
                simp: list_all2_helper
                intro!: exI
                        uval_typing_uval_typing_record.intros
                        substitutivity(2) [where ts = "map snd ls" for ls, simplified])
  done

next case u_sem_let
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (clarsimp elim!: typing_letE)
    apply (frule matches_ptrs_noalias)
    apply (frule(2) matches_ptrs_split, clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (frule(4) IH2 [rotated -1], clarsimp)
    apply (rule, force)
        apply (force intro: matches_ptrs_frame)
       apply (force dest: frame_noalias_matches_ptrs(1))
      apply (force dest!: frame_noalias_matches_ptrs(2))
     apply (blast)
    apply (fastforce intro: frame_let simp: Un_commute)
  done

next case u_sem_letbang
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (clarsimp elim!: typing_letbE)
    apply (frule matches_ptrs_noalias)
    apply (frule(2) matches_ptrs_split_bang, clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (frule(3) escapable_no_readers(1) [OF _ _ substitutivity(1)], clarsimp)
    apply (frule(4) IH2 [rotated -1], clarsimp)
     apply (rule, force)
        apply (force intro: matches_ptrs_frame)
       apply (rule frame_noalias_matches_ptrs(1), simp+, blast)
      apply (rule frame_noalias_matches_ptrs(2), simp+, blast)
     apply (simp)
    apply (clarsimp)
    apply (auto intro!: exI
                simp:   Un_assoc
                intro:  frame_let
                intro:  pointerset_helper_frame [OF _ _ refl])
  done
next case u_sem_unit      then show ?case by ( cases e, simp_all
                                             , auto elim!:  typing_unitE
                                                    intro!: exI
                                                    dest!:  matches_ptrs_proj_consumed
                                                    intro:  frame_id
                                                            uval_typing_uval_typing_record.intros)
next case u_sem_cast      then show ?case by ( cases e, simp_all
                                             , fastforce elim:   upcast_valid_cast_to
                                                         intro!: u_t_prim')
next case u_sem_tuple
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (clarsimp elim!: typing_tupleE)
    apply (frule matches_ptrs_noalias)
    apply (frule(2) matches_ptrs_split, clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (frule(2) matches_ptrs_frame, blast)
    apply (frule(5) IH2, clarsimp)
    apply (frule(1) frame_app)

    apply (frule(2) frame_noalias_matches_ptrs(2) [where u = "w \<union> w'" for w and w'])
    apply (frule(4) uval_typing_frame [rotated -1, OF _ _ frame_noalias_matches_ptrs(1)], blast)
    apply (frule(4) frame_noalias_2)
    apply (blast intro!: uval_typing_uval_typing_record.intros)
  done
next case u_sem_esac      then show ?case by ( cases e, simp_all
                                             , fastforce elim!: u_t_sumE)
next case u_sem_case_nm
  note IH1 = this(2)
  and  IH2 = this(5)
  and rest = this(1,3-4,6-)
  have HELP:
  "\<forall> ts t. ([x\<leftarrow>map (\<lambda>(c, t). (c, instantiate \<tau>s t)) ts . fst x \<noteq> t]
         = (map (\<lambda>(c, t). (c, instantiate \<tau>s t)) [x\<leftarrow>ts . fst x \<noteq> t]))"
    by (clarsimp, induct_tac ts, auto  split: prod.split)
  from rest show ?case
    apply (cases e, simp_all)
    apply (erule typing_caseE)
    apply (frule matches_ptrs_noalias)
    apply (frule(2) matches_ptrs_split, clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (frule(2) matches_ptrs_frame, blast)
    apply (frule(1) sum_downcast_u [rotated -1])
    apply (frule(4) IH2 [rotated -1])
     apply (simp, rule, simp add: HELP[rule_format], blast,blast,blast,blast)
    apply (clarsimp, auto intro!: exI intro: frame_let simp: Un_commute)
  done
next case u_sem_case_m
  note IH1 = this(2)
  and  IH2 = this(4)
  and rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (erule typing_caseE)
    apply (frule matches_ptrs_noalias)
    apply (frule(2) matches_ptrs_split, clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (frule(2) matches_ptrs_frame, blast)
    apply (erule u_t_sumE, clarsimp)
     apply (drule(1) distinct_fst [rotated 1],simp,simp)
    apply (frule(4) IH2 [rotated -1])
     apply (force intro!: matches_ptrs_some)
    apply (clarsimp, force intro!: exI simp: Un_commute intro: frame_let)
  done
next case (u_sem_if _ _ _ _ _ b)
  note IH1 = this(2)
  and  IH2 = this(4)
  and rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (frule matches_ptrs_noalias)
    apply (erule typing_ifE)
    apply (frule(2) matches_ptrs_split, clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (erule u_t_primE, clarsimp)
    apply (frule(4) IH2 [ rotated 2
                        , where e17 (* FIXME: unstable name *) = "if b then e2 else e3" for e2 and e3
                        , OF _ _ matches_ptrs_frame ])
        apply (blast, simp, cases b, simp, simp, cases b, simp, simp)
    apply (fastforce intro: frame_let)
  done
next case u_sem_struct    then show ?case by ( cases e, simp_all
                                             , fastforce intro!: uval_typing_uval_typing_record.intros
                                                         intro:  uval_typing_all_record
                                                                 [where ts = "map (instantiate \<tau>s) ts"
                                                                    for ts, simplified])
next case u_sem_member
 then show ?case
   apply ( cases e
         , simp_all )
   apply ( clarsimp elim!: typing_memberE)
   apply ( frule(5) u_sem_member(2)
         , clarsimp )
   apply ( frule(1) shareable_not_writable
         , fastforce elim!:  kind_trecE
                     intro!: kind_trec
                             substitutivity
         , clarsimp elim!: u_t_recE)
   apply ( auto dest!: uval_typing_record_nth
         , fastforce )
 done
next case u_sem_memb_b
 then show ?case
   apply ( cases e
         , simp_all )
   apply ( clarsimp elim!: typing_memberE)
   apply ( frule(5) u_sem_memb_b(2)
         , clarsimp )
   apply ( frule(1) shareable_not_writable
         , fastforce elim!:  kind_trecE
                     intro!: kind_trec
                             substitutivity
         , clarsimp)
   apply ( erule u_t_p_recE)
   apply ( auto dest!: uval_typing_record_nth
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
    apply (frule matches_ptrs_noalias)
    apply (frule(2) matches_ptrs_split,clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (erule u_t_p_recE, simp_all)
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (frule uval_typing_record_take [ where \<tau>s = "map (\<lambda>(t, y). (instantiate \<tau>s t, y)) ts" for ts
                                         , simplified
                                         , OF _ HELP [rule_format]],
           force, force intro: substitutivity, force)
    apply (elim exE conjE)
    apply (frule(2) matches_ptrs_frame, blast)
    apply (simp, erule disjE)
     apply (clarsimp)
     apply (frule(3) shareable_not_writable(1) [OF _ _ substitutivity(1)], clarsimp)
     apply (frule(4) IH2 [rotated -1], simp)
      apply (case_tac taken)
       apply (rule matches_ptrs_some [OF _ matches_ptrs_some])
               apply (simp)
              apply (force intro!: u_t_p_rec_w' simp: HELP2 map_update intro: list_helper [symmetric])
             apply (simp)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (clarsimp)
      apply (rule pointerset_helper_matches_ptrs)
        apply (rule matches_ptrs_some [OF _ matches_ptrs_some])
                apply (simp)
               apply (force intro!: u_t_p_rec_w' simp: list_helper HELP2 map_update intro: list_helper [symmetric])
              apply (simp)
             apply (blast)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (blast)
     apply (clarsimp, intro exI conjI, simp, blast, force simp: Un_commute intro: frame_let)
    apply (clarsimp)
    apply (frule(4) IH2 [rotated -1], simp)
     apply (rule matches_ptrs_some [OF _ matches_ptrs_some])
             apply (simp)
            apply (force intro!: u_t_p_rec_w' simp: list_helper HELP2 map_update intro: list_helper [symmetric])
           apply (simp)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (blast)
     apply (blast)
    apply (clarsimp, auto intro!: exI intro: frame_let pointerset_helper_frame)
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
    apply (frule matches_ptrs_noalias)
    apply (frule(2) matches_ptrs_split,clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (erule u_t_recE, simp_all)
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (clarsimp)
    apply (frule uval_typing_record_take [ where \<tau>s = "map (\<lambda>(t, y). (instantiate \<tau>s t, y)) ts" for ts
                                         , simplified
                                         , OF _ HELP [rule_format]], force, force intro: substitutivity, force)
    apply (elim exE conjE)
    apply (frule(2) matches_ptrs_frame, blast)
    apply (simp, erule disjE)
     apply (clarsimp)
     apply (frule(3) shareable_not_writable(1) [OF _ _ substitutivity(1)], clarsimp)
     apply (frule(4) IH2 [rotated -1], simp)
      apply (case_tac taken)
       apply (rule matches_ptrs_some [OF _ matches_ptrs_some])
               apply (simp)
              apply (force intro!: u_t_struct simp: map_update)
             apply (simp)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (clarsimp)
      apply (rule pointerset_helper_matches_ptrs)
        apply (rule matches_ptrs_some [OF _ matches_ptrs_some])
                apply (simp)
               apply (force intro!: u_t_struct simp: list_helper)
              apply (simp)
             apply (blast)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (blast)
     apply (clarsimp, intro exI conjI, simp, blast, force simp: Un_commute intro: frame_let)
    apply (clarsimp)
    apply (frule(4) IH2 [rotated -1], simp)
     apply (rule matches_ptrs_some [OF _ matches_ptrs_some])
             apply (simp)
            apply (fastforce intro!: u_t_struct simp: map_update)
           apply (simp)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (blast)
     apply (blast)
    apply (clarsimp, auto intro!: exI intro: frame_let pointerset_helper_frame)
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
  have HELP2: "\<forall> \<tau>s. (type_repr \<circ> fst \<circ> (\<lambda>(t, y). (instantiate \<tau>s t, y)))
                   = (\<lambda>(t,y). type_repr (instantiate \<tau>s t))"
  by (force split: prod.split)
  from rest show ?case
    apply (cases e, simp_all)
    apply (erule typing_putE)
    apply (frule matches_ptrs_noalias)
    apply (clarsimp)
    apply (frule(2) matches_ptrs_split,clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (frule(2) matches_ptrs_frame,blast )
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (frule(5) IH2, clarsimp)
    apply (frule(1) frame_noalias_uval_typing, blast)
    apply (frule(1) frame_noalias_uval_typing(2), blast)
    apply (erule u_t_p_recE, simp,clarsimp)
    apply (drule(1) frame_app)
    apply (drule(2) uval_typing_frame(2) [rotated -1], blast)
    apply (drule(1) uval_typing_frame(1) [OF frame_single_update, simplified, rotated -1], blast)
    apply (drule(2) uval_typing_frame(2) [OF frame_single_update, simplified, rotated -1])

    apply (frule(5) uval_typing_record_put [ where ts = "map (\<lambda>(t, y). (instantiate \<tau>s t, y)) ts" for ts
                                           , OF _ _ HELP [rule_format]
                                           , simplified
                                           ])
        apply (fast)
       apply (fast)
      apply (fast)
     apply (fastforce intro: substitutivity)
    apply (clarsimp, intro conjI exI, rule u_t_p_rec_w')
    apply (simp add: map_update)
    apply (auto intro!: list_helper[symmetric] simp: HELP2 map_update frame_def)
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
    apply (frule matches_ptrs_noalias)
    apply (clarsimp)
    apply (frule(2) matches_ptrs_split,clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (frule(2) matches_ptrs_frame,blast )
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (frule(5) IH2, clarsimp)
    apply (frule(1) frame_noalias_uval_typing, blast)
    apply (frule(1) frame_noalias_uval_typing(2), blast)
    apply (erule u_t_recE, simp,clarsimp)
    apply (drule(1) frame_app)
    apply (drule(2) uval_typing_frame(2) [rotated -1], blast)

    apply (frule(5) uval_typing_record_put [ where ts = "map (\<lambda>(t, y). (instantiate \<tau>s t, y)) ts" for ts
                                           , OF _ _ HELP [rule_format]
                                           , simplified
                                           ])
        apply (fast)
       apply (fast)
      apply (fast)
     apply (fastforce intro: substitutivity)
    apply (clarsimp, auto intro!: exI u_t_struct simp: map_update frame_def) 
  done
next case u_sem_split
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (cases e, simp_all)
    apply (erule typing_splitE)
    apply (frule matches_ptrs_noalias)
    apply (frule(2) matches_ptrs_split,clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (erule u_t_productE)
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (frule(3) IH2)
      apply (simp)
      apply (rule matches_ptrs_some, simp, rule matches_ptrs_some, simp)
            apply (rule matches_ptrs_frame, simp, simp)
             apply (blast)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (blast)
     apply (blast)
    apply (clarsimp, auto intro!: exI intro: frame_let pointerset_helper_frame)
  done

next case u_sem_all_empty then show ?case by ( cases es, simp_all
                                             , fastforce intro!: frame_id
                                                                 uval_typing_all.intros
                                                         dest: matches_ptrs_empty_env(2))
next case u_sem_all_cons
  note IH1  = this(2)
  and  IH2  = this(4)
  and  rest = this(1,3,5-)
  from rest show ?case
    apply (cases es, simp_all)
    apply (erule typing_all_consE, clarsimp)
    apply (frule(2) matches_ptrs_split, clarsimp)
    apply (frule(5) IH1, clarsimp)
    apply (frule matches_ptrs_noalias)
    apply (frule(7) IH2 [OF _ _ _ _ matches_ptrs_frame, rotated -1], blast, clarsimp)
    apply (frule(1) frame_app)
    apply (frule(2) frame_noalias_matches_ptrs(2) [where u = "w \<union> w'" for w and w'])
    apply (frule(4) uval_typing_frame [rotated -1, OF _ _ frame_noalias_matches_ptrs(1)], blast)
    apply (frule(4) frame_noalias_2)
    apply (blast intro!: uval_typing_all.intros)
  done

qed
inductive_cases u_t_productE': "\<Xi>, \<sigma> \<turnstile> UProduct a b :u t \<langle>r,w\<rangle>"
inductive_cases u_t_sumE': "\<Xi>, \<sigma> \<turnstile> USum c p ts :u t \<langle>r,w\<rangle>"
inductive_cases u_t_absE: "\<Xi>, \<sigma> \<turnstile> UAbstract v :u t \<langle>r,w\<rangle>"
inductive_cases u_t_funE': "\<Xi>, \<sigma> \<turnstile> UFunction f ts :u t \<langle>r,w\<rangle>"
inductive_cases u_t_ptrE: "\<Xi>, \<sigma> \<turnstile> UPtr p rp :u t \<langle>r,w\<rangle>"

lemma type_repr_heap:
shows "\<lbrakk> \<Xi>, \<sigma> \<turnstile>  v  :u  t  \<langle>r, w\<rangle>; \<Xi>, \<sigma> \<turnstile>  v  :u  t'  \<langle>r', w'\<rangle> \<rbrakk> \<Longrightarrow> type_repr t = type_repr t'"
and   "\<lbrakk> \<Xi>, \<sigma> \<turnstile>* fs :ur ts \<langle>r, w\<rangle>
       ; \<Xi>, \<sigma> \<turnstile>* fs :ur ts' \<langle>r', w'\<rangle> 
       \<rbrakk> \<Longrightarrow> (map (\<lambda>a. (type_repr (fst a))) ts) = (map (\<lambda> a. type_repr (fst a)) ts') "
by (auto dest!: type_repr_uval_repr)


lemmas preservation_mono = preservation [where \<tau>s = "[]", simplified, OF refl, simplified]


(* Lemma bucket. *)
lemma matches_ptrs_some_some:
  "\<lbrakk>\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r'', w''\<rangle>;
   \<Xi>, \<sigma> \<turnstile> a :u ta \<langle>ra, wa\<rangle>;
   \<Xi>, \<sigma> \<turnstile> b :u tb \<langle>rb, wb\<rangle>;
    wb \<inter> w'' = {}; 
    wb \<inter> r'' = {}; 
    w'' \<inter> rb = {}; 
     wa \<inter> (wb \<union> w'') = {}; 
     wa \<inter> (rb \<union> r'') = {}; 
     (wb \<union> w'') \<inter> ra = {}\<rbrakk> \<Longrightarrow> 
  \<Xi>, \<sigma> \<turnstile> 
    (a # b # \<gamma>) matches 
    (Some ta # Some tb # \<Gamma>) 
    \<langle>ra \<union> (rb \<union> r''), wa \<union> (wb \<union> w'')\<rangle>"
  by (fastforce intro!: matches_ptrs_some)

lemma uval_typing_taken_field':
  assumes "\<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s \<langle>r, w\<rangle>"
  assumes "f < length \<tau>s"
  assumes "\<tau>s!f = (t, False)"
  assumes "[] \<turnstile>  t :\<kappa>  k"
  shows "\<exists>r'. \<exists>w'. \<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s[f := (t, taken)] \<langle>r', w'\<rangle> \<and> r' \<subseteq> r \<and> w'\<subseteq> w"
  proof (cases taken)
   case False show ?thesis 
   by (rule_tac x="r" in exI,rule_tac x="w" in exI, simp)
      (metis(full_types) False list_update_id assms(1,3))
  next
   case True thus ?thesis using assms
   proof (induct fs arbitrary: f r w \<tau>s)
    case Cons then show ?case
    proof (cases f)
     case 0  with Cons(2-) show ?thesis by (fastforce elim!: u_t_r_consE type_repr_uval_repr type_repr_uval_repr_deep intro: u_t_r_cons2)  
    next 
     case Suc with Cons(2-) show ?thesis 
     apply (elim u_t_r_consE)
      apply clarsimp
      apply (frule(4) Cons(1), simp)
      apply (blast intro!: u_t_r_cons1)
     apply clarsimp
     apply (frule(4) Cons(1), simp)
     by (fastforce intro!: u_t_r_cons2)
   qed
  qed fastforce
qed
 
lemma uval_typing_taken_field:
  assumes "\<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s \<langle>r, w\<rangle>"
  assumes "f < length \<tau>s"
  assumes "\<tau>s!f = (t, False)"
  assumes "[] \<turnstile>  t :\<kappa>  k"
  shows "\<exists>r' \<subseteq> r. \<exists>w'\<subseteq> w. \<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s[f := (t, taken)] \<langle>r', w'\<rangle>"
  by (meson uval_typing_taken_field'[OF assms])

lemma uval_typing_record_nth':
  assumes "\<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s \<langle>r , w\<rangle>"
  assumes "\<tau>s ! f = (\<tau>, False)"
  assumes "f < length \<tau>s" 
  shows "\<exists> r'\<subseteq>r. \<exists>w'\<subseteq>w. \<Xi>, \<sigma> \<turnstile>  fst (fs!f)  :u  \<tau>  \<langle>r' , w'\<rangle>"
using assms proof (induct fs arbitrary: f r w \<tau>s)
     case Nil  then show ?case by force
next case Cons then show ?case
  proof (cases f)
       case 0   with Cons(2-) show ?thesis  by (fastforce elim!: u_t_r_consE)
  next case Suc with Cons(2-) show ?thesis 
    apply (elim u_t_r_consE)
     apply (drule Cons(1), simp, simp, clarsimp) 
     apply (rename_tac r'' w'')
      apply (rule_tac x=r'' in exI)
      apply (rule conjI) 
       apply blast
      apply (rule_tac x=w'' in exI)
      apply blast 
    by (drule Cons(1), auto) 
  qed
qed

end

end

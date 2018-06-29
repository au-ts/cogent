(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Cogent
imports Util
begin


section {* Utility lemmas, probably should be in a separate theory *}

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

lemma map_fst_update:
assumes "ts ! f = (t, x)"
and     "f < length ts"
shows "map fst (ts[f := (t,x')]) = map fst ts"
proof -
from assms have  "map fst ts ! f = t" by (clarsimp)
then show ?thesis by (auto simp add: map_update)
qed

lemma map_zip [simp]:
shows "map (\<lambda> (a , b). (f a, g b)) (zip as bs) = zip (map f as) (map g bs)"
by (induct as arbitrary:bs, simp, case_tac bs, simp_all)

lemma distinct_fst:
assumes "distinct (map fst ls)"
and     "(a, b) \<in> set ls"
and     "(a, b') \<in> set ls"
shows   "b = b'"
using assms
  apply (clarsimp simp: set_conv_nth distinct_conv_nth)
  apply (drule_tac x = i in spec, simp)
  apply (drule_tac x = ia in spec, simp)
  apply (case_tac "ls ! i")
  apply (case_tac "ls ! ia")
  apply (auto)
done

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
shows "filter (\<lambda>x. P (fst x)) (map (\<lambda>(a,b,c). (a, f (b,c))) ls)
     = map (\<lambda>(a,b,c). (a, f (b,c))) (filter (\<lambda>x. P (fst x)) ls)"
by (induct_tac ls, auto)

lemma filter_map_map_filter_thd3_app2:
  shows "filter (P \<circ> snd \<circ> snd) (map (\<lambda>(a, b, c). (a, f b, c)) ls) = map (\<lambda>(a, b, c). (a, f b, c)) (filter (P \<circ> snd \<circ> snd) ls)"
  by (induct_tac ls, (simp split: prod.splits)+)

lemma filtered_member: "[a] = filter f x \<Longrightarrow> a \<in> set x"
  apply (induction x)
  by (auto split: if_splits)

section {* Terms and Types of Cogent *}

type_synonym name = string

type_synonym index = nat

type_synonym field = nat

datatype num_type = U8 | U16 | U32 | U64 

datatype prim_type = Num num_type | Bool | String

datatype sigil = ReadOnly | Writable | Unboxed


datatype prim_op 
  = Plus num_type 
  | Minus num_type 
  | Times num_type 
  | Divide num_type 
  | Mod num_type
  | Not | And | Or
  | Gt num_type
  | Lt num_type 
  | Le num_type 
  | Ge num_type 
  | Eq prim_type 
  | NEq prim_type
  | BitAnd num_type 
  | BitOr num_type 
  | BitXor num_type 
  | LShift num_type
  | RShift num_type
  | Complement num_type


datatype type = TVar index
              | TVarBang index
              | TCon name "type list" sigil
              | TFun type type 
              | TPrim prim_type
              | TSum "(name \<times> (type \<times> bool)) list"
              | TProduct type type
              | TRecord "(type \<times> bool) list" sigil
              | TUnit

datatype lit = LBool bool
             | LU8 "8 word"
             | LU16 "16 word"
             | LU32 "32 word"
             | LU64 "64 word"
             (* etc *)

fun cast_to :: "num_type \<Rightarrow> lit \<Rightarrow> lit option" where
  "cast_to U8  (LU8  x) = Some (LU8 x)"
| "cast_to U16 (LU8  x) = Some (LU16 (ucast x))"
| "cast_to U16 (LU16 x) = Some (LU16 x)"
| "cast_to U32 (LU8  x) = Some (LU32 (ucast x))"
| "cast_to U32 (LU16 x) = Some (LU32 (ucast x))"
| "cast_to U32 (LU32 x) = Some (LU32 x)"
| "cast_to U64 (LU8  x) = Some (LU64 (ucast x))"
| "cast_to U64 (LU16 x) = Some (LU64 (ucast x))"
| "cast_to U64 (LU32 x) = Some (LU64 (ucast x))"
| "cast_to U64 (LU64 x) = Some (LU64 x)"

datatype 'f expr = Var index
                 | AFun 'f  "type list"
                 | Fun "'f expr" "type list"
                 | Prim prim_op "'f expr list"
                 | App "'f expr" "'f expr"
                 | Con "(name \<times> type) list" name "'f expr" (* promotes "inlined" *)
                 | Promote "(name \<times> (type \<times> bool)) list" "'f expr"
                 | Struct "type list" "'f expr list"
                 | Member "'f expr" field 
                 | Unit
                 | Lit lit
                 | Cast num_type "'f expr"
                 | Tuple "'f expr" "'f expr"
                 | Put "'f expr" field "'f expr"
                 | Let "'f expr" "'f expr"
                 | LetBang "index set" "'f expr" "'f expr"
                 | Case "'f expr" name "'f expr" "'f expr"
                 | Esac "'f expr"
                 | If "'f expr" "'f expr" "'f expr"
                 | Take "'f expr" field "'f expr"
                 | Split "'f expr" "'f expr"

datatype kind_comp = D | S | E

type_synonym kind = "kind_comp set"

type_synonym poly_type = "kind list \<times> type \<times> type"

type_synonym 'v env  = "'v list"

type_synonym 'a substitution = "'a list"

section {* Kinding rules *}

primrec sigil_kind :: "sigil \<Rightarrow> kind" where 
  "sigil_kind ReadOnly  = {D,S}"
| "sigil_kind Writable  = {E}"
| "sigil_kind Unboxed   = {D,S,E}"



inductive kinding        :: "kind env \<Rightarrow> type               \<Rightarrow> kind \<Rightarrow> bool" ("_ \<turnstile>  _ :\<kappa>  _" [30,0,20] 60) 
      and kinding_all    :: "kind env \<Rightarrow> type list          \<Rightarrow> kind \<Rightarrow> bool" ("_ \<turnstile>* _ :\<kappa>  _" [30,0,20] 60) 
      and kinding_record :: "kind env \<Rightarrow> (type \<times> bool) list \<Rightarrow> kind \<Rightarrow> bool" ("_ \<turnstile>* _ :\<kappa>r _" [30,0,20] 60) where

   kind_tvar    : "\<lbrakk> k \<subseteq> (K ! i) ; i < length K \<rbrakk> \<Longrightarrow> K \<turnstile> TVar i :\<kappa> k"
|  kind_tvarb   : "\<lbrakk> k \<subseteq> {D, S} ; i < length K \<rbrakk> \<Longrightarrow> K \<turnstile> TVarBang i :\<kappa> k"
|  kind_tcon    : "\<lbrakk> K \<turnstile>* ts :\<kappa> k ; k \<subseteq> sigil_kind s \<rbrakk> \<Longrightarrow> K \<turnstile> TCon n ts s :\<kappa> k"
|  kind_tfun    : "\<lbrakk> K \<turnstile> a :\<kappa> ka ; K \<turnstile> b :\<kappa> kb \<rbrakk> \<Longrightarrow> K \<turnstile> TFun a b :\<kappa> k"
|  kind_tprim   : "K \<turnstile> TPrim p :\<kappa> k"
|  kind_tsum    : "\<lbrakk> distinct (map fst ts); K \<turnstile>* map (fst \<circ> snd) ts :\<kappa> k \<rbrakk> \<Longrightarrow> K \<turnstile> TSum ts :\<kappa> k"
|  kind_tprod   : "\<lbrakk> K \<turnstile> t :\<kappa> k; K \<turnstile> u :\<kappa> k \<rbrakk>  \<Longrightarrow> K \<turnstile> TProduct t u :\<kappa> k"
|  kind_trec    : "\<lbrakk> K \<turnstile>* ts :\<kappa>r k ; k \<subseteq> sigil_kind s \<rbrakk> \<Longrightarrow> K \<turnstile> TRecord ts s :\<kappa> k"
|  kind_tunit   : "K \<turnstile> TUnit :\<kappa> k"

|  kind_all_empty : "K \<turnstile>* [] :\<kappa> k"
|  kind_all_cons  : "\<lbrakk> K \<turnstile> x :\<kappa> k ; K \<turnstile>* xs :\<kappa> k \<rbrakk> \<Longrightarrow> K \<turnstile>* (x # xs) :\<kappa> k"

|  kind_record_empty : "K \<turnstile>* [] :\<kappa>r k"
|  kind_record_cons1 : "\<lbrakk> K \<turnstile> x :\<kappa> k  ; K \<turnstile>* xs :\<kappa>r k \<rbrakk> \<Longrightarrow> K \<turnstile>* ((x,False) # xs) :\<kappa>r k"
|  kind_record_cons2 : "\<lbrakk> K \<turnstile> x :\<kappa> k' ; K \<turnstile>* xs :\<kappa>r k \<rbrakk> \<Longrightarrow> K \<turnstile>* ((x,True)  # xs) :\<kappa>r k"

inductive_cases kind_tvarE         [elim] : "K \<turnstile> TVar i :\<kappa> k"
inductive_cases kind_tvarbE        [elim] : "K \<turnstile> TVarBang i :\<kappa> k"
inductive_cases kind_tconE         [elim] : "K \<turnstile> TCon n ts s :\<kappa> k"
inductive_cases kind_tfunE         [elim] : "K \<turnstile> TFun a b :\<kappa> k"
inductive_cases kind_tsumE         [elim] : "K \<turnstile> TSum ts :\<kappa> k"
inductive_cases kind_tprodE        [elim] : "K \<turnstile> TProduct t u :\<kappa> k"
inductive_cases kind_trecE         [elim] : "K \<turnstile> TRecord ts s :\<kappa> k"
inductive_cases kind_all_emptyE    [elim] : "K \<turnstile>* [] :\<kappa> k"
inductive_cases kind_all_consE     [elim] : "K \<turnstile>* (x # xs) :\<kappa> k"
inductive_cases kind_record_emptyE [elim] : "K \<turnstile>* [] :\<kappa>r k"
inductive_cases kind_record_consE  [elim] : "K \<turnstile>* (x # xs) :\<kappa>r k"
inductive_cases kind_record_cons1E [elim] : "K \<turnstile>* ((x,False) # xs) :\<kappa>r k"
inductive_cases kind_record_cons2E [elim] : "K \<turnstile>* ((x,True)  # xs) :\<kappa>r k"


definition type_wellformed :: "kind env \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ wellformed" [30,20] 60) where
  "K \<turnstile> \<tau> wellformed \<equiv> \<exists>k. K \<turnstile> \<tau> :\<kappa> k"  

declare type_wellformed_def [simp]


definition type_wellformed_all :: "kind env \<Rightarrow> type list \<Rightarrow> bool" ("_ \<turnstile>* _ wellformed"[30,20]60) where
  "K \<turnstile>* \<tau>s wellformed \<equiv> \<exists>k. K \<turnstile>* \<tau>s :\<kappa> k"  

declare type_wellformed_all_def [simp]

definition proc_ctx_wellformed :: "('f \<Rightarrow> poly_type) \<Rightarrow> bool" where
  "proc_ctx_wellformed \<Xi> = (\<forall> f. let (K, \<tau>i, \<tau>o) = \<Xi> f in K \<turnstile> TFun \<tau>i \<tau>o wellformed )"

section {* Observation and type instantiation *}

primrec bang_sigil :: "sigil \<Rightarrow> sigil" where 
  "bang_sigil (ReadOnly)   = ReadOnly"
| "bang_sigil (Writable)   = ReadOnly"
| "bang_sigil (Unboxed)    = Unboxed"

fun bang :: "type \<Rightarrow> type" where 
  "bang (TVar i)       = TVarBang i"
| "bang (TVarBang i)   = TVarBang i"
| "bang (TCon n ts s)  = TCon n (map bang ts) (bang_sigil s)"
| "bang (TFun a b)     = TFun a b"
| "bang (TPrim p)      = TPrim p"
| "bang (TSum ps)      = TSum (map (\<lambda> (c, (t, b)). (c, (bang t, b))) ps)"
| "bang (TProduct t u) = TProduct (bang t) (bang u)"
| "bang (TRecord ts s) = TRecord (map (\<lambda> (t, b). (bang t, b)) ts) (bang_sigil s)"
| "bang (TUnit)        = TUnit"

fun instantiate :: "type substitution \<Rightarrow> type \<Rightarrow> type" where 
  "instantiate \<delta> (TVar i)       = (if i < length \<delta> then \<delta> ! i else TVar i)"
| "instantiate \<delta> (TVarBang i)   = (if i < length \<delta> then bang (\<delta> ! i) else TVarBang i)"
| "instantiate \<delta> (TCon n ts s)  = TCon n (map (instantiate \<delta>) ts) s"
| "instantiate \<delta> (TFun a b)     = TFun (instantiate \<delta> a) (instantiate \<delta> b)"
| "instantiate \<delta> (TPrim p)      = TPrim p"
| "instantiate \<delta> (TSum ps)      = TSum (map (\<lambda> (c, t, b). (c, instantiate \<delta> t, b)) ps)"
| "instantiate \<delta> (TProduct t u) = TProduct (instantiate \<delta> t) (instantiate \<delta> u)"
| "instantiate \<delta> (TRecord ts s) = TRecord (map (\<lambda> (t, b). (instantiate \<delta> t, b)) ts) s"
| "instantiate \<delta> (TUnit)        = TUnit"

fun specialise :: "type substitution \<Rightarrow> 'f expr \<Rightarrow> 'f expr" where 
  "specialise \<delta> (Var i)           = Var i"
| "specialise \<delta> (Fun f ts)        = Fun f (map (instantiate \<delta>) ts)"
| "specialise \<delta> (AFun f ts)       = AFun f (map (instantiate \<delta>) ts)"
| "specialise \<delta> (Prim p es)       = Prim p (map (specialise \<delta>) es)"
| "specialise \<delta> (App a b)         = App (specialise \<delta> a) (specialise \<delta> b)"
| "specialise \<delta> (Con as t e)      = Con (map (\<lambda> (c,t). (c, instantiate \<delta> t)) as) t (specialise \<delta> e)" 
| "specialise \<delta> (Promote as e)    = Promote (map (\<lambda> (c,(t,b)). (c, (instantiate \<delta> t, b))) as) (specialise \<delta> e)"
| "specialise \<delta> (Struct ts vs)    = Struct (map (instantiate \<delta>) ts) (map (specialise \<delta>) vs)"
| "specialise \<delta> (Member v f)      = Member (specialise \<delta> v) f"
| "specialise \<delta> (Unit)            = Unit"
| "specialise \<delta> (Cast t e)        = Cast t (specialise \<delta> e)"
| "specialise \<delta> (Lit v)           = Lit v"
| "specialise \<delta> (Tuple a b)       = Tuple (specialise \<delta> a) (specialise \<delta> b)"
| "specialise \<delta> (Put e f e')      = Put (specialise \<delta> e) f (specialise \<delta> e')"
| "specialise \<delta> (Let e e')        = Let (specialise \<delta> e) (specialise \<delta> e')"
| "specialise \<delta> (LetBang vs e e') = LetBang vs (specialise \<delta> e) (specialise \<delta> e')"
| "specialise \<delta> (Case e t a b)    = Case (specialise \<delta> e) t (specialise \<delta> a) (specialise \<delta> b)"
| "specialise \<delta> (Esac e)          = Esac (specialise \<delta> e)"
| "specialise \<delta> (If c t e)        = If (specialise \<delta> c) (specialise \<delta> t) (specialise \<delta> e)"
| "specialise \<delta> (Take e f e')     = Take (specialise \<delta> e) f (specialise \<delta> e')"
| "specialise \<delta> (Split v va)      = Split (specialise \<delta> v) (specialise \<delta> va)"


section {* Contexts *}
 
type_synonym ctx = "type option env"

definition empty :: "nat \<Rightarrow> ctx" where 
  "empty \<equiv> (\<lambda> x. replicate x None)"

definition singleton :: "nat \<Rightarrow> index \<Rightarrow> type \<Rightarrow> ctx" where 
  "singleton n i t \<equiv> (empty n)[i := Some t]"

declare singleton_def [simp]

definition instantiate_ctx :: "type substitution \<Rightarrow> ctx \<Rightarrow> ctx" where
  "instantiate_ctx \<delta> \<Gamma> \<equiv> map (map_option (instantiate \<delta>)) \<Gamma>"

inductive split_comp :: "kind env \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> bool"
          ("_ \<turnstile> _ \<leadsto> _ \<parallel> _" [30,0,0,20] 60) where
  none  : "K \<turnstile> None \<leadsto> None \<parallel> None"
| left  : "\<lbrakk> K \<turnstile> t :\<kappa> k         \<rbrakk> \<Longrightarrow> K \<turnstile> Some t \<leadsto> Some t \<parallel> None"
| right : "\<lbrakk> K \<turnstile> t :\<kappa> k         \<rbrakk> \<Longrightarrow> K \<turnstile> Some t \<leadsto> None   \<parallel> (Some t)"
| share : "\<lbrakk> K \<turnstile> t :\<kappa> k ; S \<in> k \<rbrakk> \<Longrightarrow> K \<turnstile> Some t \<leadsto> Some t \<parallel> Some t" 

inductive split :: "kind env \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool" ("_ \<turnstile> _ \<leadsto> _ | _" [30,0,0,20] 60) where
  split_empty : "K \<turnstile> [] \<leadsto> [] | []"
| split_cons  : "\<lbrakk> K \<turnstile> x \<leadsto> a \<parallel> b ; K \<turnstile> xs \<leadsto> as | bs \<rbrakk> \<Longrightarrow> K \<turnstile> (x # xs) \<leadsto> (a # as) | (b # bs)"

definition pred :: "nat \<Rightarrow> nat" where
  "pred n \<equiv> (case n of Suc n' \<Rightarrow> n')"

inductive split_bang :: "kind env \<Rightarrow> index set \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool" where 
  split_bang_empty : "split_bang K is [] [] []"
| split_bang_cons  : "\<lbrakk> 0 \<notin> is 
                      ; K \<turnstile> x \<leadsto> a \<parallel> b
                      ; split_bang K (pred ` is) xs as bs
                      \<rbrakk>  \<Longrightarrow> split_bang K is (x # xs) (a # as) (b # bs) "
| split_bang_bang  : "\<lbrakk> 0 \<in> is 
                      ; is' = Set.remove (0 :: index) is
                      ; split_bang K (pred ` is') xs as bs
                      \<rbrakk>  \<Longrightarrow> split_bang K is (Some x # xs) (Some (bang x) # as) (Some x # bs)"


inductive weakening_comp :: "kind env \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> bool" where
  none : "weakening_comp K None None"
| keep : "\<lbrakk> K \<turnstile> t :\<kappa> k \<rbrakk>         \<Longrightarrow> weakening_comp K (Some t) (Some t)"
| drop : "\<lbrakk> K \<turnstile> t :\<kappa> k ; D \<in> k \<rbrakk> \<Longrightarrow> weakening_comp K (Some t) None"

definition weakening :: "kind env \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool" ("_ \<turnstile> _ \<leadsto>w _" [30,0,20] 60) where 
  "weakening \<equiv> (\<lambda>K. list_all2 (weakening_comp K))"

definition is_consumed :: "kind env \<Rightarrow> ctx \<Rightarrow> bool" ("_ \<turnstile> _ consumed" [30,20] 60 ) where  
  "K \<turnstile> \<Gamma> consumed \<equiv> K \<turnstile> \<Gamma> \<leadsto>w empty (length \<Gamma>)" 

declare is_consumed_def [simp]

section {* Built-in types *}

primrec prim_op_type :: "prim_op \<Rightarrow> prim_type list \<times> prim_type" where 
  "prim_op_type (Plus t)   = ([Num t, Num t], Num t)"
| "prim_op_type (Times t)  = ([Num t, Num t], Num t)"
| "prim_op_type (Minus t)  = ([Num t, Num t], Num t)"
| "prim_op_type (Divide t) = ([Num t, Num t], Num t)"
| "prim_op_type (Mod t)    = ([Num t, Num t], Num t)"
| "prim_op_type (BitAnd t) = ([Num t, Num t], Num t)"
| "prim_op_type (BitOr t)  = ([Num t, Num t], Num t)"
| "prim_op_type (BitXor t) = ([Num t, Num t], Num t)"
| "prim_op_type (LShift t) = ([Num t, Num t], Num t)"
| "prim_op_type (RShift t) = ([Num t, Num t], Num t)"
| "prim_op_type (Complement t) = ([Num t], Num t)"
| "prim_op_type (Gt t)     = ([Num t, Num t], Bool )"
| "prim_op_type (Lt t)     = ([Num t, Num t], Bool )"
| "prim_op_type (Le t)     = ([Num t, Num t], Bool )"
| "prim_op_type (Ge t)     = ([Num t, Num t], Bool )"
| "prim_op_type (Eq t)     = ([t    , t    ], Bool )"
| "prim_op_type (NEq t)    = ([t    , t    ], Bool )"
| "prim_op_type (And)      = ([Bool , Bool ], Bool )"
| "prim_op_type (Or)       = ([Bool , Bool ], Bool )"
| "prim_op_type (Not)      = ([Bool],         Bool )"

primrec lit_type :: "lit \<Rightarrow> prim_type" where 
  "lit_type (LBool _) = Bool" 
| "lit_type (LU8  _)  = Num U8" 
| "lit_type (LU16 _)  = Num U16" 
| "lit_type (LU32 _)  = Num U32" 
| "lit_type (LU64 _)  = Num U64"

fun upcast_valid :: "num_type \<Rightarrow> num_type \<Rightarrow> bool" where
  "upcast_valid U8  U8  = True"
| "upcast_valid U8  U16 = True"
| "upcast_valid U8  U32 = True"
| "upcast_valid U8  U64 = True"
| "upcast_valid U16 U16 = True"
| "upcast_valid U16 U32 = True"
| "upcast_valid U16 U64 = True"
| "upcast_valid U32 U32 = True"
| "upcast_valid U32 U64 = True"
| "upcast_valid U64 U64 = True"
| "upcast_valid _   _   = False"

primrec prim_lbool where
  "prim_lbool (LBool b) = b"
| "prim_lbool (LU8 w) = False"
| "prim_lbool (LU16 w) = False"
| "prim_lbool (LU32 w) = False"
| "prim_lbool (LU64 w) = False"

definition prim_word_op
  where prim_word_op_def[simp]:
  "prim_word_op f8 f16 f32 f64 xs = (case (take 2 xs) of
      [LU8 x, LU8 y] \<Rightarrow> LU8 (f8 x y)
    | [LU16 x, LU16 y] \<Rightarrow> LU16 (f16 x y)
    | [LU32 x, LU32 y] \<Rightarrow> LU32 (f32 x y)
    | [LU64 x, LU64 y] \<Rightarrow> LU64 (f64 x y)
    | _ \<Rightarrow> LBool False)"

definition prim_word_comp
  where prim_word_comp_def[simp]:
  "prim_word_comp f8 f16 f32 f64 xs = (case (take 2 xs) of
      [LU8 x, LU8 y] \<Rightarrow> LBool (f8 x y)
    | [LU16 x, LU16 y] \<Rightarrow> LBool (f16 x y)
    | [LU32 x, LU32 y] \<Rightarrow> LBool (f32 x y)
    | [LU64 x, LU64 y] \<Rightarrow> LBool (f64 x y)
    | _ \<Rightarrow> LBool False)"

primrec eval_prim_op :: "prim_op \<Rightarrow> lit list \<Rightarrow> lit"
where
    "eval_prim_op Not xs = LBool (\<not> prim_lbool (hd xs))"
  | "eval_prim_op And xs = LBool (prim_lbool (hd xs) \<and> prim_lbool (xs ! 1))"
  | "eval_prim_op Or xs = LBool (prim_lbool (hd xs) \<or> prim_lbool (xs ! 1))"
  | "eval_prim_op (Eq _) xs = LBool (hd xs = xs ! 1)"
  | "eval_prim_op (NEq _) xs = LBool (hd xs \<noteq> xs ! 1)"
  | "eval_prim_op (Plus _) xs = prim_word_op (op +) (op +) (op +) (op +) xs"
  | "eval_prim_op (Minus _) xs = prim_word_op (op -) (op -) (op -) (op -) xs"
  | "eval_prim_op (Times _) xs = prim_word_op (op *) (op *) (op *) (op *) xs"
  | "eval_prim_op (Divide _) xs = prim_word_op checked_div checked_div checked_div checked_div  xs"
  | "eval_prim_op (Mod _) xs = prim_word_op checked_mod checked_mod checked_mod checked_mod xs"
  | "eval_prim_op (Gt _) xs = prim_word_comp greater greater greater greater xs"
  | "eval_prim_op (Lt _) xs = prim_word_comp less less less less xs"
  | "eval_prim_op (Le _) xs = prim_word_comp less_eq less_eq less_eq less_eq xs"
  | "eval_prim_op (Ge _) xs = prim_word_comp greater_eq greater_eq greater_eq greater_eq xs"
  | "eval_prim_op (BitAnd _) xs = prim_word_op bitAND bitAND bitAND bitAND xs"
  | "eval_prim_op (BitOr _) xs = prim_word_op bitOR bitOR bitOR bitOR xs"
  | "eval_prim_op (BitXor _) xs = prim_word_op bitXOR bitXOR bitXOR bitXOR xs"
  | "eval_prim_op (LShift _) xs = prim_word_op (checked_shift shiftl) (checked_shift shiftl)
        (checked_shift shiftl) (checked_shift shiftl) xs"
  | "eval_prim_op (RShift _) xs = prim_word_op (checked_shift shiftr) (checked_shift shiftr)
        (checked_shift shiftr) (checked_shift shiftr) xs"
  | "eval_prim_op (Complement _) xs = prim_word_op (\<lambda>x y. bitNOT x) (\<lambda>x y. bitNOT x)
        (\<lambda>x y. bitNOT x) (\<lambda>x y. bitNOT x) [hd xs, hd xs]"

lemma eval_prim_op_lit_type:
  "prim_op_type pop = (\<tau>s, \<tau>) \<Longrightarrow> map lit_type xs = \<tau>s
    \<Longrightarrow> lit_type (eval_prim_op pop xs) = \<tau>"
  by (cases pop, auto split: lit.split)

section {* Typing rules *}

(*
inductive subtyping :: "kind env \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ \<sqsubseteq> _" [30,0,0] 60) where
  tsum_subtyping: "\<lbrakk> set (map fst ts) = set (map fst ts')
                   ; \<forall> c c'. c \<in> set (map fst ts) \<longrightarrow> lookup c ts = lookup c ts' \<rbrakk> \<Longrightarrow> K \<turnstile> TSum ts \<sqsubseteq> TSum ts'"
*)

inductive typing :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> ctx \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> bool" 
          ("_, _, _ \<turnstile> _ : _" [30,0,0,0,20] 60)
      and typing_all :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> ctx \<Rightarrow> 'f expr list \<Rightarrow> type list \<Rightarrow> bool"
          ("_, _, _ \<turnstile>* _ : _" [30,0,0,0,20] 60) where

  typing_var    : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i t 
                   ; i < length \<Gamma>
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Var i : t"

| typing_afun   : "\<lbrakk> \<Xi> f = (K', t, u)
                   ; list_all2 (kinding K) ts K' 
                   ; K' \<turnstile> TFun t u wellformed
                   ; K \<turnstile> \<Gamma> consumed
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> AFun f ts : instantiate ts (TFun t u)"

| typing_fun    : "\<lbrakk> \<Xi>, K', [Some t] \<turnstile> f : u 
                   ; K \<turnstile> \<Gamma> consumed
                   ; K' \<turnstile> t wellformed
                   ; list_all2 (kinding K) ts K'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Fun f ts : instantiate ts (TFun t u)"

| typing_app    : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile> a : TFun x y
                   ; \<Xi>, K, \<Gamma>2 \<turnstile> b : x 
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> App a b : y"

| typing_con    : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile> x : t
                   ; (tag,t) \<in> set ts
                   ; K \<turnstile>* (map snd ts) wellformed
                   ; distinct (map fst ts)
                   ; ts' = map (\<lambda> (c,t). (c, (t, c \<noteq> tag))) ts
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Con ts tag x : TSum ts'"

| typing_prom   : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile> x : TSum ts
                   ; set (map fst ts) = set (map fst ts')
                   ; K \<turnstile>* (map (fst \<circ> snd) ts') wellformed
                   ; distinct (map fst ts')
                   ; \<forall>c t b. (c,t,b) \<in> set ts \<longrightarrow> (\<exists>b'. (b' \<longrightarrow> b) \<and> ((c,(t,b')) \<in> set ts'))
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Promote ts' x : TSum ts'"

| typing_cast   : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile> e : TPrim (Num \<tau>)
                   ; upcast_valid \<tau> \<tau>' 
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Cast \<tau>' e : TPrim (Num \<tau>')"

| typing_tuple  : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile> t : T 
                   ; \<Xi>, K, \<Gamma>2 \<turnstile> u : U
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Tuple t u : TProduct T U"

| typing_split  : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile> x : TProduct t u
                   ; \<Xi>, K, (Some t)#(Some u)#\<Gamma>2 \<turnstile> y : t'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Split x y : t'" 

| typing_let    : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2 
                   ; \<Xi>, K, \<Gamma>1 \<turnstile> x : t
                   ; \<Xi>, K, (Some t # \<Gamma>2) \<turnstile> y : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Let x y : u"

| typing_letb   : "\<lbrakk> split_bang K is \<Gamma> \<Gamma>1 \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile> x : t
                   ; \<Xi>, K, (Some t # \<Gamma>2) \<turnstile> y : u
                   ; K \<turnstile> t :\<kappa> k
                   ; E \<in> k
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> LetBang is x y : u"

| typing_case   : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile> x : TSum ts
                   ; (tag, (t,False)) \<in> set ts
                   ; \<Xi>, K, (Some t # \<Gamma>2) \<turnstile> a : u
                   ; \<Xi>, K, (Some (TSum ((tag, (t,True)) # filter (\<lambda> x. fst x \<noteq> tag) ts)) # \<Gamma>2) \<turnstile> b : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Case x tag a b : u"

| typing_esac   : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile> x : TSum ts
                   ; [(_, (t,False))] = filter (HOL.Not \<circ> snd \<circ> snd) ts
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Esac x : t"

| typing_if     : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile> x : TPrim Bool
                   ; \<Xi>, K, \<Gamma>2 \<turnstile> a : t
                   ; \<Xi>, K, \<Gamma>2 \<turnstile> b : t
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> If x a b : t"

| typing_prim   : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile>* args : map TPrim ts 
                   ; prim_op_type oper = (ts,t)
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Prim oper args : TPrim t"

| typing_lit    : "\<lbrakk> K \<turnstile> \<Gamma> consumed
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Lit l : TPrim (lit_type l)" 

| typing_unit   : "\<lbrakk> K \<turnstile> \<Gamma> consumed
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Unit : TUnit"

| typing_struct : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile>* es : ts
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Struct ts es : TRecord (zip ts (replicate (length ts) False)) Unboxed"

| typing_member : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile> e : TRecord ts s
                   ; K \<turnstile> TRecord ts s :\<kappa> k
                   ; S \<in> k
                   ; f < length ts
                   ; ts ! f = (t, False)
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Member e f : t"

| typing_take   : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2 
                   ; \<Xi>, K, \<Gamma>1 \<turnstile> e : TRecord ts s
                   ; s \<noteq> ReadOnly
                   ; f < length ts
                   ; ts ! f = (t, False)
                   ; K \<turnstile> t :\<kappa> k
                   ; S \<in> k \<or> taken
                   ; \<Xi>, K, (Some t # Some (TRecord (ts [f := (t,taken)]) s) # \<Gamma>2) \<turnstile> e' : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Take e f e' : u"

| typing_put    : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile> e : TRecord ts s
                   ; s \<noteq> ReadOnly
                   ; f < length ts
                   ; ts ! f = (t, taken)
                   ; K \<turnstile> t :\<kappa> k
                   ; D \<in> k \<or> taken
                   ; \<Xi>, K, \<Gamma>2 \<turnstile> e' : t
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Put e f e' : TRecord (ts [f := (t,False)]) s"

| typing_all_empty : "\<Xi>, K, empty n \<turnstile>* [] : []"

| typing_all_cons  : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                      ; \<Xi>, K, \<Gamma>1 \<turnstile>  e  : t
                      ; \<Xi>, K, \<Gamma>2 \<turnstile>* es : ts
                      \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>* (e # es) : (t # ts)"

inductive_cases typing_num     [elim]: "\<Xi>, K, \<Gamma> \<turnstile> e : TPrim (Num \<tau>)"
inductive_cases typing_bool    [elim]: "\<Xi>, K, \<Gamma> \<turnstile> e : TPrim Bool"
inductive_cases typing_varE    [elim]: "\<Xi>, K, \<Gamma> \<turnstile> Var i : \<tau>"
inductive_cases typing_appE    [elim]: "\<Xi>, K, \<Gamma> \<turnstile> App x y : \<tau>"
inductive_cases typing_litE    [elim]: "\<Xi>, K, \<Gamma> \<turnstile> Lit l : \<tau>"
inductive_cases typing_funE    [elim]: "\<Xi>, K, \<Gamma> \<turnstile> Fun f ts : \<tau>"
inductive_cases typing_afunE   [elim]: "\<Xi>, K, \<Gamma> \<turnstile> AFun f ts : \<tau>"
inductive_cases typing_ifE     [elim]: "\<Xi>, K, \<Gamma> \<turnstile> If c t e : \<tau>"
inductive_cases typing_conE    [elim]: "\<Xi>, K, \<Gamma> \<turnstile> Con ts t e : \<tau>"
inductive_cases typing_unitE   [elim]: "\<Xi>, K, \<Gamma> \<turnstile> Unit : \<tau>"
inductive_cases typing_promE   [elim]: "\<Xi>, K, \<Gamma> \<turnstile> Promote ts e : \<tau>"
inductive_cases typing_primE   [elim]: "\<Xi>, K, \<Gamma> \<turnstile> Prim p es : \<tau>"
inductive_cases typing_memberE [elim]: "\<Xi>, K, \<Gamma> \<turnstile> Member e f : \<tau>"
inductive_cases typing_tupleE  [elim]: "\<Xi>, K, \<Gamma> \<turnstile> Tuple a b : \<tau>"
inductive_cases typing_caseE   [elim]: "\<Xi>, K, \<Gamma> \<turnstile> Case x t m n : \<tau>"
inductive_cases typing_esacE   [elim]: "\<Xi>, K, \<Gamma> \<turnstile> Esac e : \<tau>"
inductive_cases typing_castE   [elim]: "\<Xi>, K, \<Gamma> \<turnstile> Cast t e : \<tau>"
inductive_cases typing_letE    [elim]: "\<Xi>, K, \<Gamma> \<turnstile> Let a b : \<tau>"
inductive_cases typing_structE [elim]: "\<Xi>, K, \<Gamma> \<turnstile> Struct ts es : \<tau>"
inductive_cases typing_letbE   [elim]: "\<Xi>, K, \<Gamma> \<turnstile> LetBang vs a b : \<tau>"
inductive_cases typing_takeE   [elim]: "\<Xi>, K, \<Gamma> \<turnstile> Take x f e : \<tau>"
inductive_cases typing_putE    [elim]: "\<Xi>, K, \<Gamma> \<turnstile> Put x f e : \<tau>"
inductive_cases typing_splitE  [elim]: "\<Xi>, K, \<Gamma> \<turnstile> Split x e : \<tau>"
inductive_cases typing_all_emptyE [elim]: "\<Xi>, K, \<Gamma> \<turnstile>* []       : \<tau>s"
inductive_cases typing_all_consE  [elim]: "\<Xi>, K, \<Gamma> \<turnstile>* (x # xs) : \<tau>s"

section {* Syntax structural judgements *}

subsection {* A-normal form *}

inductive atom ::"'f expr \<Rightarrow> bool" where 
  "atom (Var x)"
| "atom (Fun f ts)"
| "atom (AFun f ts)"
| "atom (Prim p (map Var is))"
| "atom (Con ts n (Var x))"
| "atom (Promote ts (Var x))"
| "atom (Struct ts (map Var is))"
| "atom (Cast t (Var x))"
| "atom (Member (Var x) f)"
| "atom Unit"
| "atom (Lit l)"
| "atom (Tuple (Var x) (Var y))"
| "atom (Esac (Var x))"
| "atom (App (Var a) (Var b))"
| "atom (App (Fun f ts) (Var b))"
| "atom (App (AFun f ts) (Var b))"
| "atom (Put (Var x) f (Var y))"

inductive a_normal :: "'f expr \<Rightarrow> bool" where 
  "\<lbrakk> atom x \<rbrakk> \<Longrightarrow> a_normal x"
| "\<lbrakk> atom x ; a_normal y \<rbrakk> \<Longrightarrow> a_normal (Let x y)"
| "\<lbrakk> a_normal x ; a_normal y \<rbrakk> \<Longrightarrow> a_normal (LetBang is x y)"
| "\<lbrakk> a_normal m ; a_normal n \<rbrakk> \<Longrightarrow> a_normal (Case (Var x) t m n)"
| "\<lbrakk> a_normal t ; a_normal e \<rbrakk> \<Longrightarrow> a_normal (If (Var x) t e)"
| "\<lbrakk> a_normal y \<rbrakk> \<Longrightarrow> a_normal (Split (Var x) y)"
| "\<lbrakk> a_normal y \<rbrakk> \<Longrightarrow> a_normal (Take (Var x) f y)"

inductive_cases a_normal_E:  "a_normal x"
inductive_cases a_normal_LetE:  "a_normal (Let x y)"
inductive_cases a_normal_LetBangE: "a_normal (LetBang is x y)"
inductive_cases a_normal_CaseE: "a_normal (Case x t m n)"
inductive_cases a_normal_IfE: "a_normal (If x t e)"
inductive_cases a_normal_Split: "a_normal (Split x y)"
inductive_cases a_normal_TakeE:  "a_normal (Take x f e)"

section {* Representation Types (for use in C-refinement) *}


datatype repr = RPtr repr
              | RCon name "repr list"
              | RFun
              | RPrim prim_type
              | RSum "(name \<times> repr) list"
              | RProduct "repr" "repr"
              | RRecord "repr list"
              | RUnit

fun type_repr :: "type \<Rightarrow> repr" where
  "type_repr (TFun t t')          = RFun"
| "type_repr (TPrim t)            = RPrim t"
| "type_repr (TSum ts)            = RSum (map (\<lambda>(a,(b,_)).(a, type_repr b)) ts)"
| "type_repr (TProduct a b)       = RProduct (type_repr a) (type_repr b)"
| "type_repr (TCon n ts Unboxed)  = RCon n (map type_repr ts)"
| "type_repr (TCon n ts _)        = RPtr (RCon n (map type_repr ts))"
| "type_repr (TRecord ts Unboxed) = RRecord (map (\<lambda>a. type_repr (fst a)) ts)"  
| "type_repr (TRecord ts _)       = RPtr (RRecord (map (\<lambda>a. type_repr (fst a)) ts))"
| "type_repr (TUnit)              = RUnit"

section {* Kinding lemmas *}

lemma supersumption:
fixes k' :: kind
assumes k_is_superset : "k' \<subseteq> k"
shows "K \<turnstile>  t  :\<kappa> k  \<Longrightarrow> K \<turnstile>  t  :\<kappa> k'" 
and   "K \<turnstile>* ts :\<kappa> k  \<Longrightarrow> K \<turnstile>* ts :\<kappa> k'"
and   "K \<turnstile>* fs :\<kappa>r k \<Longrightarrow> K \<turnstile>* fs :\<kappa>r k'"
using k_is_superset proof (induct rule: kinding_kinding_all_kinding_record.inducts)
qed (auto intro: subset_trans kinding_kinding_all_kinding_record.intros)


lemma kind_top:
shows "k \<subseteq> {D, S, E}"
by (force intro: kind_comp.exhaust)

lemma kinding_all_nth:
fixes n :: nat
assumes "K \<turnstile>* ts :\<kappa> k" 
and     "n < length ts"
shows   "K \<turnstile> (ts ! n) :\<kappa> k"
using assms proof (induct ts arbitrary: n)
     case Nil  then show ?case by auto
next case Cons then show ?case by (case_tac n, auto)
qed

lemma kinding_all_set:
shows "(K \<turnstile>* ts :\<kappa> k) = (\<forall> t \<in> set ts. K \<turnstile> t :\<kappa> k)"
proof (rule iffI)
     assume "K \<turnstile>* ts :\<kappa> k"
then show   "\<forall> t \<in> set ts. K \<turnstile> t :\<kappa> k"
     by (rule kinding_kinding_all_kinding_record.inducts, simp+)

next assume "\<forall> t \<in> set ts. K \<turnstile> t :\<kappa> k"
then show   "K \<turnstile>* ts :\<kappa> k" 
     by (induct ts, auto intro: kinding_kinding_all_kinding_record.intros)
qed

lemma kinding_all_subset:
assumes "K \<turnstile>* ts :\<kappa> k"
and     "set us \<subseteq> set ts"
shows   "K \<turnstile>* us :\<kappa> k"
using assms by (auto simp add: kinding_all_set)

lemma kinding_record_wellformed:
assumes "K \<turnstile>* ts :\<kappa>r k"
and     "(a,b) \<in> set ts" 
shows   "K \<turnstile> a wellformed"
using assms proof (induct ts)
     case Nil  then show ?case by (simp add:   set_conv_nth)
next case Cons then show ?case by (auto split: prod.split
                                        elim:  kinding_record.cases)
qed

lemma kinding_record_wellformed_nth:
assumes "K \<turnstile>* ts :\<kappa>r k"
and     "ts ! n = (a,b)"
and     "n < length ts" 
shows   "K \<turnstile> a wellformed"
using assms(1)
  and assms(2) [THEN sym] 
  and assms(3) by (force intro: kinding_record_wellformed [simplified]
                         simp:  set_conv_nth)


lemma kinding_all_record:
assumes "K \<turnstile>* ts :\<kappa> k"
shows   "K \<turnstile>* zip ts (replicate (length ts) False) :\<kappa>r k"
using assms proof (induct ts)
qed (force intro: kinding_kinding_all_kinding_record.intros)+


lemma kinding_all_record':
assumes "K \<turnstile>* map fst ts :\<kappa> k"
shows   "K \<turnstile>* ts :\<kappa>r k"
using assms proof (induct ts)
     case Nil         then show ?case by (force intro: kinding_kinding_all_kinding_record.intros)
next case (Cons a ts) then show ?case apply (clarsimp)
                                      apply (case_tac a)
                                      apply (case_tac b)
                                      apply (auto intro: kinding_kinding_all_kinding_record.intros)
                                      done
qed

lemma kinding_record_update:
assumes "K \<turnstile>* ts :\<kappa>r k"
and     "ts ! n = (a, b)"
and     "K \<turnstile> a :\<kappa> k'"
shows   "K \<turnstile>* (ts[ n := (a, False)]) :\<kappa>r (k \<inter> k')"
using assms proof (induct ts arbitrary: n)
     case Nil then show ?case by (force intro: kinding_kinding_all_kinding_record.intros)
next case Cons
  note A = this
  show ?case proof (cases n)
         case 0   with A show ?thesis by (force elim!:  kind_record_consE
                                                intro!: kinding_kinding_all_kinding_record.intros 
                                                intro:  supersumption)
    next case Suc with A show ?thesis by (force elim!:  kind_record_consE
                                                intro!: kinding_kinding_all_kinding_record.intros 
                                                intro:  supersumption)
  qed
qed

lemma sigil_kind_writable:
assumes "s \<noteq> ReadOnly"
and     "k \<subseteq> sigil_kind Writable"
shows   "k \<subseteq> sigil_kind s"
proof (cases s)
qed (simp_all add: assms(1) assms(2)[simplified] kind_top)

section {* Bang lemmas *}

lemma bang_sigil_idempotent:
shows "bang_sigil (bang_sigil s) = bang_sigil s"
by (cases s, simp+)

lemma bang_idempotent:
shows "bang (bang \<tau>) = bang \<tau>"
by (force intro: bang.induct [where P = "\<lambda> \<tau> . bang (bang \<tau>) = bang \<tau>"]
          simp:  bang_sigil_idempotent)

lemma bang_sigil_kind: 
shows "{D , S} \<subseteq> sigil_kind (bang_sigil s)" 
by (case_tac s,auto)

lemma bang_kind:
shows "K \<turnstile>  t  :\<kappa>  k \<Longrightarrow> K \<turnstile>  bang t                       :\<kappa>  {D, S}"
and   "K \<turnstile>* ts :\<kappa>  k \<Longrightarrow> K \<turnstile>* map bang ts                  :\<kappa>  {D, S}"
and   "K \<turnstile>* fs :\<kappa>r k \<Longrightarrow> K \<turnstile>* map (\<lambda>(a,b). (bang a, b)) fs :\<kappa>r {D, S}"
  apply (induct rule: kinding_kinding_all_kinding_record.inducts)
  by (auto intro: kinding_kinding_all_kinding_record.intros
           intro!: bang_sigil_kind
           simp add: case_prod_unfold comp_def)


section {* Instantiation *}

lemma instantiate_bang [simp]:
shows "instantiate \<delta> (bang \<tau>) = bang (instantiate \<delta> \<tau>)"
by (force intro: bang.induct [where P = "\<lambda> \<tau>. instantiate \<delta> (bang \<tau>) = bang (instantiate \<delta> \<tau>)"] 
          simp:  bang_idempotent)

find_theorems name: kinding_kinding_all_kinding_record

lemma instantiate_instantiate [simp]:
assumes "list_all2 (kinding K') \<delta>' K"
and     "length K' = length \<delta>"
shows   "K \<turnstile> x wellformed \<Longrightarrow> instantiate \<delta> (instantiate \<delta>' x) = instantiate (map (instantiate \<delta>) \<delta>') x"
using assms proof (induct x arbitrary: \<delta>' rule: instantiate.induct)

next case 3 then show ?case by (force simp: set_conv_nth
                                      dest: kinding_all_nth)
next case 8 then show ?case by (fastforce dest: kinding_record_wellformed)
next case (6 \<delta> ps) note IH   = this(1)
                   and  REST = this(2-)
  from REST show ?case apply (clarsimp)
                       apply (rule IH, simp, simp)
                       apply (auto simp:  set_conv_nth comp_def
                                   intro: kind_tsum
                                   dest!: prod_in_set(2)
                                   dest:  kinding_all_nth [ where ts = "map (fst \<circ> snd) ts" for ts
                                                          , simplified])+
                       apply (erule kinding.cases; simp_all)
                       apply (bestsimp dest: kinding_all_nth [ where ts = "map (fst \<circ> snd) ps" and n = "i" for i ps
                                                             , simplified] 
                                             sym [ where ?t = "ps ! i" for i ])
                       done
qed (force dest: list_all2_lengthD)+
                        
lemma instantiate_tprim [simp]:
shows "instantiate \<delta> \<circ> TPrim = TPrim"
by (rule ext, simp)


lemma instantiate_nothing:
shows "instantiate [] e = e"
by (induct e) (auto simp: prod_set_defs intro: map_idI)

lemma instantiate_nothing_id[simp]:
shows "instantiate [] = id"
by (rule ext, simp add: instantiate_nothing)

lemma instantiate_ctx_nothing:
shows "instantiate_ctx [] e = e"
unfolding instantiate_ctx_def
by (induct e, auto simp: map_option.id [simplified id_def])

lemma instantiate_ctx_nothing_id[simp]:
shows "instantiate_ctx [] = id"
by (rule ext, simp add: instantiate_ctx_nothing)

lemma specialise_nothing:
shows "specialise [] e = e"
by (induct e) (auto simp: prod_set_defs intro: map_idI)

lemma specialise_nothing_id[simp]:
shows "specialise [] = id"
by (rule ext, simp add: specialise_nothing)



lemmas typing_struct_instantiate = typing_struct [where ts = "map (instantiate \<delta>) ts" for ts, simplified]

subsection {* substitutivity *}

lemma substitutivity:
fixes \<delta>    :: "type substitution"
and   K K' :: "kind env"
assumes well_kinded: "list_all2 (kinding K') \<delta> K"
shows "K \<turnstile> t :\<kappa> k    \<Longrightarrow> K' \<turnstile>  instantiate \<delta> t                       :\<kappa>  k"
and   "K \<turnstile>* ts :\<kappa> k  \<Longrightarrow> K' \<turnstile>* map (instantiate \<delta>) ts                :\<kappa>  k"
and   "K \<turnstile>* fs :\<kappa>r k \<Longrightarrow> K' \<turnstile>* map (\<lambda>(a,b). (instantiate \<delta> a, b)) fs :\<kappa>r k"
using well_kinded proof (induct rule: kinding_kinding_all_kinding_record.inducts)
     case (kind_tvar k K i)
       assume "list_all2 (kinding K') \<delta> K"
       and    "i < length K"
       and    "k \<subseteq> K ! i" 
       moreover   then have "i < length \<delta>" by (auto dest: list_all2_lengthD)
       ultimately also have "K' \<turnstile> (\<delta> ! i) :\<kappa> (K ! i)" by (auto intro: list_all2_nthD)
       ultimately show ?case by (auto intro: supersumption)
next case (kind_tvarb k i K)
       assume "list_all2 (kinding K') \<delta> K"
       and    "i < length K"
       and    "k \<subseteq> {D, S}"
       moreover   then have "i < length \<delta>" by (auto dest: list_all2_lengthD)
       ultimately also have "K' \<turnstile> (\<delta> ! i) :\<kappa> (K ! i)" by (auto intro: list_all2_nthD)
       ultimately show ?case by (auto intro: supersumption bang_kind)
qed (auto intro: kinding_kinding_all_kinding_record.intros)



lemma list_all2_substitutivity:
fixes \<delta>    :: "type substitution"
and   K K' :: "kind env"
assumes well_kinded: "list_all2 (kinding K') \<delta> K"
shows "list_all2 (kinding K) ts ks \<Longrightarrow> list_all2 (kinding K') (map (instantiate \<delta>) ts) ks"
by ( induct rule: list_all2_induct
   , auto dest: substitutivity [OF well_kinded])

subsection {* Instantiation of contexts *}

lemma instantiate_ctx_weaken:
assumes "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
and     "list_all2 (kinding K') \<delta> K"
shows   "K' \<turnstile> instantiate_ctx \<delta> \<Gamma> \<leadsto>w instantiate_ctx \<delta> \<Gamma>'"
using assms(1) [simplified weakening_def] and assms(2) proof (induct rule: list_all2_induct)
     case Nil  then show ?case by (simp add: instantiate_ctx_def weakening_def) 
next case Cons then show ?case by (fastforce intro: weakening_comp.intros 
                                             elim:  weakening_comp.cases
                                             simp:  instantiate_ctx_def 
                                                    weakening_def 
                                             dest:  substitutivity)
qed


lemma instantiate_ctx_empty [simplified, simp]:
shows "instantiate_ctx \<delta> (empty l) = empty l"
by (induct l, simp_all add: empty_def
                            instantiate_ctx_def)



lemma instantiate_ctx_singleton [simplified, simp]:
shows "instantiate_ctx \<delta> (singleton l i \<tau>) = singleton l i (instantiate \<delta> \<tau>)"
by (induct l arbitrary: i, simp_all add:   instantiate_ctx_def 
                                           empty_def 
                                    split: nat.split)

lemma instantiate_ctx_length [simp]:
shows "length (instantiate_ctx \<delta> \<Gamma>) = length \<Gamma>"
by (simp add: instantiate_ctx_def)

lemma instantiate_ctx_consumed [simplified]:
assumes "K \<turnstile> \<Gamma> consumed"
and     "list_all2 (kinding K') \<delta> K"
shows   "K' \<turnstile> instantiate_ctx \<delta> \<Gamma> consumed"
using assms by (auto intro: instantiate_ctx_weaken [where \<Gamma>' = "empty (length \<Gamma>)", simplified])

lemma map_option_instantiate_split_comp:
assumes "K \<turnstile> c \<leadsto> c1 \<parallel> c2"
and     "list_all2 (kinding K') \<delta> K"
shows   "K' \<turnstile> map_option (instantiate \<delta>) c \<leadsto> map_option (instantiate \<delta>) c1 \<parallel> map_option (instantiate \<delta>) c2"
using assms(1) by ( rule split_comp.cases
                  , auto elim: split_comp.cases 
                         intro: substitutivity(1) assms(2) split_comp.intros)

lemma instantiate_ctx_split:
assumes "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
and     "list_all2 (kinding K') \<delta> K"
shows   "K' \<turnstile> instantiate_ctx \<delta> \<Gamma> \<leadsto> instantiate_ctx \<delta> \<Gamma>1 | instantiate_ctx \<delta> \<Gamma>2"
using assms proof (induct rule: split.induct)
case split_empty then show ?case by (auto simp:  instantiate_ctx_def
                                          intro: split.intros)
case split_cons  then show ?case by (auto simp:  instantiate_ctx_def
                                          intro: split.intros
                                                 map_option_instantiate_split_comp)
qed


lemma instantiate_ctx_split_bang:
assumes "split_bang K is \<Gamma> \<Gamma>1 \<Gamma>2"
and     "list_all2 (kinding K') \<delta> K"
shows   "split_bang K' is (instantiate_ctx \<delta> \<Gamma>) (instantiate_ctx \<delta> \<Gamma>1) (instantiate_ctx \<delta> \<Gamma>2)"
using assms proof (induct rule: split_bang.induct)
     case split_bang_empty then show ?case by (auto simp:  instantiate_ctx_def
                                                    intro: split_bang.intros)
next case split_bang_cons  then show ?case by (auto simp:  instantiate_ctx_def
                                                    intro: split_bang.intros
                                                           map_option_instantiate_split_comp)
next case split_bang_bang  then show ?case by (auto simp: instantiate_ctx_def 
                                                    intro: split_bang.intros)
qed


lemma instantiate_ctx_cons [simp]:
shows   "instantiate_ctx \<delta> (Some x # \<Gamma>) = Some (instantiate \<delta> x) # instantiate_ctx \<delta> \<Gamma>"
by (simp add: instantiate_ctx_def)



section {* Lemmas about contexts, splitting and weakening *}

lemma empty_length: 
shows "length (empty n) = n"
by (induct n, simp_all add: empty_def)

lemma weakening_length:
shows "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>' \<Longrightarrow> length \<Gamma> = length \<Gamma>'"
by (auto simp: weakening_def dest:list_all2_lengthD)

lemma weakening_preservation:
assumes weak: "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
and     idx:  "\<Gamma>' ! x = Some t"
shows   "\<Gamma>  ! x = Some t"
using weak[simplified weakening_def]
  and weakening_length[OF weak] 
  and idx
  proof (induct arbitrary: x rule: list_all2_induct)
     case Nil                then show ?case by auto
next case (Cons x xs y ys a) then show ?case by (case_tac a, auto elim: weakening_comp.cases)
qed           

lemma weakening_nth:
assumes weak: "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
and           "i < length \<Gamma>"
shows         "weakening_comp K (\<Gamma>!i) (\<Gamma>'!i)"
using assms by (auto simp add: weakening_def dest: list_all2_nthD)


lemma typing_to_kinding :
shows "\<Xi>, K, \<Gamma> \<turnstile>  e  : t  \<Longrightarrow> K \<turnstile>  t  wellformed" 
and   "\<Xi>, K, \<Gamma> \<turnstile>* es : ts \<Longrightarrow> K \<turnstile>* ts wellformed"
proof (induct rule: typing_typing_all.inducts)
     case typing_var    then show ?case by (fastforce dest: weakening_preservation weakening_nth
                                                      simp: empty_length 
                                                      elim: weakening_comp.cases)
next case typing_fun    then show ?case by (fastforce intro: kinding_kinding_all_kinding_record.intros 
                                                             substitutivity)
next case typing_afun   then show ?case by (fastforce intro: kinding_kinding_all_kinding_record.intros 
                                                             substitutivity)
next case typing_esac   then show ?case by (fastforce dest: filtered_member
                                                      elim: kinding.cases
                                                      simp add: kinding_all_set)
next case typing_member then show ?case by (fastforce intro: kinding_record_wellformed_nth)
next case typing_struct then show ?case by ( clarsimp
                                           , intro exI kind_trec kinding_all_record
                                           , simp_all add: kind_top )
next case typing_take   then show ?case by (simp)  
next case typing_put    then show ?case by (fastforce intro: kinding_kinding_all_kinding_record.intros
                                                             kinding_record_update)
next case (typing_con \<Xi> K \<Gamma> x t tag ts ts')
  hence "map fst ts = map fst ts'" by fastforce
  with typing_con have a1: "distinct (map fst ts')" by simp
  from typing_con have "map snd ts = map (fst \<circ> snd) ts'" by fastforce
  hence "(K \<turnstile>* map snd ts :\<kappa>  k) = (K \<turnstile>* map (fst \<circ> snd) ts' :\<kappa>  k)" for k by presburger
  with typing_con[simplified] have "\<exists>k. K \<turnstile>* map (fst \<circ> snd) ts' :\<kappa>  k" by blast
  then obtain k where a2: "K \<turnstile>* map (fst \<circ> snd) ts' :\<kappa>  k" by blast 
  hence "distinct (map fst ts') \<Longrightarrow> K \<turnstile>* map (fst \<circ> snd) ts' :\<kappa>  k \<Longrightarrow> K \<turnstile> TSum ts' :\<kappa>  k" by (elim kind_tsum)
  from a1 a2 show ?case by (fastforce elim: kind_tsum)

qed (auto intro: supersumption kinding_kinding_all_kinding_record.intros)

lemma upcast_valid_cast_to :
assumes "upcast_valid \<tau> \<tau>'"
    and "lit_type l = Num \<tau>"
obtains x where "cast_to \<tau>' l = Some x"
            and "lit_type x = Num \<tau>'"
using assms by (cases l, auto elim: upcast_valid.elims)

lemma bang_type_repr [simp]:
shows "[] \<turnstile> t :\<kappa> k \<Longrightarrow> (type_repr (bang t) = type_repr t)"
and   "[] \<turnstile>* ts :\<kappa> k \<Longrightarrow> (map (type_repr \<circ> bang) ts) = map (type_repr) ts "
and   "[] \<turnstile>* fs :\<kappa>r k \<Longrightarrow> (map (type_repr \<circ>  bang \<circ> fst) fs) = map (type_repr  \<circ> fst) fs"
by ( induct "[] :: kind list"  t k
           and "[] :: kind list" ts k
           and "[] :: kind list" fs k
     rule: kinding_kinding_all_kinding_record.inducts
   , auto, (case_tac s,auto)+)


subsection {* Specialisation *} 

lemma specialisation:
assumes well_kinded: "list_all2 (kinding K') \<delta> K"
shows "\<Xi> , K , \<Gamma> \<turnstile>  e  : \<tau>  \<Longrightarrow> \<Xi> , K' , instantiate_ctx \<delta> \<Gamma> \<turnstile> specialise \<delta> e : instantiate \<delta> \<tau> "
and   "\<Xi> , K , \<Gamma> \<turnstile>* es : \<tau>s \<Longrightarrow> \<Xi> , K' , instantiate_ctx \<delta> \<Gamma> \<turnstile>* map (specialise \<delta>) es : map (instantiate \<delta>) \<tau>s"
  using assms
proof (induct rule: typing_typing_all.inducts)
  case (typing_case K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x ts tag t a u b)
  then have "\<Xi>, K', instantiate_ctx \<delta> \<Gamma> \<turnstile> Case (specialise \<delta> x) tag (specialise \<delta> a) (specialise \<delta> b) : instantiate \<delta> u"
    using image_iff
      filter_fst_ignore_triple[where ls=ts and f="\<lambda>(t,b). (instantiate \<delta> t, b)" and P="\<lambda>p. p \<noteq> tag"]
  proof (intro typing_typing_all.typing_case)
    show "(tag, instantiate \<delta> t, False) \<in> set (map (\<lambda>(c, t, b). (c, instantiate \<delta> t, b)) ts)"
      using typing_case.hyps(4) image_iff by fastforce
  qed (force intro: instantiate_ctx_split)+
  then show ?case by simp
next case (typing_afun \<Xi> f ks t u K ts ks)
  then also have "instantiate \<delta> (instantiate ts t) = instantiate (map (instantiate \<delta>) ts) t"
    and  "instantiate \<delta> (instantiate ts u) = instantiate (map (instantiate \<delta>) ts) u"
    by (force dest: list_all2_lengthD intro: instantiate_instantiate)+
  ultimately show ?case by (auto intro!: list_all2_substitutivity
        typing_typing_all.typing_afun [simplified] 
        instantiate_ctx_consumed)
next case (typing_fun \<Xi> K t f u \<Gamma> ks ts)
  then also have "instantiate \<delta> (instantiate ts t) = instantiate (map (instantiate \<delta>) ts) t"
    and  "instantiate \<delta> (instantiate ts u) = instantiate (map (instantiate \<delta>) ts) u"
    by (force dest: list_all2_lengthD intro: instantiate_instantiate dest!: typing_to_kinding)+
  ultimately show ?case by (auto intro!: list_all2_substitutivity
        typing_typing_all.typing_fun [simplified] 
        instantiate_ctx_consumed)
next
  case (typing_prom \<Xi> K \<Gamma> x ts ts')
  then have "\<Xi>, K', instantiate_ctx \<delta> \<Gamma> \<turnstile> Promote (map (\<lambda>(c, t, b). (c, instantiate \<delta> t, b)) ts') (specialise \<delta> x) : TSum (map (\<lambda>(c, t, b). (c, instantiate \<delta> t, b)) ts')" 
  proof (intro typing_typing_all.typing_prom)
    show "K' \<turnstile>* map (fst \<circ> snd) (map (\<lambda>(c, t, b). (c, instantiate \<delta> t, b)) ts') wellformed"
      using typing_prom.hyps(4) substitutivity(1)[OF typing_prom.prems]
      by (simp add: kinding_all_set, blast)
  next
    show "\<forall>c t b. (c,t,b)\<in>set (map (\<lambda>(c, t, b). (c, instantiate \<delta> t, b)) ts) \<longrightarrow> (\<exists>b'. (b' \<longrightarrow> b) \<and> (c, t, b') \<in> set (map (\<lambda>(c, t, b). (c, instantiate \<delta> t, b)) ts'))"
    proof clarsimp
      fix c t b
      assume "(c,t,b) \<in> set ts"
      then obtain b' where "b' \<longrightarrow> b" and "(c, t, b') \<in> set ts'"
        using typing_prom.hyps(6) by blast+
      moreover then have "(c, instantiate \<delta> t, b') \<in> (\<lambda>(c, t, b). (c, instantiate \<delta> t, b)) ` set ts'"
        by (metis (mono_tags) rev_image_eqI case_prod_conv)
      ultimately show "\<exists>b'. (b' \<longrightarrow> b) \<and> (c, instantiate \<delta> t, b') \<in> (\<lambda>(c, t, b). (c, instantiate \<delta> t, b)) ` set ts'"
        by blast
    qed
  qed simp+
  then show ?case
    by simp
next
  case (typing_esac \<Xi> K \<Gamma> x ts uu t)
  then show ?case
    by (force intro!: typing_typing_all.typing_esac
                simp: filter_map_map_filter_thd3_app2
                      typing_esac.hyps(3)[symmetric])+
qed (force intro!: typing_struct_instantiate
                   typing_typing_all.intros
           dest:   substitutivity
                   instantiate_ctx_split
                   instantiate_ctx_split_bang
                   instantiate_ctx_weaken
                   instantiate_ctx_consumed
           simp:   instantiate_ctx_def [where \<Gamma> = "[]", simplified]
                   map_update
           split:  prod.splits)+


fun expr_size :: "'f expr \<Rightarrow> nat" where
  "expr_size (Let a b) = Suc ((expr_size a) + (expr_size b))"
| "expr_size (LetBang vs a b) = Suc ((expr_size a) + (expr_size b))"
| "expr_size (Fun f ts) = Suc (expr_size f)"
| "expr_size (Unit) = 0"
| "expr_size (Member x f) = Suc (expr_size x)"
| "expr_size (Cast t x) = Suc (expr_size x)"
| "expr_size (Con c x ts) = Suc (expr_size ts)"
| "expr_size (App a b) = Suc ((expr_size a) + (expr_size b))"
| "expr_size (Prim p as) = Suc (sum_list (map expr_size as))"
| "expr_size (Var v) = 0"
| "expr_size (AFun v va) = 0"
| "expr_size (Promote v va) = Suc (expr_size va)"
| "expr_size (Struct v va) = Suc (sum_list ( map expr_size va))"
| "expr_size (Lit v) = 0"
| "expr_size (Tuple v va) = Suc ((expr_size v) + (expr_size va))"
| "expr_size (Put v va vb) = Suc ((expr_size v) + (expr_size vb))"
| "expr_size (Esac x) = Suc (expr_size x)"
| "expr_size (If x a b) = Suc ((expr_size x) + (expr_size a) + (expr_size b))"
| "expr_size (Split x y) = Suc ((expr_size x) + (expr_size y))"
| "expr_size (Case x v a b) = Suc ((expr_size x) + (expr_size a) + (expr_size b))"
| "expr_size (Take x f y) = Suc ((expr_size x) + (expr_size y))"

lemma specialise_size [simp]:
  shows "expr_size (specialise \<tau>s x) = expr_size x"
proof -
have "\<forall> as . (\<forall> x. x \<in> set as \<longrightarrow> expr_size (specialise \<tau>s x) = expr_size x) \<longrightarrow>
  sum_list (map (expr_size \<circ> specialise \<tau>s) as) = sum_list (map expr_size as)"
by (rule allI, induct_tac as, simp+)
then show ?thesis by (induct x rule: expr_size.induct, auto)
qed

end

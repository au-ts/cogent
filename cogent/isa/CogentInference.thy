theory CogentInference
  imports Util
begin


datatype num_type = U8 | U16 | U32 | U64

datatype prim_type = Num num_type | Bool (* | String *)
                                  
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


type_synonym name = string
type_synonym index = nat

datatype type = TVar index
              | TFun type type
              | TPrim prim_type
              | TProduct type type
              | TUnit
              | TUnknown index

datatype lit = LBool bool
             | LNat nat

fun abs :: "prim_type \<Rightarrow> nat" where
  "abs Bool = 2"
| "abs (Num U8) = 256"
| "abs (Num U16) = 512"
| "abs (Num U32) = 1024"
| "abs (Num U64) = 2048"

fun subst_ty :: "type list \<Rightarrow> type \<Rightarrow> type" where
  "subst_ty \<delta> (TVar i)       = \<delta> ! i"
| "subst_ty \<delta> (TFun a b)     = TFun (subst_ty \<delta> a) (subst_ty \<delta> b)"
| "subst_ty \<delta> (TPrim p)      = TPrim p"
| "subst_ty \<delta> (TProduct t u) = TProduct (subst_ty \<delta> t) (subst_ty \<delta> u)"
| "subst_ty \<delta> (TUnit)        = TUnit"
| "subst_ty \<delta> (TUnknown i)   = TUnknown i"


fun max_type_var :: "type \<Rightarrow> nat" where
  "max_type_var (TVar i)       = i"
| "max_type_var (TFun a b)     = max (max_type_var a) (max_type_var b)"
| "max_type_var (TPrim p)      = 0"
| "max_type_var (TProduct t u) = max (max_type_var t) (max_type_var u)"
| "max_type_var (TUnit)        = 0"
| "max_type_var (TUnknown i)   = 0"


datatype constraint =
  CtConj constraint constraint
  | CtIBound lit type
  | CtEq type type
  | CtSub type type
  | CtTop 
  | CtBot
  | CtShare type
  | CtDrop type

fun map_types_ct :: "(type \<Rightarrow> type) \<Rightarrow> constraint \<Rightarrow> constraint" where
  "map_types_ct f (CtConj a b)    = CtConj (map_types_ct f a) (map_types_ct f b)"
| "map_types_ct f (CtIBound l t)  = CtIBound l (f t)"
| "map_types_ct f (CtEq a b)      = CtEq (f a) (f b)"
| "map_types_ct f (CtSub a b)     = CtSub (f a) (f b)"
| "map_types_ct f (CtTop)         = CtTop"
| "map_types_ct f (CtBot)         = CtBot"
| "map_types_ct f (CtShare t)     = CtShare (f t)"
| "map_types_ct f (CtDrop t)      = CtDrop (f t)"

definition subst_ct :: "type list \<Rightarrow> constraint \<Rightarrow> constraint" where
  "subst_ct \<delta> \<equiv> map_types_ct (subst_ty \<delta>)"


locale type_infer =
  fixes type_of :: "'fnname \<Rightarrow> constraint \<times> type"
begin

datatype 'f expr = Var index
                 | TypeApp 'f "type list"
                 | Prim prim_op "'f expr list"
                 | App "'f expr" "'f expr"
                 | Unit
                 | Lit lit
                 | Cast num_type "'f expr"
                 | Let "'f expr" "'f expr"
                 | If "'f expr" "'f expr" "'f expr"
                 | Sig "'f expr" type

type_synonym cg_ctx = "(type \<times> nat) list"

type_synonym ctx = "(type option) list"
definition empty :: "nat \<Rightarrow> ctx" where
  "empty \<equiv> (\<lambda> x. replicate x None)"

definition singleton :: "nat \<Rightarrow> index \<Rightarrow> type \<Rightarrow> ctx" where
  "singleton n i t \<equiv> (empty n)[i := Some t]"

lemma singleton_len:
  "length (singleton n i t) = n"
  by (simp add: local.empty_def type_infer.singleton_def)

lemma singleton_some:
  "i < n \<Longrightarrow> (singleton n i t) ! i = Some t"
  by (simp add: type_infer.empty_def type_infer.singleton_def)

lemma singleton_none:
  "j < n \<Longrightarrow> j \<noteq> i \<Longrightarrow> (singleton n i t) ! j = None"
  by (simp add: type_infer.empty_def type_infer.singleton_def)

type_synonym axm_set = "constraint list"

section {* Algorithmic Context Join (Fig 3.5) *}
inductive alg_ctx_jn :: "cg_ctx \<Rightarrow> cg_ctx \<Rightarrow> cg_ctx \<Rightarrow> constraint \<Rightarrow> bool"
          ("_ \<Join> _ \<leadsto> _ | _" [30,0,0,30] 60) where
alg_ctx_jn: 
  "\<lbrakk> map fst G = map fst G'
   ; list_all3 (\<lambda>m g g'. m = max (snd g) (snd g')) M G G'
   ; list_all3 (\<lambda>g2 g m. g2 = (fst g, m)) G2 G M
   ; C = List.map2 (\<lambda>g g'. if (snd g) = (snd g') then CtTop else CtDrop (fst g)) G G'
   ; C2 = foldr CtConj C CtTop
   \<rbrakk> \<Longrightarrow> G \<Join> G' \<leadsto> G2 | C2"

lemma alg_ctx_jn_length:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
  shows "length G1 = length G1'"
   and  "length G1 = length G2"
  using assms
  by (metis (no_types, lifting) alg_ctx_jn.simps list_all3_conv_all_nth)+

lemma alg_ctx_jn_type_same:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
  shows "\<And>i. i < length G1 \<Longrightarrow> fst (G1 ! i) = fst (G2 ! i)"
  using assms
  by (clarsimp simp add: alg_ctx_jn.simps list_all3_conv_all_nth)

lemma alg_ctx_jn_type_used_nondec_1:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
  shows "\<And>i. i < length G1 \<Longrightarrow> snd (G1 ! i) \<le> snd (G2 ! i)"
  using assms
  by (clarsimp simp add: alg_ctx_jn.simps list_all3_conv_all_nth)

lemma alg_ctx_jn_type_used_nondec_2:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
  shows "\<And>i. i < length G1' \<Longrightarrow> snd (G1' ! i) \<le> snd (G2 ! i)"
  using assms
  by (clarsimp simp add: alg_ctx_jn.simps list_all3_conv_all_nth)

section {* Constraint Semantics (Fig 3.6) *}
inductive constraint_sem :: "axm_set \<Rightarrow> constraint \<Rightarrow> bool"
          ("_ \<turnstile> _" [40, 40] 60) where
ct_sem_asm:
  "C \<in> set A \<Longrightarrow> A \<turnstile> C"
| ct_sem_conj:
  "\<lbrakk> A \<turnstile> C1
   ; A \<turnstile> C2
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtConj C1 C2"
| ct_sem_int:
  "m < abs pt \<Longrightarrow> A \<turnstile> CtIBound (LNat m) (TPrim pt)"
| ct_sem_top:
  "A \<turnstile> CtTop"
| ct_sem_refl:
  "A \<turnstile> CtEq \<tau> \<tau>"
| ct_sem_equal:
  "A \<turnstile> CtEq \<tau> \<rho> \<Longrightarrow> A \<turnstile> CtSub \<tau> \<rho>"
| ct_sem_fun:
  "\<lbrakk> A \<turnstile> CtSub \<rho>1 \<tau>1 
   ; A \<turnstile> CtSub \<tau>2 \<rho>2
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtSub (TFun \<tau>1 \<tau>2) (TFun \<rho>1 \<rho>2)"
| ct_sem_funS:
  "A \<turnstile> CtShare (TFun \<tau>1 \<tau>2)"
| ct_sem_funD:
  "A \<turnstile> CtDrop (TFun \<tau>1 \<tau>2)"
| ct_sem_primS:
  "A \<turnstile> CtShare (TPrim pt)"
| ct_sem_primD:
  "A \<turnstile> CtDrop (TPrim pt)"

section {* Context relations (Fig 3.2) *}
inductive ctx_split_comp :: "axm_set \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> bool" where
  none  : "ctx_split_comp K None None None"
| left  : "ctx_split_comp K (Some \<tau>) (Some \<tau>) None"
| right : "ctx_split_comp K (Some \<tau>) None (Some \<tau>)"
| share : "\<lbrakk> A \<turnstile> CtShare \<tau> \<rbrakk> \<Longrightarrow> ctx_split_comp K (Some \<tau>) (Some \<tau>) (Some \<tau>)"

definition context_splitting :: "axm_set \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool"
           ("_ \<turnstile> _ \<leadsto> _ \<box> _" [30,0,0,30] 60) where
  "context_splitting K \<equiv> list_all3 (ctx_split_comp K)"

inductive weakening_comp :: "axm_set \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> bool" where
  none : "weakening_comp K None None"
| keep : "weakening_comp K (Some \<tau>) (Some \<tau>)"
| drop : "\<lbrakk> A \<turnstile> CtDrop \<tau> \<rbrakk> \<Longrightarrow> weakening_comp K (Some \<tau>) None"

definition weakening :: "axm_set \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool" 
           ("_ \<turnstile> _ \<leadsto>w _" [40,0,40] 60) where
  "weakening K \<equiv> list_all2 (weakening_comp K)"

section {* Typing Rules (Fig 3.3) *}
inductive typing :: "axm_set \<Rightarrow> ctx \<Rightarrow> 'fnname expr \<Rightarrow> type \<Rightarrow> bool"
          ("_ \<ddagger> _ \<turnstile> _ : _" [40,0,0,40] 60) where
typing_var:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i \<tau>
   ; i < length \<Gamma>
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> (Var i) : \<tau>"
| typing_sig:
  "A \<turnstile> CtSub \<tau>' \<tau> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> e : \<tau>' \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Sig e \<tau> : \<tau>" 
| typing_app:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : (TFun \<tau>1 \<tau>2)
   ; A \<ddagger> \<Gamma>2 \<turnstile> e2 : \<tau>1  
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> App e1 e2 : \<tau>2"
| typing_tapp:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto>w []
   ; (C, \<tau>) = type_of name
   ; A \<turnstile> subst_ct ts C
   ; \<tau>' = subst_ty ts \<tau>
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> TypeApp name ts : \<tau>'"
| typing_let:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : \<tau>1
   ; A \<ddagger> ((Some \<tau>2) # \<Gamma>2) \<turnstile> e2 : \<tau>2
  \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Let e1 e2 : \<tau>2"
| typing_if:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : TPrim Bool
   ; A \<ddagger> \<Gamma>2 \<turnstile> e2 : \<tau>
   ; A \<ddagger> \<Gamma>2 \<turnstile> e3 : \<tau>
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> If e1 e2 e3 : \<tau>"
| typing_iop:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; T \<noteq> TPrim Bool
   ; x \<in> {Plus nt, Minus nt, Times nt, Divide nt}
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : T
   ; A \<ddagger> \<Gamma>2 \<turnstile> e2 : T
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Prim x [e1, e2] : T"
| typing_cop:
  "\<lbrakk> T \<noteq> TPrim Bool
   ; x \<in> {Eq (Num nt), NEq (Num nt), Lt nt, Gt nt, Le nt, Ge nt}
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : T 
   ; A \<ddagger> \<Gamma>2 \<turnstile> e2 : T
   ; \<tau> = TPrim Bool
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Prim x [e1, e2]: \<tau>"
| typing_bop:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; x \<in> {BitAnd nt, BitOr nt}
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : TPrim Bool
   ; A \<ddagger> \<Gamma>2 \<turnstile> e2 : TPrim Bool
   ; \<tau> = TPrim Bool
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Prim x [e1, e2] : \<tau>"
| typing_ilit:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto>w []
   ; l < abs T
   ; \<tau> = TPrim T
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Lit (LNat l) : \<tau>"
| typing_blit:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto>w []
   ; \<tau> = TPrim Bool
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Lit (LBool l) : \<tau>"

section {* Elementary Constraint Generation Rules (Fig 3.4) *}
inductive constraint_gen_elab :: "cg_ctx \<Rightarrow> nat \<Rightarrow> 'fnname expr \<Rightarrow> type \<Rightarrow> cg_ctx \<Rightarrow> nat \<Rightarrow> constraint \<Rightarrow> 'fnname expr \<Rightarrow> bool"
  ("_,_ \<turnstile> _ : _ \<leadsto> _,_ | _ | _" [30,0,0,0,0,0,0,30] 60) where
cg_var1: 
  "\<lbrakk> G!i = (\<rho>,0)
   ; i < length G 
   ; G' = G[i := (\<rho>,1)] 
   ; C = CtSub \<rho> \<tau>
   \<rbrakk> \<Longrightarrow> G,n \<turnstile> Var i : \<tau> \<leadsto> G',n | C | Sig (Var i) \<tau>"
| cg_var2: 
  "\<lbrakk> G!i = (\<rho>,n) 
   ; i < length G
   ; n > 0 
   ; G' = G[i := (\<rho>,Suc n)] 
   ; C = CtConj (CtSub \<rho> \<tau>) (CtShare \<rho>) 
   \<rbrakk> \<Longrightarrow> G,n \<turnstile> Var i : \<tau> \<leadsto> G',n | C | Sig (Var i) \<tau>"
| cg_sig: 
  "\<lbrakk> G1,n1 \<turnstile> e : \<tau>' \<leadsto> G2,n2 | C | e'
   ; C' = CtConj C (CtSub \<tau>' \<tau>)
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> (Sig e \<tau>') : \<tau> \<leadsto> G2,n2 | C' | Sig (Sig e' \<tau>') \<tau>"
| cg_app:
  "\<lbrakk> \<alpha> = TUnknown (Suc n1)
   ; G1,(Suc n1) \<turnstile> e1 : TFun \<alpha> \<tau> \<leadsto> G2,n2 | C1 | e1'
   ; G2,n2 \<turnstile> e2 : \<alpha> \<leadsto> G3,n3 | C2 | e2'
   ; C3 = CtConj C1 C2
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> App e1 e2 : \<tau> \<leadsto> G3,n3 | C3 | Sig (App e1' e2') \<tau>"
| cg_let:
  "\<lbrakk> \<alpha> = TUnknown (Suc n1)
   ; G1,(Suc n1) \<turnstile> e1 : \<alpha> \<leadsto> G2,n2 | C1 | e1'
   ; ((\<alpha>, 0) # G2),n2 \<turnstile> e2 : \<tau> \<leadsto> ((\<alpha>, m) # G3),n3 | C2 | e2' 
   ; if m = 0 then C3 = CtDrop \<alpha> else C3 = CtTop
   ; C4 = CtConj (CtConj C1 C2) C3
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Let e1 e2 : \<tau> \<leadsto> G3,n3 | C4 | Sig (Let e1' e2') \<tau>"
| cg_blit:
  "C = CtEq \<tau> (TPrim Bool) \<Longrightarrow> G,n \<turnstile> Lit (LBool l) : \<tau> \<leadsto> G,n | C | Sig (Lit (Lbool l)) \<tau>"
| cg_ilit:
  "C = CtIBound (LNat m) \<tau> \<Longrightarrow> G,n \<turnstile> Lit (LNat m) : \<tau> \<leadsto> G,n | C | Sig (Lit (LNat m)) \<tau>"
| cg_if:
  "\<lbrakk> G1,n1 \<turnstile> e1 : (TPrim Bool) \<leadsto> G2,n2 | C1 | e1'
   ; G2,n2 \<turnstile> e2 : \<tau> \<leadsto> G3,n3 | C2 | e2'
   ; G2,n3 \<turnstile> e3 : \<tau> \<leadsto> G3',n4 | C3 | e3'
   ; G3 \<Join> G3' \<leadsto> G4 | C4 
   ; C5 = CtConj (CtConj (CtConj C1 C2) C3) C4
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> If e1 e2 e3 : \<tau> \<leadsto> G4,n4 | C5 | Sig (If e1' e2' e3') \<tau>"
| cg_iop:
  "\<lbrakk> x \<in> {Plus nt, Minus nt, Times nt, Divide nt}
   ; G1,n1 \<turnstile> e1 : \<tau> \<leadsto> G2,n2 | C1 | e1'
   ; G2,n2 \<turnstile> e2 : \<tau> \<leadsto> G3,n3 | C2 | e2'
   ; C5 = CtConj (CtConj (CtIBound (LNat 0) \<tau>) C1) C2
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Prim x [e1, e2] : \<tau> \<leadsto> G3,n3 | C5 | Sig (Prim x [e1', e2']) \<tau>"
| cg_cop:
  "\<lbrakk> \<alpha> = TUnknown (Suc n1)
   ; x \<in> {Eq (Num nt), NEq (Num nt), Lt nt, Gt nt, Le nt, Ge nt}
   ; G1,(Suc n1) \<turnstile> e1 : \<alpha> \<leadsto> G2,n2 | C1 | e1'
   ; G2,n2 \<turnstile> e2 : \<alpha> \<leadsto> G3,n3 | C2 | e2'
   ; C3 = CtConj (CtConj (CtConj (CtIBound (LNat 0) \<alpha>) (CtEq \<tau> (TPrim Bool))) C1) C2 
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Prim x [e1, e2] : \<tau> \<leadsto> G3,n3 | C3 | Sig (Prim x [e1', e2']) \<tau>"
| cg_bop:
  "\<lbrakk> x \<in> {BitAnd nt, BitOr nt}
   ; G1,n1 \<turnstile> e1 : \<tau> \<leadsto> G2,n2 | C1 | e1'
   ; G2,n2 \<turnstile> e2 : \<tau> \<leadsto> G3,n3 | C2 | e2'
   ; C3 = CtConj (CtConj (CtEq \<tau> (TPrim Bool)) C1) C2
  \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Prim x [e1, e2] : \<tau> \<leadsto> G3,n3 | C3 | Sig (Prim x [e1', e2']) \<tau>"
| cg_tapp:
  "\<lbrakk> (C, \<rho>) = type_of name
   (* make fresh unknown \<beta>s for each variable past those we are substituting into the type *)
   ; m = Suc (max_type_var \<rho>) - length ts
   ; \<beta>s = map (TUnknown \<circ> (+) (Suc n1)) [0..<m]
   ; \<rho>' = subst_ty (ts @ \<beta>s) \<rho>
   ; C' = subst_ct (ts @ \<beta>s) C
   ; C2 = CtConj (CtSub \<rho>' \<tau>) C'
   ; n' = n + m
   \<rbrakk> \<Longrightarrow> G,n \<turnstile> TypeApp name ts : \<tau> \<leadsto> G,n' | C2 | Sig (TypeApp name (ts @ \<beta>s)) \<tau>"

lemma cg_num_fresh_nondec:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
  shows "n \<le> n'"
  using assms
  by (induct rule: constraint_gen_elab.inducts) force+

lemma cg_ctx_length:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
  shows "length G = length G'"
  using assms
proof (induct rule: constraint_gen_elab.inducts)
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  then show ?case
    using type_infer.alg_ctx_jn_length(2) by auto
qed (simp+)

lemma cg_ctx_type_same:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
  shows "\<And>i. i < length G \<Longrightarrow> fst (G ! i) = fst (G' ! i)"
  using assms
proof (induct rule: constraint_gen_elab.inducts)
  case (cg_var1 G i \<rho> G' C \<tau> n)
  then show ?case
    by (metis fst_conv nth_list_update_eq nth_list_update_neq)
next
  case (cg_var2 G i \<rho> n G' C \<tau>)
  then show ?case
    by (metis length_list_update map_fst_update nth_map)
next
  case (cg_let \<alpha> n1 G1 e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4)
  then show ?case
    by (metis Suc_mono cg_ctx_length length_Cons nth_Cons_Suc)
next
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  then show ?case
    using cg_ctx_length type_infer.alg_ctx_jn_type_same by auto
next
qed (auto simp add: cg_ctx_length)+

lemma cg_ctx_type_used_nondec:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
    and "i < length G"
  shows "snd (G ! i) \<le> snd (G' ! i)"
  using assms
proof (induct arbitrary: i rule: constraint_gen_elab.induct)
case (cg_var1 G i \<rho> G' C \<tau> n)
  then show ?case
    by (metis le0 nth_list_update_neq order_refl snd_conv) 
next
  case (cg_var2 G i \<rho> n G' C \<tau>)
  then show ?case
    by (metis Suc_n_not_le_n nat_le_linear nth_list_update_eq nth_list_update_neq snd_conv)
next
  case (cg_app \<alpha> n1 G1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  then show ?case
    using cg_ctx_length by fastforce
next
  case (cg_let \<alpha> n1 G1 e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4)
  then show ?case
  proof -
    have "(\<And>i. i < length ((\<alpha>, 0) # G2) \<Longrightarrow> snd (((\<alpha>, 0) # G2) ! i) \<le> snd (((\<alpha>, m) # G3) ! i))
                 \<Longrightarrow> (\<And>i. i < length G2 \<Longrightarrow> snd (G2 ! i) \<le> snd (G3 ! i))"
      using nth_Cons_Suc by force
    then show ?thesis
      using cg_let.prems cg_let.hyps cg_ctx_length le_trans
      by fastforce
  qed
next
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  then show ?case
    using cg_ctx_length alg_ctx_jn_type_used_nondec_1 le_trans
    by fastforce
next
  case (cg_iop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C5)
  then show ?case
    using cg_ctx_length by (metis dec_induct le_SucI)
next
case (cg_cop \<alpha> n1 x nt G1 e1 G2 n2 C1 e1' e2 G3 n3 C2 e2' C3 \<tau>)
  then show ?case
    using cg_ctx_length le_trans by fastforce
next
  case (cg_bop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  then show ?case
    using cg_ctx_length by fastforce
qed (blast)+

section {* Assignment Definition *}
(* when we are assigning an unknown type a type, the assigned type should not contain any
   unknown types itself *)
inductive is_known_type :: "type \<Rightarrow> bool" where
known_tvar:
  "is_known_type (TVar n)"
| known_tfun:
  "\<lbrakk> is_known_type t1
   ; is_known_type t2
   \<rbrakk> \<Longrightarrow> is_known_type (TFun t1 t2)"
| known_tprim:
  "is_known_type (TPrim pt)"
| known_tproduct:
  "\<lbrakk> is_known_type t1
   ; is_known_type t2
   \<rbrakk> \<Longrightarrow> is_known_type (TProduct t1 t2)"
| known_tunit:
  "is_known_type TUnit"

fun assign_app_ty :: "(nat \<Rightarrow> type) \<Rightarrow> type \<Rightarrow> type" where
  "assign_app_ty S (TVar n)          = TVar n"
| "assign_app_ty S (TFun t1 t2)      = TFun (assign_app_ty S t1) (assign_app_ty S t2)"
| "assign_app_ty S (TPrim pt)        = TPrim pt"
| "assign_app_ty S (TProduct t1 t2)  = TProduct (assign_app_ty S t1) (assign_app_ty S t2)"
| "assign_app_ty S TUnit             = TUnit"
| "assign_app_ty S (TUnknown n)      = S n"

fun assign_app_expr :: "(nat \<Rightarrow> type) \<Rightarrow> 'f expr \<Rightarrow> 'f expr" where
  "assign_app_expr S (Var n)            = Var n" 
| "assign_app_expr S (TypeApp e ts)     = TypeApp e (map (assign_app_ty S) ts)"
| "assign_app_expr S (Prim prim_op ts)  = Prim prim_op (map (assign_app_expr S) ts)"
| "assign_app_expr S (App e1 e2)        = App (assign_app_expr S e1) (assign_app_expr S e2)"
| "assign_app_expr S Unit               = Unit"
| "assign_app_expr S (Lit l)            = Lit l"
| "assign_app_expr S (Cast nt e)        = Cast nt (assign_app_expr S e)"
| "assign_app_expr S (Let e1 e2)        = Let (assign_app_expr S e1) (assign_app_expr S e2)"
| "assign_app_expr S (If e1 e2 e3)      = If (assign_app_expr S e1) (assign_app_expr S e2) (assign_app_expr S e3)"
| "assign_app_expr S (Sig e t)          = Sig (assign_app_expr S e) (assign_app_ty S t)"

fun "assign_app_constr" :: "(nat \<Rightarrow> type) \<Rightarrow> constraint \<Rightarrow> constraint" where
  "assign_app_constr S (CtConj c1 c2) = CtConj (assign_app_constr S c1) (assign_app_constr S c2)"
| "assign_app_constr S (CtIBound l t) = CtIBound l (assign_app_ty S t)"
| "assign_app_constr S (CtEq t1 t2) = CtEq (assign_app_ty S t1) (assign_app_ty S t2)"
| "assign_app_constr S (CtSub t1 t2) = CtSub (assign_app_ty S t1) (assign_app_ty S t2)"
| "assign_app_constr S CtTop = CtTop"
| "assign_app_constr S CtBot = CtBot"
| "assign_app_constr S (CtShare t) = CtShare (assign_app_ty S t)"
| "assign_app_constr S (CtDrop t) = CtDrop (assign_app_ty S t)"

fun "assign_app_ctx" :: "(nat \<Rightarrow> type) \<Rightarrow> ctx \<Rightarrow> ctx" where
  "assign_app_ctx S G = map (\<lambda>x. if x = None then None else Some (assign_app_ty S (the x))) G"

lemma assign_app_ctx_nth:
  "\<And>i. i < length G \<Longrightarrow> 
   (assign_app_ctx S G) ! i = (\<lambda>x. if x = None then None else Some (assign_app_ty S (the x))) (G ! i)"
  by simp

section {* split_used (Lemma 3.1) *}
(* Free Variables *)
fun fv' :: "nat \<Rightarrow> 'f expr \<Rightarrow> index set" where
  "fv' n (Var i) = (if i \<ge> n then {i} else {})"
| "fv' n (TypeApp f ts) = {}"
| "fv' n (Prim prim_op es) = fold (\<lambda>x y. (fv' n x) \<union> y) es {}"
| "fv' n (App e1 e2) = (fv' n e1) \<union> (fv' n e2)"
| "fv' n Unit = {}"
| "fv' n (Lit l) = {}"
| "fv' n (Cast nt e) = fv' n e"
| "fv' n (Let e1 e2) = (fv' n e1) \<union> (fv' (Suc n) e2)"
| "fv' n (If e1 e2 e3) = (fv' n e1) \<union> (fv' n e2) \<union> (fv' n e3)"
| "fv' n (Sig e t) = fv' n e"

abbreviation fv :: "'s expr \<Rightarrow> index set" where
  "fv t \<equiv> fv' 0 t" 

fun range :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "range m 0 = []"
| "range m (Suc n) = (if m \<ge> (Suc n) then [] else (range m n) @ [n])"

lemma range_length:
  "length (range m n) = (if m \<ge> n then 0 else (n - m))"
proof (induct n arbitrary: m)
  case (Suc n)
  then show ?case
    by (case_tac "m \<ge> (Suc n)"; simp add: Suc_diff_le)
qed (simp)

lemma range_elem:
  assumes "n > m"
    and "i < n - m"
  shows "(range m n) ! i = m + i"
  using assms
proof (induct n arbitrary: i m)
  case (Suc n)
  then show ?case
  proof (case_tac "i = n - m")
    show "i = n - m \<Longrightarrow> local.range m (Suc n) ! i = m + i"
      using type_infer.range.simps type_infer.range_length
      by (metis Suc.prems(1) diff_is_0_eq' le_add_diff_inverse less_Suc_eq_le not_less nth_append_length)
    have "i < Suc n - m \<Longrightarrow> i \<noteq> n - m \<Longrightarrow> i < n -m "
      using range_length
      by (simp add: less_diff_conv nth_append)
    then show "i < Suc n - m \<Longrightarrow> i \<noteq> n - m \<Longrightarrow> range m (Suc n) ! i = m + i"
      using assms
      using range.simps range_length
      by (metis Suc.hyps Suc.prems(1) add.commute le_less_Suc_eq less_diff_conv not_add_less1 not_less nth_append)
  qed
qed (simp)

fun ctx_restrict :: "cg_ctx \<Rightarrow> index set \<Rightarrow> ctx" (infixr "\<bar>" 60) where
"(G\<bar>ns) = map2 (\<lambda>g i. (if i \<in> ns then Some (fst g) else None)) G (range 0 (length G))"

lemma ctx_restrict_len:
  "length (G\<bar>ns) = length G"
proof -
  have "length (G\<bar>ns) = min (length G) (length (range 0 (length G)))"
    using map2_conv_all_nth by auto
  then show ?thesis
    using range_length by auto
qed

lemma ctx_restrict_nth_none:
  assumes "i \<notin> ns"
    and "i < length G"
  shows "(G\<bar>ns)!i = None"
  using assms
proof -
  let ?P="\<lambda>g i. (if i \<in> ns then Some (fst g) else None)"
  let ?r="range 0 (length G)"
  have "G\<bar>ns = map2 ?P G ?r"
    by simp
  moreover have "\<forall>i < length (G\<bar>ns). ?P (G ! i) (?r ! i) = ((G\<bar>ns) ! i)"
    by (rule_tac xs="G" in map2_imp_proj_nth; simp)
  then show ?thesis
    using assms
    using range_elem ctx_restrict_len
    by (metis add.left_neutral diff_zero gr_implies_not_zero neq0_conv)
qed
     
lemma ctx_restrict_nth_some:
  assumes "i \<in> ns"
    and "i < length G"
  shows "(G\<bar>ns)!i = Some (fst (G ! i))"
  using assms
proof -
  let ?P="\<lambda>g i. (if i \<in> ns then Some (fst g) else None)"
  let ?r="range 0 (length G)"
  have "G\<bar>ns = map2 ?P G ?r"
    by simp
  moreover have "\<forall>i < length (G\<bar>ns). ?P (G ! i) (?r ! i) = ((G\<bar>ns) ! i)"
    by (rule_tac xs="G" in map2_imp_proj_nth; simp)
  then show ?thesis
    using assms
    using range_elem ctx_restrict_len
    by (metis add.left_neutral diff_zero gr_implies_not_zero neq0_conv)
qed

lemma ctx_restrict_empty:
  "(G\<bar>{}) = empty (length G)"
proof -
  have "\<And>i. i < length G \<Longrightarrow> (G\<bar>{})!i = None"
    using ctx_restrict_nth_none by blast
  then show ?thesis
    using ctx_restrict_len empty_def
    by (metis length_replicate list_eq_iff_nth_eq nth_replicate)
qed
section {* Soundness of Generation (Thm 3.2) *}
lemma cg_sound:
  assumes "G,0 \<turnstile> e : \<tau> \<leadsto> G',n | C | e'"
    and "A \<turnstile> assign_app_constr S C" 
    and "\<forall>i. is_known_type (S i)" 
    and "\<Gamma> = map (\<lambda> (\<rho>, n). if n = 0 then None else Some \<rho>) G"
  shows "A \<ddagger> \<Gamma> \<turnstile> (assign_app_expr S e') : (assign_app_ty S \<tau>)"
  using assms
proof -
  sorry

end
end                            
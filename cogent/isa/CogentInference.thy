theory CogentInference
  imports Util
begin


datatype num_type = U8 | U16 | U32 | U64

datatype prim_type = Num num_type | Bool | String
                                  
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
                 | SLit string
                 | Cast num_type "'f expr"
                 | Let "'f expr" "'f expr"
                 | If "'f expr" "'f expr" "'f expr"
                 | Sig "'f expr" type

type_synonym cg_ctx = "(type \<times> nat) list"

inductive alg_ctx_jn :: "cg_ctx \<Rightarrow> cg_ctx \<Rightarrow> cg_ctx \<Rightarrow> constraint \<Rightarrow> bool"
            ("_ \<Join> _ \<leadsto> _ | _" [30,0,0,30] 60) where
  alg_ctx_jn: 
  "\<lbrakk> map fst G = map fst G'
   ; list_all3 (\<lambda>m g g'. m = max (snd g) (snd g')) m G G'
   ; list_all3 (\<lambda>g2 g m. g2 = (fst g, m)) G2 G M
   ; C = List.map2 (\<lambda>g g'. if (snd g) = (snd g') then CtTop else CtDrop (fst g)) G G'
   ; C2 = foldr CtConj C CtTop
   \<rbrakk> \<Longrightarrow> G \<Join> G' \<leadsto> G2 | C2"


inductive constraint_gen :: "cg_ctx \<Rightarrow> nat \<Rightarrow> 'fnname expr \<Rightarrow> type \<Rightarrow> cg_ctx \<Rightarrow> nat \<Rightarrow> constraint \<Rightarrow> bool"
            ("_,_ \<turnstile> _ : _ \<leadsto> _,_ | _" [30,0,0,0,0,0,30] 60) where
  cg_var1: 
  "\<lbrakk> G!i = (\<rho>,0) 
   ; G' = G[i := (\<rho>,1)] 
   ; C = CtSub \<rho> \<tau>
   \<rbrakk> \<Longrightarrow> G,n \<turnstile> Var i : \<tau> \<leadsto> G',n | C"
| cg_var2: 
  "\<lbrakk> G!i = (\<rho>,n) 
   ; n > 0 
   ; G' = G[i := (\<rho>,Suc n)] 
   ; C = CtConj (CtSub \<rho> \<tau>) (CtShare \<rho>) 
   \<rbrakk> \<Longrightarrow> G,n \<turnstile> Var i : \<tau> \<leadsto> G',n | C"
| cg_sig: 
  "\<lbrakk> G1,n1 \<turnstile> e : \<tau>' \<leadsto> G2,n2 | C 
   ; C' = CtConj C (CtSub \<tau>' \<tau>)
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> (Sig e \<tau>') : \<tau> \<leadsto> G2,n2 | C'"
| cg_app:
  "\<lbrakk> \<alpha> = TUnknown (Suc n1)
   ; G1,(Suc n1) \<turnstile> e1 : TFun \<alpha> \<tau> \<leadsto> G2,n2 | C1
   ; G2,n2 \<turnstile> e2 : \<alpha> \<leadsto> G3,n3 | C2
   ; C3 = CtConj C1 C2
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> App e1 e2 : \<tau> \<leadsto> G3,n3 | C3"
| cg_let:
  "\<lbrakk> \<alpha> = TUnknown (Suc n1)
   ; G1,(Suc n1) \<turnstile> e1 : \<alpha> \<leadsto> G2,n2 | C1
   ; ((\<alpha>, 0) # G2),n2 \<turnstile> e2 : \<tau> \<leadsto> ((\<alpha>, m) # G3),n3 | C2 
   ; if m = 0 then C3 = CtDrop \<alpha> else C3 = CtTop
   ; C4 = CtConj (CtConj C1 C2) C3
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Let e1 e2 : \<tau> \<leadsto> G3,n3 | C4"
| cg_blit:
  "C = CtEq \<tau> (TPrim Bool) \<Longrightarrow> G,n \<turnstile> Lit (LBool l) : \<tau> \<leadsto> G,n | C"
| cg_ilit:
  "C = CtIBound (LNat m) \<tau> \<Longrightarrow> G,n \<turnstile> Lit (LNat m) : \<tau> \<leadsto> G,n | C"
| cg_if:
  "\<lbrakk> G1,n1 \<turnstile> e1 : (TPrim Bool) \<leadsto> G2,n2 | C1
   ; G2,n2 \<turnstile> e2 : \<tau> \<leadsto> G3,n3 | C2
   ; G2,n3 \<turnstile> e3 : \<tau> \<leadsto> G3',n4 | C3
   ; G3 \<Join> G3' \<leadsto> G4 | C4 
   ; C5 = CtConj (CtConj (CtConj C1 C2) C3) C4
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> If e1 e2 e3 : \<tau> \<leadsto> G4,n4 | C5"
| cg_iop:
  "\<lbrakk> e \<in> {Prim (Plus nt), Prim (Minus nt), Prim (Times nt), Prim (Divides nt)}
   ; G1,n1 \<turnstile> e1 : \<tau> \<leadsto> G2,n2 | C1
   ; G2,n2 \<turnstile> e2 : \<tau> \<leadsto> G3,n3 | C2
   ; C5 = CtConj (CtConj (CtIBound (LNat 0) \<tau>) C1) C2
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> e [e1, e2] : \<tau> \<leadsto> G3,n3 | C5"
| cg_cop:
  "\<lbrakk> \<alpha> = TUnknown (Suc n1)
   ; e \<in> {Prim (Eq (Num nt)), Prim (NEq (Num nt)), Prim (Lt nt), Prim (Gt nt), Prim (Le nt), Prim (Ge nt)}
   ; G1,(Suc n1) \<turnstile> e1 : \<alpha> \<leadsto> G2,n2 | C1
   ; G2,n2 \<turnstile> e2 : \<alpha> \<leadsto> G3,n3 | C2
   ; C3 = CtConj (CtConj (CtConj (CtIBound (LNat 0) \<alpha>) (CtEq \<tau> (TPrim Bool))) C1) C2 
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> e [e1, e2] : \<tau> \<leadsto> G3,n3 | C3"
| cg_bop:
  "\<lbrakk> e \<in> {Prim (BitAnd nt), Prim (BitOr nt)}
   ; G1,n1 \<turnstile> e1 : \<tau> \<leadsto> G2,n2 | C1
   ; G2,n2 \<turnstile> e2 : \<tau> \<leadsto> G3,n3 | C2 
   ; C3 = CtConj (CtConj (CtEq \<tau> (TPrim Bool)) C1) C2
  \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> e [e1, e2] : \<tau> \<leadsto> G3,n3 | C3"
| cg_tapp:
  "\<lbrakk> (C, \<rho>) = type_of name
   (* make fresh unknown \<beta>s for each variable past those we are substituting into the type *)
   ; m = Suc (max_type_var \<rho>) - length ts
   ; \<beta>s = map (TUnknown \<circ> (+) (Suc n1)) [0..<m]
   ; \<rho>' = subst_ty (ts @ \<beta>s) \<rho>
   ; C' = subst_ct (ts @ \<beta>s) C
   ; C2 = CtConj (CtSub \<rho>' \<tau>) C'
   ; n' = n + m
   \<rbrakk> \<Longrightarrow> G,n \<turnstile> TypeApp name ts : \<tau> \<leadsto> G,n' | C2"

lemma
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C"
  shows "n \<ge> n'"
  using assms
proof (induct rule: constraint_gen.inducts)
case (cg_var1 G i \<rho> G' C \<tau> n)
  then show ?case sorry
next
  case (cg_var2 G i \<rho> n G' C \<tau>)
  then show ?case sorry
next
  case (cg_sig G1 n1 e \<tau>' G2 n2 C C' \<tau>)
  then show ?case sorry
next
  case (cg_app \<alpha> n1 G1 e1 \<tau> G2 n2 C1 e2 G3 n3 C2 C3)
  then show ?case sorry
next
  case (cg_let \<alpha> n1 G1 e1 G2 n2 C1 e2 \<tau> m G3 n3 C2 C3 C4)
  then show ?case sorry
next
  case (cg_blit C \<tau> G n l)
  then show ?case sorry
next
  case (cg_ilit C m \<tau> G n)
  then show ?case sorry
next
  case (cg_if G1 n1 e1 G2 n2 C1 e2 \<tau> G3 n3 C2 e3 G3' n4 C3 G4 C4 C5)
  then show ?case sorry
next
  case (cg_iop e nt Divides G1 n1 e1 \<tau> G2 n2 C1 e2 G3 n3 C2 C5)
  then show ?case sorry
next
  case (cg_cop \<alpha> n1 e nt G1 e1 G2 n2 C1 e2 G3 n3 C2 C3 \<tau>)
  then show ?case sorry
next
  case (cg_bop e nt G1 n1 e1 \<tau> G2 n2 C1 e2 G3 n3 C2 C3)
  then show ?case sorry
next
case (cg_tapp C \<rho> name m ts \<beta>s n1 \<rho>' C' C2 \<tau> n' n G)
  then show ?case sorry
qed

end
end                            
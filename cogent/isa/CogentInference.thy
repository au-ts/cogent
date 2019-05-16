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
              | TVarBang index
              | TFun type type
              | TPrim prim_type
              | TProduct type type
              | TUnit
              | TUnknown index

datatype lit = LBool bool
             | LNat nat


datatype 'f expr = Var index
                 | AFun 'f  "type list"
                 | Fun "'f expr" "type list"
                 | Prim prim_op "'f expr list"
                 | App "'f expr" "'f expr"
                 | Unit
                 | Lit lit
                 | SLit string
                 | Cast num_type "'f expr"
                 | Let "'f expr" "'f expr"
                 | If "'f expr" "'f expr" "'f expr"
                 | Sig "'f expr" type

datatype constraint =
  CtConj constraint constraint
  | CtIBound lit type
  | CtEq type type
  | CtSub type type
  | CtTop 
  | CtBot
  | CtShare type
  | CtDrop type

type_synonym cg_ctx = "(type \<times> nat) list"

inductive alg_ctx_jn :: "cg_ctx \<Rightarrow> nat \<Rightarrow> cg_ctx \<Rightarrow> nat \<Rightarrow> cg_ctx \<Rightarrow> nat \<Rightarrow> constraint \<Rightarrow> bool"
            ("_,_ \<Join> _,_ \<leadsto> _,_ | _" [30,0,0,0,0,0,30] 60) where
  "\<lbrakk> \<And>i. i < length G
   ; length G = length G'
   ; fst (G!i) = fst (G'!i)
   ; m!i = max (snd (G!i)) (snd (G'!i)) 
   ; G2!i = (fst (G!i), (m!i))
   ; if (snd (G!i)) = (snd (G'!i)) then (C!i) = CtTop else (C!i) = CtDrop (fst (G!i))
   ; C2 = foldr CtConj C CtTop
   \<rbrakk> \<Longrightarrow> G,n \<Join> G',n \<leadsto> G2,n | C2"

inductive constraint_gen :: "cg_ctx \<Rightarrow> nat \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> cg_ctx \<Rightarrow> nat \<Rightarrow> constraint \<Rightarrow> bool"
            ("_,_ \<turnstile> _ : _ \<leadsto> _,_ | _" [30,0,0,0,0,0,30] 60) where
  cg_var1: "G!i = (\<rho>,0) \<Longrightarrow> G' = G[i := (\<rho>,1)] \<Longrightarrow> G,n \<turnstile> Var i : \<tau> \<leadsto> G',n | CtSub \<rho> \<tau>"
| cg_var2: "G!i = (\<rho>,n) \<Longrightarrow> n > 0 \<Longrightarrow> G' = G[i := (\<rho>,Suc n)] \<Longrightarrow> C = CtConj (CtSub \<rho> \<tau>) (CtShare \<rho>) \<Longrightarrow> G,n \<turnstile> Var i : \<tau> \<leadsto> G',n | C"
| cg_sig: "G1,n \<turnstile> e : \<tau>' \<leadsto> G2,n | C \<Longrightarrow> C' = CtConj C (CtSub \<tau>' \<tau>) \<Longrightarrow> G1,n \<turnstile> (Sig e \<tau>') : \<tau> \<leadsto> G2,n | C'"
| cg_app:
  "\<lbrakk> G1,Suc n \<turnstile> e1 : TFun (TUnknown (Suc n)) \<tau> \<leadsto> G2,n1 | C1
   ; G2,n2 \<turnstile> e2 : TUnknown (Suc n) \<leadsto> G3,n3 | C2
   ; C3 = CtConj C1 C2
   \<rbrakk> \<Longrightarrow> G1,n \<turnstile> App e1 e2 : \<tau> \<leadsto> G3,n3 | C3"
| cg_let:
  "\<lbrakk> G1,Suc n \<turnstile> e1 : TUnknown (Suc n) \<leadsto> G2,n1 | C1
   ; (TUnknown (Suc n), 0) # G2,n1 \<turnstile> e2 : \<tau> \<leadsto> (TUnknown (Suc n), m) # G3 , n2 | C2 
   ; if m = 0 then C3 = CtDrop (TUnknown (Suc n)) else C3 = CtTop
   ; C4 = CtConj (CtConj C1 C2) C3
   \<rbrakk> \<Longrightarrow> G1, n \<turnstile> Let e1 e2 : \<tau> \<leadsto> G3, n2 | C4"
| cg_blit:
  "C = CtEq \<tau> (TPrim Bool) \<Longrightarrow> G,n \<turnstile> Lit (LBool l) : \<tau> \<leadsto> G,n | C"
| cg_ilit:
  "C = CtIBound (LNat m) \<tau> \<Longrightarrow> G,n \<turnstile> Lit (LNat m) : \<tau> \<leadsto> G,n | C"
| cg_if:
  "\<lbrakk> G1,n \<turnstile> e1 : (TPrim Bool) \<leadsto> G2,n | C1
   ; G2,n \<turnstile> e2 : \<tau> \<leadsto> G3,n | C2
   ; G2,n \<turnstile> e3 : \<tau>  \<leadsto> G'3,n | C3
   ; G3,n \<Join> G'3,n \<leadsto> G4,n | C4 
   ; C5 = CtConj (CtConj (CtConj C1 C2) C3) C4
   \<rbrakk> \<Longrightarrow> G1,n \<turnstile> If e1 e2 e3 : \<tau> \<leadsto> G4,n | C5"
end
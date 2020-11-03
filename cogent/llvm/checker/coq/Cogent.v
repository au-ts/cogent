From Coq Require Import List String ZArith.

Import ListNotations.

Variant PrimInt : Set :=
  | U8
  | U16
  | U32
  | U64
  | Boolean.

Variant Sigil : Set :=
  | Boxed (r:bool)
  | Unboxed.

Inductive type : Set :=
  | TPrim (p:PrimInt)
  | TUnit
  | TString
  | TFun (t:type) (rt:type)
  | TRecord (fs:list (string * (type * bool))) (s:Sigil) (* Ignore RecursiveParameter, DataLayout *)
  | TSum (vs:list (string * (type * bool)))
  | TCon (tn:string) (ts:list type) (s:Sigil).

Variant Operator : Set :=
  | Plus | Minus | Times | Divide | Mod
  | Not | And | Or
  | Gt | Lt | Le | Ge | Eq | NEq
  | BitAnd | BitOr | BitXor | LShift | RShift | Complement.

Inductive expr : Set :=
  | Var (n:nat * string)
  | Fun (fn:string) (ts:list type) (* Ignore DataLayout, FunNote *)
  | Op (o:Operator) (os:list expr)
  | App (f:expr) (a:expr)
  | Con (tn:string) (e:expr) (t:type)
  | Unit 
  | ILit (i:Z)
  | SLit (s:string)
  | Let (v:string) (e:expr) (b:expr)
  | LetBang (vs:list (nat * string)) (v:string) (e:expr) (b:expr)
  | Struct (fs:list (string * expr))
  | If (c:expr) (b1:expr) (b2:expr)
  | Case (e:expr) (tn:string) (b1:string * expr) (b2:string * expr) (* Ignore Likelihood *)
  | Esac (e:expr)
  | Member (e:expr) (i:Z)
  | Take (vs:string * string) (e:expr) (i:Z) (b:expr)
  | Put (e:expr) (i:Z) (v:expr)
  | Promote (t:type) (e:expr)
  | Cast (t:type) (e:expr).

Variant definition : Set :=
  | FunDef (fn:string) (t:type) (rt:type) (b:expr) (* Ignore Attr, TyVarName, Kind, DLVarName *)
  | AbsDecl (fn:string) (t:type) (rt:type) (* Ignore Attr, TyVarName, Kind, DLVarName *)
  | TypeDef (tn:string) (tv:list string) (t:option type).

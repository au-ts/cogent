From Coq Require Import List ListSet String ZArith.

Definition name := string.

Definition index := nat.

Definition field := nat.

Variant num_type : Set := U8 | U16 | U32 | U64.

Variant prim_type : Set := Num (n:num_type) | Bool | String.

Variant prim_op : Set :=
  | Plus (t:num_type)
  | Minus (t:num_type)
  | Times (t:num_type)
  | Divide (t:num_type)
  | Mod (t:num_type)
  | Not | And | Or
  | Gt (t:num_type)
  | Lt (t:num_type)
  | Le (t:num_type)
  | Ge (t:num_type)
  | Eq (t:prim_type)
  | NEq (t:prim_type)
  | BitAnd (t:num_type)
  | BitOr (t:num_type)
  | BitXor (t:num_type)
  | LShift (t:num_type)
  | RShift (t:num_type)
  | Complement (t:num_type).

Variant sigil : Set :=
  | Boxed (* Ignore access_perm, ptr_layout *)
  | Unboxed.

Variant variant_state : Set := Checked | Unchecked.
Variant record_state : Set := Taken | Present.

Inductive type : Set :=
  | TVar (i:index)
  | TVarBang (i:index)
  | TCon (n:name) (ts:list type) (s:sigil)
  | TFun (t:type) (rt:type)
  | TPrim (t:prim_type)
  | TSum (vs:list (name * (type * variant_state)))
  (* | TProduct (t1:type) (t2:type) *)
  | TRecord (fs:list (name * (type * record_state))) (s:sigil)
  | TUnit.

Variant lit : Set :=
  | LBool (b:bool)
  | LU8 (w:Z)
  | LU16 (w:Z)
  | LU32 (w:Z)
  | LU64 (w:Z).
(* NOTE: not represented as n-bit words *)

Inductive expr : Type :=
  | Var (i:index)
  (* | AFun (funtyp:'f)  (ts:list type) *)
  | Fun (f:expr) (ts:list type) 
  | Prim (op:prim_op) (os:list expr)
  | App (f:expr) (a:expr)
  | Con (ts:list (name * type * variant_state)) (n:name) (e:expr)
  | Struct (ts:list type) (es:list expr)
  | Member (e:expr) (f:field)
  | Unit
  | Lit (l:lit)
  | SLit (s:string)
  | Cast (t:num_type) (e:expr)
  (* | Tuple (e1:expr) (e2:expr) *)
  | Put (e:expr) (f:field) (v:expr)
  | Let (e:expr) (b:expr)
  | LetBang (is:set index) (e:expr) (b:expr)
  | Case (e:expr) (n:name) (b1:expr) (b2:expr)
  | Esac (e:expr) (n:name)
  | If (c:expr) (b1:expr) (b2:expr)
  | Take (e:expr) (f:field) (b:expr)
  (* | Split (e1:expr) (e2:expr) *)
  | Promote (t:type) (e:expr).

(* Pretty AST Notation *)

Import ListNotations.

Declare Scope cogent_scope.

Notation "x `+ y" := (Prim (Plus U32) [x; y]) (at level 50) : cogent_scope.
Notation "x `- y" := (Prim (Minus U32) [x; y]) (at level 50) : cogent_scope.
Notation "x `* y" := (Prim (Times U32) [x; y]) (at level 25) : cogent_scope.
Notation "x `/ y" := (Prim (Divide U32) [x; y]) (at level 25) : cogent_scope.
Notation "x `% y" := (Prim (Mod U32) [x; y]) (at level 25) : cogent_scope.
Notation "` n" := (Lit (LU32 n)) (at level 0) : cogent_scope.

From Coq Require Import List ListSet String ZArith.

From ExtLib Require Import Structures.Monads.
From ITree Require Import ITree.
From Vellvm Require Import Util.

Import Monads.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

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

Variant def : Type :=
  | FunDef (n:name) (t:type) (rt:type) (b:expr).
  (* AbsDecl, TypeDef *)

Definition prim_lbool (l:lit) : bool :=
  match l with
  | LBool b => b
  | _ => false
  end.

Definition default := LBool false.

Definition prim_word_op (f:Z -> Z -> Z) (xs:list lit) : lit :=
  match (firstn 2 xs) with
  | [LU8 x; LU8 y] => LU8 (f x y)
  | [LU16 x; LU16 y] => LU16 (f x y)
  | [LU32 x; LU32 y] => LU32 (f x y)
  | [LU64 x; LU64 y] => LU64 (f x y)
  | _ => default
  end.

Definition prim_word_comp (f:Z -> Z -> bool) (xs:list lit) : lit :=
  match (firstn 2 xs) with
  | [LU8 x; LU8 y] => LBool (f x y)
  | [LU16 x; LU16 y] => LBool (f x y)
  | [LU32 x; LU32 y] => LBool (f x y)
  | [LU64 x; LU64 y] => LBool (f x y)
  | _ => default
  end.

Definition eval_prim_op (op:prim_op) (xs:list lit) : lit :=
  match op with
  | Plus _ => prim_word_op Z.add xs
  | Minus _ => prim_word_op Z.sub xs
  | Times _ => prim_word_op Z.mul xs
  | Divide _ => prim_word_op Z.div xs
  | Mod _ => prim_word_op Z.modulo xs
  (* | Not = LBool (negb (prim_lbool (hd default xs)))
  | And = LBool (prim_lbool (hd xs) && prim_lbool (xs ! 1))
  | Or = LBool (prim_lbool (hd xs) || prim_lbool (xs ! 1))
  | Eq _ = LBool (hd xs = xs ! 1)
  | NEq _ = LBool (hd xs \<noteq> xs ! 1)
  | (Gt _) = prim_word_comp (>) xs
  | (Lt _) = prim_word_comp (<) xs
  | (Le _) = prim_word_comp (<=) xs
  | (Ge _) = prim_word_comp (>=) xs
  | (BitAnd _) = prim_word_op bitAND bitAND bitAND bitAND xs
  | (BitOr _)s = prim_word_op bitOR bitOR bitOR bitOR xs
  | (BitXor _) = prim_word_op bitXOR bitXOR bitXOR bitXOR xs
  | (LShift _) = prim_word_op (checked_shift shiftl) (checked_shift shiftl)
        (checked_shift shiftl) (checked_shift shiftl) xs
  | (RShift _) = prim_word_op (checked_shift shiftr) (checked_shift shiftr)
        (checked_shift shiftr) (checked_shift shiftr) xs
  | (Complement _) = prim_word_op (\<lambda>x y. bitNOT x) (\<lambda>x y. bitNOT x)
        (\<lambda>x y. bitNOT x) (\<lambda>x y. bitNOT x) [hd xs, hd xs] *)
  | _ => default
  end.

Inductive uval : Set :=
  | UPrim (l:lit)
  | UUnit.

Variant CogentState : Type -> Type :=
  | GetVar (i:index) : CogentState uval
  | LetVar (u:uval) : CogentState unit
  | RemVar : CogentState unit.

Section Denote.

  Context {eff : Type -> Type}.
  Context {HasCogentState : CogentState -< eff}.

  Definition denote_prim (op:prim_op) (xs:list uval) : uval := 
    UPrim (eval_prim_op op (map (fun x => match x with UPrim v => v | _ => default end) xs)).

  Fixpoint denote_expr (e:expr) : itree eff uval :=
    match e with
    | Prim op os =>
        os' <- map_monad denote_expr os ;;
        ret (denote_prim op os')
    | Lit l => ret (UPrim l)
    | Var i => trigger (GetVar i)
    | Let e b => 
        e' <- denote_expr e ;;
        trigger (LetVar e') ;;
        b' <- denote_expr b ;;
        trigger RemVar ;;
        ret b'
    | _ => ret UUnit
    end.

End Denote.

Definition env := list uval.

Definition handle_state : forall A, CogentState A -> stateT env (itree void1) A :=
  fun _ e γ =>
    match e with
    | GetVar i => ret (γ, nth i γ UUnit)
    | LetVar u => ret (u :: γ, tt)
    | RemVar => ret (tl γ, tt)
    end.

Definition interp_cogent {A} (t:itree CogentState A) : itree void1 (env * A) :=
  interp handle_state t [].

(* Pretty AST Notation *)

Declare Scope cogent_scope.

Notation "x `+ y" := (Prim (Plus U32) [x; y]) (at level 50) : cogent_scope.
Notation "x `- y" := (Prim (Minus U32) [x; y]) (at level 50) : cogent_scope.
Notation "x `* y" := (Prim (Times U32) [x; y]) (at level 25) : cogent_scope.
Notation "x `/ y" := (Prim (Divide U32) [x; y]) (at level 25) : cogent_scope.
Notation "x `% y" := (Prim (Mod U32) [x; y]) (at level 25) : cogent_scope.
Notation "` n" := (Lit (LU32 n)) (at level 0) : cogent_scope.

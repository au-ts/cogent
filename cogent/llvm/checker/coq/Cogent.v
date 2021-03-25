From Coq Require Import List ListSet String ZArith.

Import ListNotations.

Section Syntax.

  Definition name := string.
  Definition index := nat.
  Definition field := nat.
  Definition addr := nat. (* doesn't actually matter *)

  Variant num_type : Set := 
  | U8 
  (* | U16  *)
  | U32 
  | U64.

  Variant prim_type : Set := Num (n : num_type) | Bool | String.

  Variant prim_op : Set :=
    | Plus (t : num_type)
    | Minus (t : num_type)
    | Times (t : num_type)
    | Divide (t : num_type)
    | Mod (t : num_type).
    (* | Not | And | Or
    | Gt (t : num_type)
    | Lt (t : num_type)
    | Le (t : num_type)
    | Ge (t : num_type)
    | Eq (t : prim_type)
    | NEq (t : prim_type)
    | BitAnd (t : num_type)
    | BitOr (t : num_type)
    | BitXor (t : num_type)
    | LShift (t : num_type)
    | RShift (t : num_type)
    | Complement (t : num_type). *)

  Variant sigil : Set :=
    | Boxed (* Ignore access_perm, ptr_layout *)
    | Unboxed.

  Variant variant_state : Set := Checked | Unchecked.
  Variant record_state : Set := Taken | Present.

  Inductive type : Set :=
    (* | TVar (i : index)
    | TVarBang (i : index)
    | TCon (n : name) (ts : list type) (s : sigil) *)
    | TFun (t : type) (rt : type)
    | TPrim (t : prim_type)
    (* | TSum (vs : list (name * (type * variant_state))) *)
    | TRecord (fs : list (name * (type * record_state))) (s : sigil)
    | TUnit.

  Inductive repr : Set :=
    | RPtr (r : repr)
    (* | RCon (n : name) (rs : list repr) *)
    | RFun
    | RPrim (t : prim_type)
    (* | RSum (ts : list (name * repr)) *)
    | RRecord (rs : list repr)
    | RUnit.

  Fixpoint type_repr (t : type) : repr :=
    match t with
    | TPrim p => RPrim p
    | TFun _ _ => RFun
    | TRecord ts s => 
        let r := RRecord (map (fun '(_, (f, _)) => type_repr f) ts) in
          match s with Boxed => RPtr r | Unboxed => r end
    | TUnit => RUnit
    end.
  
  Variant lit : Set :=
    | LBool (b : bool)
    | LU8 (w : Z)
    (* | LU16 (w : Z) *)
    | LU32 (w : Z)
    | LU64 (w : Z).
  (* NOTE: not represented as n-bit words *)

  Inductive expr : Type :=
    | Unit
    | Lit (l : lit)
    (* | SLit (s : string) *)
    | LVar (i : index)
    (* | Let (e : expr) (b : expr) *)
    (* | LetBang (is : set index) (e : expr) (b : expr) *)
    (* | BPrim (op : prim_op) (a b : expr) *)
    (* | If (c : expr) (b1 : expr) (b2 : expr) *)
    (* | Cast (t : num_type) (e : expr) *)

    (* | Struct (ts : list type) (es : list expr) *)
    (* | Member (e : expr) (f : field) *)
    (* | Take (e : expr) (f : field) (b : expr) *)
    (* | Put (e : expr) (f : field) (v : expr) *)

    (* | Con (ts : list (name * type * variant_state)) (n : name) (e : expr) *)
    (* | Promote (t : type) (e : expr) *)
    (* | Esac (e : expr) (n : name) *)
    (* | Case (e : expr) (n : name) (b1 : expr) (b2 : expr) *)
  
    (* | Fun (n : name) (ft : type) *)
    (* | App (f : expr) (a : expr) *)
    (* | AFun (funtyp : 'f)  (ts : list type) *)
    .

  Variant def : Type :=
    | FunDef (n : name) (t : type) (rt : type) (b : expr).
    (* AbsDecl, TypeDef *)

  Definition cogent_prog := list def.

End Syntax.

Section Primitive.

  Definition prim_lbool (l : lit) : bool :=
    match l with
    | LBool b => b
    | _ => false
    end.

  Definition prim_word_op (f : Z -> Z -> Z) (xs : list lit) : option lit :=
    match (firstn 2 xs) with
    | [LU8 x; LU8 y] => Some (LU8 (f x y))
    (* | [LU16 x; LU16 y] => Some (LU16 (f x y)) *)
    | [LU32 x; LU32 y] => Some (LU32 (f x y))
    | [LU64 x; LU64 y] => Some (LU64 (f x y))
    | _ => None
    end.

  Definition prim_word_comp (f : Z -> Z -> bool) (xs : list lit) : option lit :=
    match (firstn 2 xs) with
    | [LU8 x; LU8 y] => Some (LBool (f x y))
    (* | [LU16 x; LU16 y] => Some (LBool (f x y)) *)
    | [LU32 x; LU32 y] => Some (LBool (f x y))
    | [LU64 x; LU64 y] => Some (LBool (f x y))
    | _ => None
    end.

  Definition eval_prim_op (op : prim_op) (xs : list lit) : option lit :=
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
    end.

  Definition cast_to (n : num_type) (l : lit) : option lit :=
    match n, l with
    | U8, (LU8  x)  => Some (LU8 x)
    (* | U16, (LU8  x) => Some (LU16 x) *)
    (* | U16, (LU16 x) => Some (LU16 x) *)
    | U32, (LU8  x) => Some (LU32 x)
    (* | U32, (LU16 x) => Some (LU32 x) *)
    | U32, (LU32 x) => Some (LU32 x)
    | U64, (LU8  x) => Some (LU64 x)
    (* | U64, (LU16 x) => Some (LU64 x) *)
    | U64, (LU32 x) => Some (LU64 x)
    | U64, (LU64 x) => Some (LU64 x)
    | _, _ => None
    end.

End Primitive.

From Coq Require Import List ListSet String ZArith.

From Vellvm Require Import DynamicValues Numeric.Integers.

Import ListNotations.

Section Syntax.

  Definition name := string.
  Definition index := nat.
  Definition field := nat.

  Variant num_type : Set := 
  | U8 
  (* Vellvm doesn't seem to have formalised i16 directly in its semantics *)
  (* | U16 *)
  | U32 
  | U64.

  Variant prim_type : Set := 
    | Num (n : num_type)
    | Bool
    | String.

  Variant prim_op : Set :=
    | Plus (t : num_type)
    | Minus (t : num_type)
    | Times (t : num_type)
    | Divide (t : num_type)
    | Mod (t : num_type)
    | And
    | Or
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
    (* | Not *)
    (* | Complement (t : num_type) *)
    .

  Variant sigil : Set :=
    | Boxed (* Ignore access_perm, ptr_layout *)
    | Unboxed.

  Variant variant_state : Set := Checked | Unchecked.
  Variant record_state : Set := Taken | Present.

  Inductive type : Set :=
    (* | TVar (i : index) *)
    (* | TVarBang (i : index) *)
    (* | TCon (n : name) (ts : list type) (s : sigil) *)
    | TFun (t : type) (rt : type)
    | TPrim (t : prim_type)
    | TSum (vs : list (name * type * variant_state))
    | TRecord (fs : list (name * (type * record_state))) (s : sigil)
    | TUnit.

  Inductive repr : Set :=
    | RPtr (r : repr)
    (* | RCon (n : name) (rs : list repr) *)
    | RFun
    | RPrim (t : prim_type)
    | RSum (ts : list (name * repr))
    | RRecord (rs : list repr)
    | RUnit.

  Fixpoint type_repr (t : type) : repr :=
    match t with
    | TPrim p => RPrim p
    | TFun _ _ => RFun
    | TRecord ts s => 
        let r := RRecord (map (fun '(_, (f, _)) => type_repr f) ts) in
          match s with Boxed => RPtr r | Unboxed => r end
    | TSum ts => RSum (map (fun '(a, b, _) => (a, type_repr b)) ts)
    | TUnit => RUnit
    end.
  
  Variant lit : Set :=
    | LBool (b : bool)
    | LU8 (w : Z)
    (* | LU16 (w : Z) *)
    | LU32 (w : Z)
    | LU64 (w : Z).
  (* NOTE: not represented as n-bit words *)
  Scheme Equality for lit.

  Definition tags := list (name * type * variant_state).

  Inductive expr : Type :=
    | Unit
    | Lit (l : lit)
    (* | SLit (s : string) *)
    | Var (i : index)
    | Let (e : expr) (b : expr)
    (* | LetBang (is : set index) (e : expr) (b : expr) *)
    | Prim (op : prim_op) (os : list expr)
    | If (c : expr) (b1 : expr) (b2 : expr)
    | Cast (t : num_type) (e : expr)

    | Struct (ts : list type) (es : list expr)
    | Member (e : expr) (f : field)
    | Take (e : expr) (f : field) (b : expr)
    | Put (e : expr) (f : field) (v : expr)

    | Con (ts : tags) (n : name) (e : expr)
    | Promote (t : type) (e : expr)
    | Esac (ts : tags) (e : expr)
    | Case (ts : tags) (e : expr) (n : name) (b1 : expr) (b2 : expr)
  
    | Fun (f : expr)
    | App (f : expr) (a : expr)
    (* | AFun (funtyp : 'f)  (ts : list type) *)
    .

  (* Improved induction principle thanks to @amblafont *)
  Definition expr_ind' :

  forall P : expr -> Prop,
    P Unit ->
    (forall l : lit, P (Lit l)) ->
    (forall i : index, P (Var i)) ->
    (forall e : expr, P e -> forall b : expr, P b -> P (Let e b)) ->
    (* in the Prim case, we add the assumption Forall P os *)
    (forall (op : prim_op) (os : list expr), Forall P os -> P (Prim op os)) ->
    (forall c : expr, P c -> forall b1 : expr, P b1 -> forall b2 : expr, P b2 -> P (If c b1 b2)) ->
    (forall (t : num_type) (e : expr), P e -> P (Cast t e)) ->
    (* in the Struct case, we add the assumption Forall P es *)
    (forall (ts : list type) (es : list expr), Forall P es -> P (Struct ts es)) ->
    (forall e : expr, P e -> forall f : field, P (Member e f)) ->
    (forall e : expr, P e -> forall (f : field) (b : expr), P b -> P (Take e f b)) ->
    (forall e : expr, P e -> forall (f : field) (v : expr), P v -> P (Put e f v)) ->
    (forall (ts : tags) (n : name) (e : expr), P e -> P (Con ts n e)) ->
    (forall (t : type) (e : expr), P e -> P (Promote t e)) ->
    (forall (ts : tags) (e : expr), P e -> P (Esac ts e)) ->
    (forall (ts : tags) (e : expr),  P e -> forall (n : name) (b1 : expr), 
      P b1 -> forall b2 : expr, P b2 -> P (Case ts e n b1 b2)) ->
    (forall f14 : expr, P f14 -> P (Fun f14)) ->
    (forall f15 : expr, P f15 -> forall a : expr, P a -> P (App f15 a)) -> forall e : expr,
      P e :=
        fun (P : expr -> Prop) (f : P Unit)
        (f0 : forall l : lit, P (Lit l))
        (f1 : forall i : index, P (Var i))
        (f2 : forall e : expr, P e -> forall b : expr, P b -> P (Let e b))
        (f3 : forall (op : prim_op) (os : list expr), Forall P os -> P (Prim op os))
        (f4 : forall c : expr, P c -> forall b1 : expr, P b1 -> forall b2 : expr, P b2 -> P (If c b1 b2))
        (f5 : forall (t : num_type) (e : expr), P e -> P (Cast t e))
        (f6 : forall (ts : list type) (es : list expr), Forall P es -> P (Struct ts es))
        (f7 : forall e : expr, P e -> forall f : field, P (Member e f))
        (f8 : forall e : expr, P e -> forall (f : field) (b : expr), P b -> P (Take e f b))
        (f9 : forall e : expr, P e -> forall (f : field) (v : expr), P v -> P (Put e f v))
        (f10 : forall (ts : tags) (n : name) (e : expr), P e -> P (Con ts n e))
        (f11 : forall (t : type) (e : expr), P e -> P (Promote t e))
        (f12 : forall (ts : tags) (e : expr), P e -> P (Esac ts e))
        (f13 : forall (ts : tags) (e : expr), P e -> forall (n : name) (b1 : expr),
          P b1 -> forall b2 : expr, P b2 -> P (Case ts e n b1 b2))
        (f14 : forall f14 : expr, P f14 -> P (Fun f14))
        (f15 : forall f15 : expr, P f15 -> forall a : expr, P a -> P (App f15 a)) =>
          fix F (e : expr) : P e :=
            match e as e0 return (P e0) with
            | Unit => f
            | Lit l => f0 l
            | Var i => f1 i
            | Let e0 b => f2 e0 (F e0) b (F b)
            | Prim op os => f3 op os
                (* applying the induction hypothesis requires a proof that Forall P os.
                This is done by a list recursion *)
                (list_ind _ (Forall_nil P) (fun a _ H => Forall_cons a (F a) H) _)
            | If c b1 b2 => f4 c (F c) b1 (F b1) b2 (F b2)
            | Cast t e0 => f5 t e0 (F e0)
            | Struct ts es => f6 ts es
                (* as above *)
                (list_ind _ (Forall_nil P) (fun a _ H => Forall_cons a (F a) H) _)
            | Member e0 f12 => f7 e0 (F e0) f12
            | Take e0 f12 b => f8 e0 (F e0) f12 b (F b)
            | Put e0 f12 v => f9 e0 (F e0) f12 v (F v)
            | Con ts n e0 => f10 ts n e0 (F e0)
            | Promote t e0 => f11 t e0 (F e0)
            | Esac ts e0 => f12 ts e0 (F e0)
            | Case ts e0 n b1 b2 => f13 ts e0 (F e0) n b1 (F b1) b2 (F b2)
            | Fun f16 => f14 f16 (F f16)
            | App f16 a => f15 f16 (F f16) a (F a)
            end.

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

  Definition prim_word_op (f8 : Int8.int -> Int8.int -> Int8.int)
                          (* (f16 : Int16.int -> Int16.int -> Int16.int) *)
                          (f32 : Int32.int -> Int32.int -> Int32.int)
                          (f64 : Int64.int -> Int64.int -> Int64.int)
                          (xs : list lit) : option lit :=
    match (firstn 2 xs) with
    | [LU8 x; LU8 y] => Some (LU8 (Int8.unsigned (f8 (Int8.repr x) (Int8.repr y))))
    (* | [LU16 x; LU16 y] => Some (LU16 (Int16.unsigned (f16 (Int16.repr x) (Int16.repr y)))) *)
    | [LU32 x; LU32 y] => Some (LU32 (Int32.unsigned (f32 (Int32.repr x) (Int32.repr y))))
    | [LU64 x; LU64 y] => Some (LU64 (Int64.unsigned (f64 (Int64.repr x) (Int64.repr y))))
    | _ => None
    end.
  
  Definition prim_bool_op (f : bool -> bool -> bool) (xs : list lit) : option lit :=
    match (firstn 2 xs) with
    | [LBool x; LBool y] => Some (LBool (f x y))
    | _ => None
    end.
  
  Definition prim_word_comp (f8 : Int8.int -> Int8.int -> bool)
                            (* (f16 : Int16.int -> Int16.int -> bool) *)
                            (f32 : Int32.int -> Int32.int -> bool)
                            (f64 : Int64.int -> Int64.int -> bool)
                            (xs : list lit) : option lit :=
    match (firstn 2 xs) with
    | [LU8 x; LU8 y] => Some (LBool (f8 (Int8.repr x) (Int8.repr y)))
    (* | [LU16 x; LU16 y] => Some (LBool (f16 (Int16.repr x) (Int16.repr y))) *)
    | [LU32 x; LU32 y] => Some (LBool (f32 (Int32.repr x) (Int32.repr y)))
    | [LU64 x; LU64 y] => Some (LBool (f64 (Int64.repr x) (Int64.repr y)))
    | _ => None
    end.
  
  Definition prim_lit_comp (f : lit -> lit -> bool) (xs : list lit) : option lit :=
    match (firstn 2 xs) with
    | [x; y] => Some (LBool (f x y))
    | _ => None
    end.

  Definition eval_prim_op (op : prim_op) : list lit -> option lit :=
    match op with
    | Plus _ => prim_word_op Int8.add Int32.add Int64.add
    | Minus _ => prim_word_op Int8.sub Int32.sub Int64.sub
    | Times _ => prim_word_op Int8.mul Int32.mul Int64.mul
    | Divide _ => prim_word_op Int8.divu Int32.divu Int64.divu
    | Mod _ => prim_word_op Int8.modu Int32.modu Int64.modu
    | And => prim_bool_op andb
    | Or => prim_bool_op orb
    | Gt _ => prim_word_comp (Int8.cmpu Cgt) (Int32.cmpu Cgt) (Int64.cmpu Cgt)
    | Lt _ => prim_word_comp (Int8.cmpu Clt) (Int32.cmpu Clt) (Int64.cmpu Clt)
    | Le _ => prim_word_comp (Int8.cmpu Cle) (Int32.cmpu Cle) (Int64.cmpu Cle)
    | Ge _ => prim_word_comp (Int8.cmpu Cge) (Int32.cmpu Cge) (Int64.cmpu Cge)
    | Eq _ => prim_lit_comp lit_beq
    | NEq _ => prim_lit_comp (fun x y => negb (lit_beq x y))
    | BitAnd _ => prim_word_op Int8.and Int32.and Int64.and
    | BitOr _ => prim_word_op Int8.or Int32.or Int64.or
    | BitXor _ => prim_word_op Int8.xor Int32.xor Int64.xor
    | LShift _ => prim_word_op Int8.shl Int32.shl Int64.shl
    | RShift _ => prim_word_op Int8.shru Int32.shru Int64.shru
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

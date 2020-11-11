From Coq Require Import List ZArith String.
From Vellvm Require Import LLVMAst.
From Checker Require Import Cogent Types.

Import ListNotations.

(* Codegen state *)

Definition T := typ.

Record state : Set := mkState
  { block : code T
  ; fresh : Z
  }.

Definition codegen t := state -> (state * t).

Definition pure {t:Type} (x:t) : codegen t := fun s => (s, x).

Definition bind {t u:Type} (c:codegen t) (f:t -> codegen u) : codegen u :=
  fun s =>
    let (s', v) := c s
      in f v s'.

Definition run {t:Type} (c:codegen t) := c (mkState [] 0).

Notation "f >>= g" := (bind f g) (at level 82, left associativity).

Notation "x <- f ; g" := (f >>= fun x => g) (at level 85, f at next level, right associativity).

Notation "g <$> f" := (f >>= fun x => pure (g x)) (at level 81, left associativity).

Definition instr (t:T) (i:instr T) : codegen (texp T) :=
  fun s =>
    let n := fresh s in
      (mkState (block s ++ [(IId (Anon n), i)]) 1
      , (t, EXP_Ident (ID_Local (Anon n)))
      ).

(* Compiler *)

Definition compile_prim_op (o:prim_op) : (ibinop * typ * typ) :=
  match o with
  | Plus t => (Add false false, convert_num_type t, convert_num_type t)
  | Minus t => (Sub false false, convert_num_type t, convert_num_type t)
  | Times t => (Mul false false, convert_num_type t, convert_num_type t)
  | Divide t => (UDiv false, convert_num_type t, convert_num_type t)
  | Mod t => (URem, convert_num_type t, convert_num_type t)
  | _ => (Xor, TYPE_Void, TYPE_Void)
  (* | Not 
  | And 
  | Or
  | Gt t
  | Lt t
  | Le t
  | Ge t
  | Eq (t:prim_type)
  | NEq (t:prim_type)
  | BitAnd t
  | BitOr t
  | BitXor t
  | LShift t
  | RShift t
  | Complement t *)
  end.

Fixpoint compile_expr (e:expr) : codegen (texp T) :=
  match e with
  | Prim op [oa; ob] =>
      let '(op', t, rt) := compile_prim_op op in
        va <- snd <$> compile_expr oa;
        vb <- snd <$> compile_expr ob;
        instr rt (INSTR_Op (OP_IBinop op' t va vb)) 
  | Lit l => pure match l with
    | LBool b => (TYPE_I 8, EXP_Integer (if b then 1 else 0))
    | LU8 w => (TYPE_I 8, EXP_Integer w)
    | LU16 w => (TYPE_I 16, EXP_Integer w)
    | LU32 w => (TYPE_I 32, EXP_Integer w)
    | LU64 w => (TYPE_I 64, EXP_Integer w)
    end
  | _ => pure (TYPE_Void, EXP_Undef)
  end.

(* Definition checkExp (cogentExp:expr) (llvmExp:exp typ) : Prop := compile cogentExp = llvmExp. *)

Open Scope cogent_scope.

Definition prog : expr := `1 `+ `2 `* `3.

Compute run (compile_expr prog).

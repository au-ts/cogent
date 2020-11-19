From Coq Require Import List ZArith String.

From ExtLib Require Import Data.Monads.StateMonad Structures.Monads Structures.Functor.
From Vellvm Require Import LLVMAst.

From Checker Require Import Cogent Types.

Definition T := typ.

Section Compiler.

  Import MonadNotation.
  Import FunctorNotation.
  Import ListNotations.
  Local Open Scope monad_scope.

  Definition CodegenValue : Type := texp T.
  (* Can't use record for state?: https://github.com/coq-community/coq-ext-lib/issues/48 *)
  Definition CodegenState : Type := (code T * Z * list (texp T)).
  Definition fresh : CodegenState -> Z := fun x => snd (fst x).
  Definition block : CodegenState -> code T := fun x => fst (fst x).
  Definition vars : CodegenState -> list (texp T) := snd.

  Variable m : Type -> Type.
  Context {Monad_m: Monad m}.
  Context {State_m: MonadState CodegenState m}.


  Definition instr (t:T) (i:instr T) : m CodegenValue :=
    s <- get ;;
    let n := fresh s in
      put (block s ++ [(IId (Anon n), i)], n + 1, vars s) ;;
      ret (t, EXP_Ident (ID_Local (Anon n))).
  
  Definition set_vars (vs:list (texp T)) : m unit :=
    s <- get ;;
    put (block s, fresh s, vs).

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

  Definition undef : CodegenValue := (TYPE_Void, EXP_Null). (* undefined *)

  Fixpoint compile_expr (e:expr) : m CodegenValue :=
    match e with
    | Prim op [oa; ob] =>
        let '(op', t, rt) := compile_prim_op op in
        va <- snd <$> compile_expr oa ;;
        vb <- snd <$> compile_expr ob ;;
        instr rt (INSTR_Op (OP_IBinop op' t va vb)) 
    | Lit l => ret match l with
      | LBool b => (TYPE_I 8, EXP_Integer (if b then 1 else 0))
      | LU8 w => (TYPE_I 8, EXP_Integer w)
      | LU16 w => (TYPE_I 16, EXP_Integer w)
      | LU32 w => (TYPE_I 32, EXP_Integer w)
      | LU64 w => (TYPE_I 64, EXP_Integer w)
      end
    | Var i =>
        s <- get ;;
        ret (nth i (vars s) undef)
    | Let e b =>
        e' <- compile_expr e ;;
        s <- get ;;
        set_vars (e' :: vars s) ;;
        b' <- compile_expr b ;;
        set_vars (vars s) ;;
        ret b'
    | _ => ret undef
    end.

  Definition startState: CodegenState := ([], 0, []).


End Compiler.

Definition run (p:expr) := runState (compile_expr (state CodegenState) p) startState.

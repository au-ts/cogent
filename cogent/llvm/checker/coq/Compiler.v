From Coq Require Import List ZArith String.

From ExtLib Require Import Structures.Monads Structures.Functor.
From RecordUpdate Require Import RecordSet.
From Vellvm Require Import LLVMAst Util.

From Checker Require Import Cogent Types State.

Import ListNotations.
Import RecordSetNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.

Section Compiler.

  Definition CodegenValue : Type := texp typ.
  Record CodegenState : Type := mk_state {
    entry : block typ
  ; blocks: list (block typ)
  ; fresh_anon : Z
  ; fresh_void : Z
  ; fresh_block : Z
  ; vars : list (texp typ)
  }.
  Instance etaCodegenState : Settable _ := settable! mk_state <
    entry
  ; blocks
  ; fresh_anon
  ; fresh_void
  ; fresh_block
  ; vars
  >.

  Instance etaBlock : Settable _ := settable! (@mk_block typ) <blk_id;blk_phis; blk_code; blk_term; blk_comments>.

  Definition empty_block (n:block_id) : block typ :=
    mk_block n [] [] (IVoid 0, TERM_Ret_void) None.

  Variable m : Type -> Type.
  Context {Monad_m: Monad m}.
  Context {State_m: MonadState CodegenState m}.

  Definition current_block : m block_id :=
    s <- get ;;
    ret (blk_id (hd (entry s) (blocks s))).

  Definition update_block (f:block typ -> block typ) (s:CodegenState) : CodegenState :=
    match blocks s with
    | [] => s <|entry := f (entry s)|>
    | x :: xs => s <|blocks := f x :: xs|>
    end.
  
  Definition new_block (n:block_id) : m unit :=
    s <- get ;;
    put (s <|blocks := empty_block n :: blocks s|>).
  
  Definition branch_blocks : m (block_id * block_id * block_id) :=
    s <- get ;;
    let n := fresh_block s in
      put (s <|fresh_block := n + 1|>) ;;
      ret (
        Name ("if_" ++ string_of_Z n)
      , Name ("then_" ++ string_of_Z n)
      , Name ("done_" ++ string_of_Z n)
      ).

  Definition instr (t:typ) (i:instr typ) : m CodegenValue :=
    s <- get ;;
    let n := fresh_anon s in
      put (
        update_block (
          fun x => x <|blk_code := blk_code x ++ [(IId (Anon n), i)]|>
        ) s <|fresh_anon := n + 1|>
      ) ;;
      ret (t, EXP_Ident (ID_Local (Anon n))).

  Definition term (t:terminator typ) : m unit :=
    s <- get ;;
    let n := fresh_void s in
      put (update_block (fun x => x <|blk_term := (IVoid n, t)|>) s <|fresh_void := n + 1|>) ;;
      ret tt.
  
  Definition phi (t:typ) (args:list (block_id * exp typ)) : m CodegenValue :=
    s <- get ;;
    let n := fresh_anon s in
      put (
        update_block (
          fun x => x <|blk_phis := blk_phis x ++ [(Anon n, Phi t args)]|>
        ) s <|fresh_anon := n + 1|>
      ) ;;
      ret (t, EXP_Ident (ID_Local (Anon n))).
  
  Definition set_vars (vs:list (texp typ)) : m unit :=
    s <- get ;;
    put (s <|vars := vs|>).

  Definition compile_prim_op (o:prim_op) : (exp typ -> exp typ -> exp typ) * typ :=
    match o with
    | Plus t => (OP_IBinop (Add false false) (convert_num_type t), convert_num_type t)
    | Minus t => (OP_IBinop (Sub false false) (convert_num_type t), convert_num_type t)
    | Times t => (OP_IBinop (Mul false false) (convert_num_type t), convert_num_type t)
    | Divide t => (OP_IBinop (UDiv false) (convert_num_type t), convert_num_type t)
    | Mod t => (OP_IBinop URem (convert_num_type t), convert_num_type t)
    | _ => (OP_IBinop Xor TYPE_Void, TYPE_Void)
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
        let (op', rt) := compile_prim_op op in
        va <- snd <$> compile_expr oa ;;
        vb <- snd <$> compile_expr ob ;;
        instr rt (INSTR_Op (op' va vb)) 
    | Lit l => ret match l with
      | LBool b => (TYPE_I 1, EXP_Integer (if b then 1 else 0))
      | LU8 w => (TYPE_I 8, EXP_Integer w)
      | LU16 w => (TYPE_I 16, EXP_Integer w)
      | LU32 w => (TYPE_I 32, EXP_Integer w)
      | LU64 w => (TYPE_I 64, EXP_Integer w)
      end
    | Unit => ret (TYPE_I 2, EXP_Integer 0)
    | If c b1 b2 =>
        c' <- compile_expr c ;;
        '(br_true, br_false, br_exit) <- branch_blocks ;;
        term (TERM_Br c' br_true br_false) ;;

        new_block br_true ;;
        b1' <- compile_expr b1 ;;
        br_true' <- current_block ;;
        term (TERM_Br_1 br_exit) ;;

        new_block br_false;;
        b2' <- compile_expr b2 ;;
        br_false' <- current_block ;;
        term (TERM_Br_1 br_exit) ;;

        new_block br_exit ;;
        phi (fst b1') [(br_true', snd b1'); (br_false', snd b2')]
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
  
  Definition compile_type (t:type) : typ :=
    match t with
    | TPrim p => match p with
      | Num n => convert_num_type n
      | Bool => TYPE_I 8
      | String => TYPE_Pointer (TYPE_I 8)
      end
    | TUnit => TYPE_I 8
    | _ => TYPE_Void
    end.

  Definition start_state (t:typ) : CodegenState := {|
    entry := empty_block (Name "entry_0")
  ; blocks := []
  ; fresh_anon := 0
  ; fresh_void := 0
  ; fresh_block := 0
  ; vars := [(t, EXP_Ident (ID_Local (Name "a_0")))]
  |}.

End Compiler.

Definition build_expr (p:expr) (t:type) : CodegenState :=
  execState (v <- compile_expr _ p ;; term _ (TERM_Ret v)) (start_state (compile_type t)).

Definition compile_def (d:def) : toplevel_entity typ (block typ * list (block typ)) :=
  match d with
  | FunDef n t rt b => 
      let state := build_expr b t in  
        TLE_Definition {|
          df_prototype := {|
            dc_name := Name n
          ; dc_type := TYPE_Function (compile_type rt) [compile_type t]
          ; dc_param_attrs := ([], [])
          ; dc_linkage := None
          ; dc_visibility := None
          ; dc_dll_storage := None
          ; dc_cconv := None
          ; dc_attrs := []
          ; dc_section := None
          ; dc_align := None
          ; dc_gc := None|}
        ; df_args := [(Name "a_0")]
        ; df_instrs := (entry state, rev (blocks state))
        |}
  end.

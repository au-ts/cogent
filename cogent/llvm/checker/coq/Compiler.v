From Coq Require Import List ZArith String.

From ExtLib Require Import Structures.Monads Structures.Functor Structures.Reducible Data.List.
From RecordUpdate Require Import RecordSet.
From Vellvm Require Import LLVMAst Util Utils.Error.

From Checker Require Import Cogent Types Util.ErrorWithState.

Import ListNotations.
Import RecordSetNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.

Section Compiler.

  Definition CodegenValue : Type := texp typ.

  Record CodegenState : Type := mk_state {
    entry : block typ
  ; blocks : list (block typ)
  ; fresh_anon : Z
  ; fresh_block : Z
  ; vars : list (texp typ)
  }.

  Instance etaCodegenState : Settable _ := settable! mk_state <
    entry
  ; blocks
  ; fresh_anon
  ; fresh_block
  ; vars
  >.

  Instance etaBlock : Settable _ := settable! (@mk_block typ) <blk_id;blk_phis; blk_code; blk_term; blk_comments>.

  Definition empty_block (n : block_id) : block typ :=
    mk_block n [] [] TERM_Ret_void None.

  Definition cerr := errS CodegenState.

  Definition current_block : cerr block_id :=
    s <- get ;;
    ret (blk_id (hd (entry s) (blocks s))).

  Definition update_block (f : block typ -> block typ) (s : CodegenState) : CodegenState :=
    match blocks s with
    | [] => s <|entry := f (entry s)|>
    | x :: xs => s <|blocks := f x :: xs|>
    end.
  
  Definition new_block (n : block_id) : cerr unit :=
    s <- get ;;
    put (s <|blocks := empty_block n :: blocks s|>).
  
  Definition branch_blocks : cerr (block_id * block_id * block_id) :=
    s <- get ;;
    let n := fresh_block s in
      put (s <|fresh_block := n + 1|>) ;;
      ret (
        Name ("if_" ++ string_of_Z n)
      , Name ("then_" ++ string_of_Z n)
      , Name ("done_" ++ string_of_Z n)
      ).

  Definition instr (t : typ) (i : instr typ) : cerr CodegenValue :=
    s <- get ;;
    let n := fresh_anon s in
      put (
        update_block (
          fun x => x <|blk_code := blk_code x ++ [(IId (Anon n), i)]|>
        ) s <|fresh_anon := n + 1|>
      ) ;;
      ret (t, EXP_Ident (ID_Local (Anon n))).

  Definition term (t : terminator typ) : cerr unit :=
    s <- get ;;
    put (update_block (fun x => x <|blk_term := t|>) s) ;;
    ret tt.
  
  Definition phi (t : typ) (args : list (block_id * exp typ)) : cerr CodegenValue :=
    s <- get ;;
    let n := fresh_anon s in
      put (
        update_block (
          fun x => x <|blk_phis := blk_phis x ++ [(Anon n, Phi t args)]|>
        ) s <|fresh_anon := n + 1|>
      ) ;;
      ret (t, EXP_Ident (ID_Local (Anon n))).
  
  Definition set_vars (vs : list (texp typ)) : cerr unit :=
    s <- get ;;
    put (s <|vars := vs|>).

  Definition compile_prim_op (o : prim_op) : (exp typ -> exp typ -> exp typ) * typ :=
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
    | Eq (t : prim_type)
    | NEq (t : prim_type)
    | BitAnd t
    | BitOr t
    | BitXor t
    | LShift t
    | RShift t
    | Complement t *)
    end.

  Fixpoint compile_type (t : type) : typ :=
    match t with
    | TPrim p => match p with
      | Num n => convert_num_type n
      | Bool => TYPE_I 8
      | String => TYPE_Pointer (TYPE_I 8)
      end
    | TRecord ts s => 
        let t' := TYPE_Struct (map (fun '(_, (f, _)) => compile_type f) ts) in
          match s with Boxed => TYPE_Pointer t' | Unboxed => t' end
    | TUnit => TYPE_I 8
    end.

  Fixpoint compile_expr (e : expr) : cerr CodegenValue :=
    match e with
    | Prim op os =>
        match os with
        | [oa; ob] => 
            let (op', rt) := compile_prim_op op in
              va <- snd <$> compile_expr oa ;;
              vb <- snd <$> compile_expr ob ;;
              instr rt (INSTR_Op (op' va vb)) 
        | _ => raise "wrong number of primitive arguments"
        end
    | Lit l => ret match l with
      | LBool b => (TYPE_I 1, EXP_Integer (if b then 1 else 0))
      | LU8 w => (TYPE_I 8, EXP_Integer w)
      | LU16 w => (TYPE_I 16, EXP_Integer w)
      | LU32 w => (TYPE_I 32, EXP_Integer w)
      | LU64 w => (TYPE_I 64, EXP_Integer w)
      end
    | Var i =>
        s <- get ;;
        match (nth_error (vars s) i) with
        | Some v => ret v
        | None => raise "unknown variable"
        end
    | Let e b =>
        e' <- compile_expr e ;;
        s <- get ;;
        set_vars (e' :: vars s) ;;
        b' <- compile_expr b ;;
        set_vars (vars s) ;;
        ret b'
    | Unit => ret (TYPE_I 2, EXP_Integer 0)
    | If c t e =>
        c' <- compile_expr c ;;
        '(br_true, br_false, br_exit) <- branch_blocks ;;
        term (TERM_Br c' br_true br_false) ;;

        new_block br_true ;;
        t' <- compile_expr t ;;
        br_true' <- current_block ;;
        term (TERM_Br_1 br_exit) ;;

        new_block br_false;;
        e' <- compile_expr e ;;
        br_false' <- current_block ;;
        term (TERM_Br_1 br_exit) ;;

        new_block br_exit ;;
        phi (fst t') [(br_true', snd t'); (br_false', snd e')]
    | Cast t e =>
        '(from_t, v) <- compile_expr e ;;
        let t' := convert_num_type t in
        instr t' (INSTR_Op (OP_Conversion Zext from_t v t'))
    | Struct ts es =>
        (* foldM *)
        let t := TYPE_Struct (map compile_type ts) in
        let undef := (t, EXP_Undef) in
        es' <- map_monad compile_expr es ;;
        let zipped := (combine (seq 0 (length es')) es') in
        foldM (fun '(i, v) s => instr t (INSTR_Op (OP_InsertValue s v [Z.of_nat i]))) (ret undef) zipped
    end.

  Definition start_state (t : typ) : CodegenState := {|
    entry := empty_block (Name "entry_0")
  ; blocks := []
  ; fresh_anon := 0
  ; fresh_block := 0
  ; vars := [(t, EXP_Ident (ID_Local (Name "a_0")))]
  |}.

  Definition build_expr (p : expr) (t : type) : err CodegenState :=
    execErrS (v <- compile_expr p ;; term (TERM_Ret v)) (start_state (compile_type t)).

  Definition compile_fun n t rt b : err (definition typ (block typ * list (block typ))) :=
    state <- build_expr b t ;;
    ret {|
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
    |}.

  Definition compile_def (d : def) : err (toplevel_entity typ (block typ * list (block typ))) :=
    match d with
    | FunDef n t rt b => TLE_Definition <$> compile_fun n t rt b
    end.

  Definition compile_cogent := map_monad compile_def.

End Compiler.

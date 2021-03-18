From Coq Require Import List ZArith String.

From ExtLib Require Import Structures.Monads Structures.Functor Structures.Reducible Data.List.
From RecordUpdate Require Import RecordSet.
From Vellvm Require Import LLVMAst Util Utils.Error.

From Checker Require Import Cogent Types Utils.ErrorWithState Utils.Instances Utils.Codegen.

Import ListNotations.
Import RecordSetNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.

Section Compiler.

  Definition segment : Type := texp typ * block_id * list (block typ).

  (* Definition CodegenValue : Type := texp typ.
   

  (* use similar strategy to helix *)
  Definition segment : Type := block_id * list (block typ).

  Record CodegenState : Type := mk_state {
    fresh_void : Z
  ; fresh_anon : Z
  ; fresh_block : Z
  ; vars : list (texp typ)
  }.

  Global Instance etaCodegenState : Settable _ := settable! mk_state <
    fresh_void
  ; fresh_anon
  ; fresh_block
  ; vars
  >.

  Global Instance etaBlock : Settable _ := settable! (@mk_block typ) <blk_id;blk_phis; blk_code; blk_term; blk_comments>.

  Definition empty_block (n : block_id) : block typ :=
    mk_block n [] [] TERM_Ret_void None.

  Definition cerr := errS CodegenState.

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

  Definition bind {A} (var : CodegenValue) (action : cerr A) : cerr A :=
    s <- get ;;
    set_vars (var :: vars s) ;;
    res <- action ;;
    set_vars (vars s) ;;
    ret res. *)

  (* Definition int32 (n : int) : texp typ := (TYPE_I 32, EXP_Integer n). *)


  Definition compile_prim_op (o : prim_op) : (exp typ -> exp typ -> exp typ) * typ :=
    match o with
    | Plus t => (OP_IBinop (Add false false) (convert_num_type t), convert_num_type t)
    | Minus t => (OP_IBinop (Sub false false) (convert_num_type t), convert_num_type t)
    | Times t => (OP_IBinop (Mul false false) (convert_num_type t), convert_num_type t)
    | Divide t => (OP_IBinop (UDiv false) (convert_num_type t), convert_num_type t)
    | Mod t => (OP_IBinop URem (convert_num_type t), convert_num_type t)
    end.

  Fixpoint compile_type (t : type) : typ :=
    match t with
    | TPrim p => match p with
      | Num n => convert_num_type n
      | Bool => TYPE_I 8
      | String => TYPE_Pointer (TYPE_I 8)
      end
    | TFun t rt => TYPE_Pointer (TYPE_Function (compile_type rt) [compile_type t])
    | TRecord ts s => 
        let t' := TYPE_Struct (map (fun '(_, (f, _)) => compile_type f) ts) in
          match s with Boxed => TYPE_Pointer t' | Unboxed => t' end
    | TUnit => TYPE_I 8
    end.

  Fixpoint compile_expr (e : expr) (next_blk : block_id) : cerr segment :=
    (* define some nested functions that are mutually recursive with compile_expr *)
    (* let fix load_member e f : cerr (CodegenValue * CodegenValue) :=
      e' <- compile_expr e ;;
      f' <- match field_type (fst e') f with
      | UnboxField t => instr t (INSTR_Op (OP_ExtractValue e' [Z.of_nat f]))
      | BoxField t => 
          let idxs := map int32 [0; Z.of_nat f] in
          p <- instr (TYPE_Pointer t) (INSTR_Op (OP_GetElementPtr (deref_type (fst e')) e' idxs)) ;;
          instr t (INSTR_Load false t p None)
      | Invalid => raise "invalid member access"
      end ;;
      ret (e', f') in *)
    match e with
    | Prim op os =>
        match os with
        | [a; b] => 
            let (op', rt) := compile_prim_op op in
              prim_blk <- incBlockNamed "Prim" ;;
              '((_, b_val), b_blk, b_blks) <- compile_expr b prim_blk ;;
              '((_, a_val), a_blk, a_blks) <- compile_expr a b_blk ;;
              new_local <- incLocal ;;
              ret ((rt, EXP_Ident (ID_Local (new_local))), a_blk, a_blks ++ b_blks ++ [code_block prim_blk next_blk [(IId new_local, INSTR_Op (op' a_val b_val))]])
        | _ => raise "wrong number of primitive arguments"
        end
    | Lit l => ret (match l with
      | LBool b => (TYPE_I 1, EXP_Integer (if b then 1 else 0))
      | LU8 w => (TYPE_I 8, EXP_Integer w)
      (* | LU16 w => (TYPE_I 16, EXP_Integer w) *)
      | LU32 w => (TYPE_I 32, EXP_Integer w)
      | LU64 w => (TYPE_I 64, EXP_Integer w)
      end, next_blk, [])
    | Var i => 
        v <- getStateVar "unknown variable" i ;;
        ret (v, next_blk, [])
    | Let e b =>
        let_blk <- incBlockNamed "Let" ;;
        '(e', e_blk, e_blks) <- compile_expr e let_blk ;;
        addVars [e'] ;;
        '(b', b_blk, b_blks) <- compile_expr b next_blk ;;
        dropVars 1 ;;
        ret (b', e_blk, e_blks ++ [code_block let_blk b_blk []] ++ b_blks)
    | Unit => ret ((TYPE_I 8, EXP_Integer 0), next_blk, [])
    (* | If c t e =>
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
        let t := TYPE_Struct (map compile_type ts) in
        let undef := (t, EXP_Undef) in
        es' <- map_monad compile_expr es ;;
        let zipped := (combine (seq 0 (length es')) es') in
        foldM (fun '(i, v) s => instr t (INSTR_Op (OP_InsertValue s v [Z.of_nat i]))) (ret undef) zipped
    | Member e f => snd <$> load_member e f
    | Take e f b => load_member e f >>= fold bind (compile_expr b)
    | Put e f v =>
        e' <- compile_expr e ;;
        v' <- compile_expr v ;;
        match field_type (fst e') f with
        | UnboxField t => instr t (INSTR_Op (OP_InsertValue e' v' [Z.of_nat f]))
        | BoxField t => 
            let idxs := map int32 [0; Z.of_nat f] in
            p <- instr (TYPE_Pointer t) (INSTR_Op (OP_GetElementPtr (deref_type (fst e')) e' idxs)) ;;
            instr t (INSTR_Store false v' p None) ;;
            ret e'
        | Invalid => raise "invalid member access"
        end
    | Fun n ft => ret (compile_type ft, EXP_Ident (ID_Global (Name n)))
    | App f a =>
        a' <- compile_expr a ;;
        f' <- compile_expr f ;;
        instr (return_type (deref_type (fst f'))) (INSTR_Call f' [a']) *)
    end.

  (* Definition build_expr (p : expr) (t : type) : err CodegenState :=
    execErrS (v <- compile_expr p ;; term (TERM_Ret v)) (start_state (compile_type t)). *)

  Definition compile_fun n t rt b : cerr (definition typ (block typ * list (block typ))) :=
    ret_blk <- incBlockNamed "Return" ;;
    '(result, _, body) <- compile_expr b ret_blk ;;
    body' <- body_non_empty_cast (body ++ [{|
      blk_id    := ret_blk ;
      blk_phis  := [];
      blk_code  := [];
      blk_term  := TERM_Ret result;
      blk_comments := None
    |}]) ;;
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
    ; df_args := [(Name "a0")]
    ; df_instrs := body'
    |}.

  Definition compile_def (d : def) : err (toplevel_entity typ (block typ * list (block typ))) :=
    match d with
    | FunDef n t rt b => evalErrS (TLE_Definition <$> compile_fun n t rt b) (start_state (compile_type t))
    end.

  Definition compile_cogent : cogent_prog -> err (toplevel_entities typ (block typ * list (block typ))) :=
    map_monad compile_def.

  (* Definition compile_cogent (e : expr) := compile_expr e (Name "exit") (newState (TYPE_I 8)). *)
  

End Compiler.

From Coq Require Import List ZArith String.

From ExtLib Require Import Structures.Monads Structures.Functor Structures.Reducible Data.List.
From RecordUpdate Require Import RecordSet.
From Vellvm Require Import LLVMAst Util Utils.Error.

From Checker Require Import Cogent Types Utils.ErrorWithState Utils.Instances.

Import ListNotations.
Import RecordSetNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.

Section Compiler.

  Definition im : Type := texp typ.
  Definition fragment : Type := im * code typ.

  Record CodegenState : Type := mk_state {
    fresh_void : Z
  ; fresh_local : Z
  ; vars : list im
  }.

  Global Instance etaCodegenState : Settable _ := settable! mk_state <
    fresh_void
  ; fresh_local
  ; vars
  >.

  Definition start_state (t : typ) : CodegenState := {|
    fresh_void := 0
  ; fresh_local := 0
  ; vars  := [(t, EXP_Ident (ID_Local (Name "a0")))]
  |}.

  Definition cerr := errS CodegenState.

  Definition local : cerr raw_id := 
    s <- get ;;
    put (s <|fresh_local := fresh_local s + 1|>) ;;
    ret (Anon (fresh_local s)).

  (* Definition instr (t : typ) (i : instr typ) : cerr im :=
    s <- get ;;
    let n := fresh_local s in
      put (
        update_block (
          fun x => x <|blk_code := blk_code x ++ [(IId (Anon n), i)]|>
        ) s <|fresh_local := n + 1|>
      ) ;;
      ret (t, EXP_Ident (ID_Local (Anon n))). *)

  Definition set_vars (vs : list im) : cerr unit :=
    s <- get ;;
    put (s <|vars := vs|>).
  
  Definition get_var (n : nat) : cerr im :=
    s <- get ;;
    option2errS "unknown variable" (nth_error (vars s) n).

  Definition int_n (sz : N) (n : int) : texp typ := (TYPE_I sz, EXP_Integer n).
  Definition int1  := int_n 1.
  Definition int8  := int_n 8.
  Definition int32 := int_n 32.
  Definition int64 := int_n 64.

  Definition compile_lit (l : lit) : im := 
    match l with
    | LBool b => int1 (if b then 1 else 0)
    | LU8 w => int8 w
    | LU32 w => int32 w
    | LU64 w => int64 w
    end.

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
      | Bool => TYPE_I 1
      | String => TYPE_Pointer (TYPE_I 8)
      end
    | TFun t rt => TYPE_Pointer (TYPE_Function (compile_type rt) [compile_type t])
    | TRecord ts s => 
        let t' := TYPE_Struct (map (fun '(_, (f, _)) => compile_type f) ts) in
          match s with Boxed => TYPE_Pointer t' | Unboxed => t' end
    | TUnit => TYPE_I 8
    end.

  Fixpoint compile_expr (e : expr) : cerr fragment :=
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
    | BPrim op a b =>
        let (op', rt) := compile_prim_op op in
        '((_, a_val), a_code) <- compile_expr a ;;
        '((_, b_val), b_code) <- compile_expr b ;;
        r_id <- local ;;
        ret ((rt, EXP_Ident (ID_Local (r_id))), a_code ++ b_code ++ [(IId r_id, INSTR_Op (op' a_val b_val))])
    | Lit l => ret (compile_lit l, [])
    | Var i =>
        v <- get_var i ;;
        ret (v, [])
    | Let e b =>
        '(e_res, e_code) <- compile_expr e ;;
        s <- get ;;
        set_vars (e_res :: vars s) ;;
        '(b_res, b_code) <- compile_expr b ;;
        ret (b_res, e_code ++ b_code)
    | Unit => ret (int8 0, [])
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
    '(res, body) <- compile_expr b ;;
    let entry : block typ := {|
      blk_id := Anon 0
    ; blk_phis := []
    ; blk_code := body
    ; blk_term := TERM_Ret res
    ; blk_comments := None
    |} in
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
    ; df_instrs := (entry, [])
    |}.

  Definition compile_def (d : def) : err (toplevel_entity typ (block typ * list (block typ))) :=
    match d with
    | FunDef n t rt b => evalErrS (TLE_Definition <$> compile_fun n t rt b) (start_state (compile_type t))
    end.

  Definition compile_cogent : cogent_prog -> err (toplevel_entities typ (block typ * list (block typ))) :=
    map_monad compile_def.

  (* Definition compile_cogent (e : expr) := compile_expr e (Name "exit") (newState (TYPE_I 8)). *)
  

End Compiler.

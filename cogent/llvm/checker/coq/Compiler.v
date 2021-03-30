From Coq Require Import List ZArith String.

From ExtLib Require Import Structures.Monads Structures.Functor Structures.Reducible Data.List.
From Vellvm Require Import LLVMAst Util Utils.Error.

From Checker Require Import HelixLib.Codegen HelixLib.ErrorWithState Cogent Types Utils.Instances.

Import ListNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.

Section Utils.

  (* Intermediate values / registers *)
  Definition im : Type := texp typ.

  (* LLVM types *)
  Definition int_n (sz : N) (n : int) : im := (TYPE_I sz, EXP_Integer n).
  Definition int1  := int_n 1.
  Definition int8  := int_n 8.
  Definition int32 := int_n 32.
  Definition int64 := int_n 64.

  (* Block generation helpers *)
  Definition code_block (bid next_bid : block_id) (c : code typ) : list (block typ) := [
    {|blk_id    := bid
    ; blk_phis  := []
    ; blk_code  := c
    ; blk_term  := TERM_Br_1 next_bid
    ; blk_comments := None
    |}].
  
  Definition nop_block (bid next_bid : block_id) : list (block typ) := code_block bid next_bid [].
  
  Definition cond_block (bid true_bid false_bid : block_id) (c : im) : list (block typ) := [
    {|blk_id    := bid
    ; blk_phis  := []
    ; blk_code  := []
    ; blk_term  := TERM_Br c true_bid false_bid
    ; blk_comments := None
    |}].
  
  Definition phi_block (bid next_bid : block_id) (p : list (local_id * phi typ)) := [
    {|blk_id    := bid
    ; blk_phis  := p
    ; blk_code  := []
    ; blk_term  := TERM_Br_1 next_bid
    ; blk_comments := None
    |}].

End Utils.

Section Compiler.

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
  
  Fixpoint compile_expr (e : expr) (next_bid: block_id) : cerr segment :=
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
    | Unit => ret (int8 0, next_bid, [])
    | Lit l => ret (compile_lit l, next_bid, [])
    | Var i =>
        v <- getStateVar "unknown variable" i ;;
        ret (v, next_bid, [])
    | Let e b =>
        let_bid <- incBlockNamed "Let" ;;
        '(e', e_bid, e_blks) <- compile_expr e let_bid ;;
        addVars [e'] ;;
        '(b', b_bid, b_blks) <- compile_expr b next_bid ;;
        dropVars 1 ;;
        ret (b', e_bid, e_blks ++ nop_block let_bid b_bid ++ b_blks)
    | BPrim op a b =>
        let (op', rt) := compile_prim_op op in
        prim_bid <- incBlockNamed "Prim" ;;
        '(b', b_bid, b_blks) <- compile_expr b prim_bid ;;
        '(a', a_bid, a_blks) <- compile_expr a b_bid ;;
        new_local <- incLocal ;;
        let prim_blks := code_block prim_bid next_bid [(IId new_local, INSTR_Op (op' (snd a') (snd b')))] in
        ret ((rt, EXP_Ident (ID_Local new_local)), a_bid, a_blks ++ b_blks ++ prim_blks)
    | If c t e =>
        if_bid <- incBlockNamed "If" ;;
        '(c', c_bid, c_blks) <- compile_expr c if_bid ;;
        tp_bid <- incBlockNamed "Then_Post" ;;
        '(t', t_bid, t_blks) <- compile_expr t tp_bid ;;
        ep_bid <- incBlockNamed "Else_Post" ;;
        '(e', e_bid, e_blks) <- compile_expr e ep_bid ;;
        fi_bid <- incBlockNamed "Fi" ;;
        let post_blks := nop_block tp_bid fi_bid ++ nop_block ep_bid fi_bid in
        let if_blks := cond_block if_bid t_bid e_bid c' in
        new_local <- incLocal ;;
        let fi_blks := phi_block fi_bid next_bid [(new_local, Phi (fst t') [(tp_bid, snd t'); (ep_bid, snd e')])] in
        ret ((fst t', EXP_Ident (ID_Local new_local)), c_bid, c_blks ++ if_blks ++ t_blks ++ e_blks ++ post_blks ++ fi_blks)
    (* | Cast t e =>
        '(from_t, v) <- compile_expr e ;;
        let t' := convert_num_type t in
        instr t' (INSTR_Op (OP_Conversion Zext from_t v t')) *)
    (* | Struct ts es =>
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
        end *)
    | App (Fun f) a => 
        app_bid <- incBlockNamed "App" ;;
        '(a', a_bid, a_blks) <- compile_expr a app_bid ;;
        s <- get ;;
        put (setVars s [a']) ;;
        '(f', f_bid, f_blks) <- compile_expr f next_bid ;;
        s' <- get ;;
        put (setVars s' (Γ s)) ;;
        ret (f', a_bid, a_blks ++ nop_block app_bid f_bid ++ f_blks)
    | Fun f => raise "naked function"
    | App f a => raise "expression is not a function"
    | _ => raise "unsupported"
    end.

  Definition compile_fun n t rt b : cerr (definition typ (block typ * list (block typ))) :=
    rid <- incBlockNamed "Return" ;;
    '(res, _, body) <- compile_expr b rid ;;
    let retblock := {|
      blk_id := rid
    ; blk_phis := []
    ; blk_code := []
    ; blk_term := TERM_Ret res
    ; blk_comments := None
    |} in
    body' <- body_non_empty_cast (body ++ [retblock]) ;;
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
    ; df_args := [Name "a0"]
    ; df_instrs := body'
    |}.

  Definition compile_def (d : def) : err (toplevel_entity typ (block typ * list (block typ))) :=
    match d with
    | FunDef n t rt b => evalErrS (TLE_Definition <$> compile_fun n t rt b) (newState (compile_type t, EXP_Ident (ID_Local (Name "a0"))))
    end.

  Definition vellvm_prog : Type := toplevel_entities typ (block typ * list (block typ)).

  (* Top-level compilation function *)
  Definition compile_cogent : cogent_prog -> err vellvm_prog :=
    map_monad compile_def.

End Compiler.

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
  Definition i1  := (int_n 1).
  Definition i8  := (int_n 8).
  Definition i32 := (int_n 32).
  Definition i64 := (int_n 64).

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

Local Notation "l %= op" := (IId l, op) (at level 99).
Local Notation "v %~ op" := (IVoid v, op) (at level 99).
Local Notation "t %% l" := ((t, EXP_Ident (ID_Local l))) (at level 10).
Local Notation "t * % l" := (TYPE_Pointer t %% l) (at level 10).
Local Notation "b1 ~> b2" := (nop_block b1 b2) (at level 10).
Local Notation "b1 : c ~> b2" := (code_block b1 b2 c) (at level 10).

Section Compiler.

  Definition compile_lit (l : lit) : im := 
    match l with
    | LBool b => i1 (if b then 1 else 0)
    | LU8 w => i8 w
    | LU32 w => i32 w
    | LU64 w => i64 w
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
    | TSum ts => TYPE_Struct (TYPE_I 32 :: (map (fun '(_, t, _) => compile_type t) ts))
    | TUnit => TYPE_I 8
    end.
  
  (* Definition unsafe_cast (i : im) (t : type) (next_bid : block_id) : cerr segment :=
    let t' := compile_type t in
    load_bid <- incBlockNamed "UnsafeCast" ;;
    p <- incLocal ;;
    v <- incVoid ;;
    c <- incLocal ;;
    r <- incLocal ;;
    let cast_blks := code_block load_bid next_bid [
      p %= INSTR_Alloca (fst i) None None;
      v %~ INSTR_Store false i (fst i* %p) None;
      c %= INSTR_Op (OP_Conversion Bitcast (fst i) (snd i) (TYPE_Pointer t'));
      r %= INSTR_Load false t' (t'* %c) None
    ] in
    ret (r, load_bid, cast_blks).
   *)

  Fixpoint find_tag (ts : tags) (n : name) : cerr nat :=
    match ts with
    | [] => raise "unknown tag"
    | (t, _, _) :: tl =>
        if eqb t n
          then ret 1%nat
          else r <- find_tag tl n ;; ret (r + 1)%nat
    end.

  Fixpoint unchecked_tag (ts : tags) : cerr nat :=
    match ts with
    | [] => raise "all tags checked"
    | (_, _, Unchecked) :: tl => ret 1%nat
    | _ :: tl => r <- unchecked_tag tl ;; ret (r + 1)%nat
    end.

  Definition tag_type (e : im) (i : nat) : cerr typ :=
    match field_type (fst e) i with
    | UnboxField t => ret t
    | _ => raise "invalid variant representation"
    end.
  
  Fixpoint compile_expr (e : expr) (next_bid : block_id) : cerr segment :=
    (* define some nested functions that are mutually recursive with compile_expr *)
    let fix load_member e f next_bid : cerr (@segment (im * im)) :=
      load_bid <- incBlockNamed "Field" ;;
      '(e', e_bid, e_blks) <- compile_expr e load_bid ;;
      '(f', load_code) <-
        match field_type (fst e') f with
        | UnboxField t =>
            l <- incLocal ;;
            ret (t %% l, [
              l %= INSTR_Op (OP_ExtractValue e' [Z.of_nat f])
            ])
        | BoxField t => 
            p <- incLocal ;;
            l <- incLocal ;;
            ret (t %% l, [
              p %= INSTR_Op (OP_GetElementPtr (deref_type (fst e')) e' [i32 0; i32 (Z.of_nat f)]);
              l %= INSTR_Load false t (t* %p) None
            ])
        | Invalid => raise "invalid member access"
        end ;;
      ret ((e', f'), e_bid, e_blks ++ code_block load_bid next_bid load_code) in
    match e with
    | Unit => ret (i8 0, next_bid, [])
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
        ret (b', e_bid, e_blks ++ let_bid ~> b_bid ++ b_blks)
    | BPrim op a b =>
        let (op', rt) := compile_prim_op op in
        prim_bid <- incBlockNamed "Prim" ;;
        '(b', b_bid, b_blks) <- compile_expr b prim_bid ;;
        '(a', a_bid, a_blks) <- compile_expr a b_bid ;;
        l <- incLocal ;;
        let prim_blks := code_block prim_bid next_bid [
          l %= INSTR_Op(op' (snd a') (snd b'))
        ] in
        ret (rt %%l, a_bid, a_blks ++ b_blks ++ prim_blks)
    | If c t e =>
        if_bid <- incBlockNamed "If" ;;
        '(c', c_bid, c_blks) <- compile_expr c if_bid ;;
        tp_bid <- incBlockNamed "Then_Post" ;;
        '(t', t_bid, t_blks) <- compile_expr t tp_bid ;;
        ep_bid <- incBlockNamed "Else_Post" ;;
        '(e', e_bid, e_blks) <- compile_expr e ep_bid ;;
        ip_bid <- incBlockNamed "If_Post" ;;
        let post_blks := tp_bid ~> ip_bid ++ ep_bid ~> ip_bid in
        let if_blks := cond_block if_bid t_bid e_bid c' in
        l <- incLocal ;;
        let ip_blks := phi_block ip_bid next_bid [
          (l, Phi (fst t') [(tp_bid, snd t'); (ep_bid, snd e')])
        ] in
        ret (fst t' %%l, c_bid, c_blks ++ if_blks ++ t_blks ++ e_blks ++ post_blks ++ ip_blks)
    | Cast t e =>
        let t' := convert_num_type t in
        cast_bid <- incBlockNamed "Cast" ;;
        '(e', e_bid, e_blks) <- compile_expr e cast_bid ;;
        l <- incLocal ;;
        let cast_blks := code_block cast_bid next_bid [
          l %= INSTR_Op (OP_Conversion Zext (fst e') (snd e') t')
        ] in
        ret (t' %%l, e_bid, e_blks ++ cast_blks)
    | Struct ts es =>
        let t := TYPE_Struct (map compile_type ts) in
        let undef := (t, EXP_Undef) in
        struct_bid <- incBlockNamed "Struct" ;;
        '(es', es_bid, es_blks) <- foldM
          (fun e '(es', es_bid, es_blks) =>
            '(e', e_bid, e_blks) <- compile_expr e es_bid ;;
            ret (e' :: es', e_bid, e_blks ++ es_blks)) 
          (ret ([], struct_bid, [])) es ;;
        '(struct, struct_code) <- foldM
          (fun '(i, e) '(s, c) =>
            l <- incLocal ;;
            ret (t %% l, (l %= INSTR_Op (OP_InsertValue s e [Z.of_nat i])) :: c))
          (ret (undef, [])) (combine (seq 0 (length es')) es') ;;
        ret (struct, es_bid, es_blks ++ code_block struct_bid next_bid struct_code)
    | Member e f =>
        '((e', f'), l_bid, l_blks) <- load_member e f next_bid ;;
        ret (f', l_bid, l_blks)
    | Take e f b => 
        take_bid <- incBlockNamed "Take" ;;
        '((e', f'), l_bid, l_blks) <- load_member e f take_bid ;;
        addVars [f'; e'] ;;
        '(b', b_bid, b_blks) <- compile_expr b next_bid ;;
        dropVars 2 ;;
        ret (b', l_bid, l_blks ++ take_bid ~> b_bid ++ b_blks)
    | Put e f v =>
        put_bid <- incBlockNamed "Put" ;;
        '(v', v_bid, v_blks) <- compile_expr v put_bid ;;
        '(e', e_bid, e_blks) <- compile_expr e v_bid ;;
        '(struct, put_code) <-
          match field_type (fst e') f with
          | UnboxField t =>
              l <- incLocal ;;
              ret (t %% l, [
                l %= INSTR_Op (OP_InsertValue e' v' [Z.of_nat f])
              ])
          | BoxField t =>
              p <- incLocal ;;
              vd <- incVoid ;;
              ret (e', [
                p %= INSTR_Op (OP_GetElementPtr (deref_type (fst e')) e' [i32 0; i32 (Z.of_nat f)]);
                vd%~ INSTR_Store false v' (t* %p) None
              ])
          | Invalid => raise "invalid member access"
          end ;;
        ret (struct, e_bid, e_blks ++ v_blks ++ code_block put_bid next_bid put_code)
    | Con ts tag x =>
        let t := compile_type (TSum ts) in
        i <- find_tag ts tag ;;
        let undef := (t, EXP_Undef) in
        con_bid <- incBlockNamed "Con" ;;
        '(x', x_bid, x_blks) <- compile_expr x con_bid ;;
        l <- incLocal ;;
        l' <- incLocal ;;
        let con_blks := code_block con_bid next_bid [
          l %= INSTR_Op (OP_InsertValue undef (i32 (Z.of_nat i)) [0]);
          l' %= INSTR_Op (OP_InsertValue (t %% l) x' [Z.of_nat i])
        ] in
        ret (t %% l', x_bid, x_blks ++ con_blks)
    | Promote _ e => compile_expr e next_bid
    | Esac ts x =>
        i <- unchecked_tag ts ;;
        esac_bid <- incBlockNamed "Esac" ;;
        '(x', x_bid, x_blks) <- compile_expr x esac_bid ;;
        l <- incLocal ;;
        let esac_blks := code_block esac_bid next_bid [
          l %= INSTR_Op (OP_ExtractValue x' [Z.of_nat i])
        ] in
        t <- tag_type x' i ;;
        ret (t %% l, x_bid, x_blks ++ esac_blks)
    | Case ts x tag m n =>
        i <- find_tag ts tag ;;
        case_bid <- incBlockNamed "Case" ;;
        '(x', x_bid, x_blks) <- compile_expr x case_bid ;;
        match_bid <- incBlockNamed "Match" ;;
        t <- incLocal ;;
        v <- incLocal ;;
        c <- incLocal ;;
        let case_blks := code_block case_bid match_bid [
          t %= INSTR_Op (OP_ExtractValue x' [0]);
          v %= INSTR_Op (OP_ExtractValue x' [Z.of_nat i]);
          c %= INSTR_Op (OP_ICmp Eq (TYPE_I 32) (EXP_Integer (Z.of_nat i)) (EXP_Ident (ID_Local t)))
        ] in
        mp_bid <- incBlockNamed "Match_Post" ;;
        t <- tag_type x' i ;;
        addVars [t %% v] ;;
        '(m', m_bid, m_blks) <- compile_expr m mp_bid ;;
        dropVars 1 ;;
        np_bid <- incBlockNamed "NoMatch_Post" ;;
        addVars [x'] ;;
        '(n', n_bid, n_blks) <- compile_expr n np_bid ;;
        dropVars 1 ;;
        cp_bid <- incBlockNamed "Case_Post" ;;
        let post_blks := mp_bid ~> cp_bid ++ np_bid ~> cp_bid in
        let match_blks := cond_block match_bid m_bid n_bid (TYPE_I 1 %% c) in
        l <- incLocal ;;
        let cp_blks := phi_block cp_bid next_bid [
          (l, Phi (fst m') [(mp_bid, snd m'); (np_bid, snd n')])
        ] in
        ret (fst m' %%l, x_bid, x_blks ++ case_blks ++ match_blks ++ m_blks ++ n_blks ++ post_blks ++ cp_blks)
    | App (Fun f) a => 
        app_bid <- incBlockNamed "App" ;;
        '(a', a_bid, a_blks) <- compile_expr a app_bid ;;
        s <- get ;;
        put (setVars s [a']) ;;
        '(f', f_bid, f_blks) <- compile_expr f next_bid ;;
        s' <- get ;;
        put (setVars s' (Γ s)) ;;
        ret (f', a_bid, a_blks ++ app_bid ~> f_bid ++ f_blks)
    | Fun f => raise "naked function"
    | App f a => raise "expression is not a function"
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

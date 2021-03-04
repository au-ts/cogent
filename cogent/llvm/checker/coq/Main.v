From Coq Require Import List String ZArith.

From ITree Require Import ITree. 
From Vellvm Require Import LLVMAst.

From Checker Require Import Cogent Compiler Denote.
From Input Require Import LLVM Source.

(* Definition checkExp (cogentExp : expr) (llvmExp : exp typ) : Prop := compile cogentExp = llvmExp. *)

Import ListNotations.

(* Compute run prog. *)

(* Open Scope cogent_scope.
Definition prog : expr := `1 `+ `2 `* `3.
Compute (burn 100 (denote_expr prog)). *)

(* LLVM Import *)

(* Check LLVMInput. *)

(* Definition never : block typ := mk_block (Name "never") [] [] (IVoid 0%Z, TERM_Ret_void) None. *)

(* Definition fixer : list (toplevel_entity typ (list (block typ))) -> list (toplevel_entity typ (block typ * list (block typ))) :=
  map (fun tle =>
    match tle with
      | TLE_Definition d =>
          let i := df_instrs d in
            TLE_Definition (mk_definition _ (df_prototype d) (df_args d) (hd never i, tl i))
      | TLE_Comment x =>  TLE_Comment x
      | TLE_Target x => TLE_Target x
      | TLE_Datalayout x => TLE_Datalayout x
      | TLE_Declaration x => TLE_Declaration x
      | TLE_Type_decl x y => TLE_Type_decl x y
      | TLE_Source_filename x => TLE_Source_filename x
      | TLE_Global x => TLE_Global x
      | TLE_Metadata x y => TLE_Metadata x y
      | TLE_Attribute_group x y => TLE_Attribute_group x y
    end
  ). *)

(* Definition mcfg := mcfg_of_tle (fixer LLVMInput). *)

(* Definition funs := m_definitions mcfg. *)

(* Import D. *)

(* Compute function_denotation. *)

(* Definition bodies := map df_instrs funs. *)

(* Check map denote_cfg bodies. *)

(* Definition main_args := [UVALUE_I64 (DynamicValues.Int64.zero); UVALUE_Addr (Addr.null)]. *)

(* Compute  (burn 1000 (denote_vellvm_main (mcfg_of_tle LLVMInput))). *)

(* Cogent Import *)

Compute compile_cogent CogentInput.

Compute burn 50 (
  run_cogent
    (UPrim (LU8 1)) 
    (Let (Var 0) (Let (Lit (LU8 1)) (Let (Lit (LU8 2)) (Struct [TPrim (Num U8);TPrim (Num U8)] [Var 1;Var 0]))))
).

From Coq Require Import List ZArith.
From Vellvm Require Import LLVMAst.
From Checker Require Import Cogent.

Import ListNotations.

Open Scope Z_scope.

Definition comp := @Basics.compose.

Definition primIntSizeBits (p:PrimInt) : Z :=
  match p with
  | U8 => 8
  | U16 => 16
  | U32 => 32
  | U64 => 64
  | Boolean => 8
  end.

Fixpoint toLLVMType (t:type) : typ :=
  match t with
  | TUnit => TYPE_I 8
  | TPrim p => TYPE_I (primIntSizeBits p)
  | TString => TYPE_Pointer (TYPE_I 8)
  | TFun t rt => TYPE_Pointer (TYPE_Function (toLLVMType rt) [toLLVMType t])
  | TRecord ts Boxed => TYPE_Pointer (TYPE_Struct (map (fun x => toLLVMType (fst (snd (x)))) ts))
  | TRecord ts Unboxed => TYPE_Struct (map (fun '(_,(x,_)) => toLLVMType x) ts)
  | _ => TYPE_Void
  end.

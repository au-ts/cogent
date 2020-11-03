From Coq Require Import List ZArith String.
From Vellvm Require Import LLVMAst.
From Checker Require Import Cogent Types.

Import ListNotations.

Definition B := TRecord [("p1", (TPrim U32, false)); ("p1", (TPrim U32, false))] Unboxed.

Compute toLLVMType (TFun B B).

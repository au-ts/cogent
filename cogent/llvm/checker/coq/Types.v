From Coq Require Import ZArith.
From Vellvm Require Import LLVMAst.
From Checker Require Import Cogent.

Open Scope Z_scope.

Definition toLLVMType (t:type) : typ :=
  match t with
  | TUnit => TYPE_I 8
  | _ => TYPE_I 0
  end.

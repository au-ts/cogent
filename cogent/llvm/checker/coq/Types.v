From Coq Require Import ZArith.
From Vellvm Require Import LLVMAst.
From Checker Require Import Cogent.

Open Scope Z_scope.

Definition convert_num_type (t : num_type) : typ :=
  TYPE_I match t with
  | U8 => 8
  | U16 => 16
  | U32 => 32
  | U64 => 64
  end.

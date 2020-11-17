From Coq Require Import List String ZArith.

From ITree Require Import ITree.
From Vellvm Require Import LLVMAst.

From Checker Require Import Cogent Compiler.
From Input Require Import LLVM.

(* Definition checkExp (cogentExp:expr) (llvmExp:exp typ) : Prop := compile cogentExp = llvmExp. *)

Import ListNotations.

Open Scope cogent_scope.

Definition prog : expr := `1 `+ `2 `* `3.

(* Compute run prog. *)

Compute (burn 100 (denote_expr prog)).

(* LLVM Import *)

Compute LLVMInput.

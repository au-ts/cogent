From Coq Require Import List ZArith.

From ITree Require Import ITree.
From Vellvm Require Import LLVMAst.

From Checker Require Import Cogent Compiler.

(* Definition checkExp (cogentExp:expr) (llvmExp:exp typ) : Prop := compile cogentExp = llvmExp. *)

Import ListNotations.

Open Scope cogent_scope.

Definition prog : expr := `1 `+ `2 `* `3.

(* Compute run prog. *)

Compute (burn 100 (denote_expr prog)).

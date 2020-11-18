From Coq Require Import List String ZArith.

From ITree Require Import ITree.
From Vellvm Require Import LLVMAst.

From Checker Require Import Cogent Compiler.
From Input Require Import LLVM Source.

(* Definition checkExp (cogentExp:expr) (llvmExp:exp typ) : Prop := compile cogentExp = llvmExp. *)

Import ListNotations.

(* Compute run prog. *)

(* Open Scope cogent_scope.
Definition prog : expr := `1 `+ `2 `* `3.
Compute (burn 100 (denote_expr prog)). *)

(* LLVM Import *)

(* Compute LLVMInput. *)

(* Cogent Import *)

(* Compute CogentInput. *)
Compute (burn 100 (interp_cogent _ (denote_expr CogentInput))).

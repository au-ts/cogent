From Coq Require Import List String ZArith.

From ITree Require Import ITree. 
From Vellvm Require Import LLVMAst.

From Checker Require Import Cogent Compiler Denotation.
From Input Require Import LLVM Source.

Import ListNotations.

(* Semantics *)

Compute burn 50 (run_cogent CogentInput "main" UUnit).

(* Compile to AST *)

Compute compile_cogent CogentInput.

(* Compile to string *)

From QuickChick Require Import QuickChick.
From Vellvm Require Import ShowAST.

Local Open Scope string.

Compute match (compile_cogent CogentInput) with inl m => m | inr tles => newline ++ (show tles) end.


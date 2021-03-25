(* Taken from Helix's LLVMGen.Compiler.v *)

Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Vellvm.Semantics.IntrinsicsDefinitions.
Require Import Vellvm.Utils.Util.
Require Import Vellvm.Utils.Error.
Require Import Vellvm.Numeric.Floats.
Require Import Vellvm.Semantics.TopLevel.
Require Import Vellvm.Syntax.LLVMAst.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.
From Coq Require Import ZArith.

Require Import ExtLib.Structures.Monads.
Require Import HelixLib.ErrorWithState.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.

Set Implicit Arguments.
Set Strict Implicit.

(* Both [String] and [List] define [(++)] notation. We use both.
   To avoid implicit scoping, we re-define one for String *)
Notation "x @@ y" := (String.append x y) (right associativity, at level 60) : string_scope.

Notation Var := (texp typ).

Section withErrorStateMonad.

  Record IRState :=
    mkIRState
      {
        block_count: nat ;
        local_count: nat ;
        void_count : nat ;
        Γ: list Var
      }.

  Definition newState (arg:Var): IRState :=
    {|
      block_count := 0 ;
      local_count := 0 ;
      void_count  := 0 ;
      Γ := [arg]
    |}.

  Definition cerr := errS IRState.

  Definition setVars (s:IRState) (newvars:list Var): IRState :=
    {|
      block_count := block_count s ;
      local_count := local_count s ;
      void_count  := void_count s ;
      Γ := newvars
    |}.

  (* Returns n-th varable from state or error if [n] index oob *)
  Definition getStateVar (msg:string) (n:nat): cerr Var :=
    st <- get ;;
    option2errS msg (List.nth_error (Γ st) n).

  Definition evalCErrS {St:Type} {A:Type} (c : errS St A) (initial : St) : cerr A :=
    match c initial with
    | inl msg => raise msg
    | inr (s,v) => ret v
    end.

End withErrorStateMonad.

Definition add_comments (b:block typ) (xs:list string): block typ :=
  {|
    blk_id    := blk_id b;
    blk_phis  := blk_phis b;
    blk_code  := blk_code b;
    blk_term  := blk_term b;
    blk_comments := match blk_comments b with
                    | None => Some xs
                    | Some ys => Some (ys++xs)
                    end
  |}.

Definition add_comment (bs:list (block typ)) (xs:list string): list (block typ) :=
  match bs with
  | nil => nil
  | b::bs => (add_comments b xs)::bs
  end.

Definition incBlockNamed (prefix:string): (cerr block_id) :=
  st <- get  ;;
  put
    {|
      block_count := S (block_count st);
      local_count := local_count st ;
      void_count := void_count st ;
      Γ := Γ st
    |} ;;
  ret (Name (prefix ++ string_of_nat (block_count st))).

Definition incBlock := incBlockNamed "b".

Definition incLocalNamed (prefix:string): (cerr raw_id) :=
  st <- get ;;
  put
    {|
      block_count := block_count st ;
      local_count := S (local_count st) ;
      void_count  := void_count st ;
      Γ := Γ st
    |} ;;
  ret (Name (prefix @@ string_of_nat (local_count st))).

Definition incLocal := incLocalNamed "l".

Definition incVoid: (cerr int) :=
  st <- get ;;
  put
    {|
      block_count := block_count st ;
      local_count := local_count st ;
      void_count  := S (void_count st) ;
      Γ := Γ st
    |} ;;
  ret (Z.of_nat (void_count st)).

Definition addVars (newvars: list Var): cerr unit :=
  st <- get ;;
  put
    {|
      block_count := block_count st ;
      local_count := local_count st ;
      void_count  := void_count st ;
      Γ := newvars ++ Γ st
    |}.

Definition intrinsic_exp (d:declaration typ): exp typ :=
  EXP_Ident (ID_Global (dc_name d)).

(* TODO: move *)
Fixpoint drop_err {A:Type} (n:nat) (lst:list A) : err (list A)
  := match n, lst with
     | O, xs => ret xs
     | S n', (_::xs) => drop_err n' xs
     | _, _ => raise "drop on empty list"
     end.

Definition dropVars (n: nat): cerr unit :=
  st <- get ;;
  Γ' <- err2errS (drop_err n (Γ st)) ;;
  put {|
      block_count := block_count st ;
      local_count := local_count st ;
      void_count  := void_count st ;
      Γ := Γ'
    |}.

Definition swap_err {A:Type} (lst:list A) : err (list A)
  := match lst with
     | (x :: y :: xs) => ret (y :: x :: xs)
     | _ => raise "drop on empty list"
     end.

(* Swap top most elements on list. Used in IMapLoopBody *)
Definition swapVars : cerr unit :=
  st <- get ;;
  Γ' <- err2errS (swap_err (Γ st)) ;;
  put {|
      block_count := block_count st ;
      local_count := local_count st ;
      void_count  := void_count st ;
      Γ := Γ'
    |}.

(* Result and list of blocks with entry point *)
Definition segment:Type := Var * block_id * list (block typ).

Definition body_non_empty_cast (body : list (block typ)) : cerr (block typ * list (block typ)) :=
  match body with
  | [] => raise "Attempting to generate a function containing no block"
  | b::body => ret (b,body)
  end.

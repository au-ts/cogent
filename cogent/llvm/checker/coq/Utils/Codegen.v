From Coq Require Import List ZArith String.

From ExtLib Require Import Structures.Monads.

From Vellvm Require Import LLVMAst Util Utils.Error.

From Checker Require Import Utils.ErrorWithState.

Import ListNotations.
Import MonadNotation.

Local Open Scope monad_scope.

Section HelixInspired.

  Notation "x @@ y" := (String.append x y) (right associativity, at level 60) : string_scope.

  Record CodegenState :=
    mkCodegenState
      {
        block_count : nat ;
        local_count : nat ;
        void_count : nat ;
        Γ : list (texp typ)
      }.

  Definition cerr := errS CodegenState.

  (* Definition setVars (s : CodegenState) (newvars : list (texp typ)) : CodegenState :=
    {|
      block_count := block_count s ;
      local_count := local_count s ;
      void_count  := void_count s ;
      Γ := newvars
    |}. *)

  (* Returns n-th varable from state or error if [n] index oob *)
  Definition getStateVar (msg : string) (n : nat) : cerr (texp typ) :=
    st <- get ;;
    option2errS msg (List.nth_error (Γ st) n).

  (* Definition evalCErrS {St : Type} {A : Type} (c : errS St A) (initial : St) : cerr A :=
    match c initial with
    | inl msg => raise msg
    | inr (s,v) => ret v
    end. *)

  (* Definition add_comments (b : block typ) (xs : list string) : block typ :=
    {|
      blk_id    := blk_id b;
      blk_phis  := blk_phis b;
      blk_code  := blk_code b;
      blk_term  := blk_term b;
      blk_comments := match blk_comments b with
                      | None => Some xs
                      | Some ys => Some (ys++xs)
                      end
    |}. *)

  (* Definition add_comment (bs : list (block typ)) (xs : list string) : list (block typ) :=
    match bs with
    | nil => nil
    | b::bs => (add_comments b xs)::bs
    end. *)

  Definition incBlockNamed (prefix : string) : (cerr block_id) :=
    st <- get  ;;
    put
      {|
        block_count := S (block_count st);
        local_count := local_count st ;
        void_count := void_count st ;
        Γ := Γ st
      |} ;;
    ret (Name (prefix ++ string_of_nat (block_count st))).

  Definition incBlock : (cerr block_id) :=
    st <- get  ;;
    put
      {|
        block_count := S (block_count st);
        local_count := local_count st ;
        void_count := void_count st ;
        Γ := Γ st
      |} ;;
    ret (Anon (Z.of_nat (block_count st))).

  Definition incLocalNamed (prefix : string) : (cerr raw_id) :=
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

  Definition incVoid : (cerr int) :=
    st <- get ;;
    put
      {|
        block_count := block_count st ;
        local_count := local_count st ;
        void_count  := S (void_count st) ;
        Γ := Γ st
      |} ;;
    ret (Z.of_nat (void_count st)).

  Definition addVars (newvars : list (texp typ)) : cerr unit :=
    st <- get ;;
    put
      {|
        block_count := block_count st ;
        local_count := local_count st ;
        void_count  := void_count st ;
        Γ := newvars ++ Γ st
      |}.

  Fixpoint drop_err {A : Type} (n : nat) (lst : list A) : err (list A)
    := match n, lst with
      | O, xs => ret xs
      | S n', (_::xs) => drop_err n' xs
      | _, _ => raise "drop on empty list"
      end.

  Definition dropVars (n : nat) : cerr unit :=
    st <- get ;;
    Γ' <- err2errS (drop_err n (Γ st)) ;;
    put {|
        block_count := block_count st ;
        local_count := local_count st ;
        void_count  := void_count st ;
        Γ := Γ'
      |}.

  Definition body_non_empty_cast (body : list (block typ)) : cerr (block typ * list (block typ)) :=
    match body with
    | [] => raise "Attempting to generate a function containing no block"
    | b::body => ret (b,body)
    end.

End HelixInspired.

Section AdditionalHelpers.

  Definition code_block (id next : block_id) (c : code typ) : block typ := {|
    blk_id    := id ;
    blk_phis  := [];
    blk_code  := c;
    blk_term  := TERM_Br_1 next;
    blk_comments := None
  |}.

  Definition start_state (t : typ) : CodegenState := {|
    block_count := 0 ;
    local_count := 0 ;
    void_count  := 0 ;
    Γ := [(t, EXP_Ident (ID_Local (Name "a0")))]
  |}.

End AdditionalHelpers.

From Coq Require Import List ZArith String.

From ExtLib Require Import Structures.Monads.
From ITree Require Import ITree Events.State Events.Exception Events.FailFacts.
From Vellvm Require Import Util Utils.Error.

From Checker Require Import Cogent.

Import Monads.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Inductive uval : Set :=
| UPrim (l : lit)
| URecord (us : list (uval * repr))
| UUnit
| UPtr (a : addr) (r : repr).

Variant VarE : Type -> Type :=
| PeekVar (i : index) : VarE uval
| PushVar (u : uval) : VarE unit
| PopVar : VarE unit.

Variant MemE : Type -> Type :=
| LoadMem (a : addr) : MemE (option uval)
| StoreMem (a : addr) (u : uval) : MemE unit.

Definition FailE := exceptE string.

Definition CogentE := VarE +' MemE +' FailE.

Section Denote.

  Definition option_bind {A T} (x : option A) (f : A -> T) (m : string) : itree CogentE T := 
    match x with
    | Some y => ret (f y)
    | None => throw m
    end.

  Definition extract_prim (x : uval) : itree CogentE lit :=
    match x with
    | UPrim v => ret v
    | _ => throw "not a prim"
    end.
  
  Definition denote_prim (op : prim_op) (xs : list uval) : itree CogentE uval := 
    xs' <- map_monad extract_prim xs ;;
    option_bind (eval_prim_op op xs') UPrim "op error".

  Definition access_member (fs : list (uval * repr)) (f : nat) : itree CogentE uval :=
    option_bind (nth_error fs f) fst "invalid member access".
  
  Fixpoint denote_expr (e : expr) : itree CogentE uval :=
    match e with
    | Prim op os =>
        os' <- map_monad denote_expr os ;;
        denote_prim op os'
    | Lit l => ret (UPrim l)
    | Var i => trigger (PeekVar i)
    | Let e b => 
        e' <- denote_expr e ;;
        trigger (PushVar e') ;;
        b' <- denote_expr b ;;
        trigger PopVar ;;
        ret b'
    | Unit => ret UUnit
    | If c t e =>
        c' <- denote_expr c ;;
        match c' with
        | UPrim (LBool b) => denote_expr (if b then t else e)
        | _ => throw "expression is not a boolean"
        end
    | Cast t e =>
        e' <- denote_expr e ;;
        match e' with
        | UPrim l => option_bind (cast_to t l) UPrim "invalid cast"
        | _ => throw "invalid cast"
        end
    | Struct ts es =>
        es' <- map_monad denote_expr es ;;
        ret (URecord (combine es' (map type_repr ts)))
    | Member e f =>
        e' <- denote_expr e ;;
        match e' with
        | URecord fs => access_member fs f
        | UPtr p r =>
            m <- trigger (LoadMem p) ;;
            match m with
            | Some (URecord fs) => access_member fs f
            | _ => throw "invalid memory access"
            end
        | _ => throw "expression is not a record"
        end
    end.

  Definition denote_fun (b : expr) : uval -> itree CogentE uval :=
    fun a =>
      trigger (PushVar a) ;;
      b' <- denote_expr b ;;
      trigger PopVar ;;
      ret b'.

  (* Definition denote_funs (p : cogent_prog) (uval -> itree E uval ) : = .
  
  
  Definition denote_cogent (p : cogent_prog) := . *)
  

End Denote.

From ExtLib Require Import Data.Map.FMapAList Core.RelDec Data.String Structures.Maps.

Section Interpretation.

  Definition locals := list uval.
  Definition empty_locals : locals:= [].
  
  Definition handle_var : VarE ~> stateT locals (itree (MemE +' FailE)) :=
    fun _ e s =>
      match e with
      | PeekVar i =>
          match nth_error s i with
          | Some v => ret (s, v)
          | None => throw "unknown variable"
          end
      | PushVar u => ret (u :: s, tt)
      | PopVar => ret (tl s, tt)
      end.

  Definition interp_var : itree CogentE ~> stateT locals (itree (MemE +' FailE)) :=
    interp_state (case_ handle_var pure_state).

  Definition memory := alist addr uval.
  Definition empty_memory : memory := empty.
  Definition dummy_memory : memory := 
    alist_add _ 23 (URecord [(UPrim (LU8 5), RPrim (Num U8))]) empty_memory.

  Definition handle_mem : MemE ~> stateT memory (itree FailE) :=
    fun _ e s =>
      match e with
      | LoadMem a => ret (s, alist_find _ a s)
      | StoreMem a u => ret (alist_add _ a u s, tt)
      end.
  
  Definition interp_mem : itree (MemE +' FailE) ~> stateT memory (itree FailE) :=
    interp_state (case_ handle_mem pure_state).

  (* from Helix *)
  Definition handle_failure : FailE ~> failT (itree void1) :=
    fun _ _ => ret None. (* want to keep error message somehow? *)

  Definition inject_signature {E} : void1 ~> E := fun _ (x : void1 _) => match x with end.
  Hint Unfold inject_signature : core.
  (* end from Helix *)

  Definition interp_cogent {E A} (l0 : itree CogentE A) (vars : locals) (mem : memory) : failT (itree E) (memory * (locals * A)) :=
    let l1 := interp_var _ l0 vars in
    let l2 := interp_mem _ l1 mem in
    let l3 := interp_fail handle_failure l2 in
    translate inject_signature l3.

  Definition run_cogent (a : uval) (f : expr) : failT (itree void1) (memory * (locals * uval)) :=
    interp_cogent (denote_fun f a) empty_locals dummy_memory.

End Interpretation.

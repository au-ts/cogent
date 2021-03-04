From Coq Require Import List String.

From ExtLib Require Import Structures.Monads.
From ITree Require Import ITree Events.State Events.Exception Events.FailFacts.
From Vellvm Require Import Util.

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
| UPtr (r : repr).

Variant VarE : Type -> Type :=
| PeekVar (i : index) : VarE uval
| PushVar (u : uval) : VarE unit
| PopVar : VarE unit.

Definition FailE := exceptE string.

Definition CogentE := VarE +' FailE.

Section Denote.

  Definition extract_prim (x : uval) : itree CogentE lit :=
    match x with
    | UPrim v => ret v
    | _ => throw "not a prim"
    end.
  
  Definition denote_prim (op : prim_op) (xs : list uval) : itree CogentE uval := 
    xs' <- map_monad extract_prim xs ;;
    match eval_prim_op op xs' with
    | Some p => ret (UPrim p)
    | None => throw "op error"
    end.

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
        | _ => throw "condition is not boolean"
        end
    | Cast t e =>
        e' <- denote_expr e ;;
        match e' with
        | UPrim l => 
            match cast_to t l with
            | Some l' => ret (UPrim l')
            | None => throw "invalid cast"
            end
        | _ => throw "invalid cast"
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

Section Interpretation.

  Definition local_vars := list uval.

  Definition handle_var : VarE ~> stateT local_vars (itree FailE) :=
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

  Definition interp_var : itree CogentE ~> stateT local_vars (itree FailE) :=
    interp_state (case_ handle_var pure_state).

  (* from Helix *)
  Definition handle_failure : FailE ~> failT (itree void1) :=
    fun _ _ => ret None.

  Definition inject_signature {E} : void1 ~> E := fun _ (x : void1 _) => match x with end.
  Hint Unfold inject_signature : core.

  Definition interp_cogent {E A} (t : itree CogentE A) (vars : local_vars) : failT (itree E) (local_vars * A) :=
    translate inject_signature (interp_fail handle_failure (interp_var _ t vars)).
  (* end from Helix *)

  Definition run_cogent (a : uval) (f : expr) : failT (itree void1) (local_vars * uval) :=
    interp_cogent (denote_fun f a) [].

End Interpretation.

From Coq Require Import List.

From ExtLib Require Import Structures.Monads.
From ITree Require Import ITree.
From Vellvm Require Import Util.

From Checker Require Import Cogent.

Import Monads.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Inductive uval : Set :=
| UPrim (l:lit)
| UUnit.

Variant CogentState : Type -> Type :=
| PeekVar (i:index) : CogentState uval
| PushVar (u:uval) : CogentState unit
| PopVar : CogentState unit.

Section Denote.

  Context {eff : Type -> Type}.
  Context {HasCogentState : CogentState -< eff}.

  Definition denote_prim (op:prim_op) (xs:list uval) : uval := 
    UPrim (eval_prim_op op (map (fun x => match x with UPrim v => v | _ => default end) xs)).

  Fixpoint denote_expr (e:expr) : itree eff uval :=
    match e with
    | Prim op os =>
        os' <- map_monad denote_expr os ;;
        ret (denote_prim op os')
    | Lit l => ret (UPrim l)
    | Var i => trigger (PeekVar i)
    | Let e b => 
        e' <- denote_expr e ;;
        trigger (PushVar e') ;;
        b' <- denote_expr b ;;
        trigger PopVar ;;
        ret b'
    | _ => ret UUnit
    end.

  Definition denote_fun (b:expr) : uval -> itree eff uval :=
    fun a =>
      trigger (PushVar a) ;;
      b' <- denote_expr b ;;
      trigger PopVar ;;
      ret b'.

End Denote.

Definition env := list uval.

Definition handle_state : forall A, CogentState A -> stateT env (itree void1) A :=
fun _ e γ =>
  match e with
  | PeekVar i => ret (γ, nth i γ UUnit)
  | PushVar u => ret (u :: γ, tt)
  | PopVar => ret (tl γ, tt)
  end.

Definition interp_cogent {A} (t:itree CogentState A) : itree void1 (env * A) :=
  interp handle_state t [].

Definition run_cogent (a:uval) (f:expr) := interp_cogent (denote_fun f a).

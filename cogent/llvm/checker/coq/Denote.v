From Coq Require Import List.

From ExtLib Require Import Structures.Monads.
From ITree Require Import ITree Events.State.
From Vellvm Require Import Util.

From Checker Require Import Cogent.

Import Monads.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Inductive uval : Set :=
| UPrim (l:lit)
| UUnit
| UError.

Variant VarE : Type -> Type :=
| PeekVar (i:index) : VarE uval
| PushVar (u:uval) : VarE unit
| PopVar : VarE unit.

Section Denote.

  Context {E : Type -> Type}.
  Context {HasVar : VarE -< E}.

  Definition denote_prim (op:prim_op) (xs:list uval) : uval := 
    UPrim (eval_prim_op op (map (fun x => match x with UPrim v => v | _ => default end) xs)).

  Fixpoint denote_expr (e:expr) : itree E uval :=
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
    | Unit => ret UUnit
    | If c t e =>
        c' <- denote_expr c ;;
        match c' with
        | UPrim (LBool b) => denote_expr (if b then t else e)
        | _ => ret UError
        end
    | Cast t e =>
        e' <- denote_expr e ;;
        ret match e' with
        | UPrim l => 
            match cast_to t l with
            | Some l' => UPrim l'
            | None => UError
            end
        | _ => UError
        end
    | _ => ret UError
    end.

  Definition denote_fun (b:expr) : uval -> itree E uval :=
    fun a =>
      trigger (PushVar a) ;;
      b' <- denote_expr b ;;
      trigger PopVar ;;
      ret b'.

  (* Definition denote_funs (p:cogent_prog) (uval -> itree E uval ):= .
  
  
  Definition denote_cogent (p:cogent_prog) := . *)
  

End Denote.

Definition vars := list uval.

Definition h_var {E : Type -> Type } `{stateE vars -< E} : VarE ~> itree E :=
  fun _ e =>
    match e with
    | PeekVar i => s <- get ;; ret (nth i s UError)
    | PushVar u => s <- get ;; put (u :: s)
    | PopVar => s <- get ;; put (tl s)
    end.


Definition interp_cogent {E A} (t:itree (VarE +' E) A) : stateT vars (itree E) A :=
  let t' := interp (bimap h_var (id_ E)) t in
  run_state t'.



Definition run_cogent (a:uval) (f:expr) : itree void1 (vars * uval) :=
  interp_cogent (denote_fun f a) [].

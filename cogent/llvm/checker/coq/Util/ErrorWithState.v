(* Lifted from https://github.com/vzaliva/helix/blob/master/coq/Util/ErrorWithState.v *)

Require Import Coq.Strings.String.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadExc.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.EitherMonad.

Require Import Vellvm.Utils.Error.

Section withState.

  Variable St : Type.
  
  Definition errS A := St -> string + (St*A).

  Global Instance Monad_errS: Monad errS :=
    { ret  := fun _ x => fun s => inr (s,x)
      ; bind := fun _ _ m f => fun s => match m s with
                                  | inl v => inl v
                                  | inr (s',x) => f x s'
                                  end
    }.

  Global Instance Exception_errS : MonadExc string errS :=
    { raise := fun _ v => fun s => inl v
      ; catch := fun _ c h => fun s => match c s with
                                 | inl v => h v s
                                 | inr x => inr x
                                 end
    }.

  Global Instance State_errS: MonadState St errS :=
    {
      get := fun s => inr (s,s)
      ; put := fun t s => inr (t, tt)
    }.

  (* Unwrapping/running monad *)
  
  (* Returns value *)
  Definition evalErrS {A:Type} (c : errS A) (initial : St) : err A :=
  match c initial with
  | inl msg => raise msg
  | inr (s,v) => ret v
  end.

  (* Returns state *)
  Definition execErrS {A:Type} (c : errS A) (initial : St) : err St :=
  match c initial with
  | inl msg => raise msg
  | inr (s,v) => ret s
  end.

  (* -- lifting [err] -- *)

  Definition err2errS {A: Type}: (err A) -> (errS A)
    := fun e => match e with
             | inl msg => raise msg
             | inr v => ret v
             end.

  (* -- lifting [option] -- *)
  
  Definition option2errS {A: Type} (msg:string) (o:option A): (errS A)
    := match o with
       | Some v => ret v
       | None => raise msg
       end.
  
End withState.

Arguments option2errS {St} {A} (_) (_).
Arguments err2errS {St} {A} (_).
Arguments evalErrS {St} {A} (_) (_).
Arguments execErrS {St} {A} (_) (_).
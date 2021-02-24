(* See: https://github.com/coq-community/coq-ext-lib/issues/48 *)

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monoid.

Set Implicit Arguments.
Set Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Section StateType.
  Variable S : Type.

  Record state (t : Type) : Type := mkState
  { runState : S -> t * S }.

  Definition evalState {t} (c : state t) (s : S) : t :=
    fst (runState c s).

  Definition execState {t} (c : state t) (s : S) : S :=
    snd (runState c s).


  Global Instance Monad_state : Monad state :=
  { ret  := fun _ v => mkState (fun s => (v, s))
  ; bind := fun _ _ c1 c2 =>
    mkState (fun s =>
      let (v,s) := runState c1 s in
      runState (c2 v) s)
  }.

  Global Instance MonadState_state : MonadState S state :=
  { get := mkState (fun x => (x,x))
  ; put := fun v => mkState (fun _ => (tt, v))
  }.

End StateType.

Arguments evalState {S} {t} (c) (s).
Arguments execState {S} {t} (c) (s).

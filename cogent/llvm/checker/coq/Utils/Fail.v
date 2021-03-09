From Coq Require Import String.

From ExtLib Require Import Structures.Monad.

From ITree Require Import Basics.

Section FailT.

  (* nicer failT that keeps track of first message, but no proofs *)
  (* replace with ITree.Events.FailFacts if need be *)

  Context {m : Type -> Type} {Fm: Functor.Functor m} {Mm : Monad m} {MIm : MonadIter m}.

  Definition failT (m : Type -> Type) (a : Type) : Type :=
    m (string + a)%type.

  Global Instance failT_fun : Functor.Functor (failT m) :=
  {|
    Functor.fmap := fun x y f => 
      Functor.fmap (fun x => match x with | inl x => inl x | inr x => inr (f x) end)
  |}.

  Global Instance failT_monad : Monad (failT m) :=
  {|
    ret := fun _ x => ret (inr x);
    bind := fun _ _ c k =>
      bind (m := m) c (fun x => match x with | inl x => ret (inl x) | inr x => k x end)
  |}.

  Global Instance failT_iter  : MonadIter (failT m) :=
    fun A I body i => Basics.iter (M := m) (I := I) (R := string + A) 
      (fun i => bind (m := m)
        (body i)
        (fun x =>
          match x with
          | inl x       => ret (inr (inl x))
          | inr (inl j) => ret (inl j)
          | inr (inr a) => ret (inr (inr a))
          end))
      i.

End FailT.

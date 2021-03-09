From Coq Require Import List.

From ExtLib Require Import Structures.Reducible.

Import ListNotations.

Global Instance Foldable_pair {T} : Foldable (T * T) T :=
  fun _ f x '(a, b) => f a (f b x).

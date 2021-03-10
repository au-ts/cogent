From Coq Require Import String.

From ExtLib Require Import Structures.Reducible.

Section Pair.

Global Instance Foldable_pair {T} : Foldable (T * T) T :=
  fun _ f x '(a, b) => f a (f b x).

End Pair.


From ExtLib Require Import Data.String Core.RelDec Structures.Maps Data.Map.FMapAList.

From ITree Require Import Events.MapDefault.

Section Map.

(* from https://github.com/DeepSpec/InteractionTrees/blob/master/tutorial/Imp.v *)

Instance RelDec_string : RelDec (@eq string) :=
  { rel_dec := fun s1 s2 => if string_dec s1 s2 then true else false}.

Instance RelDec_string_Correct: RelDec_Correct RelDec_string.
Proof.
  constructor; intros x y.
  split.
  - unfold rel_dec; simpl.
    destruct (string_dec x y) eqn:EQ; [intros _; apply string_dec_sound; assumption | intros abs; inversion abs].
  - intros EQ; apply string_dec_sound in EQ; unfold rel_dec; simpl; rewrite EQ; reflexivity.
Qed.

End Map.
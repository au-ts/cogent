(* Taken from Helix's LLVMGen.IdLemmas.v *)

(** * Valid identifiers

  When generating variable and block id names, we allow any purely alphabetical prefix
  to be appended with the current freshness generator.
  
  The predicate [is_correct_prefix] is used to check prefixes. It computes and can therefore always simply be discharged by [reflexivity].
  In particular [solve_prefix] takes care of it.

  The main result of this file is [valid_prefix_neq_differ] ensuring that the variables we generate are distinct without having to worry about the prefixes.

*)

Require Import HelixLib.Correctness_Prelude.

Set Implicit Arguments.
Set Strict Implicit.

Import  Ascii. 
Definition is_connector (c : ascii) : bool :=
  match c with
  | "095" => true
  | _ => false
  end.

Definition is_alpha (c : ascii) : bool :=
  if CeresString.is_upper c then true else if
      CeresString.is_lower c then true else
      if is_connector c then true else false.

Definition is_correct_prefix (s : string) : bool :=
  CeresString.string_forall is_alpha s.

Lemma string_forall_forallb (f : ascii → bool) (s : string) :
    CeresString.string_forall f s
    <->
    forallb f (list_ascii_of_string s).
Admitted.

Lemma list_ascii_of_string_append :
  forall s1 s2,
    list_ascii_of_string (s1 @@ s2) ≡
    List.app (list_ascii_of_string s1) (list_ascii_of_string s2).
Admitted.

Lemma string_forall_append (f : ascii → bool) (s1 s2 : string) :
  CeresString.string_forall f s1 ->
  CeresString.string_forall f s2 ->
  CeresString.string_forall f (s1 @@ s2).
Admitted.

Lemma string_of_nat_not_alpha : forall n,
  CeresString.string_forall (fun c => negb (is_alpha c)) (string_of_nat n).
Admitted.

Lemma is_correct_prefix_String : forall c s,
    is_correct_prefix (String c s) ->
    is_correct_prefix s /\ is_alpha c.
Admitted.

Import Ascii String.

Lemma valid_prefix_string_of_nat_aux :
  forall n k s,
    is_correct_prefix s ->
    string_of_nat n ≡ s @@ string_of_nat k ->
    n ≡ k /\ s ≡ EmptyString.
Admitted.

Lemma valid_prefix_string_of_nat_forward :
  forall s1 s2 n k,
    is_correct_prefix s1 ->
    is_correct_prefix s2 ->
    s1 @@ string_of_nat n ≡ s2 @@ string_of_nat k ->
    n ≡ k /\ s1 ≡ s2.
Admitted.
      
Lemma valid_prefix_neq_differ :
  forall s1 s2 n k,
    is_correct_prefix s1 ->
    is_correct_prefix s2 ->
    n ≢ k ->
    s1 @@ string_of_nat n ≢ s2 @@ string_of_nat k.
Admitted.

Lemma is_correct_prefix_append: forall s1 s2,
    is_correct_prefix s1 ->
    is_correct_prefix s2 ->
    is_correct_prefix (s1 @@ s2).
Admitted.

Hint Resolve is_correct_prefix_append : PREFIX.

Ltac solve_prefix :=
  try solve
      [ eauto with PREFIX
      | now (unfold append; cbn; reflexivity)
      ].

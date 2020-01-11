theory SquareProof
  imports
  "Square_Shallow_Normal"
begin

(* Our cogent function is available for us to use *)
value "square 5"

(* reasoning about our function *)
lemma square_correct: "square n = n^2"
  apply (induct n)
  using square_def apply simp
  using square_def apply simp
  by (simp add: power2_eq_square)

end
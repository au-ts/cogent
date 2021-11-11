(*
This file is generated by Cogent

*)

theory Generated_NormalProof
imports "CogentShallow.Shallow_Normalisation_Tac"
"Generated_Shallow_Desugar"
"Generated_Shallow_Normal"
begin

ML \<open>
val Cogent_functions = ["wordarray_get_u32","wordarray_length_u32","wordarray_put2_u32","add","sum_arr","dec","dec_arr","inc","inc_arr","mul","mul_arr"]
\<close>

ML \<open>
val normalisation_thms = normalisation_tac_all @{context} "Generated_Shallow_Desugar" "Generated_Shallow_Normal" [] [] Cogent_functions
\<close>


end
(*
This file is generated by Cogent

*)

theory Generated_TypeProof
imports "Cogent.TypeProofGen"
"Cogent.AssocLookup"
begin

definition
  abbreviatedType1 :: " Cogent.type"
where
  "abbreviatedType1 \<equiv> TRecord [(''arr'', (TCon ''WordArray'' [TPrim (Num U32)] (Boxed Writable undefined), Present)), (''idx'', (TPrim (Num U32), Present)), (''val'', (TPrim (Num U32), Present))] Unboxed"

lemmas abbreviated_type_defs =
  abbreviatedType1_def

definition
  wordarray_put2_0_type :: " Cogent.kind list \<times>  Cogent.type \<times>  Cogent.type"
where
  "wordarray_put2_0_type \<equiv> ([], (abbreviatedType1, TCon ''WordArray'' [TPrim (Num U32)] (Boxed Writable undefined)))"

definition
  wordarray_put2_u32_type :: " Cogent.kind list \<times>  Cogent.type \<times>  Cogent.type"
where
  "wordarray_put2_u32_type \<equiv> ([], (abbreviatedType1, TCon ''WordArray'' [TPrim (Num U32)] (Boxed Writable undefined)))"

definition
  wordarray_put2_u32 :: "string Cogent.expr"
where
  "wordarray_put2_u32 \<equiv> Let (Var 0) (App (AFun ''wordarray_put2_0'' []) (Var 0))"

ML \<open>
val Cogent_functions = ["wordarray_put2_u32"]
val Cogent_abstract_functions = ["wordarray_put2_0"]
\<close>

definition
  \<Xi> :: " string \<Rightarrow>  Cogent.kind list \<times>  Cogent.type \<times>  Cogent.type"
where
  "\<Xi> \<equiv> assoc_lookup [(''wordarray_put2_0'', wordarray_put2_0_type), (''wordarray_put2_u32'', wordarray_put2_u32_type)] ([], TUnit, TUnit)"

definition
  "\<xi> \<equiv> assoc_lookup [(''wordarray_put2_0'', (\<lambda>_ _. False))]"

definition
  "wordarray_put2_u32_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some abbreviatedType1] TyTrLeaf"

ML \<open> open TTyping_Tactics \<close>

ML_quiet \<open>
val typing_helper_1_script : tac list = [
(ForceTac [@{thm kinding_def},@{thm kinding_all_def},@{thm kinding_variant_def},@{thm kinding_record_def}])
] \<close>


lemma typing_helper_1[unfolded abbreviated_type_defs] :
  "kinding [] abbreviatedType1 {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic \<open> map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_1_script |> EVERY \<close>)
  done

ML_quiet \<open>
val typing_helper_2_script : tac list = [
(ForceTac [])
] \<close>


lemma typing_helper_2[unfolded abbreviated_type_defs] :
  "type_wellformed 0 abbreviatedType1"
  apply (unfold abbreviated_type_defs)?
  apply (tactic \<open> map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_2_script |> EVERY \<close>)
  done

ML_quiet \<open>
val typing_helper_3_script : tac list = [
(SimpTac ([],[(nth @{thms HOL.simp_thms} (25-1)),(nth @{thms HOL.simp_thms} (26-1))]))
] \<close>


lemma typing_helper_3[unfolded abbreviated_type_defs] :
  "list_all2 (kinding []) [] []"
  apply (unfold abbreviated_type_defs)?
  apply (tactic \<open> map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_3_script |> EVERY \<close>)
  done

ML_quiet \<open>
val typing_helper_4_script : tac list = [
(ForceTac [])
] \<close>


lemma typing_helper_4[unfolded abbreviated_type_defs] :
  "type_wellformed 0 (TFun abbreviatedType1 (TCon ''WordArray'' [TPrim (Num U32)] (Boxed Writable undefined)))"
  apply (unfold abbreviated_type_defs)?
  apply (tactic \<open> map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_4_script |> EVERY \<close>)
  done

ML_quiet \<open>
val wordarray_put2_u32_typecorrect_script : hints treestep list = [
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_1})]),
StepDown,
StepDown,
Val (KindingTacs [(RTac @{thm typing_helper_1})]),
StepUp,
Val (TypingTacs []),
Val (TypingTacs [(RTac @{thm typing_app}),(SplitsTac [SOME [(RTac @{thm split_comp.right}),(RTac @{thm type_wellformed_prettyI}),(SimpTac ([],@{thms type_wellformed.simps})),(RTac @{thm typing_helper_2})],NONE]),(RTac @{thm typing_afun'}),(SimpTac ([@{thm \<Xi>_def},@{thm wordarray_put2_0_type_def[unfolded abbreviated_type_defs]}],[])),(RTac @{thm typing_helper_3}),(SimpSolveTac ([],[])),(SimpSolveTac ([],[])),(RTac @{thm type_wellformed_prettyI}),(SimpTac ([],@{thms type_wellformed.simps})),(RTac @{thm typing_helper_4}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_1}]),(SimpSolveTac ([],[]))]),
StepUp,
StepUp
] \<close>


ML_quiet \<open>
val wordarray_put2_u32_ttyping_details_future = get_all_typing_details_future false @{context} "wordarray_put2_u32"
   wordarray_put2_u32_typecorrect_script
\<close>


lemma wordarray_put2_u32_typecorrect :
  "\<Xi>, prod.fst wordarray_put2_u32_type, (wordarray_put2_u32_typetree, [Some (prod.fst (prod.snd wordarray_put2_u32_type))]) T\<turnstile> wordarray_put2_u32 : prod.snd (prod.snd wordarray_put2_u32_type)"
  apply (tactic \<open> resolve_future_typecorrect @{context} wordarray_put2_u32_ttyping_details_future \<close>)
  done

ML_quiet \<open>
val (_, wordarray_put2_u32_typing_tree, wordarray_put2_u32_typing_bucket)
= Future.join wordarray_put2_u32_ttyping_details_future
\<close>


end

(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

(*
 * Slightly nontrivial testcase for C refinement.
 * Program specification generated from:
 *   cogent -Od --fnormalisation=knf --flet-in-if pass_middle-size-example.cogent -gpass_middle-size-example
 *   cogent -Od --fnormalisation=knf --flet-in-if pass_middle-size-example.cogent --type-proof=Middle --fml-typing-tree
 *)

theory Middle_C
imports
  "../Deep_Embedding_Auto"
  "../COGENT_Corres"
  "../Corres_Tac"
  "../TypeProofGen"
  "../Tidy"
begin

definition
  "abbreviatedType1 \<equiv> TRecord [(TRecord [(TRecord [(TPrim (Num U32), False), (TPrim (Num U32), False)] Writable, True), (TPrim Bool, False)] Writable, False), (TRecord [(TPrim (Num U32), False), (TPrim (Num U32), False)] Writable, False), (TPrim Bool, False), (TPrim (Num U32), False)] Unboxed"

definition
  "abbreviatedType2 \<equiv> TRecord [(TPrim (Num U32), False), (TPrim (Num U32), False)] Writable"

definition
  "abbreviatedType3 \<equiv> TRecord [(abbreviatedType2, True), (TPrim Bool, False)] Writable"

definition
  "abbreviatedType4 \<equiv> TRecord [(TRecord [(abbreviatedType2, False), (TPrim Bool, False)] Writable, False), (TPrim Bool, False)] Unboxed"

definition
  "abbreviatedType5 \<equiv> TRecord [(abbreviatedType2, False), (TPrim Bool, False)] Writable"

lemmas abbreviated_type_defs =
  abbreviatedType3_def
  abbreviatedType5_def
  abbreviatedType2_def
  abbreviatedType4_def
  abbreviatedType1_def

definition
  "foo_type \<equiv> ([], (TRecord [(abbreviatedType5, False), (TPrim Bool, False)] Unboxed, TRecord [(abbreviatedType3, False), (abbreviatedType2, False), (TPrim Bool, False), (TPrim (Num U32), False)] Unboxed))"

definition
  "foo \<equiv> Take (Var 0) 0 (Take (Var 1) 1 (Take (Var 2) 1 (If (Var 2) (Let (Put (Var 1) 1 (Var 2)) (Take (Var 0) 0 (Take (Var 0) 1 (Let (Lit (LU8 0)) (Let (Cast U32 (Var 0)) (Let (Put (Var 3) 1 (Var 0)) (Struct [abbreviatedType3, abbreviatedType2, TPrim Bool, TPrim (Num U32)] [Var 6, Var 0, Var 8, Var 3]))))))) (Let (Lit (LBool True)) (Let (Put (Var 2) 1 (Var 0)) (Take (Var 0) 0 (Let (Lit (LU8 0)) (Let (Cast U32 (Var 0)) (Let (Put (Var 2) 0 (Var 0)) (Let (Put (Var 4) 0 (Var 0)) (Take (Var 0) 0 (Take (Var 0) 1 (Let (Lit (LU8 0)) (Let (Cast U32 (Var 0)) (Let (Put (Var 3) 1 (Var 0)) (Struct [abbreviatedType3, abbreviatedType2, TPrim Bool, TPrim (Num U32)] [Var 6, Var 0, Var 15, Var 3]))))))))))))))))"

ML {*
val COGENT_functions = ["foo"]
val COGENT_abstract_functions = []
*}

definition
  "\<Xi> func_name' \<equiv> case func_name' of ''foo'' \<Rightarrow> foo_type"

definition
  "foo_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some abbreviatedType5, Some (TRecord [(abbreviatedType5, True), (TPrim Bool, False)] Unboxed)] (TyTrSplit (Cons None (Cons (Some TSK_L) (Cons None []))) [] TyTrLeaf [Some (TPrim Bool), Some (TRecord [(abbreviatedType5, True), (TPrim Bool, True)] Unboxed)] (TyTrSplit (Cons None (Cons (Some TSK_L) (Cons (Some TSK_L) (append (replicate 2 None) [])))) [] TyTrLeaf [Some (TPrim Bool), Some (TRecord [(abbreviatedType2, False), (TPrim Bool, True)] Writable)] (TyTrSplit (append (replicate 2 None) (Cons (Some TSK_S) (append (replicate 4 None) []))) [] TyTrLeaf [] (TyTrSplit (Cons (Some TSK_S) (Cons (Some TSK_S) (Cons (Some TSK_S) (append (replicate 4 None) [])))) [] (TyTrSplit (Cons None (Cons (Some TSK_L) (Cons (Some TSK_L) (append (replicate 4 None) [])))) [] TyTrLeaf [Some abbreviatedType5] (TyTrSplit (Cons (Some TSK_L) (append (replicate 7 None) [])) [] TyTrLeaf [Some abbreviatedType2, Some abbreviatedType3] (TyTrSplit (Cons (Some TSK_L) (append (replicate 9 None) [])) [] TyTrLeaf [Some (TPrim (Num U32)), Some (TRecord [(TPrim (Num U32), False), (TPrim (Num U32), True)] Writable)] (TyTrSplit (append (replicate 12 None) []) [] TyTrLeaf [Some (TPrim (Num U8))] (TyTrSplit (Cons (Some TSK_L) (append (replicate 12 None) [])) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (Cons (Some TSK_L) (append (replicate 2 None) (Cons (Some TSK_L) (append (replicate 10 None) [])))) [] TyTrLeaf [Some abbreviatedType2] TyTrLeaf)))))) [] (TyTrSplit (append (replicate 2 None) (Cons (Some TSK_L) (append (replicate 4 None) []))) [] TyTrLeaf [Some (TPrim Bool)] (TyTrSplit (Cons (Some TSK_L) (Cons None (Cons (Some TSK_L) (append (replicate 5 None) [])))) [] TyTrLeaf [Some abbreviatedType5] (TyTrSplit (Cons (Some TSK_L) (append (replicate 8 None) [])) [] TyTrLeaf [Some abbreviatedType2, Some abbreviatedType3] (TyTrSplit (append (replicate 11 None) []) [] TyTrLeaf [Some (TPrim (Num U8))] (TyTrSplit (Cons (Some TSK_L) (append (replicate 11 None) [])) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (Cons (Some TSK_L) (Cons None (Cons (Some TSK_L) (append (replicate 10 None) [])))) [] TyTrLeaf [Some abbreviatedType2] (TyTrSplit (Cons (Some TSK_L) (append (replicate 3 None) (Cons (Some TSK_L) (append (replicate 9 None) [])))) [] TyTrLeaf [Some abbreviatedType5] (TyTrSplit (Cons (Some TSK_L) (append (replicate 14 None) [])) [] TyTrLeaf [Some abbreviatedType2, Some abbreviatedType3] (TyTrSplit (Cons (Some TSK_L) (append (replicate 16 None) [])) [] TyTrLeaf [Some (TPrim (Num U32)), Some (TRecord [(TPrim (Num U32), False), (TPrim (Num U32), True)] Writable)] (TyTrSplit (append (replicate 19 None) []) [] TyTrLeaf [Some (TPrim (Num U8))] (TyTrSplit (Cons (Some TSK_L) (append (replicate 19 None) [])) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (Cons (Some TSK_L) (append (replicate 2 None) (Cons (Some TSK_L) (append (replicate 17 None) [])))) [] TyTrLeaf [Some abbreviatedType2] TyTrLeaf))))))))))))))))"

ML {* open TTyping_Tactics *}

ML_quiet {*
val typing_helper_1_script : tac list = [
(RTac @{thm kind_tprim})
] *}


lemma typing_helper_1[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim (Num U32)) {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_1_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_2_script : tac list = [
(RTac @{thm kind_trec}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_1}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_1}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_2[unfolded abbreviated_type_defs] :
  "kinding [] abbreviatedType2 {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_2_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_3_script : tac list = [
(RTac @{thm kind_tprim})
] *}


lemma typing_helper_3[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim Bool) {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_3_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_4_script : tac list = [
(RTac @{thm kind_trec}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_2}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_3}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_4[unfolded abbreviated_type_defs] :
  "kinding [] abbreviatedType5 {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_4_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_5_script : tac list = [
(RTac @{thm kind_trec[where k = "{E}"]}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_4}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_3}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_5[unfolded abbreviated_type_defs] :
  "kinding [] (TRecord [(abbreviatedType5, False), (TPrim Bool, False)] Unboxed) {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_5_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_6_script : tac list = [
(RTac @{thm kind_tprim})
] *}


lemma typing_helper_6[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim Bool) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_6_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_7_script : tac list = [
(RTac @{thm kind_trec[where k = "{E,S,D}"]}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_4}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_6}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_7[unfolded abbreviated_type_defs] :
  "kinding [] (TRecord [(abbreviatedType5, True), (TPrim Bool, False)] Unboxed) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_7_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_8_script : tac list = [
(RTac @{thm kind_trec[where k = "{E,S,D}"]}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_4}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_6}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_8[unfolded abbreviated_type_defs] :
  "kinding [] (TRecord [(abbreviatedType5, True), (TPrim Bool, True)] Unboxed) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_8_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_9_script : tac list = [
(RTac @{thm kind_trec[where k = "{E}"]}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_2}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_6}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_9[unfolded abbreviated_type_defs] :
  "kinding [] (TRecord [(abbreviatedType2, False), (TPrim Bool, True)] Writable) {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_9_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_10_script : tac list = [
(RTac @{thm kind_trec[where k = "{E}"]}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_2}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_3}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_10[unfolded abbreviated_type_defs] :
  "kinding [] abbreviatedType3 {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_10_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_11_script : tac list = [
(RTac @{thm kind_tprim[where k = "{E,S,D}"]})
] *}


lemma typing_helper_11[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim (Num U32)) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_11_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_12_script : tac list = [
(RTac @{thm kind_trec[where k = "{E}"]}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_1}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_11}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_12[unfolded abbreviated_type_defs] :
  "kinding [] (TRecord [(TPrim (Num U32), False), (TPrim (Num U32), True)] Writable) {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_12_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_13_script : tac list = [
(RTac @{thm kind_tprim[where k = "{E,S,D}"]})
] *}


lemma typing_helper_13[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim (Num U8)) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_13_script |> EVERY *})
  done

ML_quiet {*
val foo_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_4})],
KindingTacs [(RTac @{thm typing_helper_7})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_4})],
KindingTacs [(RTac @{thm typing_helper_6})],
KindingTacs [(RTac @{thm typing_helper_8})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_6})],
KindingTacs [(RTac @{thm typing_helper_6})],
KindingTacs [(RTac @{thm typing_helper_9})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_6})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_4})],
TypingTacs [(RTac @{thm typing_put'}),(SplitsTac (7,[(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_9})]),(2,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_6})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_9}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[@{thm Product_Type.prod.inject}])),(RTac @{thm typing_helper_6}),(RTac @{thm disjI2[where Q = "True"]}),(SimpTac ([],[])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_6}]),(SimpTac ([],[])),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_2})],
KindingTacs [(RTac @{thm typing_helper_10})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_2})],
KindingTacs [(RTac @{thm typing_helper_11})],
KindingTacs [(RTac @{thm typing_helper_12})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_11})],
KindingTacs [(RTac @{thm typing_helper_13})],
TypingTacs [(RTac @{thm typing_lit'}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_11})],
TypingTacs [(RTac @{thm typing_cast}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_13}]),(SimpTac ([],[])),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_2})],
TypingTacs [(RTac @{thm typing_put'}),(SplitsTac (14,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_11})]),(3,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_12})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_12}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[@{thm Product_Type.prod.inject}])),(RTac @{thm typing_helper_11}),(RTac @{thm disjI2[where Q = "True"]}),(SimpTac ([],[])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_11}]),(SimpTac ([],[])),(SimpTac ([],[]))],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_6})],
TypingTacs [(RTac @{thm typing_lit'}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_6}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_4})],
TypingTacs [(RTac @{thm typing_put'}),(SplitsTac (8,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_6})]),(2,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_9})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_9}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[@{thm Product_Type.prod.inject}])),(RTac @{thm typing_helper_6}),(RTac @{thm disjI2[where Q = "True"]}),(SimpTac ([],[])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_6}]),(SimpTac ([],[])),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_2})],
KindingTacs [(RTac @{thm typing_helper_10})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_2})],
KindingTacs [(RTac @{thm typing_helper_13})],
TypingTacs [(RTac @{thm typing_lit'}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_11})],
TypingTacs [(RTac @{thm typing_cast}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_13}]),(SimpTac ([],[])),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_2})],
TypingTacs [(RTac @{thm typing_put'}),(SplitsTac (13,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_11})]),(2,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_2})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_2}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[@{thm Product_Type.prod.inject}])),(RTac @{thm typing_helper_11}),(RTac @{thm disjI1}),(SimpTac ([],[])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_11}]),(SimpTac ([],[])),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_4})],
TypingTacs [(RTac @{thm typing_put'}),(SplitsTac (14,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_2})]),(4,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_10})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_10}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[@{thm Product_Type.prod.inject}])),(RTac @{thm typing_helper_2}),(RTac @{thm disjI2[where Q = "True"]}),(SimpTac ([],[])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_2}]),(SimpTac ([],[])),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_2})],
KindingTacs [(RTac @{thm typing_helper_10})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_2})],
KindingTacs [(RTac @{thm typing_helper_11})],
KindingTacs [(RTac @{thm typing_helper_12})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_11})],
KindingTacs [(RTac @{thm typing_helper_13})],
TypingTacs [(RTac @{thm typing_lit'}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_11})],
TypingTacs [(RTac @{thm typing_cast}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_13}]),(SimpTac ([],[])),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_2})],
TypingTacs [(RTac @{thm typing_put'}),(SplitsTac (21,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_11})]),(3,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_12})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_12}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[@{thm Product_Type.prod.inject}])),(RTac @{thm typing_helper_11}),(RTac @{thm disjI2[where Q = "True"]}),(SimpTac ([],[])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_11}]),(SimpTac ([],[])),(SimpTac ([],[]))],
TypingTacs []
] *}


ML_quiet {*
val foo_ttyping_details_future = get_all_typing_details_future @{context} "foo"
   foo_typecorrect_script*}

lemma foo_typecorrect :
  "\<Xi>, fst foo_type, (foo_typetree, [Some (fst (snd foo_type))]) T\<turnstile> foo : snd (snd foo_type)"
  apply (tactic {* resolve_future_typecorrect @{context} foo_ttyping_details_future *})
  done

ML_quiet {*
val (_, foo_typing_tree, foo_typing_bucket)
= Future.join foo_ttyping_details_future
*}



(* C semantics, generated by C parser *)
new_C_include_dir "../../cogent/tests"
install_C_file "pass_middle-size-example.c"

autocorres [ts_rules=nondet, no_opt, gen_word_heaps, skip_word_abs] "pass_middle-size-example.c"

instantiation bool_t_C :: cogent_C_val
begin
definition type_rel_bool_t_C_def:
  "type_rel typ (_ :: bool_t_C itself) \<equiv> (typ = RPrim Bool)"

definition val_rel_bool_t_C_def:
  "val_rel uv (x :: bool_t_C) \<equiv> (boolean_C x = 0 \<or> boolean_C x = 1) \<and>
                                uv = UPrim (LBool (boolean_C x \<noteq> 0))"
instance ..
end

(* Relation between COGENT and C data *)
local_setup{* local_setup_val_rel_type_rel_put_them_in_buckets "pass_middle-size-example.c" *}

(* Lemma bucket.*)
ML{* TypeRelSimp.get @{context} *}
ML{* ValRelSimp.get @{context} *}

lemmas val_rel_simps[ValRelSimp] = val_rel_word val_rel_ptr_def val_rel_bool_t_C_def
lemmas type_rel_simps[TypeRelSimp] = type_rel_word type_rel_ptr_def type_rel_bool_t_C_def

class cogent_C_heap = cogent_C_val +
  fixes is_valid    :: "lifted_globals \<Rightarrow> 'a ptr \<Rightarrow> bool"
  fixes heap        :: "lifted_globals \<Rightarrow> 'a ptr \<Rightarrow> 'a"
  fixes heap_update :: "(('a ptr \<Rightarrow> 'a) \<Rightarrow> 'a ptr \<Rightarrow> 'a) \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals"

local_setup{* local_setup_instantiate_cogent_C_heaps_store_them_in_buckets "pass_middle-size-example.c"*}
ML{* HeapSimp.get @{context}; IsValidSimp.get @{context} *}

locale middle_cogent = "pass_middle-size-example" + update_sem_init
begin

(* Relation between program heaps *)
definition
  heap_rel_ptr ::
  "(funtyp, abstyp, ptrtyp) store \<Rightarrow> lifted_globals \<Rightarrow>
   ('a :: cogent_C_heap) ptr \<Rightarrow> bool"
where
  "heap_rel_ptr \<sigma> h p \<equiv>
   (\<forall>uv.
     \<sigma> (ptr_val p) = Some uv \<longrightarrow>
     type_rel (uval_repr uv) TYPE('a) \<longrightarrow>
     is_valid h p \<and> val_rel uv (heap h p))"

lemma heap_rel_ptr_meta:
  "heap_rel_ptr = heap_rel_meta is_valid heap"
  by (simp add: heap_rel_ptr_def[abs_def] heap_rel_meta_def[abs_def])

local_setup{* local_setup_heap_rel "pass_middle-size-example.c" *}
print_theorems

definition state_rel :: "((funtyp, abstyp, ptrtyp) store \<times> lifted_globals) set"
where
  "state_rel = {(\<sigma>, h). heap_rel \<sigma> h}"

local_setup{* local_setup_take_put_member_case_esac_specialised_lemmas "pass_middle-size-example.c" *}
print_theorems

(* Lemma buckets are generated in the above local_setup.*)
ML{* TakeBoxed.get @{context} *}
ML{* TakeUnboxed.get @{context} *}
ML{* PutBoxed.get @{context} *}
ML{* LetPutBoxed.get @{context} *}
ML{* MemberBoxed.get @{context} *}
ML{* Case.get @{context} *}
ML{* MemberReadOnly.get @{context} *}

(* The set of thms the automation did not manage to prove.*)
ML{* Unborn_Thms.get @{context} *}

(* You can add new proofs using attributes.*)
declare TrueI[MemberReadOnly]
(* MemberBoxed is now augmented with True.*)
ML{* MemberReadOnly.get @{context} *}
declare TrueI[MemberReadOnly del]


(* Preprocess AutoCorres output *)
local_setup {* tidy_C_fun_def' "foo" *}
thm foo'_def foo'_def'

(* Defined late because it relies on bool_t_C *)
lemmas corres_if = corres_if_base[where bool_val' = boolean_C,
                     OF _ _ val_rel_bool_t_C_def[THEN meta_eq_to_obj_eq, THEN iffD1]]

(* Defined late because it relies on LET_TRUE *)
lemmas corres_nested_let = corres_nested_let_base[OF LET_TRUE_def]

(* Corres tactic *)
lemmas list_to_map_simps = list_to_map_more[where f=Var] list_to_map_singleton[where f=Var]

(* Proof using corres_tac *)
lemma foo_corres:
  "val_rel a a' \<Longrightarrow> corres state_rel foo (foo' a') \<xi> [a] \<Xi> [Some (fst (snd foo_type))] \<sigma> s"
  apply (tactic {* corres_tac @{context}
    (peel_two foo_typing_tree)
    @{thms foo_def foo'_def' foo_type_def abbreviated_type_defs} [] []
    @{thm corres_if} [] @{thms } @{thms } []
    @{thm LETBANG_TRUE_def} @{thms list_to_map_simps} true *})
  done
end
end

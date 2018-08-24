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
This build info header is now disabled by --fno-gen-header.
--------------------------------------------------------------------------------
We strongly discourage users from generating individual files for Isabelle
proofs, as it will end up with an inconsistent collection of output files (i.e.
Isabelle input files).
*)

theory Test_TypeProof_Normal imports
  "~/bilby/c-refinement/TypeProofGen"
  "~/bilby/cogent/isa/Mono"
  AutoCorres
begin

definition
  "abbreviatedType1 \<equiv> TRecord [(TUnit, False), (TUnit, False)] Unboxed"

definition
  "abbreviatedType2 \<equiv> TRecord [(TUnit, False), (TVar 0, False)] Unboxed"

definition
  "abbreviatedType3 \<equiv> TRecord [(TVar 0, False), (TVar 1, False)] Unboxed"

lemmas abbreviated_type_defs =
  abbreviatedType1_def
  abbreviatedType2_def
  abbreviatedType3_def

definition
  f_type :: " Cogent.kind list \<times>  Cogent.type \<times>  Cogent.type"
where
  "f_type \<equiv> ([{}, {}], (abbreviatedType3, abbreviatedType3))"

definition
  "f \<equiv> Take (Var 0) 0 (Take (Var 1) 1 (Struct [TVar 0, TVar 1] [Var 2, Var 0]))"

definition
  g_type :: " Cogent.kind list \<times>  Cogent.type \<times>  Cogent.type"
where
  "g_type \<equiv> ([{}], (abbreviatedType2, abbreviatedType2))"

definition
  "g \<equiv> Take (Var 0) 0 (Take (Var 1) 1 (Let (Struct [TUnit, TVar 0] [Var 2, Var 0]) (App (Fun f [TUnit, TVar 0]) (Var 0))))"

definition
  h_type :: " Cogent.kind list \<times>  Cogent.type \<times>  Cogent.type"
where
  "h_type \<equiv> ([], (abbreviatedType1, abbreviatedType1))"

definition
  "h \<equiv> Take (Var 0) 0 (Take (Var 1) 1 (Let (Struct [TUnit, TUnit] [Var 2, Var 0]) (App (Fun g [TUnit]) (Var 0))))"

ML {*
val Cogent_functions = ["f","g","h"]
val Cogent_abstract_functions = []
*}

definition
  \<Xi> :: " string \<Rightarrow>  Cogent.kind list \<times>  Cogent.type \<times>  Cogent.type"
where
  "\<Xi> func_name' \<equiv> case func_name' of ''f'' \<Rightarrow> f_type | ''g'' \<Rightarrow> g_type | ''h'' \<Rightarrow> h_type"

definition
  "f_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some (TVar 0), Some (TRecord [(TVar 0, True), (TVar 1, False)] Unboxed)] (TyTrSplit (Cons None (Cons (Some TSK_L) (Cons None []))) [] TyTrLeaf [Some (TVar 1), Some (TRecord [(TVar 0, True), (TVar 1, True)] Unboxed)] TyTrLeaf)"

definition
  "g_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some TUnit, Some (TRecord [(TUnit, True), (TVar 0, False)] Unboxed)] (TyTrSplit (Cons None (Cons (Some TSK_L) (Cons None []))) [] TyTrLeaf [Some (TVar 0), Some (TRecord [(TUnit, True), (TVar 0, True)] Unboxed)] (TyTrSplit (Cons (Some TSK_L) (Cons (Some TSK_L) (Cons (Some TSK_L) (append (replicate 2 None) [])))) [] TyTrLeaf [Some abbreviatedType2] TyTrLeaf))"

definition
  "h_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some TUnit, Some (TRecord [(TUnit, True), (TUnit, False)] Unboxed)] (TyTrSplit (Cons None (Cons (Some TSK_L) (Cons None []))) [] TyTrLeaf [Some TUnit, Some (TRecord [(TUnit, True), (TUnit, True)] Unboxed)] (TyTrSplit (Cons (Some TSK_L) (Cons (Some TSK_L) (Cons (Some TSK_L) (append (replicate 2 None) [])))) [] TyTrLeaf [Some abbreviatedType1] TyTrLeaf))"

ML {* open TTyping_Tactics *}

ML_quiet {*
val typing_helper_1_script : tac list = [
(RTac @{thm kind_tvar}),
(SimpTac ([],[])),
(SimpTac ([],[]))
] *}


lemma typing_helper_1[unfolded abbreviated_type_defs] :
  "kinding [{}, {}] (TVar 0) {}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_1_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_2_script : tac list = [
(RTac @{thm kind_tvar}),
(SimpTac ([],[])),
(SimpTac ([],[]))
] *}


lemma typing_helper_2[unfolded abbreviated_type_defs] :
  "kinding [{}, {}] (TVar 1) {}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_2_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_3_script : tac list = [
(RTac @{thm kind_trec[where k = "{}"]}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_1}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_2}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_3[unfolded abbreviated_type_defs] :
  "kinding [{}, {}] abbreviatedType3 {}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_3_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_4_script : tac list = [
(RTac @{thm kind_trec[where k = "{}"]}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_1}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_2}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_4[unfolded abbreviated_type_defs] :
  "kinding [{}, {}] (TRecord [(TVar 0, True), (TVar 1, False)] Unboxed) {}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_4_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_5_script : tac list = [
(RTac @{thm kind_trec[where k = "{E,S,D}"]}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_1}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_2}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_5[unfolded abbreviated_type_defs] :
  "kinding [{}, {}] (TRecord [(TVar 0, True), (TVar 1, True)] Unboxed) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_5_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_6_script : tac list = [
(RTac @{thm kind_tunit})
] *}


lemma typing_helper_6[unfolded abbreviated_type_defs] :
  "kinding [{}] TUnit {}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_6_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_7_script : tac list = [
(RTac @{thm kind_tvar}),
(SimpTac ([],[])),
(SimpTac ([],[]))
] *}


lemma typing_helper_7[unfolded abbreviated_type_defs] :
  "kinding [{}] (TVar 0) {}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_7_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_8_script : tac list = [
(RTac @{thm kind_trec[where k = "{}"]}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_6}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_7}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_8[unfolded abbreviated_type_defs] :
  "kinding [{}] abbreviatedType2 {}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_8_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_9_script : tac list = [
(RTac @{thm kind_tunit[where k = "{E,S,D}"]})
] *}


lemma typing_helper_9[unfolded abbreviated_type_defs] :
  "kinding [{}] TUnit {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_9_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_10_script : tac list = [
(RTac @{thm kind_trec[where k = "{}"]}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_9}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_7}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_10[unfolded abbreviated_type_defs] :
  "kinding [{}] (TRecord [(TUnit, True), (TVar 0, False)] Unboxed) {}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_10_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_11_script : tac list = [
(RTac @{thm kind_trec[where k = "{E,S,D}"]}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_9}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_7}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_11[unfolded abbreviated_type_defs] :
  "kinding [{}] (TRecord [(TUnit, True), (TVar 0, True)] Unboxed) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_11_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_12_script : tac list = [
(SimpTac ([],[(nth @{thms HOL.simp_thms} (25-1)),(nth @{thms HOL.simp_thms} (26-1))])),
(RTac @{thm conjI}),
(RTac @{thm typing_helper_6}),
(RTac @{thm typing_helper_7})
] *}


lemma typing_helper_12[unfolded abbreviated_type_defs] :
  "list_all2 (kinding [{}]) [TUnit, TVar 0] [{}, {}]"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_12_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_13_script : tac list = [
(RTac @{thm kind_tunit})
] *}


lemma typing_helper_13[unfolded abbreviated_type_defs] :
  "kinding [] TUnit {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_13_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_14_script : tac list = [
(RTac @{thm kind_trec[where k = "{E,S,D}"]}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_13}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_13}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_14[unfolded abbreviated_type_defs] :
  "kinding [] abbreviatedType1 {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_14_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_15_script : tac list = [
(RTac @{thm kind_trec[where k = "{E,S,D}"]}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_13}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_13}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_15[unfolded abbreviated_type_defs] :
  "kinding [] (TRecord [(TUnit, True), (TUnit, False)] Unboxed) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_15_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_16_script : tac list = [
(RTac @{thm kind_trec[where k = "{E,S,D}"]}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_13}),
(RTac @{thm kind_record_cons2}),
(RTac @{thm typing_helper_13}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_16[unfolded abbreviated_type_defs] :
  "kinding [] (TRecord [(TUnit, True), (TUnit, True)] Unboxed) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_16_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_17_script : tac list = [
(RTac @{thm kind_tunit})
] *}


lemma typing_helper_17[unfolded abbreviated_type_defs] :
  "kinding [] TUnit {}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_17_script |> EVERY *})
  done

ML_quiet {*
val typing_helper_18_script : tac list = [
(SimpTac ([],[(nth @{thms HOL.simp_thms} (25-1)),(nth @{thms HOL.simp_thms} (26-1))])),
(RTac @{thm typing_helper_17})
] *}


lemma typing_helper_18[unfolded abbreviated_type_defs] :
  "list_all2 (kinding []) [TUnit] [{}]"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_18_script |> EVERY *})
  done

ML_quiet {*
val f_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_1})],
KindingTacs [(RTac @{thm typing_helper_4})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_1})],
KindingTacs [(RTac @{thm typing_helper_2})],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_2})],
TypingTacs []
] *}

ML {*
fun get_typing_tree ctxt f proof =
  let val abbrev_defs = Proof_Context.get_thms ctxt "abbreviated_type_defs"
                        handle ERROR _ => []
      val defs = maps (Proof_Context.get_thms ctxt)
                   (map (prefix f) ["_def", "_type_def", "_typetree_def"] @ ["replicate_unfold", "One_nat_def"])
                 @ abbrev_defs
  in extract_subproofs
       (Syntax.read_term ctxt
         ("Trueprop (\<Xi>, fst " ^ f ^ "_type, (" ^ f ^ "_typetree, [Some (fst (snd " ^ f ^ "_type))])" ^
          "            T\<turnstile> " ^ f ^ " : snd (snd " ^ f ^ "_type))")
        |> cterm_of (Proof_Context.theory_of ctxt))
       (map (fn x => ((), x))
            (asm_full_simp_tac (ctxt addsimps defs) 1 ::
             map (fn t => t ctxt) proof))
       is_typing ctxt
     |> (fn r => case r of
            Right tr => tr | Left tr => (@{trace} tr; error ("get_typing_tree failed for function " ^ f)))
  end

fun get_all_typing_details k ctxt name script : details = let
    val simp_one = Simplifier.rewrite_rule ctxt @{thms One_nat_def[THEN eq_reflection]}
    val tacs = TTyping_Tactics.mk_ttsplit_tacs name k ctxt script
               |> map (fn t => case t of
                           RTac thm => RTac (simp_one thm)
                         | WeakeningTac thms => WeakeningTac (map simp_one thms)
                         | _ => t)
               |> map interpret_tac
    val tacs' = map (fn f => fn ctxt => f ctxt 1) tacs
    val orig_typing_tree = get_typing_tree ctxt name tacs'
    val typecorrect_thms = map (Goal.finish ctxt) (map tree_hd orig_typing_tree)
      |> map (simplify ctxt #> Thm.varifyT_global)
    val typing_tree = map (tree_map (cleanup_typing_tree_thm ctxt)) orig_typing_tree
    val bucket = typing_tree_to_bucket typing_tree
  in (typecorrect_thms, typing_tree, bucket) end

fun get_all_typing_details_future k ctxt name script
    = Future.fork (fn () => get_all_typing_details k ctxt name script)
*}



declare [[ML_print_depth=99]]
ML {*
TTyping_Tactics.mk_ttsplit_tacs "f" @{term "[{}, {}] :: kind list"} @{context} f_typecorrect_script
*}
declare [[ML_print_depth=10]]

ML {*
get_all_typing_details @{term "[{}, {}] :: kind list"} @{context} "f" f_typecorrect_script
*}



ML_quiet {*
val f_ttyping_details_future = get_all_typing_details_future @{term "[{}, {}] :: kind list"} @{context} "f"
   f_typecorrect_script*}

lemma f_typecorrect :
  "\<Xi>, fst f_type, (f_typetree, [Some (fst (snd f_type))]) T\<turnstile> f : snd (snd f_type)"
  apply (tactic {* resolve_future_typecorrect f_ttyping_details_future *})
  done

ML_quiet {*
val g_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_8})],
KindingTacs [(RTac @{thm typing_helper_9})],
KindingTacs [(RTac @{thm typing_helper_10})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_9})],
KindingTacs [(RTac @{thm typing_helper_7})],
KindingTacs [(RTac @{thm typing_helper_11})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_7})],
KindingTacs [(RTac @{thm typing_helper_8})],
TypingTacs [],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (6,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_8})])])),(RTac @{thm typing_fun'}),(RTac @{thm f_typecorrect[simplified f_type_def f_typetree_def abbreviated_type_defs, simplified]}),(RTac @{thm typing_helper_12}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{}"]}),(RTac @{thm typing_helper_3}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_8}]),(SimpTac ([],[]))]
] *}

lemma
  "\<Xi>, fst g_type, (g_typetree, [Some (fst (snd g_type))]) T\<turnstile> g : snd (snd g_type)"
  apply (simp add: g_def g_type_def g_typetree_def abbreviated_type_defs)
  apply (tactic {*
    EVERY (map (fn tac => tac @{context} 1)
            (TTyping_Tactics.mk_ttsplit_tacs "g" @{term "[{}] :: kind list"} @{context} g_typecorrect_script
             |> map (fn t => case t of RTac thm => RTac (Simplifier.rewrite_rule @{context} @{thms One_nat_def[THEN eq_reflection]} thm) | _ => t)
             |> map interpret_tac))
    *})
  done

ML {*
get_all_typing_details @{term "[{}] :: kind list"} @{context} "g"
   g_typecorrect_script
*}

ML_quiet {*
val g_ttyping_details_future = get_all_typing_details_future @{term "[{}] :: kind list"} @{context} "g"
   g_typecorrect_script*}


lemma g_typecorrect :
  "\<Xi>, fst g_type, (g_typetree, [Some (fst (snd g_type))]) T\<turnstile> g : snd (snd g_type)"
  apply (tactic {* resolve_future_typecorrect g_ttyping_details_future *})
  done

ML_quiet {*
val h_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_14})],
KindingTacs [(RTac @{thm typing_helper_13})],
KindingTacs [(RTac @{thm typing_helper_15})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_13})],
KindingTacs [(RTac @{thm typing_helper_13})],
KindingTacs [(RTac @{thm typing_helper_16})],
TypingTacs [],
KindingTacs [(RTac @{thm typing_helper_13})],
KindingTacs [(RTac @{thm typing_helper_14})],
TypingTacs [],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (6,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_14})])])),(RTac @{thm typing_fun'}),(RTac @{thm g_typecorrect[simplified g_type_def g_typetree_def abbreviated_type_defs, simplified]}),(RTac @{thm typing_helper_18}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{}"]}),(RTac @{thm typing_helper_8}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_14}]),(SimpTac ([],[]))]
] *}


ML_quiet {*
val h_ttyping_details_future = get_all_typing_details_future @{term "[] :: kind list"} @{context} "h"
   h_typecorrect_script*}


lemma h_typecorrect :
  "\<Xi>, fst h_type, (h_typetree, [Some (fst (snd h_type))]) T\<turnstile> h : snd (snd h_type)"
  apply (tactic {* resolve_future_typecorrect h_ttyping_details_future *})
  done

ML_quiet {*
val (_, f_typing_tree, f_typing_bucket)
= Future.join f_ttyping_details_future
*}


ML_quiet {*
val (_, g_typing_tree, g_typing_bucket)
= Future.join g_ttyping_details_future
*}


ML_quiet {*
val (_, h_typing_tree, h_typing_bucket)
= Future.join h_ttyping_details_future
*}

context value_sem begin
schematic_goal "monoexpr g = ?g"
  apply (clarsimp simp: g_def f_def)
  by (rule refl)

schematic_goal "monoexpr h = ?h"
  apply (clarsimp simp: h_def)
  by (rule refl)

schematic_goal "monoexpr h = ?h"
  apply (clarsimp simp: h_def g_def f_def)
  by (rule refl)

end


end

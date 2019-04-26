(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory TypeProofGen imports
  "../cogent/isa/CogentHelper"
  "../cogent/isa/ProofTrace"
begin

ML {*

fun debug_print_to_file pathstr s = File.write (Path.explode pathstr) s

val LOG_FILE = Path.basic "TypeProofTactic.log"
fun log_to_file strs = File.append LOG_FILE (strs ^"\n")
fun log_error str = log_to_file ("*** " ^ str)
fun log_info str  = log_to_file ("    " ^ str)
fun raise_error err =
  let
    val _   = log_error err
  in
     raise ERROR err
  end

*}


(* Convert ttyping subproofs to standard typing subproofs. *)
lemma ttsplit_imp_split':
  "ttsplit k \<Gamma> splits xs \<Gamma>1 ys \<Gamma>2 \<Longrightarrow>
    k \<turnstile> snd \<Gamma> \<leadsto> drop (length xs) (snd \<Gamma>1) | drop (length ys) (snd \<Gamma>2)"
  by (fastforce dest: ttsplit_imp_split)

(* TODO: This has to be double-checked. 
         The True in the assumption seems very suspicious.*)
lemma ttsplit_inner_imp_split:
  "ttsplit_inner k splits True \<Gamma>b \<Gamma>1 \<Gamma>2 \<Longrightarrow>
   k \<turnstile> snd (TyTrSplit splits xs T1 ys T2, \<Gamma>b) \<leadsto>
     drop (length xs) (snd (T1, xs @ \<Gamma>1)) | drop (length ys) (snd (T2, ys @ \<Gamma>2))"
  by (fast dest: ttsplitI[THEN ttsplit_imp_split'])

lemma ttsplit_bang_imp_split_bang':
  "ttsplit_bang is splits k \<Gamma> xs \<Gamma>1 ys \<Gamma>2 \<Longrightarrow>
    split_bang k is (snd \<Gamma>) (drop (length xs) (snd \<Gamma>1)) (drop (length ys) (snd \<Gamma>2))"
  by (fastforce dest: ttsplit_bang_imp_split_bang)


lemma drop_appended_list: "drop (length xs) (xs @ ys) = ys"
  by simp

lemma drop_eval_simps:
  "drop 0 xs = xs"
  "drop (Suc n) (x # xs) = drop n xs"
  by simp+

lemma length_eval_simps:
  "length [] = 0"
  "length (x # xs) = Suc (length xs)"
  by simp+

(* Generate type system lemma buckets *)
ML {*
fun is_typing t = head_of t |>
  (fn h => is_const "TypeTrackingTyping.ttyping" h orelse
           is_const "TypeTrackingTyping.ttsplit" h orelse
           is_const "TypeTrackingTyping.ttsplit_bang" h orelse
           is_const "TypeTrackingTyping.ttsplit_inner" h orelse
           is_const "Cogent.typing" h orelse
           is_const "Cogent.split" h orelse
           is_const "Cogent.kinding" h);
(* NB: flattening the proof tree is unsafe in general, but this program is a small example *)
fun flatten_Tree (Tree (x, ts)) = x :: List.concat (map flatten_Tree ts);
fun uniq cmp (x::y::xs) = (case cmp (x,y) of EQUAL => uniq cmp (x::xs)
                                           | _ => x::uniq cmp (y::xs))
  | uniq _ xs = xs

fun get_typing_tree ctxt f proof =
  let val abbrev_defs = Proof_Context.get_thms ctxt "abbreviated_type_defs"
                        handle ERROR _ => []
      val defs = maps (Proof_Context.get_thms ctxt)
                   (map (prefix f) ["_def", "_type_def", "_typetree_def"] @ ["replicate_unfold"])
                 @ abbrev_defs
  in extract_subproofs
       (Syntax.read_term ctxt
         ("Trueprop (\<Xi>, fst " ^ f ^ "_type, (" ^ f ^ "_typetree, [Some (fst (snd " ^ f ^ "_type))])" ^
          "            T\<turnstile> " ^ f ^ " : snd (snd " ^ f ^ "_type))")
        |> Thm.cterm_of ctxt)
       (map (fn x => ((), x))
            (asm_full_simp_tac (ctxt addsimps defs) 1 ::
             map (fn t => t ctxt) proof))
       is_typing ctxt
     |> (fn r => case r of
            Right tr => tr | _ => error ("get_typing_tree failed for function " ^ f))
  end

fun simplify_thm ctxt thm =
  Conv.fconv_rule (Simplifier.rewrite ctxt) thm

val cleanup_ss : simpset =
  put_simpset HOL_basic_ss @{context}
    addsimps @{thms
      Product_Type.fst_conv
      Product_Type.snd_conv
      drop_appended_list
      drop_eval_simps
      length_eval_simps
    }
  |> simpset_of

fun cleanup_typing_tree_thm ctxt thm =
  Goal.finish ctxt thm
    |> (fn t =>
       (
        (t RS @{thm ttsplit_imp_split'}) handle THM _ =>
        (t RS @{thm ttsplit_inner_imp_split}) handle THM _ =>
        (t RS @{thm ttsplit_bang_imp_split_bang'}) handle THM _ =>
        (t RS @{thm ttyping_imp_typing}) handle THM _ =>
        t
       )
    |> Simplifier.simplify (put_simpset cleanup_ss ctxt)
    |> (fn t => let
        val t' = Simplifier.simplify ctxt t
        val _ = if (Thm.prop_of t = Thm.prop_of t')
          then ()
          else (log_info (@{make_string} t); log_info (@{make_string} t'); ())
      in t' end))
  |> Thm.varifyT_global

fun get_final_typing_tree ctxt f proof =
  get_typing_tree ctxt f proof
  |> map (tree_map (cleanup_typing_tree_thm ctxt))

val typing_tree_to_bucket =
  map flatten_Tree #> List.concat
  #> sort_distinct Thm.thm_ord

fun get_typing_bucket ctxt f proof =
  get_typing_tree ctxt f proof
  |> map flatten_Tree |> List.concat
  |> map (cleanup_typing_tree_thm ctxt)
  |> sort Thm.thm_ord |> uniq Thm.thm_ord

type details = (thm list * thm Tree list * thm list)

fun get_all_typing_details ctxt name script : details = let
    val _ = (log_info ("solving " ^ name))
    val timer_total = Timing.start ()
    val timer = Timing.start ()
    val tacs = TTyping_Tactics.mk_ttsplit_tacs_final name
        @{term "[] :: kind env"} ctxt script
    val tacs' = map (fn f => fn ctxt => f ctxt 1) tacs
    val res = Timing.result timer
    val _ = (@{print} "phase: make tacs"; @{print} res)
    val _ = (log_info (name ^ "|phase: make tacs"); log_info (@{make_string} res))
    val timer = Timing.start ()
    val orig_typing_tree = get_typing_tree ctxt name tacs'
    val res = Timing.result timer
    val _ = (@{print} "phase: solve typing tree"; @{print} res)
    val _ = (log_info (name ^ "|phase: solve typing tree"); log_info (@{make_string} res))
    val timer = Timing.start ()
    val typecorrect_thms = map (Goal.finish ctxt) (map tree_hd orig_typing_tree)
      |> map (simplify ctxt #> Thm.varifyT_global)
    val res = Timing.result timer
    val _ = (@{print} "phase: simplify tree"; @{print} res)
    val _ = (log_info (name ^ "|phase: simplify tree"); log_info (@{make_string} res))
    val timer = Timing.start ()
    val typing_tree = map (tree_map (cleanup_typing_tree_thm ctxt)) orig_typing_tree
    val res = Timing.result timer
    val _ = (@{print} "phase: clean tree"; @{print} res)
    val _ = (log_info (name ^ "|phase: clean tree"); log_info (@{make_string} res))
    val timer = Timing.start ()
    val bucket = typing_tree_to_bucket typing_tree
    val res = Timing.result timer
    val _ = (@{print} "phase: make bucket"; @{print} res)
    val _ = (log_info (name ^ "|phase: make bucket"); log_info (@{make_string} res))
    val res = Timing.result timer_total
    val _ = (@{print} "solve time total"; @{print} res)
    val _ = (log_info (name ^ "|solve time total"); log_info (@{make_string} res))
  in (typecorrect_thms, typing_tree, bucket) end

fun get_all_typing_details_future ctxt name script
    = Future.fork (fn () => get_all_typing_details ctxt name script)

fun resolve_future_typecorrect ctxt details
    = resolve_tac ctxt (#1 (Future.join details : details)) 1
*}

end

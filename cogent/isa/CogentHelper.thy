(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory CogentHelper
imports "TypeTrackingSemantics" "ML_Old" Data
keywords "ML_quiet" :: thy_decl % "ML"
begin

(* Rewrite rules to get expressions in the assumptions *)

lemma typing_lit': "\<lbrakk> K \<turnstile> \<Gamma> consumed; t = lit_type l \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Lit l : TPrim t"
  by (simp only: typing_lit)

lemma typing_put':  "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                     ; \<Xi>, K, \<Gamma>1 \<turnstile> e : TRecord ts s
                     ; sigil_perm s \<noteq> Some ReadOnly
                     ; f < length ts
                     ; ts ! f = (n,t, taken)
                     ; K \<turnstile> t :\<kappa> k
                     ; D \<in> k \<or> taken
                     ; \<Xi>, K, \<Gamma>2 \<turnstile> e' : t
                     ; ts' = (ts [f := (n,t,False)])
                     \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Put e f e' : TRecord ts' s"
  by (simp add: typing_put)

lemma typing_prim' : "\<lbrakk> prim_op_type oper = (ts,t)
                      ; ts' = map TPrim ts
                      ; \<Xi>, K, \<Gamma> \<turnstile>* args : ts'
                      \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Prim oper args : TPrim t"
  by (simp only: typing_prim)


lemma typing_con' : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile> x : t
                     ; (tag, t, False) \<in> set ts
                     ; K \<turnstile>* (map (fst \<circ> snd) ts) wellformed
                     ; distinct (map fst ts)
                     ; map fst ts = map fst ts'
                     ; map (fst \<circ> snd) ts = map (fst \<circ> snd) ts'
                     ; list_all2 (\<lambda>x y. snd (snd y) \<longrightarrow> snd (snd x)) ts ts'
                     \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Con ts tag x : TSum ts'"
  by (simp add: typing_con)

lemma typing_struct': "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile>* es : ts
                       ; length ns = length ts
                       ; distinct ns
                       ; ts' = (zip ns (zip ts (replicate (length ts) False)))
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Struct ts es : TRecord ts' Unboxed"
  by (simp only: typing_struct)

lemma typing_afun': "\<lbrakk> \<Xi> f = (ks, t, u)
                     ; list_all2 (kinding K) ts ks
                     ; t' = instantiate ts (TFun t u)
                     ; ks \<turnstile> TFun t u wellformed
                     ; K \<turnstile> \<Gamma> consumed
                     \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> AFun f ts : t'"
  by (simp only: typing_afun)

lemma typing_fun': "\<lbrakk> \<Xi>, ks, (typtree, [Some t]) T\<turnstile> f : u
                    ; list_all2 (kinding K) ts ks
                    ; t' = instantiate ts (TFun t u)
                    ; ks \<turnstile> t wellformed
                    ; K \<turnstile> \<Gamma> consumed
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Fun f ts : t'"
  by (auto simp only: typing_fun snd_conv dest: ttyping_imp_typing)

lemma typing_var_weak: "\<lbrakk> K \<turnstile> t :\<kappa> k
                   ; K \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i t
                   ; i < length \<Gamma>
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Var i : t"
  (* weaker than typing_var - the kinding assumption lets
     us easily instantiate t *)
  by (simp only: typing_var)

lemma typing_all_empty': "\<Gamma> = empty n \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>* [] : []"
  by (simp only: typing_all_empty)

lemma typing_all_empty'':
  "set \<Gamma> \<subseteq> {None}
    \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>* [] : []"
  apply (rule typing_all_empty'[where n="length \<Gamma>"])
  apply (clarsimp simp: Cogent.empty_def list_eq_iff_nth_eq)
  apply (frule subsetD, erule nth_mem)
  apply simp
  done

lemma split_bang_bang' :"\<lbrakk> 0 \<in> is
                      ; x' = bang x
                      ; is' = pred ` (Set.remove 0 is)
                      ; split_bang K is' xs as bs
                      \<rbrakk>  \<Longrightarrow> split_bang K is (Some x # xs) (Some x' # as) (Some x # bs)"
                      by (simp only: split_bang_bang)

definition
  type_ctx_wellformed :: "kind env \<Rightarrow> ctx \<Rightarrow> bool"
where
  "type_ctx_wellformed K \<Gamma> = (\<forall>t. Some t \<in> set \<Gamma> \<longrightarrow> K \<turnstile> t wellformed)"

definition ttsplit_weak :: "kind env \<Rightarrow> tree_ctx \<Rightarrow> type_split_kind option list
        \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> bool"
where
  "ttsplit_weak K \<Gamma> sps xs \<Gamma>1 ys \<Gamma>2 =
    (\<exists>\<Gamma>b \<Gamma>1a \<Gamma>2a T1 T2. \<Gamma> = (TyTrSplit sps xs T1 ys T2, \<Gamma>b)
        \<and> \<Gamma>1 = (T1, xs @ \<Gamma>1a)
        \<and> \<Gamma>2 = (T2, ys @ \<Gamma>2a)
        \<and> ttsplit_inner K sps False \<Gamma>b \<Gamma>1a \<Gamma>2a)"

lemma ttsplit_weak_lemma:
  "ttsplit_weak K \<Gamma> sps xs \<Gamma>1 ys \<Gamma>2
    \<Longrightarrow> type_ctx_wellformed K (snd \<Gamma>1)
    \<Longrightarrow> type_ctx_wellformed K (snd \<Gamma>2)
    \<Longrightarrow> ttsplit K \<Gamma> sps xs \<Gamma>1 ys \<Gamma>2"
  apply (clarsimp simp: ttsplit_def ttsplit_weak_def type_ctx_wellformed_def)
  apply (subst ttsplit_inner_def, clarsimp)
  apply (clarsimp simp: ttsplit_inner_def in_set_conv_nth all_conj_distrib)
  apply (clarsimp simp: image_def Product_Type.split_def set_zip)
  apply (drule_tac x=y in spec)+
  apply clarsimp
  apply (drule_tac x=i in spec)+
  apply (clarsimp split: if_splits)
  done

lemma ttsplit_weakI:
  "ttsplit_inner K sps False \<Gamma>b \<Gamma>1 \<Gamma>2 \<Longrightarrow> xs' = xs @ \<Gamma>1 \<Longrightarrow> ys' = ys @ \<Gamma>2
    \<Longrightarrow> ttsplit_weak K (TyTrSplit sps xs T1 ys T2, \<Gamma>b) sps xs (T1, xs') ys (T2, ys')"
  by (simp add: ttsplit_weak_def)

lemmas ttyping_type_ctx_wellformed = ttyping_type_wellformed[folded type_ctx_wellformed_def]

lemma ttsplit_triv_type_ctxt_wellformed:
  "ttsplit_triv \<Gamma> x \<Gamma>1 y \<Gamma>2
    \<Longrightarrow> type_ctx_wellformed K (snd \<Gamma>1) \<or> type_ctx_wellformed K (snd \<Gamma>2)
    \<Longrightarrow> type_ctx_wellformed K (snd \<Gamma>)"
  by (auto simp: ttsplit_triv_def type_ctx_wellformed_def)

lemma ttyping_case':  "\<lbrakk> ttsplit K \<Gamma> ijs [] \<Gamma>1 [] \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 T\<turnstile> x : TSum ts
                   ; (tag, t, False) \<in> set ts
                   ; ttsplit_triv \<Gamma>2 [Some t] \<Gamma>3 [Some (TSum (tagged_list_update tag (t, True) ts))] \<Gamma>4
                   ; \<Xi>, K, \<Gamma>3 T\<turnstile> a : u
                   ; \<Xi>, K, \<Gamma>4 T\<turnstile> b : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Case x tag a b : u"
  by (simp only: ttyping_case[rotated])

lemma ttyping_take': "\<lbrakk> ttsplit K \<Gamma> ijs [] \<Gamma>1 [Some t, Some (TRecord ts' s)] \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 T\<turnstile> e : TRecord ts s
                   ; sigil_perm s \<noteq> Some ReadOnly
                   ; f < length ts
                   ; ts ! f = (n, t, False)
                   ; K \<turnstile> t :\<kappa> k
                   ; ts = ts'[f := (n, t, False)] \<and> fst (ts' ! f) = n \<and> fst (snd (ts' ! f)) = t \<and> (S \<in> k \<or> snd (snd (ts' ! f)))
                   ; \<Xi>, K, \<Gamma>2 T\<turnstile> e' : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Take e f e' : u"
  apply clarify
  apply (rule ttyping_take[rotated], assumption+)
  apply simp
  done

definition
  "duplicate_list xs = xs @ xs"

lemma replicate_numeral:
  "replicate (numeral (num.Bit0 n)) x = duplicate_list (replicate (numeral n) x)"
  "replicate (numeral (num.Bit1 n)) x = x # duplicate_list (replicate (numeral n) x)"
  "replicate (numeral num.One) x = [x]"
    apply (simp only: numeral_Bit0 replicate_add duplicate_list_def)
   apply (simp only: eval_nat_numeral(3) numeral_Bit0 replicate_Suc replicate_add duplicate_list_def)
  apply simp
  done

lemmas replicate_unfold = replicate_numeral replicate_Suc replicate_0 duplicate_list_def append.simps

abbreviation(input)
  "NoneT == (None :: Cogent.type option)"
abbreviation(input)
  "SomeT == (Some :: Cogent.type \<Rightarrow> _)"

lemma list_update_eq_id:
  "length xs = n \<Longrightarrow> (i < n \<Longrightarrow> xs ! i = x) \<Longrightarrow> xs [i := x] = xs"
  by (induct xs arbitrary: i n, auto split: nat.split)

lemmas ttsplit_innerI_True = ttsplit_innerI[where kndng=True, simplified]

ML {*

structure TTyping_Tactics = struct

fun REPEAT_SUBGOAL tac s0 =
  let fun repeat tac s = if Thm.nprems_of s < Thm.nprems_of s0 then Seq.succeed s else
                           case Seq.pull (tac s) of
                               NONE => Seq.succeed s
                             | SOME (s', ss) => Seq.maps (repeat tac) (Seq.cons s' ss)
  in repeat tac s0 end

fun weakening_tac ctxt kinding_thms =
  let val kinding_tac = FIRST (map (fn t => rtac t 1) kinding_thms)
      val weakening_comp_tac =
        DETERM (rtac @{thm none} 1 ORELSE
                (rtac @{thm drop} 1 THEN kinding_tac THEN asm_full_simp_tac ctxt 1) ORELSE
                (rtac @{thm keep} 1 THEN kinding_tac))
  in
    asm_full_simp_tac (ctxt addsimps @{thms weakening_def}
                            delsimps @{thms HOL.simp_thms(25) HOL.simp_thms(26)}) 1
    THEN REPEAT_SUBGOAL (CHANGED (rtac @{thm conjI} 1 ORELSE weakening_comp_tac))
  end

fun cogent_splits_tac ctxt kinding_thms =
  let val kinding_tac = FIRST (map (fn t => rtac t 1) kinding_thms)
      val split_tac =
        DETERM (rtac @{thm split_comp.none} 1 ORELSE
                (rtac @{thm split_comp.share} 1 THEN kinding_tac THEN asm_full_simp_tac ctxt 1) ORELSE
                (rtac @{thm split_comp.left} 1 THEN kinding_tac) ORELSE
                (rtac @{thm split_comp.right} 1 THEN kinding_tac))
  in
    REPEAT_SUBGOAL (CHANGED (rtac @{thm split_cons} 1 ORELSE rtac @{thm split_empty} 1 ORELSE split_tac))
  end

fun cogent_guided_ttsplits_tac ctxt sz script =
  let fun mktac i [] =
            if i = sz then rtac @{thm ttsplit_innerI(5)} 1 else
            rtac @{thm ttsplit_innerI(1)} 1 THEN mktac (i+1) []
        | mktac i ((n, tacs)::script') =
            if i = n
            then EVERY (map (fn t => DETERM (t ctxt)) tacs) THEN
                 mktac (i+1) script'
            else rtac @{thm ttsplit_innerI(1)} 1 THEN
                 mktac (i+1) ((n, tacs)::script')
  in rtac @{thm ttsplitI} 1 THEN
       mktac 0 script THEN
       asm_full_simp_tac ctxt 1 THEN
       asm_full_simp_tac ctxt 1
  end


datatype tac = RTac of thm
             | SimpTac of thm list * thm list
             | ForceTac of thm list
             | WeakeningTac of thm list
             | SplitsTac of int * (int * tac list) list

val simp = SimpTac ([], [])

datatype hints = KindingTacs of tac list
  | TTSplitBangTacs of tac list
  | TypingTacs of tac list

exception HINTS of string * hints leaftree

fun kinding (Leaf (KindingTacs tac)) = tac
  | kinding hint_tree_bad = raise HINTS ("kinding", hint_tree_bad)

fun typing_hint (Leaf (TypingTacs tacs)) = tacs
  | typing_hint hint_tree_bad = raise HINTS ("typing", hint_tree_bad)

fun apply_split @{term "Some TSK_L"} hints t = ((t, NONE), hints)
  | apply_split @{term "Some TSK_S"} hints t = ((t, t), hints)
  | apply_split @{term "Some TSK_NS"} hints t = let
    val (kindhint, hints) = (case hints of
                      kindhint :: hints => (kindhint, hints)
                    | _ => raise HINTS ("apply_split: no kind hint found", Branch hints))
    val tacs = kinding kindhint
    val thm = case tacs of [RTac thm] => thm
      | _ => raise HINTS ("apply_split: kindhint failed to create an RTac", kindhint)
  in ((SOME thm, t), hints) end
  | apply_split @{term "None :: type_split_kind option"} hints t = ((NONE, t), hints)
  | apply_split t _ _ = raise TERM ("apply_split", [t])

fun apply_splits ((sp, t) :: sp_ts) hints = let
    val ((x, y), hints) = apply_split sp hints t
    val ((xs, ys), hints) = apply_splits sp_ts hints
  in (((x :: xs), (y :: ys)), hints) end
  | apply_splits [] hints = (([], []), hints)

fun interpret_tac (RTac r) _ = rtac r
  | interpret_tac (SimpTac (a, d)) ctxt = asm_full_simp_tac (ctxt addsimps a delsimps d)
  | interpret_tac (ForceTac a) ctxt = force_tac (ctxt addsimps a)
  | interpret_tac (WeakeningTac thms) ctxt = K (weakening_tac ctxt thms)
  | interpret_tac (SplitsTac (n, tacs)) ctxt = K (cogent_guided_splits_tac ctxt n tacs)
and cogent_guided_splits_tac ctxt sz script =
  let fun mktac i [] =
            if i = sz then rtac @{thm split_empty} 1 else
            rtac @{thm split_cons} 1 THEN rtac @{thm split_comp.none} 1 THEN mktac (i+1) []
        | mktac i ((n, tacs)::script') =
            if i = n
            then rtac @{thm split_cons} 1 THEN EVERY (map (fn t => interpret_tac t ctxt 1) tacs) THEN
                 mktac (i+1) script'
            else rtac @{thm split_cons} 1 THEN rtac @{thm split_comp.none} 1 THEN
                 mktac (i+1) ((n, tacs)::script')
  in mktac 0 script end

fun kind_proof_single (@{term SomeT} $ t) k ctxt hint = let
    val tac = (case hint of
            (KindingTacs tac) => tac
            | _ => raise ERROR ("kind_proof_single: not a kinding tac")) (* TODO should work out a more principled way of error detection with state here *)
    val t = betapplys (@{term "kinding"}, [k, t, (@{schematic_term "?k :: kind"})])
    val ct = Thm.cterm_of ctxt (@{term Trueprop} $ t)
    val rs = EVERY (map (fn t => interpret_tac t ctxt 1) tac) (Thm.trivial ct)
    val t = (case Seq.pull rs of
          NONE => raise TERM ("kind_proof_single: failed", [k, t])
        | SOME (t, _) => t)
    in SOME t end
  | kind_proof_single @{term NoneT} k ctxt hints = NONE
  | kind_proof_single _ _ _ _ = raise ERROR ("kind_proof_single: thm not a Some or a None")

fun kind_proofs ((@{term SomeT} $ t) :: ts) k ctxt hints = let
    val (hintshd, hints) = (case hints of
                        (hintshd :: hints) => (hintshd, hints)
                      | _ => raise HINTS  ("kind_proofs: not enough hints", Branch hints))
    val tacs = kinding hintshd
(*
    val _ = case tacs of
        [RTac thm] => Display.pretty_thm ctxt thm |> Pretty.writeln
      | _ => warning "unexpected kinding tacs"
*)
    val t = betapplys (@{term "kinding"}, [k, t, (@{schematic_term "?k :: kind"})])
    val ct = Thm.cterm_of ctxt (@{term Trueprop} $ t)
    val rs = EVERY (map (fn t => interpret_tac t ctxt 1) tacs) (Thm.trivial ct)
    val t = (case Seq.pull rs of
          NONE => raise TERM ("kind_proofs: failed", [k, t])
        | SOME (t, _) => t)
    val (ts, hints) = kind_proofs ts k ctxt hints
  in (SOME t :: ts, hints) end
  | kind_proofs (@{term NoneT} :: ts) k ctxt hints = let
    val (ts, hints) = kind_proofs ts k ctxt hints
  in (NONE :: ts, hints) end
  | kind_proofs [] _ _ hints = ([], hints)
  | kind_proofs ts _ _ _ = raise TERM ("kind_proofs", ts)

fun follow_tt (Const (@{const_name TyTrSplit}, _) $ sps $ x $ T1 $ y $ T2, ts) k ctxt hints = let
    val ((ts1, ts2), hints) = apply_splits (HOLogic.dest_list sps ~~ ts) hints
    val (x_proofs, hints) = kind_proofs (HOLogic.dest_list x) k ctxt hints
    val (y_proofs, hints) = kind_proofs (HOLogic.dest_list y) k ctxt hints
  in (((T1, x_proofs @ ts1), (T2, y_proofs @ ts2)), hints) end
  | follow_tt (tt, _) _ _ _ = raise TERM ("follow_tt", [tt])

fun ttsplit_inner (@{term "Some TSK_S"} :: tsks) (SOME p :: Gamma) = let
    val rest = ttsplit_inner tsks Gamma
  in [RTac @{thm ttsplit_innerI_True(4)}, RTac p] @ [simp] @ rest end
  | ttsplit_inner (@{term "Some TSK_L"} :: tsks) (SOME p :: Gamma) = let
    val rest = ttsplit_inner tsks Gamma
  in [RTac @{thm ttsplit_innerI_True(3)}, RTac p] @ rest end
  | ttsplit_inner (@{term "None :: type_split_kind option"} :: tsks) (SOME p :: Gamma) = let
    val rest = ttsplit_inner tsks Gamma
  in [RTac @{thm ttsplit_innerI_True(2)}, RTac p] @ rest end
  | ttsplit_inner (@{term "None :: type_split_kind option"} :: tsks) (NONE :: Gamma) = let
    val rest = ttsplit_inner tsks Gamma
  in [RTac @{thm ttsplit_innerI_True(1)}] @ rest end
  | ttsplit_inner [] [] = [RTac @{thm ttsplit_innerI(5)}]
  | ttsplit_inner tsks _ = raise TERM ("ttsplit_inner", tsks)

fun ttsplit (Const (@{const_name TyTrSplit}, _) $ sps $ _ $ _ $ _ $ _, Gamma) = let
    val inner = ttsplit_inner (HOLogic.dest_list sps) Gamma
  in [RTac @{thm ttsplitI}] @ inner @ [simp, simp] end
  | ttsplit (t, _) = raise TERM ("ttsplit", [t])

fun ttsplit_bang_inner (@{term "Some TSK_S"} :: tsks) (SOME p :: Gamma) = let
    val rest = ttsplit_bang_inner tsks Gamma
  in [RTac @{thm ttsplit_bang_innerI(4)}, RTac p, simp] @ rest end
  | ttsplit_bang_inner (@{term "Some TSK_L"} :: tsks) (SOME p :: Gamma) = let
    val rest = ttsplit_bang_inner tsks Gamma
  in [RTac @{thm ttsplit_bang_innerI(3)}, RTac p] @ rest end
  | ttsplit_bang_inner (@{term "None :: type_split_kind option"} :: tsks) (SOME p :: Gamma) = let
    val rest = ttsplit_bang_inner tsks Gamma
  in [RTac @{thm ttsplit_bang_innerI(2)}, RTac p] @ rest end
  | ttsplit_bang_inner (@{term "None :: type_split_kind option"} :: tsks) (NONE :: Gamma) = let
    val rest = ttsplit_bang_inner tsks Gamma
  in [RTac @{thm ttsplit_bang_innerI(1)}] @ rest end
  | ttsplit_bang_inner (@{term "Some TSK_NS"} :: tsks) (SOME p :: Gamma) = let
    val rest = ttsplit_bang_inner tsks Gamma
  in [RTac @{thm ttsplit_bang_innerI(5)}, RTac p, simp] @ rest end
  | ttsplit_bang_inner [] [] = [RTac @{thm ttsplit_bang_innerI(6)}]
  | ttsplit_bang_inner tsks _ = raise TERM ("ttsplit_bang_inner", tsks)

fun ttsplit_bang (Const (@{const_name TyTrSplit}, _) $ sps $ _ $ _ $ _ $ _, Gamma) = let
    val inner = ttsplit_bang_inner (HOLogic.dest_list sps) Gamma
  in [RTac @{thm ttsplit_bangI}, simp, simp, SimpTac (@{thms set_eq_subset}, [])] @ inner end
  | ttsplit_bang (t, _) = raise TERM ("ttsplit", [t])

fun dest_nat (@{term Suc} $ n) = dest_nat n + 1
  | dest_nat (@{term "0 :: nat"}) = 0
  | dest_nat n = HOLogic.dest_number n |> snd

fun dest_all_vars' (Const (@{const_name Var}, _) $ i :: vs)
    = (dest_nat i :: dest_all_vars' vs)
  | dest_all_vars' [] = []
  | dest_all_vars' ts = raise TERM ("dest_all_vars", ts)

val dest_all_vars = try (dest_all_vars' o HOLogic.dest_list)

fun the_G _ (SOME p) = p
  | the_G G NONE = raise THM ("the_G", 1, (map (fn NONE => @{thm TrueI} | SOME t => t) G))

fun typing_all_vars _ _ [] = let
  in [RTac @{thm typing_all_empty''}, simp] end
  | typing_all_vars ctxt G (ix :: ixs) = let
    fun null (NONE : thm option) = true
      | null _ = false
    fun step (i, p) = RTac @{thm split_cons} :: (if member (op =) ixs i
      then (if i = ix then [RTac @{thm split_comp.share}, RTac (the_G G p), simp]
          else [RTac @{thm split_comp.right}, RTac (the_G G p)])
      else (if null p then [RTac @{thm split_comp.none}]
          else [RTac @{thm split_comp.left}, RTac (the_G G p)]))
    val steps = maps step (0 upto (length G - 1) ~~ G)
    val thms = map_filter I G
    fun thm_r (i, p) = (if member (op =) ixs i then p else NONE)
    val G' = map thm_r (0 upto (length G - 1) ~~ G)
    val rest = typing_all_vars ctxt G' ixs
  in [RTac @{thm typing_all_cons}] @ steps @ [RTac @{thm split_empty},
    RTac @{thm typing_var_weak[unfolded singleton_def Cogent.empty_def]},
      RTac (the_G G (nth G ix)), simp, WeakeningTac thms, simp] @ rest end

fun typing (Const (@{const_name Var}, _) $ i) G _ hints = let
    val i = dest_nat i
    val thm = the_G G (nth G i)
    val thms = map_filter I G
    val _ = (case typing_hint hints of
               [] => ()
             | _ => raise HINTS ("too many tacs", hints))
  in ([RTac @{thm typing_var_weak[unfolded singleton_def Cogent.empty_def]},
                RTac thm, simp, WeakeningTac thms, simp]) end
  | typing (Const (@{const_name Struct}, _) $ _ $ xs) G ctxt hints
  = (case dest_all_vars xs of SOME ixs => let
      val _ = (case typing_hint hints of
                 [] => ()
               | _ => raise HINTS ("too many tacs", hints))
  in ([RTac @{thm typing_struct'}] @ typing_all_vars ctxt G ixs @ [simp]) end
    | NONE => typing_hint hints)
  | typing (Const (@{const_name Prim}, _) $ _ $ xs) G ctxt hints
  = (case dest_all_vars xs of SOME ixs => let
    val _ = (case typing_hint hints of
               [] => ()
             | _ => raise HINTS ("too many tacs", hints))
  in ([RTac @{thm typing_prim'}, simp, simp] @ typing_all_vars ctxt G ixs) end
    | NONE => typing_hint hints)
  | typing _ _ _ hints = let
    in typing_hint hints end

fun ttyping (Const (@{const_name Split}, _) $ x $ y) tt k ctxt hint_tree = let
    val (splithints, typxhint, typyhint) = (case hint_tree of
        Branch [Branch splithints, typxhint, typyhint] => (splithints, typxhint, typyhint)
      | Leaf (TypingTacs _) => raise HINTS ("ttyping(Const): expected ttyping rule, got typing rule", hint_tree)
      | _ => raise HINTS ("ttyping(Const): hints in incorrect form", hint_tree))
    val ((ltt, rtt), splithints) = follow_tt tt k ctxt splithints
    val _ = (case splithints of [] => () | _ => raise HINTS ("ttyping(Const): hints not exhausted", hint_tree))
    val split_tac = ttsplit tt
    val l_tac = ttyping x ltt k ctxt typxhint
    val r_tac = ttyping y rtt k ctxt typyhint
  in ([RTac @{thm ttyping_split}] @ split_tac @ l_tac @ r_tac) end
  | ttyping (Const (@{const_name Let}, _) $ x $ y) tt k ctxt hint_tree = let
    val (splithints, typxhint, typyhint) = (case hint_tree of
        Branch [Branch splithints, typxhint, typyhint] => (splithints, typxhint, typyhint)
      | Leaf (TypingTacs _) => raise HINTS ("ttyping(Let): expected ttyping rule, got typing rule", hint_tree)
      | _ => raise HINTS  ("ttyping(Let): hints in incorrect form", hint_tree))
    val ((ltt, rtt), splithints) = follow_tt tt k ctxt splithints
    val _ = (case splithints of [] => () | _ => raise HINTS ("ttyping(Let): hints not exhausted", hint_tree))
    val split_tac = ttsplit tt
    val (l_tac) = ttyping x ltt k ctxt typxhint
    val (r_tac) = ttyping y rtt k ctxt typyhint
  in ([RTac @{thm ttyping_let}] @ split_tac @ l_tac @ r_tac) end
  | ttyping (Const (@{const_name LetBang}, _) $ _ $ x $ y) tt k ctxt hint_tree = let
    val (splitbanghints, splithints, typxhint, typyhint, kindhint) = (case hint_tree of
        Branch [Branch splitbanghints, Branch splithints, typxhint, typyhint, kindhint] =>
               (splitbanghints, splithints, typxhint, typyhint, kindhint)
      | Leaf (TypingTacs _) => raise HINTS ("ttyping(LetBang): expected ttyping rule, got typing rule", hint_tree)
      | _ => raise HINTS  ("ttyping(LetBang): hints in incorrect form", hint_tree))
    val ((ltt, rtt), splithints) = follow_tt tt k ctxt (append splitbanghints splithints)
    val _ = (case splithints of [] => () | _ => raise HINTS ("ttyping(LetBang): hints not exhausted", hint_tree))
    val tsb_tac = ttsplit_bang tt
    val x_tac = ttyping x ltt k ctxt typxhint
    val y_tac = ttyping y rtt k ctxt typyhint
    val k_tac = kinding kindhint
  in ([RTac @{thm ttyping_letb}] @ tsb_tac @ x_tac @ y_tac @ k_tac @ [simp]) end
  | ttyping (Const (@{const_name Cogent.If}, _) $ c $ x $ y) tt k ctxt hint_tree = let
    val (typxhint, splithints, typahint, typbhint) = (case hint_tree of
        Branch [typxhint, Branch splithints, typahint, typbhint] =>
               (typxhint, splithints, typahint, typbhint)
      | Leaf (TypingTacs _) => raise HINTS ("ttyping(If): expected ttyping rule, got typing rule", hint_tree)
      | _ => raise HINTS  ("ttyping(If): hints in incorrect form", hint_tree))
    val ((condtt, casestt), splithints) = follow_tt tt k ctxt splithints
    (* The tt tree is generated with an additional split here.
       Technically it should be unnecessary, but would require changing how things work ~ v.jackson / 2018.09.19 *)
    val ((x_tt, y_tt), splithints) = follow_tt casestt k ctxt splithints
    val _ = (case splithints of [] => () | _ => raise HINTS ("ttyping(If): hints not exhausted", hint_tree))
    val split_tac = ttsplit tt
    val c_tac = ttyping c condtt k ctxt typxhint
    val x_tac = ttyping x x_tt k ctxt typahint
    val y_tac = ttyping y y_tt k ctxt typbhint
  in ([RTac @{thm ttyping_if}] @ split_tac
    @ [simp, RTac @{thm ttsplit_trivI}, simp, simp] @ c_tac @ x_tac @ y_tac) end
  | ttyping (Const (@{const_name Case}, _) $ x $ _ $ m $ nm) tt k ctxt hint_tree = let
    val (typxhint, splithints, typahint, typbhint) = (case hint_tree of
        Branch [typxhint, Branch splithints, typahint, typbhint] =>
               (typxhint, splithints, typahint, typbhint)
      | Leaf (TypingTacs _) => raise HINTS ("ttyping(Case): expected ttyping rule, got typing rule", hint_tree)
      | _ => raise HINTS  ("ttyping(Case): hints in incorrect form", hint_tree))
    val ((ltt, rtt), splithints) = follow_tt tt k ctxt splithints
    val x_tac = ttyping x ltt k ctxt typxhint
    val ((m_tt, nm_tt), splithints) = follow_tt rtt k ctxt splithints
    val _ = (case splithints of [] => () | _ => raise HINTS ("ttyping(Case): hints not exhausted", hint_tree))
    val split_tac = ttsplit tt
    val m_tac = ttyping m m_tt k ctxt typahint
    val nm_tac = ttyping nm nm_tt k ctxt typbhint
  in ([RTac @{thm ttyping_case'}] @ split_tac @ x_tac @ [simp]
    @ [simp, RTac @{thm ttsplit_trivI}, simp, simp] @ m_tac @ nm_tac) end
  | ttyping (Const (@{const_name Take}, _) $ x $ _ $ y) tt k ctxt hint_tree = let
    val (splithints, typehint, kindhint, type'hint) = (case hint_tree of
        Branch [Branch splithints, typehint, kindhint, type'hint] =>
               (splithints, typehint, kindhint, type'hint)
      | Leaf (TypingTacs _) => raise HINTS ("ttyping(Take): expected ttyping rule, got typing rule", hint_tree)
      | _ => raise HINTS  ("ttyping(Take): hints in incorrect form", hint_tree))
    val ((ltt, rtt), splithints) = follow_tt tt k ctxt splithints
    val _ = (case splithints of [] => () | _ => raise HINTS ("ttyping(Take): hints not exhausted", hint_tree))
    val split_tac = ttsplit tt
    val x_tac = ttyping x ltt k ctxt typehint
    val k_tac = kinding kindhint
    val y_tac = ttyping y rtt k ctxt type'hint
  in ([RTac @{thm ttyping_take'}] @ split_tac @ x_tac
    @ [simp, simp, simp] @ k_tac @ [simp] @ y_tac) end
  | ttyping x (@{term TyTrLeaf}, G) _ ctxt hint_tree = let
    val ty_tac = typing x G ctxt hint_tree
  in ([RTac @{thm ttyping_default}, SimpTac (@{thms composite_anormal_expr_def}, [])] @ ty_tac) end
  | ttyping t _ _ _ _ = raise TERM ("ttyping", [t])

fun mk_ttsplit_tacs nm k ctxt hint_tree = let
    (* construct a simpset that knows about the definitions we find in a ttyping *)
    val ss = put_simpset HOL_basic_ss ctxt
        addsimps @{thms replicate_unfold}
        addsimps (Proof_Context.get_thms ctxt "abbreviated_type_defs")
    (* get the definitions we care about for our function *)
    val body_def = Proof_Context.get_thm ctxt (nm ^ "_def")
    val ty_def = Proof_Context.get_thm ctxt (nm ^ "_type_def")
    val tt_def = Proof_Context.get_thm ctxt (nm ^ "_typetree_def")
    (* simplify, then extract the actual definitions (i.e. the right part of the definition) *)
    val body = body_def |> simplify ss |> safe_mk_meta_eq |> Thm.concl_of |> Logic.dest_equals |> snd
    val tt   = tt_def |> simplify ss |> safe_mk_meta_eq |> Thm.concl_of |> Logic.dest_equals |> snd
    val ty   = ty_def |> simplify ss |> safe_mk_meta_eq |> Thm.concl_of |> Logic.dest_equals |> snd
    (* the unsimplified definition of the typetree *)
    val ity  = ty |> HOLogic.dest_prod |> snd |> HOLogic.dest_prod |> fst
    (* get the first kinding hint *)
    val (kinding_hint, hint_tree) = (case hint_tree of
                                                Branch [Leaf kindh, ttyph] => (kindh, ttyph)
                                              | _ => raise HINTS ("mk_ttsplit_tac: hints don't start with a kinding", hint_tree))
    val ps = kind_proof_single (@{term SomeT} $ ity) k ctxt kinding_hint
    (* generate the tactics *)
    val tacs = ttyping body (tt, [ps]) k ctxt hint_tree
  in tacs end

fun mk_ttsplit_tacs_final nm k ctxt hint_tree
    = map (fn tac => (tac, interpret_tac tac)) (mk_ttsplit_tacs nm k ctxt hint_tree)

fun apply_ttsplit_tacs_simple nm ctxt hints
    = mk_ttsplit_tacs_final nm @{term "[] :: kind env"} ctxt hints
    |> map (fn (_, t) => DETERM (t ctxt 1))
    |> EVERY

fun tactic_debug_tac ctxt tacs = let
  fun inner i (tac :: tacs) t = (case Seq.pull (tac ctxt t)
    of SOME (t', _) => (inner (i + 1) tacs t')
     | NONE => (tracing (string_of_int i) ; Seq.empty))
     | inner _ [] t = Seq.single t
in inner 0 tacs end

end (* end TTyping_Tactics *)
*}

ML {*
val _ =
  Outer_Syntax.command @{command_keyword "ML_quiet"} "ML text within theory or local theory"
    (Parse.ML_source >> (fn source =>
      Toplevel.generic_theory
        (ML_Context.exec (fn () =>
            ML_Context.eval_source (ML_Compiler.verbose false ML_Compiler.flags) source) #>
          Local_Theory.propagate_ml_env)));
*}

end

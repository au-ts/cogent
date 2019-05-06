(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory CogentHelper
imports "TypeTrackingTyping" "ML_Old"
keywords "ML_quiet" :: thy_decl % "ML"
begin

(* Rewrite rules to get expressions in the assumptions *)

lemma typing_lit': "\<lbrakk> K \<turnstile> \<Gamma> consumed; t = lit_type l \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Lit l : TPrim t" 
  by (simp only: typing_lit)

lemma typing_put':  "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                     ; \<Xi>, K, \<Gamma>1 \<turnstile> e : TRecord ts s
                     ; s \<noteq> ReadOnly
                     ; f < length ts
                     ; ts ! f = (t, taken)
                     ; K \<turnstile> t :\<kappa> k
                     ; D \<in> k \<or> taken
                     ; \<Xi>, K, \<Gamma>2 \<turnstile> e' : t
                     ; ts' = (ts [f := (t,False)])
                     \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Put e f e' : TRecord ts' s"
  by (simp add: typing_put)

lemma typing_prim' : "\<lbrakk> prim_op_type oper = (ts,t)
                      ; ts' = map TPrim ts
                      ; \<Xi>, K, \<Gamma> \<turnstile>* args : ts' 
                      \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Prim oper args : TPrim t"
  by (simp only: typing_prim)

lemma typing_con': "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile> x : t; (tag,t) \<in> set ts 
                    ; ts' = (map snd ts)
                    ; K \<turnstile>* ts' wellformed
                    ; distinct (map fst ts)
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Con ts tag x : TSum ts" 
  by (simp only: typing_con)

lemma typing_struct': "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile>* es : ts
                       ; ts' =  (zip ts (replicate (length ts) False))
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
  by (force intro!: split_bang.intros simp add: split_bang_comp.simps)

definition
  type_ctx_wellformed :: "kind env \<Rightarrow> ctx \<Rightarrow> bool"
where
  "type_ctx_wellformed K \<Gamma> = (\<forall>t. Some t \<in> set \<Gamma> \<longrightarrow> K \<turnstile> t wellformed)"

definition type_ctx_wellformed' :: "kind env \<Rightarrow> ctx \<Rightarrow> bool" where
  "type_ctx_wellformed' K \<Gamma> = list_all (\<lambda>t. \<forall>t'. t = Some t' \<longrightarrow> K \<turnstile> t' wellformed) \<Gamma>"

lemma type_ctx_wellformed_iff_type_ctx_wellformed':
  "type_ctx_wellformed K \<Gamma> = type_ctx_wellformed' K \<Gamma>"
proof -
  have "(\<forall>t. Some t \<in> set \<Gamma> \<longrightarrow> K \<turnstile> t wellformed) = (\<forall>t\<in>set \<Gamma>. \<forall>t'. t = Some t' \<longrightarrow> K \<turnstile> t' wellformed)"
    by blast
  also have "... = list_all (\<lambda>t. \<forall>t'. t = Some t' \<longrightarrow> K \<turnstile> t' wellformed) \<Gamma>"
    by (clarsimp simp add: list_all_iff)
  finally show ?thesis
    unfolding type_ctx_wellformed_def type_ctx_wellformed'_def
    by blast
qed

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
  apply (clarsimp simp add: type_ctx_wellformed_iff_type_ctx_wellformed' type_ctx_wellformed'_def
      ttsplit_def ttsplit_weak_def ttsplit_inner_conv_all_nth)
  apply (clarsimp simp add: list_all_length)
  apply (drule_tac x=i in spec)+
  apply clarsimp
  apply (erule ttsplit_inner_comp.cases)
    apply (clarsimp simp add: ttsplit_inner_comp.simps, blast)+
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
                   ; (tag, t) \<in> set ts
                   ; ttsplit_triv \<Gamma>2 [Some t] \<Gamma>3 [Some (TSum (filter (\<lambda> x. fst x \<noteq> tag) ts))] \<Gamma>4
                   ; \<Xi>, K, \<Gamma>3 T\<turnstile> a : u
                   ; \<Xi>, K, \<Gamma>4 T\<turnstile> b : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Case x tag a b : u"
  by (simp only: ttyping_case[rotated])

lemma ttyping_take': "\<lbrakk> ttsplit K \<Gamma> ijs [] \<Gamma>1 [Some t, Some (TRecord ts' s)] \<Gamma>2 
                   ; \<Xi>, K, \<Gamma>1 T\<turnstile> e : TRecord ts s
                   ; s \<noteq> ReadOnly
                   ; f < length ts
                   ; ts ! f = (t, False)
                   ; K \<turnstile> t :\<kappa> k
                   ; ts = ts'[f := (t, False)] \<and> fst (ts' ! f) = t \<and> (S \<in> k \<or> snd (ts' ! f))
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

(*
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
*)

datatype tac = RTac of thm
             | SimpTac of thm list * thm list
             | ForceTac of thm list
             | WeakeningTac of thm list
             | SplitsTac of int * (int * tac list) list
             | BlackBoxTac of (Proof.context -> int -> tactic)

val simp = SimpTac ([], [])

datatype hints = KindingTacs of tac list
  | TTSplitBangTacs of tac list
  | TypingTacs of tac list

exception HINTS of string * hints list

fun kinding (KindingTacs tac :: hints) = (tac, hints)
  | kinding hints = raise HINTS ("kinding", hints)

fun typing_hint (TypingTacs tac :: hints) = (tac, hints)
  | typing_hint hints = raise HINTS ("typing", hints)

fun apply_split @{term "Some TSK_L"} hints t = ((t, NONE), hints)
  | apply_split @{term "Some TSK_S"} hints t = ((t, t), hints)
  | apply_split @{term "Some TSK_NS"} hints t = let
    val (tacs, hints) = kinding hints
    val thm = case tacs of [RTac thm] => thm 
      | _ => raise HINTS ("apply_split: TSK_NS", [KindingTacs tacs])
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
  | interpret_tac (BlackBoxTac tac) ctxt = tac ctxt
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

fun kind_proofs ((@{term SomeT} $ t) :: ts) k ctxt hints = let
    val (tacs, hints) = kinding hints
(*
    val _ = case tacs of
        [RTac thm] => Display.pretty_thm ctxt thm |> Pretty.writeln
      | _ => warning "unexpected kinding tacs"
*)
    val t = betapplys (@{term "kinding"}, [k, t, @{schematic_term "?k :: kind"}])
    val ct = Thm.cterm_of ctxt (@{term Trueprop} $ t)
    val rs = EVERY (map (fn t => interpret_tac t ctxt 1) tacs) (Thm.trivial ct)
    val t = (case Seq.pull rs of NONE => raise TERM ("kind_proofs: failed", [k, t])
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
  in ((T1, x_proofs @ ts1), (T2, y_proofs @ ts2), hints) end
  | follow_tt (tt, _) _ _ _ = raise TERM ("follow_tt", [tt])

fun ttsplit_inner (@{term "Some TSK_S"} :: tsks) (SOME p :: Gamma) ctxt =
    let
      val rest = ttsplit_inner tsks Gamma
    in resolve_tac ctxt @{thms ttsplit_innerI_True(4)}
      THEN' (resolve_tac ctxt [p])
      THEN' simp_tac ctxt
      THEN' rest ctxt
    end
  | ttsplit_inner (@{term "Some TSK_L"} :: tsks) (SOME p :: Gamma) ctxt =
    let
      val rest = ttsplit_inner tsks Gamma
    in resolve_tac ctxt @{thms ttsplit_innerI_True(3)}
      THEN' (resolve_tac ctxt [p])
      THEN' rest ctxt
    end
  | ttsplit_inner (@{term "None :: type_split_kind option"} :: tsks) (SOME p :: Gamma) ctxt =
    let
      val rest = ttsplit_inner tsks Gamma
    in resolve_tac ctxt @{thms ttsplit_innerI_True(2)}
      THEN' (resolve_tac ctxt [p])
      THEN' rest ctxt
    end
  | ttsplit_inner (@{term "None :: type_split_kind option"} :: tsks) (NONE :: Gamma) ctxt =
    let
      val rest = ttsplit_inner tsks Gamma
    in resolve_tac ctxt @{thms ttsplit_innerI_True(1)}
      THEN' rest ctxt
    end
  | ttsplit_inner [] [] ctxt = resolve_tac ctxt @{thms ttsplit_innerI_True(5)}
  | ttsplit_inner tsks _ _ = raise TERM ("ttsplit_inner", tsks)

fun ttsplit (Const (@{const_name TyTrSplit}, _) $ sps $ _ $ _ $ _ $ _, Gamma) = let
    val inner = BlackBoxTac (ttsplit_inner (HOLogic.dest_list sps) Gamma)
  in [RTac @{thm ttsplitI}, inner, simp, simp] end
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
    val hints = case typing_hint hints of
                  ([], hints) => hints
                | _ => raise ERROR "typing hints were incorrectly generated"
  in ([RTac @{thm typing_var_weak[unfolded singleton_def Cogent.empty_def]},
      RTac thm, simp, WeakeningTac thms, simp], hints) end
  | typing (Const (@{const_name Struct}, _) $ _ $ xs) G ctxt hints
  = (case dest_all_vars xs of SOME ixs => let
    val hints =  case typing_hint hints of
                   ([], hints) => hints
                 | _ => raise ERROR "typing hints were incorrectly generated"
  in ([RTac @{thm typing_struct'}] @ typing_all_vars ctxt G ixs @ [simp], hints) end
    | NONE => typing_hint hints)
  | typing (Const (@{const_name Prim}, _) $ _ $ xs) G ctxt hints
  = (case dest_all_vars xs of SOME ixs => let
    val hints = case typing_hint hints of
                  ([], hints) => hints
                | _ => raise ERROR "typing hints were incorrectly generated"
  in ([RTac @{thm typing_prim'}, simp, simp] @ typing_all_vars ctxt G ixs, hints) end
    | NONE => typing_hint hints)
  | typing _ _ _ hints = typing_hint hints

fun ttyping (Const (@{const_name Split}, _) $ x $ y) tt k ctxt hints = let
    val (ltt, rtt, hints) = follow_tt tt k ctxt hints
    val split_tac = ttsplit tt
    val (l_tac, hints) = ttyping x ltt k ctxt hints
    val (r_tac, hints) = ttyping y rtt k ctxt hints
  in ([RTac @{thm ttyping_split}] @ split_tac @ l_tac @ r_tac, hints) end
  | ttyping (Const (@{const_name Let}, _) $ x $ y) tt k ctxt hints = let
    val (ltt, rtt, hints) = follow_tt tt k ctxt hints
    val split_tac = ttsplit tt
    val (l_tac, hints) = ttyping x ltt k ctxt hints
    val (r_tac, hints) = ttyping y rtt k ctxt hints
  in ([RTac @{thm ttyping_let}] @ split_tac @ l_tac @ r_tac, hints) end
  | ttyping (Const (@{const_name LetBang}, _) $ _ $ x $ y) tt k ctxt hints = let
    val (ltt, rtt, hints) = follow_tt tt k ctxt hints
    val tsb_tac = ttsplit_bang tt
    val (x_tac, hints) = ttyping x ltt k ctxt hints
    val (y_tac, hints) = ttyping y rtt k ctxt hints
    val (k_tac, hints) = kinding hints
  in ([RTac @{thm ttyping_letb}] @ tsb_tac @ x_tac @ y_tac @ k_tac @ [simp], hints) end
  | ttyping (Const (@{const_name Cogent.If}, _) $ c $ x $ y) tt k ctxt hints = let
    val (ltt, rtt, hints) = follow_tt tt k ctxt hints
    val (x_tt, y_tt, hints) = follow_tt rtt k ctxt hints
    val split_tac = ttsplit tt
    val (c_tac, hints) = ttyping c ltt k ctxt hints
    val (x_tac, hints) = ttyping x x_tt k ctxt hints
    val (y_tac, hints) = ttyping y y_tt k ctxt hints
  in ([RTac @{thm ttyping_if}] @ split_tac
    @ [simp, RTac @{thm ttsplit_trivI}, simp, simp] @ c_tac @ x_tac @ y_tac, hints) end
  | ttyping (Const (@{const_name Case}, _) $ x $ _ $ m $ nm) tt k ctxt hints = let
    val (ltt, rtt, hints) = follow_tt tt k ctxt hints
    val (m_tt, nm_tt, hints) = follow_tt rtt k ctxt hints
    val split_tac = ttsplit tt
    val (x_tac, hints) = ttyping x ltt k ctxt hints
    val (m_tac, hints) = ttyping m m_tt k ctxt hints
    val (nm_tac, hints) = ttyping nm nm_tt k ctxt hints
  in ([RTac @{thm ttyping_case'}] @ split_tac @ x_tac @ [simp]
    @ [simp, RTac @{thm ttsplit_trivI}, simp, simp] @ m_tac @ nm_tac, hints) end
  | ttyping (Const (@{const_name Take}, _) $ x $ _ $ y) tt k ctxt hints = let
    val (ltt, rtt, hints) = follow_tt tt k ctxt hints
    val split_tac = ttsplit tt
    val (x_tac, hints) = ttyping x ltt k ctxt hints
    val (k_tac, hints) = kinding hints
    val (y_tac, hints) = ttyping y rtt k ctxt hints
  in ([RTac @{thm ttyping_take'}] @ split_tac @ x_tac
    @ [simp, simp, simp] @ k_tac @ [simp] @ y_tac, hints) end
  | ttyping x (@{term TyTrLeaf}, G) _ ctxt hints = let
    val (ty_tac, hints) = typing x G ctxt hints
  in ([RTac @{thm ttyping_default}, SimpTac (@{thms composite_anormal_expr_def}, [])] @ ty_tac, hints) end
  | ttyping t _ _ _ _ = raise TERM ("ttyping", [t])

fun mk_ttsplit_tacs nm k ctxt hints = let
    val ss = put_simpset HOL_basic_ss ctxt
        addsimps @{thms replicate_unfold}
        addsimps (Proof_Context.get_thms ctxt "abbreviated_type_defs")
    val body_def = Proof_Context.get_thm ctxt (nm ^ "_def")
    val ty_def = Proof_Context.get_thm ctxt (nm ^ "_type_def")
    val tt_def = Proof_Context.get_thm ctxt (nm ^ "_typetree_def")
    val (_, body) = Logic.dest_equals (Thm.concl_of (safe_mk_meta_eq (simplify ss body_def)))
    val (_, tt) = Logic.dest_equals (Thm.concl_of (safe_mk_meta_eq (simplify ss tt_def)))
    val (_, ty) = Logic.dest_equals (Thm.concl_of (safe_mk_meta_eq (simplify ss ty_def)))
    val (ity, _) = HOLogic.dest_prod ty |> snd |> HOLogic.dest_prod
    val (ps, hints) = kind_proofs [@{term SomeT} $ ity] k ctxt hints
    val (tacs, hints) = ttyping body (tt, ps) k ctxt hints
    val _ = case hints of [] => () | _ => raise HINTS ("mk_ttsplit_tacs: remaining", hints)
  in tacs end

fun mk_ttsplit_tacs_final nm k ctxt hints
    = map interpret_tac (mk_ttsplit_tacs nm k ctxt hints)

fun apply_ttsplit_tacs_simple nm ctxt hints
    = mk_ttsplit_tacs_final nm @{term "[] :: kind env"} ctxt hints
    |> map (fn t => DETERM (t ctxt 1))
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

(*
  This file contains all the Isabelle shallow embedding to C correspondence theorems for word
  array functions.
*)
theory WordArray_SCCorres
  imports WordArray_Abstractions
begin

context WordArray begin

  
section "scorres of word array functions"


ML \<open>
fun get_wa_valRel "Bool" = error ("Can't find valRel_WordArrayBool")
  | get_wa_valRel "U8" = @{thm valRel_WordArrayU8}
  | get_wa_valRel "U16" = @{thm valRel_WordArrayU16}
  | get_wa_valRel "U32" = @{thm valRel_WordArrayU32}
  | get_wa_valRel "U64" = @{thm valRel_WordArrayU64}
  | get_wa_valRel x = error ("Can't find valRel_WordArray" ^ x)
\<close>

lemmas valRel_WordArray_simps = valRel_WordArrayU8 
                                valRel_WordArrayU16
                                valRel_WordArrayU32
                                valRel_WordArrayU64 

ML \<open>
fun wa_length_tac ctxt =
let  
  fun clarsimp_add thms = Clasimp.clarsimp_tac (add_simps thms ctxt) 1;
  val base_simpset = @{thms val.scorres_def valRel_records wordarray_length' valRel_WordArray_simps};
in
  clarsimp_add base_simpset 
  THEN etac @{thm v_sem_appE} 1
  THEN ALLGOALS (fn i => etac @{thm v_sem_afunE} i)
  THEN etac @{thm v_sem_varE} 1
  THEN clarsimp_add @{thms val_wa_length_def}
  THEN rtac @{thm FalseE} 1
  THEN clarsimp_add []
end;

val goal = @{cterm "valRel \<xi>p (v:: 32 word WordArray) v' \<Longrightarrow> val.scorres (wordarray_length v) (App (AFun ''wordarray_length'' ts) (Var 0)) [v'] \<xi>p"};
val proof_state = Goal.init goal;
val n = proof_state |> wa_length_tac @{context} |>  Seq.hd |> Goal.finish @{context}
\<close>

lemma scorres_wordarray_length_u8:
  "\<lbrakk>valRel \<xi>p (v:: 8 word WordArray) v'\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_length v) (App (AFun ''wordarray_length'' ts) (Var 0)) [v'] \<xi>p"
  by (tactic \<open>wa_length_tac @{context}\<close>)

lemma scorres_wordarray_length_u16:
  "\<lbrakk>valRel \<xi>p (v:: 16 word WordArray) v'\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_length v) (App (AFun ''wordarray_length'' ts) (Var 0)) [v'] \<xi>p"
  by (tactic \<open>wa_length_tac @{context}\<close>)

lemma scorres_wordarray_length_u32:
  "\<lbrakk>valRel \<xi>p (v:: 32 word WordArray) v'\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_length v) (App (AFun ''wordarray_length'' ts) (Var 0)) [v'] \<xi>p"
  by (tactic \<open>wa_length_tac @{context}\<close>)


lemma scorres_wordarray_length_u64:
  "\<lbrakk>valRel \<xi>p (v:: 64 word WordArray) v'\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_length v) (App (AFun ''wordarray_length'' ts) (Var 0)) [v'] \<xi>p"
  by (tactic \<open>wa_length_tac @{context}\<close>)


ML \<open>
fun wa_get_tac ctxt =
let  
  fun clarsimp_add thms = Clasimp.clarsimp_tac (add_simps thms ctxt);
  val base_simpset = @{thms val.scorres_def valRel_records wordarray_get' valRel_WordArray_simps};
in
  clarsimp_add base_simpset 1
  THEN rtac @{thm conjI} 1
  THEN ALLGOALS (fn i => clarsimp_add [] i 
    THEN etac @{thm v_sem_appE} i
    THEN etac @{thm v_sem_afunE} i
    THEN etac @{thm v_sem_varE} i
    THEN clarsimp_add @{thms val_wa_get_def} i)
  THEN TRYALL (fn i => rtac @{thm FalseE} i
    THEN etac @{thm v_sem_afunE} i
    THEN clarsimp_add [] i)
end;

val goal = @{cterm "valRel \<xi>p (v:: (32 word WordArray, 32 word) RR) v'
    \<Longrightarrow> val.scorres (wordarray_get v) (App (AFun ''wordarray_get'' ts) (Var 0)) [v'] \<xi>p"};
val proof_state = Goal.init goal;
val n = proof_state |> wa_get_tac @{context} |>  Seq.hd 
val b = dresolve_tac
\<close>

lemma scorres_wordarray_get_u8:
  "valRel \<xi>p (v:: (8 word WordArray, 32 word) RR) v'
    \<Longrightarrow> val.scorres (wordarray_get v) (App (AFun ''wordarray_get'' ts) (Var 0)) [v'] \<xi>p"
  apply (tactic \<open>wa_get_tac @{context}\<close>)
  done

lemma scorres_wordarray_get_u16:
  "valRel \<xi>p (v:: (16 word WordArray, 32 word) RR) v'
    \<Longrightarrow> val.scorres (wordarray_get v) (App (AFun ''wordarray_get'' ts) (Var 0)) [v'] \<xi>p"
  apply (tactic \<open>wa_get_tac @{context}\<close>)
  done

lemma scorres_wordarray_get_u32:
  "valRel \<xi>p (v:: (32 word WordArray, 32 word) RR) v'
    \<Longrightarrow> val.scorres (wordarray_get v) (App (AFun ''wordarray_get'' ts) (Var 0)) [v'] \<xi>p"
  apply (tactic \<open>wa_get_tac @{context}\<close>)
  done

lemma scorres_wordarray_get_u64:
  "valRel \<xi>p (v:: (64 word WordArray, 32 word) RR) v'
    \<Longrightarrow> val.scorres (wordarray_get v) (App (AFun ''wordarray_get'' ts) (Var 0)) [v'] \<xi>p"
  apply (tactic \<open>wa_get_tac @{context}\<close>)
  done

lemma related_lists_update_nth_eq:
  "\<lbrakk>length ys = length xs; j < length xs; \<forall>i < length xs. xs ! i = f (ys ! i)\<rbrakk> 
    \<Longrightarrow> xs[i := f v] ! j = f (ys[i := v] ! j)"
  apply (erule_tac x = j in allE)
  apply (case_tac " i = j"; clarsimp)
  done     

ML \<open>

fun inst_param_tac param_nms var_nms thm tac ({context, params, ...} : Subgoal.focus) =
let
  fun mk_inst a b = ((b, 0), (snd o hd o (filter (fn v => fst v = a))) params) 
  val insts = map2 mk_inst param_nms var_nms
  val inst_thm = Drule.infer_instantiate context insts thm
in 
  tac context [inst_thm] 1
end
  
\<close>

ML \<open>
fun wa_put2_tac ctxt =
let  
  fun clarsimp_add thms = Clasimp.clarsimp_tac (add_simps thms ctxt);
  val base_simpset = @{thms val.scorres_def valRel_records wordarray_put2' valRel_WordArray_simps};
  val helper_thm = @{thm related_lists_update_nth_eq}
in
  clarsimp_add base_simpset 1
  THEN etac @{thm v_sem_appE} 1
  THEN ALLGOALS (fn i => etac @{thm v_sem_afunE} i)
  THEN rtac @{thm FalseE} 2
  THEN clarsimp_add [] 2
  THEN etac @{thm v_sem_varE} 1
  THEN clarsimp_add @{thms val_wa_put2_def} 1
  THEN Subgoal.FOCUS_PARAMS (inst_param_tac ["i"] ["j"] helper_thm resolve_tac) ctxt 1
  THEN ALLGOALS (fn i => asm_full_simp_tac ctxt i)
end;
\<close>
ML \<open>
val goal = @{cterm "valRel \<xi>p (v:: (32 word WordArray, 32 word, 32 word) WordArrayPutP) v'
    \<Longrightarrow> val.scorres (wordarray_put2 v) (App (AFun ''wordarray_put2'' ts) (Var 0)) [v'] \<xi>p"};
val proof_state = Goal.init goal;
val n = proof_state |> wa_put2_tac @{context} |> Seq.hd 
\<close>

lemma scorres_wordarray_put2_u8:
  "\<lbrakk>valRel \<xi>p (v:: (8 word WordArray, 32 word, 8 word) WordArrayPutP) v'\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_put2 v) (App (AFun ''wordarray_put2'' ts) (Var 0)) [v'] \<xi>p"
  by (tactic \<open> wa_put2_tac @{context}\<close>)

lemma scorres_wordarray_put2_u16:
  "\<lbrakk>valRel \<xi>p (v:: (16 word WordArray, 32 word, 16 word) WordArrayPutP) v'\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_put2 v) (App (AFun ''wordarray_put2'' ts) (Var 0)) [v'] \<xi>p"
  by (tactic \<open> wa_put2_tac @{context}\<close>)

lemma scorres_wordarray_put2_u32:
  "\<lbrakk>valRel \<xi>p (v:: (32 word WordArray, 32 word, 32 word) WordArrayPutP) v'\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_put2 v) (App (AFun ''wordarray_put2'' ts) (Var 0)) [v'] \<xi>p"
  by (tactic \<open>wa_put2_tac @{context}\<close>)

lemma scorres_wordarray_put2_u64:
  "\<lbrakk>valRel \<xi>p (v:: (64 word WordArray, 32 word, 64 word) WordArrayPutP) v'\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_put2 v) (App (AFun ''wordarray_put2'' ts) (Var 0)) [v'] \<xi>p"
  by (tactic \<open> wa_put2_tac @{context}\<close>)

lemma map_forall:
  "\<lbrakk>length xs = length ys; \<forall>i<length xs. xs ! i = f(ys ! i)\<rbrakk> \<Longrightarrow> xs = map f ys"
  apply (induct xs arbitrary: ys; clarsimp)
  apply (drule_tac x = "tl ys" in meta_spec; clarsimp)
  apply (drule meta_mp)
   apply linarith
  apply (drule meta_mp)
   apply clarsimp
   apply (erule_tac x = "Suc i" in allE)
   apply clarsimp
   apply (simp add: tl_drop_1)
  apply clarsimp  
  by (metis list.sel(3) list_exhaust_size_gt0 list_to_map_more nth_Cons_0 zero_less_Suc)

lemma take_1_drop:
  "i < length xs \<Longrightarrow> List.take (Suc 0) (List.drop i xs) = [xs ! i]"
  apply (induct xs arbitrary: i)
   apply (simp add: take_Suc_conv_app_nth)
  by (simp add: drop_Suc_nth)

lemma take_drop_Suc:
  "i < l \<and> i < length xs \<Longrightarrow> 
    List.take (l - i) (List.drop i xs) = (xs ! i) # List.take (l - Suc i) (List.drop (Suc i) xs)"
  apply clarsimp
  by (metis Cons_nth_drop_Suc Suc_diff_Suc take_Suc_Cons)


lemma take_drop_Suc_app:
  "\<lbrakk>i < l; Suc l \<le> length xs\<rbrakk> \<Longrightarrow>
    List.take (Suc l - i) (List.drop i xs) = List.take (l - i) (List.drop i xs) @ [xs ! l]"
  apply (induct i)
   apply (simp add: take_Suc_conv_app_nth)
  apply clarsimp
  apply (subst Suc_diff_Suc[symmetric])
   apply arith
  apply (subst take_hd_drop[symmetric])
   apply simp
  apply simp
  using Suc_le_lessD hd_drop_conv_nth by blast
  

lemma scorres_wordarray_fold_no_break_u32:
  "\<lbrakk>valRel \<xi>p \<lparr>WordArrayMapP.arr\<^sub>f = (arr::32 word WordArray), frm\<^sub>f = (frm::32 word), to\<^sub>f = to,
      f\<^sub>f = f, acc\<^sub>f = (acc::32 word), obsv\<^sub>f = obsv\<rparr> v'\<rbrakk>
    \<Longrightarrow> val.scorres 
    (wordarray_fold_no_break \<lparr>WordArrayMapP.arr\<^sub>f = arr, frm\<^sub>f = frm, to\<^sub>f = to, f\<^sub>f = f, 
        acc\<^sub>f = acc, obsv\<^sub>f = obsv\<rparr>) (App (AFun ''wordarray_fold_no_break'' ts) (Var 0)) [v'] \<xi>p1"
  apply (clarsimp simp: val.scorres_def)
  apply (erule v_sem_appE; erule v_sem_afunE; clarsimp)
  apply (erule v_sem_varE; clarsimp)
  apply (clarsimp simp: val_wa_foldnb_0p_def)
  apply (case_tac func; clarsimp)
   apply (clarsimp simp: wordarray_fold_no_break' valRel_records valRel_WordArrayU32)
   apply (induct to arbitrary: v')
    apply (erule val_wa_foldnb_bod.elims; clarsimp)
   apply clarsimp
   apply (drule unatSuc; clarsimp)
   apply (case_tac "length xs < Suc (unat to)")
    apply (drule val_wa_foldnb_bod_back_step'; simp)
   apply (case_tac "unat frm \<ge> Suc (unat to)")
    apply clarsimp
    apply (erule val_wa_foldnb_bod.elims; clarsimp)
   apply (case_tac "unat frm = unat to")
    apply (clarsimp simp: take_1_drop)
    apply (erule val_wa_foldnb_bod.elims; clarsimp)
    apply (erule val_wa_foldnb_bod.elims; clarsimp)
    apply (erule_tac x = "\<lparr>ElemAO.elem\<^sub>f = arr ! unat frm, acc\<^sub>f = acc, obsv\<^sub>f = obsv\<rparr>" in allE)
    apply clarsimp
    apply (erule_tac x = "VRecord [VPrim (LU32 (arr ! unat frm)), VPrim (LU32 acc), obsva]" in allE)
    apply clarsimp
    apply (erule v_sem_appE; clarsimp)
    apply (erule v_sem_varE; clarsimp)
   apply clarsimp
   apply (drule val_wa_foldnb_bod_back_step; simp)
    apply (meson Suc_le_eq nat_neq_iff word_unat.Rep_eqD)
   apply clarsimp
   apply (drule_tac x = r' in meta_spec)
   apply (drule_tac x = xs in meta_spec)
   apply (drule_tac x = obsva in meta_spec)
   apply (drule_tac x = x61 in meta_spec)
   apply (drule_tac x = x62 in meta_spec)
   apply (drule_tac x = "VRecord [VAbstract (VWA (TPrim (Num U32)) xs), VPrim (LU32 frm), 
      VPrim (LU32 to), VFunction x61 x62, VPrim (LU32 acc), obsva]" in meta_spec)
   apply clarsimp
   apply (subst take_drop_Suc_app)
     apply (meson Suc_le_eq nat_neq_iff word_unat.Rep_eqD)
    apply simp
   apply clarsimp
   apply (erule_tac x = "\<lparr>ElemAO.elem\<^sub>f = arr ! unat to, 
    acc\<^sub>f = fold (\<lambda>a b. f \<lparr>ElemAO.elem\<^sub>f = a, acc\<^sub>f = b, obsv\<^sub>f = obsv\<rparr>)
      (take (unat to - unat frm) (List.drop (unat frm) arr)) acc, obsv\<^sub>f = obsv\<rparr>" in allE)
   apply (erule_tac x = "VRecord [VPrim (LU32 (arr ! unat to)),
    VPrim (LU32 (fold (\<lambda>a b. f \<lparr>ElemAO.elem\<^sub>f = a, acc\<^sub>f = b, obsv\<^sub>f = obsv\<rparr>)
      (take (unat to - unat frm) (List.drop (unat frm) arr)) acc)), obsva]" in allE)
   apply clarsimp
   apply (erule v_sem_appE; clarsimp)
   apply (erule v_sem_varE; clarsimp)
  apply (clarsimp simp: wordarray_fold_no_break' valRel_records valRel_WordArrayU32)
  apply (induct to arbitrary: v')
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
  apply clarsimp
  apply (drule unatSuc; clarsimp)
  apply (case_tac "length xs < Suc (unat to)")
   apply (drule val_wa_foldnb_bod_back_step'; simp)
  apply (case_tac "unat frm \<ge> Suc (unat to)")
   apply clarsimp
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
  apply (case_tac "unat frm = unat to")
   apply (clarsimp simp: take_1_drop)
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
   apply (erule_tac x = "\<lparr>ElemAO.elem\<^sub>f = arr ! unat frm, acc\<^sub>f = acc, obsv\<^sub>f = obsv\<rparr>" in allE)
   apply clarsimp
   apply (erule_tac x = "VRecord [VPrim (LU32 (arr ! unat frm)), VPrim (LU32 acc), obsva]" in allE)
   apply clarsimp
   apply (erule v_sem_appE; clarsimp?)
    apply (erule v_sem_varE; clarsimp)
    apply (erule_tac x = resa in allE)
    apply (clarsimp split: if_splits simp: val_wa_length_def val_wa_get_def val_wa_put2_def)
   apply (erule v_sem_afunE; clarsimp)
  apply clarsimp
  apply (drule val_wa_foldnb_bod_back_step; simp)
   apply (meson Suc_le_eq nat_neq_iff word_unat.Rep_eqD)
  apply clarsimp
  apply (drule_tac x = r' in meta_spec)
  apply (drule_tac x = xs in meta_spec)
  apply (drule_tac x = obsva in meta_spec)
  apply (drule_tac x = x71 in meta_spec)
  apply (drule_tac x = x72 in meta_spec)
  apply (drule_tac x = "VRecord [VAbstract (VWA (TPrim (Num U32)) xs), VPrim (LU32 frm), 
     VPrim (LU32 to), VAFunction x71 x72, VPrim (LU32 acc), obsva]" in meta_spec)
  apply clarsimp
  apply (subst take_drop_Suc_app)
    apply (meson Suc_le_eq nat_neq_iff word_unat.Rep_eqD)
   apply simp
  apply clarsimp
  apply (erule_tac x = "\<lparr>ElemAO.elem\<^sub>f = arr ! unat to, 
   acc\<^sub>f = fold (\<lambda>a b. f \<lparr>ElemAO.elem\<^sub>f = a, acc\<^sub>f = b, obsv\<^sub>f = obsv\<rparr>)
     (take (unat to - unat frm) (List.drop (unat frm) arr)) acc, obsv\<^sub>f = obsv\<rparr>" in allE)
  apply (erule_tac x = "VRecord [VPrim (LU32 (arr ! unat to)),
   VPrim (LU32 (fold (\<lambda>a b. f \<lparr>ElemAO.elem\<^sub>f = a, acc\<^sub>f = b, obsv\<^sub>f = obsv\<rparr>)
     (take (unat to - unat frm) (List.drop (unat frm) arr)) acc)), obsva]" in allE)
  apply clarsimp
  apply (erule v_sem_appE; clarsimp?)
   apply (erule v_sem_varE; clarsimp)
   apply (erule_tac x = r in allE)
   apply (clarsimp split: if_splits simp: val_wa_length_def val_wa_get_def val_wa_put2_def)
  apply (erule v_sem_afunE; clarsimp)
  done

section "Correspondence From Isabelle Shallow Embedding to C"

theorem shallow_C_wordarray_put2_corres:
"\<lbrakk>\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_put2_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr) (App (AFun ''wordarray_put2_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_put2_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st;
 value_sem.rename_mono_prog wa_abs_typing_v rename \<Xi> \<xi>m \<xi>p;
 vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C wa_abs_repr wa_abs_upd_val rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
 value_sem.proc_env_matches wa_abs_typing_v \<xi>m \<Xi>;
 value_sem.matches wa_abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C wa_abs_repr wa_abs_typing_u wa_abs_upd_val rename (Generated.state_rel wa_abs_repr)
     (Generated_Shallow_Desugar.wordarray_put2_u32 vv\<^sub>s) Generated_TypeProof.wordarray_put2_u32
     (main_pp_inferred.wordarray_put2_u32' uv\<^sub>C) \<xi>0 \<xi>m \<xi>p [uv\<^sub>m] [vv\<^sub>m] \<Xi>
     [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))] \<sigma> s"
  apply clarsimp
  apply (frule val_rel_shallow_C_elim(1))
  apply (clarsimp simp: valRel_WordArrayPutP valRel_WordArrayU32)
  apply (drule_tac x = 0 in meta_spec)
  apply (drule_tac x = "[uv\<^sub>m]" in meta_spec)
  apply (drule_tac x = uv\<^sub>C in meta_spec)
  apply (drule_tac x = "[option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]" in meta_spec)
  apply (drule_tac x = \<sigma> in meta_spec)
  apply (drule_tac x = s in meta_spec)
  apply (clarsimp simp: corres_shallow_C_def)
  apply (monad_eq simp: wordarray_put2_u32'_def)
  apply (drule meta_mp)
   apply (drule val_rel_shallow_C_elim(3); simp)
  apply (drule meta_mp)
   apply (subst \<Xi>_def; subst wordarray_put2_u32_type_def; subst wordarray_put2_0_type_def; clarsimp)
  apply (clarsimp simp: corres_def)
  apply (erule impE)
   apply (rule_tac x = r in exI)
   apply (rule_tac x = x in exI)
   apply (frule u_v_matches_to_matches_ptrs)
   apply (clarsimp simp: \<Xi>_def wordarray_put2_u32_type_def wordarray_put2_0_type_def)
  apply clarsimp
  apply (erule_tac x = r' in allE)
  apply (erule_tac x = s' in allE)
  apply clarsimp
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = ra in exI)
  apply (clarsimp simp: Generated_TypeProof.wordarray_put2_u32_def)
  apply (rule conjI)
   apply (rule_tac \<sigma>' = \<sigma> and a' = uv\<^sub>m in u_sem_let)
    apply (rule u_sem_var[where i = 0 and \<gamma> = "[_]", simplified])
   apply (rule u_sem_abs_app)
     apply (rule u_sem_afun)
    apply (rule u_sem_var)
   apply (erule u_sem_appE; clarsimp)
    apply (erule u_sem_afunE; clarsimp)
    apply (erule u_sem_varE; clarsimp)
   apply (erule u_sem_afunE; clarsimp)
  apply (rule_tac x = "VAbstract (VWA (TPrim (Num U32)) (xs[unat (WordArrayPutP.idx\<^sub>f vv\<^sub>s) := VPrim (LU32 (WordArrayPutP.val\<^sub>f vv\<^sub>s))]))" in exI)
  apply clarsimp
  apply (rule conjI)
   apply (rule v_sem_let)
    apply (rule v_sem_var)
   apply (rule v_sem_abs_app)
     apply (rule v_sem_afun)
    apply (rule v_sem_var)
   apply (clarsimp simp: val_wa_put2_def)
  apply (clarsimp simp: Generated_Shallow_Desugar.wordarray_put2_u32_def wordarray_put2')
  apply (subst val_rel_shallow_C_def)
  apply (clarsimp simp: valRel_WordArrayPutP valRel_WordArrayU32)
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x = i in allE)
   apply clarsimp
   apply (case_tac "i = unat (WordArrayPutP.idx\<^sub>f vv\<^sub>s)"; clarsimp)
  apply (frule_tac i = 0 and 
                   \<tau> = "(prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))" 
                       in u_v_matches_proj_single'; simp)
  apply clarsimp
  apply (frule val_rel_shallow_C_elim(3); clarsimp simp: val_rel_simp)
  apply (erule u_v_recE)
  apply (erule u_v_r_consE; clarsimp simp: Generated_TypeProof.wordarray_put2_u32_type_def abbreviatedType2_def)
  apply (erule u_v_r_consE; clarsimp)+
  apply (erule u_v_r_emptyE; clarsimp)
  apply (erule u_v_primE)+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (erule u_v_p_absE; clarsimp)
  apply (erule u_sem_appE; erule u_sem_afunE; clarsimp)
  apply (erule u_sem_varE; clarsimp)
  apply (rule_tac x = "TCon ''WordArray'' [TPrim (Num U32)] (Boxed Writable undefined)" in exI)
  apply (rule_tac x = ra in exI)
  apply (rule_tac x = "insert (ptr_val (t2_C.arr_C uv\<^sub>C)) wa" in exI)
  apply (clarsimp simp: upd_wa_put2_0_def)
  apply (rule_tac ptrl = undefined and a = a in u_v_p_abs_w[where ts = "[TPrim (Num U32)]", simplified])
     apply simp
    apply (clarsimp simp: wa_abs_upd_val_def)
    apply (case_tac a; clarsimp)
    apply (case_tac x11; clarsimp)
    apply (case_tac x5; clarsimp)
    apply (rule conjI)
     apply (clarsimp simp: wa_abs_typing_u_def)
    apply (rule conjI)
     apply (clarsimp simp: wa_abs_typing_v_def)
     apply (erule_tac x = i in allE)
     apply clarsimp
     apply (case_tac "i = unat (t2_C.idx_C uv\<^sub>C)"; clarsimp)
    apply clarsimp
    apply (rule conjI; clarsimp)
     apply (drule distinct_indices)
     apply (erule_tac x = i in allE)+
     apply clarsimp
     apply (erule_tac x = "t2_C.idx_C uv\<^sub>C" in allE)
     apply (clarsimp simp: word_less_nat_alt)
    apply (erule_tac x = i in allE)
    apply clarsimp
    apply (case_tac "unat i = unat (t2_C.idx_C uv\<^sub>C)"; clarsimp simp: wa_abs_typing_u_def)
   apply (clarsimp simp: wa_abs_upd_val_def)
   apply (erule_tac x = "idx_C uv\<^sub>C" in allE)
   apply clarsimp
  apply clarsimp
  done



theorem shallow_C_wordarray_length_corres:
"\<lbrakk>\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr) (App (AFun ''wordarray_length_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_length_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st;
 value_sem.rename_mono_prog wa_abs_typing_v rename \<Xi> \<xi>m \<xi>p;
 vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C wa_abs_repr wa_abs_upd_val rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
 value_sem.proc_env_matches wa_abs_typing_v \<xi>m \<Xi>;
 value_sem.matches wa_abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_length_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C wa_abs_repr wa_abs_typing_u wa_abs_upd_val rename (Generated.state_rel wa_abs_repr)
     (Generated_Shallow_Desugar.wordarray_length_u32 vv\<^sub>s) Generated_TypeProof.wordarray_length_u32
     (main_pp_inferred.wordarray_length_u32' uv\<^sub>C) \<xi>0 \<xi>m \<xi>p [uv\<^sub>m] [vv\<^sub>m] \<Xi>
     [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_length_u32_type))] \<sigma> s"
  apply clarsimp
  apply (drule_tac x = 0 in meta_spec)
  apply (drule_tac x = "[uv\<^sub>m]" in meta_spec)
  apply (drule_tac x = uv\<^sub>C in meta_spec)
  apply (drule_tac x = "[option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_length_u32_type))]" in meta_spec)
  apply (drule_tac x = \<sigma> in meta_spec)
  apply (drule_tac x = s in meta_spec)
  apply (clarsimp simp:  corres_shallow_C_def)
  apply (monad_eq simp: wordarray_length_u32'_def)
  apply (drule meta_mp)
   apply (drule val_rel_shallow_C_elim(3); simp)
  apply (drule meta_mp)
   apply (subst \<Xi>_def; subst wordarray_length_u32_type_def; subst wordarray_length_0_type_def; simp)
  apply (clarsimp simp: corres_def)
  apply (erule impE)
   apply (rule_tac x = r in exI)
   apply (rule_tac x = x in exI)
   apply (frule u_v_matches_to_matches_ptrs)
   apply (clarsimp simp: \<Xi>_def wordarray_length_u32_type_def wordarray_length_0_type_def)
  apply clarsimp
  apply (erule_tac x = r' in allE)
  apply (erule_tac x = s' in allE)
  apply clarsimp
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = ra in exI)
  apply (clarsimp simp: Generated_TypeProof.wordarray_length_u32_def)
  apply (rule conjI)
   apply (rule_tac \<sigma>' = \<sigma> and a' = uv\<^sub>m in u_sem_let)
    apply (rule u_sem_var[where i = 0 and \<gamma> = "[_]", simplified])
   apply (rule u_sem_abs_app)
     apply (rule u_sem_afun)
    apply (rule u_sem_var)
   apply (erule u_sem_appE; clarsimp)
    apply (erule u_sem_afunE; clarsimp)
    apply (erule u_sem_varE; clarsimp)
   apply (erule u_sem_afunE; clarsimp)
  apply (monad_eq simp: wordarray_length_0'_def val_rel_simp)
  apply (rule_tac x = "VPrim (LU32 (SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C s uv\<^sub>C))))" in exI)
  apply (frule_tac i = 0 and 
                   \<tau> = "(prod.fst (prod.snd Generated_TypeProof.wordarray_length_u32_type))" 
                       in u_v_matches_proj_single'; simp)
  apply (clarsimp simp: Generated_TypeProof.wordarray_length_u32_type_def)
  apply (frule val_rel_shallow_C_elim(1); clarsimp simp: valRel_WordArrayU32)
  apply (frule val_rel_shallow_C_elim(3); clarsimp simp: val_rel_simp)
  apply (erule u_v_p_absE; clarsimp)
  apply (clarsimp simp: wa_abs_upd_val_def)
  apply (case_tac a; clarsimp)
  apply (case_tac x11; clarsimp)
  apply (case_tac x5; clarsimp)
  apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta)
  apply (drule_tac p =  uv\<^sub>C and 
                  uv = "UAbstract (UWA (TPrim (Num x1)) x12 x13)" in all_heap_rel_ptrD; 
         clarsimp simp: is_valid_simp heap_simp wa_abs_repr_def wa_abs_typing_u_def type_rel_simp val_rel_simp)
  apply (rule conjI)
   apply (rule v_sem_let)
    apply (rule v_sem_var)
   apply (rule v_sem_abs_app)
     apply (rule v_sem_afun)
    apply (rule v_sem_var)
   apply (clarsimp simp: val_wa_length_def)
  apply (subst val_rel_shallow_C_def)
  apply (rule_tac x = "TPrim (Num U32)" in exI)
  apply (rule_tac x = "{}" in exI)+
  apply (clarsimp simp: Generated_Shallow_Desugar.wordarray_length_u32_def wordarray_length')
  apply (rule conjI)
   apply (metis word_unat.Rep_inverse)
  apply (rule conjI)
   apply (rule u_v_prim[where l = "LU32 _", simplified])
  apply (clarsimp simp: val_rel_simp)
  done


theorem shallow_C_wordarray_get_corres:
"\<lbrakk>\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_get_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr) (App (AFun ''wordarray_get_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_get_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st;
 value_sem.rename_mono_prog wa_abs_typing_v rename \<Xi> \<xi>m \<xi>p; vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C wa_abs_repr wa_abs_upd_val rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
 value_sem.proc_env_matches wa_abs_typing_v \<xi>m \<Xi>;
 value_sem.matches wa_abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_get_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C wa_abs_repr wa_abs_typing_u wa_abs_upd_val rename (Generated.state_rel wa_abs_repr)
     (Generated_Shallow_Desugar.wordarray_get_u32 vv\<^sub>s) Generated_TypeProof.wordarray_get_u32
     (main_pp_inferred.wordarray_get_u32' uv\<^sub>C) \<xi>0 \<xi>m \<xi>p [uv\<^sub>m] [vv\<^sub>m] \<Xi>
     [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_get_u32_type))] \<sigma> s"
  apply clarsimp
  apply (frule val_rel_shallow_C_elim(1))
  apply (clarsimp simp: valRel_RR valRel_WordArrayU32)
  apply (drule_tac x = 0 in meta_spec)
  apply (drule_tac x = "[uv\<^sub>m]" in meta_spec)
  apply (drule_tac x = uv\<^sub>C in meta_spec)
  apply (drule_tac x = "[option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_get_u32_type))]" in meta_spec)
  apply (drule_tac x = \<sigma> in meta_spec)
  apply (drule_tac x = s in meta_spec)
  apply (clarsimp simp:  corres_shallow_C_def)
  apply (monad_eq simp: wordarray_get_u32'_def)
  apply (drule meta_mp)
   apply (drule val_rel_shallow_C_elim(3); simp)
  apply (drule meta_mp)
   apply (subst \<Xi>_def; subst wordarray_get_u32_type_def; subst wordarray_get_0_type_def; clarsimp)
  apply (clarsimp simp: corres_def)
  apply (erule impE)
   apply (rule_tac x = r in exI)
   apply (rule_tac x = x in exI)
   apply (frule u_v_matches_to_matches_ptrs)
   apply (clarsimp simp: \<Xi>_def wordarray_get_u32_type_def wordarray_get_0_type_def)
  apply clarsimp
  apply (erule_tac x = r' in allE)
  apply (erule_tac x = s' in allE)
  apply clarsimp
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = ra in exI)
  apply (clarsimp simp: Generated_TypeProof.wordarray_get_u32_def)
  apply (rule conjI)
   apply (rule_tac \<sigma>' = \<sigma> and a' = uv\<^sub>m in u_sem_let)
    apply (rule u_sem_var[where i = 0 and \<gamma> = "[_]", simplified])
   apply (rule u_sem_abs_app)
     apply (rule u_sem_afun)
    apply (rule u_sem_var)
   apply (erule u_sem_appE; clarsimp)
    apply (erule u_sem_afunE; clarsimp)
    apply (erule u_sem_varE; clarsimp)
   apply (erule u_sem_afunE; clarsimp)
  apply (rule_tac x = "VPrim (LU32 r')" in exI)
  apply (frule_tac i = 0 and 
                   \<tau> = "(prod.fst (prod.snd Generated_TypeProof.wordarray_get_u32_type))" 
                       in u_v_matches_proj_single'; simp)
  apply clarsimp
  apply (frule val_rel_shallow_C_elim(3))
  apply (clarsimp simp: val_rel_simp wordarray_get_u32_type_def abbreviatedType3_def)
  apply (erule u_v_recE)
  apply (erule u_v_r_consE; clarsimp)+
  apply (erule u_v_r_emptyE)
  apply (erule u_v_primE)
  apply (subst (asm) lit_type.simps; simp)
  apply (erule u_v_p_absE; clarsimp)
  apply (erule u_sem_appE; erule u_sem_afunE; clarsimp)
  apply (erule u_sem_varE; clarsimp simp: upd_wa_get_0_def)
  apply (simp add: word_less_nat_alt)
  apply (rule conjI)
   apply (rule v_sem_let)
    apply (rule v_sem_var)
   apply (rule v_sem_abs_app)
     apply (rule v_sem_afun)
    apply (rule v_sem_var)
   apply (clarsimp simp: val_wa_get_def wa_abs_upd_val_def)
   apply (erule_tac x = "t1_C.p2_C uv\<^sub>C" in allE; clarsimp simp: word_less_nat_alt)
  apply (subst val_rel_shallow_C_def)
  apply (rule_tac x = "TPrim (Num U32)" in exI)
  apply (rule_tac x = "{}" in exI)+
  apply (clarsimp simp: Generated_Shallow_Desugar.wordarray_get_u32_def wordarray_get' wa_abs_upd_val_def word_less_nat_alt)
  apply (erule_tac x = "unat (t1_C.p2_C uv\<^sub>C)" in allE)
  apply (force simp: val_rel_simp intro!: u_v_prim[where l = "LU32 _", simplified])
  done
(*
theorem
"\<lbrakk>\<And>i \<gamma> v' \<Gamma>' \<sigma>' st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_length_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_length_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>1 \<gamma> \<Xi>  \<Gamma>' \<sigma>' st;
 \<And>v' i \<gamma> \<Gamma> \<sigma> s.
    \<lbrakk>t5_C.f_C v' = FUN_ENUM_sum; i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma> ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_fold_no_break_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u)
         (App (AFun ''wordarray_fold_no_break_0'' []) (Var i)) (do x <- main_pp_inferred.wordarray_fold_no_break_0' v';
gets (\<lambda>s. x)
                                                                od)
         \<xi>1 \<gamma> \<Xi>  \<Gamma> \<sigma> s;
 value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m1 \<xi>p1;
 vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p1 \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
 value_sem.proc_env_matches abs_typing_v \<xi>m1 \<Xi>;
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.sum_arr_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.sum_arr vv\<^sub>s) Generated_TypeProof.sum_arr (main_pp_inferred.sum_arr' uv\<^sub>C) \<xi>1 \<xi>m1 \<xi>p1
     [uv\<^sub>m] [vv\<^sub>m] \<Xi> [option.Some (prod.fst (prod.snd Generated_TypeProof.sum_arr_type))] \<sigma> s"
  apply (monad_eq simp: sum_arr'_def  corres_shallow_C_def)
  apply (drule_tac x = 0 in meta_spec)
  apply (drule_tac x = "[uv\<^sub>m]" in meta_spec)
  apply (drule_tac x = "uv\<^sub>C" in meta_spec)
  apply (drule_tac x = "[option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))]" in meta_spec)
  apply (drule_tac x = \<sigma> in meta_spec)
  apply (drule_tac x = s in meta_spec)
  apply clarsimp
  apply (drule meta_mp)
   apply (frule val_rel_shallow_C_elim(3))
   apply clarsimp
  apply (clarsimp simp: corres_def)
  apply (erule impE)
   apply (rule_tac x = r in exI)
   apply (rule_tac x = x in exI)
   apply (frule u_v_matches_to_matches_ptrs)
   apply (clarsimp simp: \<Xi>_def sum_arr_type_def wordarray_length_0_type_def)
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (erule_tac x = ra in allE)
   apply (erule_tac x = s' in allE)
   apply clarsimp
   apply (drule_tac x = "t5_C uv\<^sub>C 0 ra FUN_ENUM_sum 0 (unit_t_C 0)" in meta_spec)
   apply (drule_tac x = 0 in meta_spec)
   apply (subgoal_tac "\<exists>a. val_rel a (t5_C uv\<^sub>C 0 ra FUN_ENUM_sum 0 (unit_t_C 0))")
    prefer 2
  thm val_rel_t5_C_def



  
  oops
*) 
end (* of context *)

end
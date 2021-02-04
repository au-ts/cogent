(*
  This file contains all the Isabelle shallow embedding to C correspondence theorems for word
  array functions.
*)
theory WordArray_SVCorres
  imports WordArray_Shallow WordArray_VAbsFun
begin

subsection "Shallow Word Array Value Relation"
text 
  "The shallow embedding of a word array is a list of words. Currently we only support word
   arrays with primitive words as values. In the future, we hope to extend this to elements which
   are non-linear."

overloading
  valRel_WordArrayUX \<equiv> valRel
begin
  definition valRel_WordArrayUX: 
    "\<And>\<xi> x v. valRel_WordArrayUX (\<xi> :: (funtyp,vabstyp) vabsfuns) (x :: (('a :: len8) word) WordArray) (v :: (funtyp, vabstyp) vval) \<equiv> 
      (if len_of TYPE('a) = 8 then 
        \<exists>xs. v = VAbstract (VWA (TPrim (Num U8)) xs) \<and> length x = length xs \<and> (\<forall>i < length xs. (xs ! i) = VPrim (LU8 (ucast (x ! i))))
      else if len_of TYPE('a) = 16 then 
        \<exists>xs. v = VAbstract (VWA (TPrim (Num U16)) xs) \<and> length x = length xs \<and> (\<forall>i < length xs. (xs ! i) = VPrim (LU16 (ucast (x ! i))))
      else if len_of TYPE('a) = 32 then 
        \<exists>xs. v = VAbstract (VWA (TPrim (Num U32)) xs) \<and> length x = length xs \<and> (\<forall>i < length xs. (xs ! i) = VPrim (LU32 (ucast (x ! i))))
      else if len_of TYPE('a) = 64 then 
        \<exists>xs. v = VAbstract (VWA (TPrim (Num U64)) xs) \<and> length x = length xs \<and> (\<forall>i < length xs. (xs ! i) = VPrim (LU64 (ucast (x ! i))))
      else False)"
end

(* Alternate definitions for the valRel relations for word arrays

overloading
  valRel_WordArrayU8 \<equiv> valRel
begin
  definition valRel_WordArrayU8: 
    "\<And>\<xi> x v. valRel_WordArrayU8 (\<xi> :: (funtyp,vabstyp) vabsfuns) (x :: (8 word) WordArray) (v :: (funtyp, vabstyp) vval) \<equiv> 
      \<exists>xs. v = VAbstract (VWA (TPrim (Num U8)) xs) \<and> length x = length xs \<and> (\<forall>i < length xs. xs ! i = VPrim (LU8 (x ! i)))"
end

overloading
  valRel_WordArrayU16 \<equiv> valRel
begin
  definition valRel_WordArrayU16: 
    "\<And>\<xi> x v. valRel_WordArrayU16 (\<xi> :: (funtyp,vabstyp) vabsfuns) (x :: (16 word) WordArray) (v :: (funtyp, vabstyp) vval) \<equiv> 
      \<exists>xs. v = VAbstract (VWA (TPrim (Num U16)) xs) \<and> length x = length xs \<and> (\<forall>i < length xs. xs ! i = VPrim (LU16 (x ! i)))"
end

overloading
  valRel_WordArrayU32 \<equiv> valRel
begin
  definition valRel_WordArrayU32: 
    "\<And>\<xi> x v. valRel_WordArrayU32 (\<xi> :: (funtyp,vabstyp) vabsfuns) (x :: (32 word) WordArray) (v :: (funtyp, vabstyp) vval) \<equiv> 
      \<exists>xs. v = VAbstract (VWA (TPrim (Num U32)) xs) \<and> length x = length xs \<and> (\<forall>i < length xs. xs ! i = VPrim (LU32 (x ! i)))"
end

overloading
  valRel_WordArrayU64 \<equiv> valRel
begin
  definition valRel_WordArrayU64: 
    "\<And>\<xi> x v. valRel_WordArrayU64 (\<xi> :: (funtyp,vabstyp) vabsfuns) (x :: (64 word) WordArray) (v :: (funtyp, vabstyp) vval) \<equiv> 
      \<exists>xs. v = VAbstract (VWA (TPrim (Num U64)) xs) \<and> length x = length xs \<and> (\<forall>i < length xs. xs ! i = VPrim (LU64 (x ! i)))"
end


*)

context WordArray begin

  
section "Shallow to Deep Corresondence Lemmas (@{term val.scorres}) for Word Array Functions"

lemmas valRel_WordArray_simps = valRel_WordArrayUX

subsection "wordarray_length"
text 
  "@{term wordarray_length} returns the length of a word array.
  
   Below is a proof tactic to prove @{term val.scorres} for wordarray_length. The proof is
   quite simple as @{term val.scorres} can be proven by simplifying the @{term valRel} definitions
   and by applying the @{term v_sem} introduction rules."
ML \<open>
fun wa_length_tac ctxt =
let  
  fun clarsimp_add thms i = Clasimp.clarsimp_tac (add_simps thms ctxt) i;
  fun clarsimp_split thm i = Clasimp.clarsimp_tac (Splitter.add_split thm ctxt) i 
  val base_simpset = @{thms val.scorres_def valRel_records wordarray_length' valRel_WordArray_simps};
in
  clarsimp_add base_simpset 1
  THEN clarsimp_split @{thm if_split_asm} 1
  THEN ALLGOALS (fn a =>
    etac @{thm v_sem_appE} a
    THEN etac @{thm v_sem_afunE} a
    THEN etac @{thm v_sem_varE} a
    THEN clarsimp_add @{thms val_wa_length_def} a
    THEN TRYALL (fn i => rtac @{thm FalseE} i
      THEN etac @{thm v_sem_afunE} i
      THEN clarsimp_add [] i))
end;

val goal = @{cterm "valRel \<xi>p (v:: (('a :: len8) word) WordArray) v' \<Longrightarrow> val.scorres (wordarray_length v) (App (AFun ''wordarray_length'' ts) (Var 0)) [v'] \<xi>p"};
val proof_state = Goal.init goal;
val n = proof_state |> wa_length_tac @{context} |>  Seq.hd
\<close>

lemma
  "\<xi>p' ''wordarray_length'' =  val_wa_length \<Longrightarrow> val.scorres((wordarray_length:: ('a :: len8) word WordArray \<Rightarrow> 32 word)) (AFun ''wordarray_length'' ts) \<gamma> \<xi>p'"
  apply (clarsimp simp: val.scorres_def)
  apply (erule v_sem_afunE)
  apply (clarsimp simp: val_wa_length_def  wordarray_length' valRel_WordArray_simps split: if_splits)
  done

lemma scorres_wordarray_length:
  "\<lbrakk>i < length \<gamma>; \<xi>p' ''wordarray_length'' =  val_wa_length;
    valRel \<xi>p' (v:: ('a :: len8) word WordArray) (\<gamma> ! i)\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_length v) (App (AFun ''wordarray_length'' ts) (Var i)) \<gamma> \<xi>p'"
  by (tactic \<open>wa_length_tac @{context}\<close>)

\<comment>\<open> Proofs for alternate definition of @{term valRel} for word arrays \<close>
(*lemma scorres_wordarray_length_u8:
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
*)

subsection "wordarray_get"
text 
  "@{term wordarray_get} is similar to the @{term nth} function for lists, except is does not cause
   and error when the index requested is out of bounds. Instead it returns the value @{term 0}. One
   issue with this behaviour is that it that we cannot define a generic @{term valRel} relation for
   word arrays as word arrays of other types may not have a sensible @{term 0} value.
   
   Below is a proof tactic to prove @{term val.scorres} for wordarray_get. The proof is
   slightly more tricky than @{term wordarray_length}, but it essentially can be proven using
   the simplifier to unfold the @{term valRel} definitions and by applying the @{term v_sem} 
   introduction rules where necessary."
ML \<open>
fun wa_get_tac ctxt =
let  
  fun clarsimp_add thms = Clasimp.clarsimp_tac (add_simps thms ctxt);
  fun clarsimp_split thm i = Clasimp.clarsimp_tac (Splitter.add_split thm ctxt) i 
  val base_simpset = @{thms val.scorres_def valRel_records wordarray_get' valRel_WordArray_simps};
in
  clarsimp_add base_simpset 1
  THEN clarsimp_split @{thm if_split_asm} 1
  THEN ALLGOALS (fn a =>
    rtac @{thm conjI} a
    THEN ALLGOALS (fn i => clarsimp_add [] i 
      THEN etac @{thm v_sem_appE} i
      THEN etac @{thm v_sem_afunE} i
      THEN etac @{thm v_sem_varE} i
      THEN clarsimp_add @{thms val_wa_get_def ucast_id} i)
    THEN TRYALL (fn i => rtac @{thm FalseE} i
      THEN etac @{thm v_sem_afunE} i
      THEN clarsimp_add [] i))
end;

val goal = @{cterm "valRel \<xi>p (v:: (32 word WordArray, 32 word) T0) v'
    \<Longrightarrow> val.scorres (wordarray_get v) (App (AFun ''wordarray_get'' ts) (Var 0)) [v'] \<xi>p"};
val proof_state = Goal.init goal;
val n = proof_state |> wa_get_tac @{context} |>  Seq.hd 
\<close>

\<comment>\<open> @{term valRel} does not exist for @{typ "('a :: len8) word"} so we can't make a generalised
   lemma like we did for @{term wordarray_length}. \<close>

lemma scorres_wordarray_get_u8:
  "\<lbrakk>i < length \<gamma>;  \<xi>p' ''wordarray_get'' =  val_wa_get;
    valRel \<xi>p' (v:: (8 word WordArray, 32 word) T0) (\<gamma> ! i)\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_get v) (App (AFun ''wordarray_get'' ts) (Var i)) \<gamma> \<xi>p'"
  by (tactic \<open>wa_get_tac @{context}\<close>)

lemma scorres_wordarray_get_u16:
  "\<lbrakk>i < length \<gamma>;  \<xi>p' ''wordarray_get'' =  val_wa_get;
    valRel \<xi>p' (v:: (16 word WordArray, 32 word) T0) (\<gamma> ! i)\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_get v) (App (AFun ''wordarray_get'' ts) (Var i)) \<gamma> \<xi>p'"
  by (tactic \<open>wa_get_tac @{context}\<close>)

lemma scorres_wordarray_get_u32:
  "\<lbrakk>i < length \<gamma>;  \<xi>p' ''wordarray_get'' =  val_wa_get;
    valRel \<xi>p' (v:: (32 word WordArray, 32 word) T0) (\<gamma> ! i)\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_get v) (App (AFun ''wordarray_get'' ts) (Var i)) \<gamma> \<xi>p'"
  by (tactic \<open>wa_get_tac @{context}\<close>)

lemma scorres_wordarray_get_u64:
  "\<lbrakk>i < length \<gamma>; \<xi>p' ''wordarray_get'' =  val_wa_get;
    valRel \<xi>p' (v:: (64 word WordArray, 32 word) T0) (\<gamma> ! i)\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_get v) (App (AFun ''wordarray_get'' ts) (Var i)) \<gamma> \<xi>p'"
  by (tactic \<open>wa_get_tac @{context}\<close>)

subsection "wordarray_put2"

text
  "@{term wordarray_put2} has the same behaviour as @{term list_update}."

lemma related_lists_update_nth_eq:
  "\<lbrakk>length ys = length xs; j < length xs; \<forall>i < length xs. xs ! i = f (ys ! i)\<rbrakk> 
    \<Longrightarrow> xs[i := f v] ! j = f (ys[i := v] ! j)"
  apply (erule_tac x = j in allE)
  apply (case_tac " i = j"; clarsimp)
  done     

text
  "Below is a proof tactic to prove @{term val.scorres} for wordarray_put2. The proof tactic was
   slightly more tricky than @{term wordarray_get} to create. However, the core part is the same as
   the proof @{thm scorres_wordarray_get_u8}, and the only major difference is the addition of the
   helper lemma @{thm related_lists_update_nth_eq}."

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
  fun clarsimp_split thm i = Clasimp.clarsimp_tac (Splitter.add_split thm ctxt) i
  val base_simpset = @{thms val.scorres_def valRel_records wordarray_put2' valRel_WordArray_simps};
  val helper_thm = @{thm related_lists_update_nth_eq}
in
  clarsimp_add base_simpset 1
  THEN clarsimp_split @{thm if_split_asm} 1
  THEN ALLGOALS (fn a =>
    etac @{thm v_sem_appE} a
    THEN etac @{thm v_sem_afunE} a
    THEN etac @{thm v_sem_varE} a
    THEN clarsimp_add @{thms val_wa_put2_def ucast_id} a
    THEN Subgoal.FOCUS_PARAMS (inst_param_tac ["i"] ["j"] helper_thm resolve_tac) ctxt a
    THEN ALLGOALS (fn i => asm_full_simp_tac ctxt i)
    THEN etac @{thm v_sem_afunE} a
    THEN rtac @{thm FalseE} a
    THEN clarsimp_add [] a)
end;
\<close>
ML \<open>
val goal = @{cterm "valRel \<xi>p (v:: (32 word WordArray, 32 word, 32 word) WordArrayPutP) v'
    \<Longrightarrow> val.scorres (wordarray_put2 v) (App (AFun ''wordarray_put2'' ts) (Var 0)) [v'] \<xi>p"};
val proof_state = Goal.init goal;
val n = proof_state |> wa_put2_tac @{context} |> Seq.hd 
\<close>

lemma scorres_wordarray_put2_u8:
  "\<lbrakk>k < length \<gamma>;  \<xi>p' ''wordarray_put2'' =  val_wa_put2;
    valRel \<xi>p' (v:: (8 word WordArray, 32 word, 8 word) WordArrayPutP) (\<gamma> ! k)\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_put2 v) (App (AFun ''wordarray_put2'' ts) (Var k)) \<gamma> \<xi>p'"
  by (tactic \<open> wa_put2_tac @{context}\<close>)

lemma scorres_wordarray_put2_u16:
  "\<lbrakk>k < length \<gamma>;  \<xi>p' ''wordarray_put2'' =  val_wa_put2;
    valRel \<xi>p' (v:: (16 word WordArray, 32 word, 16 word) WordArrayPutP) (\<gamma> ! k)\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_put2 v) (App (AFun ''wordarray_put2'' ts) (Var k)) \<gamma> \<xi>p'"
  by (tactic \<open> wa_put2_tac @{context}\<close>)

lemma scorres_wordarray_put2_u32:
  "\<lbrakk>k < length \<gamma>;  \<xi>p' ''wordarray_put2'' =  val_wa_put2;
    valRel \<xi>p' (v:: (32 word WordArray, 32 word, 32 word) WordArrayPutP) (\<gamma> ! k)\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_put2 v) (App (AFun ''wordarray_put2'' ts) (Var k)) \<gamma> \<xi>p'"
  by (tactic \<open> wa_put2_tac @{context}\<close>)

lemma scorres_wordarray_put2_u64:
  "\<lbrakk>k < length \<gamma>;  \<xi>p' ''wordarray_put2'' =  val_wa_put2;
    valRel \<xi>p' (v:: (64 word WordArray, 32 word, 64 word) WordArrayPutP) (\<gamma> ! k)\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_put2 v) (App (AFun ''wordarray_put2'' ts) (Var k)) \<gamma> \<xi>p'"
  by (tactic \<open> wa_put2_tac @{context}\<close>)

subsection "wordarray_fold_no_break"

text 
  "@{term wordarray_fold_no_break} is very similar to the list @{term fold} function. It differs
   from the traditional @{term fold} function as it can be applied to only a specified range of
   a list. It also takes an addition observer argument which remains unchanged throughout the
   @{term fold} operation and can be used throughout the @{term fold} operation. This can easily be
   emulated with the traditional @{term fold} function."

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
  "\<lbrakk>i < Suc l; Suc l \<le> length xs\<rbrakk> \<Longrightarrow>
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

abbreviation "upd_rec_field rec i v \<equiv> (case rec of VRecord fs \<Rightarrow> VRecord (fs[i := v]))"

text 
  \<open> We cannot generalise this unless you can prove that
    @{term "\<forall>a b. valRel \<xi>\<^sub>i (a :: 'a) b \<longleftrightarrow> valRel \<xi>\<^sub>j a b"} which is generally not true for
    functions.\<close>
lemma scorres_wordarray_fold_no_break_u32:
  "\<lbrakk>i < length \<gamma>; \<xi>p1' ''wordarray_fold_no_break'' = val_wa_foldnbp \<xi>p';
    valRel \<xi>p' \<lparr>WordArrayMapNoBreakP.arr\<^sub>f = (arr:: 32 word WordArray), frm\<^sub>f = (frm::32 word), to\<^sub>f = to,
      f\<^sub>f = f, acc\<^sub>f = (acc :: 'b), obsv\<^sub>f = obsv\<rparr> (\<gamma> ! i); 
    \<forall>x x'. valRel \<xi>p' (x :: 'b) x' \<longleftrightarrow> valRel \<xi>p1' x x'\<rbrakk>
    \<Longrightarrow> val.scorres 
    (wordarray_fold_no_break \<lparr>WordArrayMapNoBreakP.arr\<^sub>f = arr, frm\<^sub>f = frm, to\<^sub>f = to, f\<^sub>f = f, 
        acc\<^sub>f = acc, obsv\<^sub>f = obsv\<rparr>) (App (AFun ''wordarray_fold_no_break'' ts) (Var i)) \<gamma> \<xi>p1'"
  apply (clarsimp simp: val.scorres_def)
  apply (erule v_sem_appE; erule v_sem_afunE; clarsimp)
  apply (erule v_sem_varE; clarsimp)
  apply (clarsimp simp: val_wa_foldnbp_def)
  apply (clarsimp simp: wordarray_fold_no_break' valRel_records valRel_WordArray_simps)
  apply (induct to arbitrary: i \<gamma>)
   apply clarsimp
   apply (erule val_wa_foldnb_bod.elims; clarsimp split: if_split_asm)
  apply clarsimp
  apply (drule unatSuc; clarsimp)
  apply (rename_tac to r xs func acca obsva i \<gamma>)
  apply (case_tac "length xs < Suc (unat to)")
   apply (drule val_wa_foldnb_bod_back_step'; simp?)
   apply (drule_tac x = r in meta_spec)
   apply (drule_tac x = xs in meta_spec)
   apply (drule_tac x = func in meta_spec)
   apply (drule_tac x = acca in meta_spec)
   apply (drule_tac x = obsva in meta_spec)
   apply (drule_tac x = i in meta_spec)
   apply (drule_tac x = "\<gamma>[i := upd_rec_field (\<gamma> ! i) 2 (VPrim (LU32 to))]" in meta_spec)
   apply clarsimp
  apply (case_tac "unat frm \<ge> Suc (unat to)")
   apply clarsimp
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
  apply (drule val_wa_foldnb_bod_back_step; clarsimp)
  apply (rename_tac r')
  apply (drule_tac x = r' in meta_spec)
  (*apply (drule_tac x = t in meta_spec)*)
  apply (drule_tac x = xs in meta_spec)
  apply (drule_tac x = func in meta_spec)
  apply (drule_tac x = acca in meta_spec)
  apply (drule_tac x = obsva in meta_spec)
  apply clarsimp
  apply (drule_tac x = i in meta_spec)
  apply (drule_tac x = "\<gamma>[i := upd_rec_field (\<gamma> ! i) 2 (VPrim (LU32 to))]" in meta_spec)
  apply clarsimp
  apply (subst take_drop_Suc_app; simp?)
(*   apply (clarsimp split: if_split_asm)*)
  apply (clarsimp simp: ucast_id)
  apply (case_tac func; clarsimp)
   apply (erule_tac x = "\<lparr>ElemAO.elem\<^sub>f = arr ! unat to, 
    acc\<^sub>f = fold (\<lambda>a b. f \<lparr>ElemAO.elem\<^sub>f = a, acc\<^sub>f = b, obsv\<^sub>f = obsv\<rparr>)
      (take (unat to - unat frm) (List.drop (unat frm) arr)) acc, obsv\<^sub>f = obsv\<rparr>" in allE)
   apply (erule_tac x = "VRecord [xs ! unat to, r', obsva]" in allE)
   apply clarsimp
   apply (erule v_sem_appE; clarsimp)
   apply (erule v_sem_varE; clarsimp)
(*   apply (erule impE)
  apply (clarsimp split: if_split_asm; erule_tac x = "unat to" in allE; clarsimp)*)
  apply (erule_tac x = "\<lparr>ElemAO.elem\<^sub>f = arr ! unat to, 
    acc\<^sub>f = fold (\<lambda>a b. f \<lparr>ElemAO.elem\<^sub>f = a, acc\<^sub>f = b, obsv\<^sub>f = obsv\<rparr>)
      (take (unat to - unat frm) (List.drop (unat frm) arr)) acc, obsv\<^sub>f = obsv\<rparr>" in allE)
  apply (erule_tac x = "VRecord [xs ! unat to, r', obsva]" in allE)
  apply clarsimp
  apply (erule v_sem_appE; erule v_sem_afunE; clarsimp)
  apply (erule v_sem_varE; clarsimp)
  done

subsection "wordarray_map_no_break"

lemma min_word_0:
  "min x (0 :: ('a :: len8 word)) = 0"
  by simp

lemma max_word_0:
  "max x (0 :: ('a :: len8 word)) = x"
  apply (unfold max_def)
  by simp

lemma myslice_nth_last:
  "\<lbrakk>frm < Suc to; Suc to \<le> length xs; length xs' = to - frm\<rbrakk>
    \<Longrightarrow> ((List.take frm xs) @ xs' @ x # (List.drop (Suc to) xs)) ! to = x"
  apply (cut_tac xs = "(List.take frm xs)" and
      ys = " xs' @ x # (List.drop (Suc to) xs)" and 
      n = "to - frm" in nth_append_length_plus)
  apply simp
  apply (cut_tac xs = xs' and
      ys = "x # List.drop (Suc to) xs" and
      n = 0 in nth_append_length_plus)
  apply simp
  done

lemma scorres_wordarray_map_no_break_u32:
  "\<lbrakk>i < length \<gamma>; \<xi>p1' ''wordarray_map_no_break'' = val_wa_mapAccumnbp \<xi>p';
    valRel \<xi>p' \<lparr>WordArrayMapNoBreakP.arr\<^sub>f = (arr:: 32 word WordArray), frm\<^sub>f = (frm::32 word), to\<^sub>f = to,
      f\<^sub>f = f, acc\<^sub>f = (acc :: 'b), obsv\<^sub>f = obsv\<rparr> (\<gamma> ! i); \<forall>x x'. valRel \<xi>p' (x :: 'b) x' \<longleftrightarrow> valRel \<xi>p1' x x'\<rbrakk>
    \<Longrightarrow> val.scorres 
    (wordarray_map_no_break \<lparr>WordArrayMapNoBreakP.arr\<^sub>f = arr, frm\<^sub>f = frm, to\<^sub>f = to, f\<^sub>f = f, 
        acc\<^sub>f = acc, obsv\<^sub>f = obsv\<rparr>) (App (AFun ''wordarray_map_no_break'' ts) (Var i)) \<gamma> \<xi>p1'"
  apply (clarsimp simp: val.scorres_def)
  apply (erule v_sem_appE; erule v_sem_afunE; clarsimp)
  apply (erule v_sem_varE; clarsimp)
  apply (clarsimp simp: val_wa_mapAccumnbp_def)
  apply (clarsimp simp: wordarray_map_no_break' valRel_records valRel_WordArray_simps)
  apply (induct to arbitrary: i \<gamma>)
  apply clarsimp
   apply (erule val_wa_mapAccumnb_bod.elims; clarsimp split: if_split_asm simp: ucast_id)
  apply clarsimp
  apply (drule unatSuc; clarsimp)
  apply (rename_tac to r xs func acca obsva i \<gamma>)
  apply (case_tac "length xs < Suc (unat to)")
   apply (drule val_wa_mapAccumnb_bod_back_step'; simp?)
   apply (clarsimp simp: ucast_id)
   apply (drule_tac x = r in meta_spec)
   apply (drule_tac x = xs in meta_spec)
   apply (drule_tac x = func in meta_spec)
   apply (drule_tac x = acca in meta_spec)
   apply (drule_tac x = obsva in meta_spec)
   apply (drule_tac x = i in meta_spec)
   apply (drule_tac x = "\<gamma>[i := upd_rec_field (\<gamma> ! i) 2 (VPrim (LU32 to))]" in meta_spec)
   apply clarsimp
   apply (clarsimp split: if_split_asm prod.splits simp: word_less_nat_alt word_le_nat_alt)
  apply (case_tac "unat frm \<ge> Suc (unat to)")
   apply clarsimp
   apply (erule val_wa_mapAccumnb_bod.elims)
   apply (clarsimp split: if_split_asm simp: ucast_id word_less_nat_alt word_le_nat_alt)
  apply (frule val_wa_mapAccumnb_bod_preservation'; clarsimp)
  apply (rename_tac rxs racc)
  apply (drule val_wa_mapAccumnb_bod_back_step; clarsimp simp: ucast_id)
  apply (rename_tac racc')
  apply (drule_tac x = "VRecord [VAbstract (VWA (TPrim (Num U32))
    (rxs[unat to := VPrim (LU32 (arr ! unat to))])), racc']" in meta_spec)
  apply clarsimp
  apply (drule_tac x = xs in meta_spec)
  apply (drule_tac x = func in meta_spec)
  apply (drule_tac x = acca in meta_spec)
  apply (drule_tac x = obsva in meta_spec)
  apply clarsimp
  apply (drule_tac x = i in meta_spec)
  apply (drule_tac x = "\<gamma>[i := upd_rec_field (\<gamma> ! i) 2 (VPrim (LU32 to))]" in meta_spec)
  apply clarsimp
  apply (subst take_drop_Suc_app; simp?)+
  apply (clarsimp simp: mapAccum_step)
  apply (clarsimp split: prod.splits if_splits simp: word_less_nat_alt word_le_nat_alt)
  apply (rename_tac rxs' racc')
  apply (cut_tac acc = acc and 
      xs = "(take (unat to - unat frm) (List.drop (unat frm) arr))" and 
      f = "(\<lambda>a b. (T0.p1\<^sub>f (f \<lparr>ElemAO.elem\<^sub>f = a, acc\<^sub>f = b, obsv\<^sub>f = obsv\<rparr>),
                 T0.p2\<^sub>f (f \<lparr>ElemAO.elem\<^sub>f = a, acc\<^sub>f = b, obsv\<^sub>f = obsv\<rparr>)))" in mapAccum_length)
  apply (case_tac func; clarsimp)
   apply (rename_tac racc'a rxs' racc' fn ts)
   apply (erule_tac x = "\<lparr>ElemAO.elem\<^sub>f = arr ! unat to, acc\<^sub>f = racc', obsv\<^sub>f = obsv\<rparr>" in allE)
   apply (erule_tac x = "VRecord [VPrim (LU32 (arr ! unat to)), racc'a, obsva]" in allE)
   apply clarsimp
   apply (erule v_sem_appE; clarsimp)
   apply (erule v_sem_varE; clarsimp)
   apply (erule_tac x = " VRecord [rxs ! unat to, racc]" in allE; clarsimp)
   apply (rename_tac j)
   apply (erule_tac x = j in allE; clarsimp)
   apply (erule_tac x = j in allE; clarsimp)
   apply (case_tac "j = unat to"; clarsimp simp: myslice_nth_last nth_append)
  apply (rename_tac racc'a rxs' racc' fn ts)
  apply (erule_tac x = "\<lparr>ElemAO.elem\<^sub>f = arr ! unat to, acc\<^sub>f = racc', obsv\<^sub>f = obsv\<rparr>" in allE)
  apply (erule_tac x = "VRecord [VPrim (LU32 (arr ! unat to)), racc'a, obsva]" in allE)
  apply clarsimp
  apply (erule v_sem_appE; erule v_sem_afunE; clarsimp)
  apply (erule v_sem_varE; clarsimp)
  apply (rotate_tac -2)
  apply (erule_tac x = " VRecord [rxs ! unat to, racc]" in allE; clarsimp)
  apply (rename_tac j)
  apply (erule_tac x = j in allE; clarsimp)
  apply (erule_tac x = j in allE; clarsimp)
  apply (case_tac "j = unat to"; clarsimp simp: myslice_nth_last nth_append)
  done

end (* of context *)

end
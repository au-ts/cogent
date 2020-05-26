theory WordArrayT
  imports "AutoCorres.AutoCorres" "WordArraySpec"
begin

install_C_file "main_pp_inferred.c"
autocorres  [ts_rules = nondet] "main_pp_inferred.c"

context main_pp_inferred begin

type_synonym u32 = "32 word"

section \<open> Frame Constraints \<close>

definition frame_word32_ptr :: "lifted_globals \<Rightarrow> (word32 ptr) set \<Rightarrow> lifted_globals \<Rightarrow> (word32 ptr)  set \<Rightarrow> (word32 ptr) set \<Rightarrow> bool"
  where
  "frame_word32_ptr s p\<^sub>i s' p\<^sub>o ign \<equiv> \<forall>p :: word32 ptr. 
                          (p \<in> p\<^sub>i \<and> p \<notin> p\<^sub>o \<and> p \<notin> ign \<longrightarrow> \<not> is_valid_w32 s' p) \<comment> \<open>leak freedom\<close>
                       \<and>  (p \<notin> p\<^sub>i \<and> p \<in> p\<^sub>o \<and> p \<notin> ign\<longrightarrow> \<not> is_valid_w32 s  p) \<comment> \<open>fresh allocation\<close>
                       \<and>  (p \<notin> p\<^sub>i \<and> p \<notin> p\<^sub>o \<and> p \<notin> ign \<longrightarrow> 
                               (is_valid_w32 s p = is_valid_w32 s' p) \<and>  is_valid_w32 s p \<longrightarrow>
                               heap_w32 s  p = heap_w32 s' p)" \<comment> \<open>inertia\<close>

definition frame_WordArray_u32_C_ptr :: "lifted_globals \<Rightarrow> (WordArray_u32_C ptr) set \<Rightarrow> lifted_globals \<Rightarrow> (WordArray_u32_C ptr) set \<Rightarrow> (WordArray_u32_C ptr) set \<Rightarrow> bool"
  where
  "frame_WordArray_u32_C_ptr s p\<^sub>i s' p\<^sub>o ign \<equiv> \<forall>p :: WordArray_u32_C ptr. 
                       (p \<in> p\<^sub>i \<and> p \<notin> p\<^sub>o \<and> p \<notin> ign \<longrightarrow> \<not> is_valid_WordArray_u32_C s' p) \<comment> \<open>leak freedom\<close>
                       \<and>  (p \<notin> p\<^sub>i \<and> p \<in> p\<^sub>o \<and> p \<notin> ign \<longrightarrow> \<not> is_valid_WordArray_u32_C s  p) \<comment> \<open>fresh allocation\<close>
                       \<and>  (p \<notin> p\<^sub>i \<and> p \<notin> p\<^sub>o \<and> p \<notin> ign \<longrightarrow> 
                               (is_valid_WordArray_u32_C s p = is_valid_WordArray_u32_C s' p) \<and>
                               (is_valid_WordArray_u32_C s p \<longrightarrow>
                               heap_WordArray_u32_C s  p = heap_WordArray_u32_C s' p))" \<comment> \<open>inertia\<close>

lemmas frame_def = frame_WordArray_u32_C_ptr_def frame_word32_ptr_def

lemma frame_triv_w32_ptr: "frame_WordArray_u32_C_ptr state P state P ign"
  using frame_WordArray_u32_C_ptr_def by blast

lemma frame_triv_w32: "frame_word32_ptr state P state P ign"
  using frame_word32_ptr_def by blast

lemmas frame_triv = frame_triv_w32_ptr frame_triv_w32

lemma frame_weaken_w32:
  "\<lbrakk> A \<subseteq> A'; frame_word32_ptr s A s' A I\<rbrakk> \<Longrightarrow> frame_word32_ptr s A' s' A' I"
  apply (clarsimp simp add: frame_word32_ptr_def)
  by blast

lemma frame_combine_w32:
  "\<lbrakk>frame_word32_ptr s A s' A' I\<^sub>A; frame_word32_ptr s B s' B' I\<^sub>B; 
    I\<^sub>A \<inter> A = {}; I\<^sub>A \<inter> A' = {}; I\<^sub>B \<inter> B = {}; I\<^sub>B \<inter> B' = {}; I = (I\<^sub>A \<union> I\<^sub>B) - (A \<union> A' \<union> B \<union> B')\<rbrakk> 
    \<Longrightarrow> frame_word32_ptr s (A \<union> B) s' (A' \<union> B') I"
  apply (clarsimp simp add: frame_word32_ptr_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x = p in allE)+
   apply clarsimp
   apply (erule disjE; clarsimp; blast)
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x = p in allE)+
   apply clarsimp
   apply (erule disjE; clarsimp; blast)
  apply clarsimp
  done


lemma frame_weaken_w32_ptr:
  "\<lbrakk> A \<subseteq> A'; frame_WordArray_u32_C_ptr s A s' A I\<rbrakk> \<Longrightarrow> frame_WordArray_u32_C_ptr s A' s' A' I"
  apply (clarsimp simp add: frame_WordArray_u32_C_ptr_def)
  by blast

lemma frame_combine_w32_ptr:
  "\<lbrakk>frame_WordArray_u32_C_ptr s A s' A' I\<^sub>A; frame_WordArray_u32_C_ptr s B s' B' I\<^sub>B; 
    I\<^sub>A \<inter> A = {}; I\<^sub>A \<inter> A' = {}; I\<^sub>B \<inter> B = {}; I\<^sub>B \<inter> B' = {}; I = (I\<^sub>A \<union> I\<^sub>B) - (A \<union> A' \<union> B \<union> B')\<rbrakk> 
    \<Longrightarrow> frame_WordArray_u32_C_ptr s (A \<union> B) s' (A' \<union> B') I"
  apply (clarsimp simp add: frame_WordArray_u32_C_ptr_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x = p in allE)+
   apply clarsimp
   apply (erule disjE; clarsimp; blast)
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x = p in allE)+
   apply clarsimp
   apply (erule disjE; clarsimp; blast)
  apply clarsimp
  done

lemmas frame_weaken = frame_weaken_w32 frame_weaken_w32_ptr

lemmas frame_combine = frame_combine_w32 frame_combine_w32_ptr

section \<open> Helper things \<close>

subsection \<open> misc pointer lemmas \<close>

lemma cptr_add_add[simp]:
  "p +\<^sub>p m +\<^sub>p n = p +\<^sub>p (m + n)"
  by (cases p) (simp add: algebra_simps CTypesDefs.ptr_add_def)

subsection \<open> Helper Word Lemmas \<close>

lemma word_mult_cancel_right: 
  fixes a b c :: "('a::len) word"
  assumes "0 \<le> a" "0 \<le> b" "0 \<le> c"
  assumes "uint a * uint c \<le> uint (max_word :: ('a::len) word)"
  assumes "uint b * uint c \<le> uint (max_word :: ('a::len) word)"
  shows "a * c = b * c \<longleftrightarrow> c = 0 \<or> a = b"
  apply (rule iffI)
   using assms
   apply (unfold word_mult_def word_of_int_def)
    apply (clarsimp simp:Abs_word_inject max_word_def uint_word_of_int m1mod2k uint_0_iff)
   apply fastforce
   done

lemmas words_mult_cancel_right = 
  word_mult_cancel_right[where 'a=8]
  word_mult_cancel_right[where 'a=16]  
  word_mult_cancel_right[where 'a=32] 
  word_mult_cancel_right[where 'a=64]

lemma order_indices:     
  fixes ptr :: "('a::c_type) ptr"
  assumes "n * size_of (TYPE('a)) \<le> unat (max_word :: 32 word)"
  assumes "m * size_of (TYPE('a)) \<le> unat (max_word :: 32 word)"
  assumes "n < m"
  assumes "size_of (TYPE('a)) > 0"
  shows "ptr +\<^sub>p int n \<noteq> ptr +\<^sub>p int m"
  apply (simp add: ptr_add_def)
  apply (rule notI)
  using assms
  apply (subst (asm) word_mult_cancel_right; simp add: uint_nat)
    apply (subst le_unat_uoi[where z = "max_word:: 32 word"])
     apply (metis le_def multi_lessD nat_less_le neq0_conv)
    apply (subst le_unat_uoi[where z = "max_word:: 32 word"])
     apply (metis le_def multi_lessD nat_less_le neq0_conv)
    apply (metis assms(1) int_ops(7) of_nat_mono)
   apply (subst le_unat_uoi[where z = "max_word:: 32 word"])
    apply (metis le_def multi_lessD nat_less_le neq0_conv)
   apply (subst le_unat_uoi[where z = "max_word:: 32 word"])
    apply (metis le_def multi_lessD nat_less_le neq0_conv)
    apply (metis int_ops(7) of_nat_mono)
  apply (erule disjE)
  using le_unat_uoi apply fastforce
  by (metis (mono_tags, hide_lams) le_unat_uoi less_irrefl_nat mult_cancel2 of_nat_mult)

lemma distinct_indices:
  fixes ptr :: "('a::c_type) ptr"
  assumes "n * size_of (TYPE('a)) \<le> unat (max_word :: 32 word)"
  assumes "m * size_of (TYPE('a)) \<le> unat (max_word :: 32 word)"
  assumes "n \<noteq> m"
  assumes "size_of (TYPE('a)) > 0"
  shows "ptr +\<^sub>p int n \<noteq> ptr +\<^sub>p int m"
  using assms
  apply (case_tac "n < m")
   apply (erule order_indices; clarsimp)
  by (metis linorder_neqE_nat order_indices)
find_theorems "?a + ?b = ?a + ?c"
subsection \<open> arrlist \<close>

fun arrlist :: "('a :: c_type ptr \<Rightarrow> 'b) \<Rightarrow> ('a :: c_type ptr \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> 'a ptr \<Rightarrow> bool"
  where
  "arrlist h v [] p = True" |
  "arrlist h v (x # xs) p = (v p \<and> h p = x \<and> arrlist h v xs (p +\<^sub>p 1))"

lemma arrlist_nth_value:
  assumes "arrlist h v xs p" "i < length xs"
  shows "h (p +\<^sub>p i) = xs ! i"
  using assms
proof (induct i arbitrary: p xs)
  case 0
  then show ?case
    apply(cases xs)
    by(auto)
next
  case (Suc i)
  then have "i < length (tl xs)" by (cases xs) auto
  have "h (p +\<^sub>p 1 +\<^sub>p int i) = tl xs ! i"
    apply(rule Suc)
     apply(case_tac [!] xs)
    using Suc by auto
  then show ?case using Suc by (auto simp: nth_tl)
qed


lemma arrlist_nth_valid:
  assumes "arrlist h v xs p"  "i < length xs"
  shows "v (p +\<^sub>p i)"
  using assms
proof (induct i arbitrary: p xs)
  case 0 then show ?case by (cases xs) auto
next
  case (Suc i)
  then have "i < length (tl xs)" by (cases xs) auto
  have "v ((p +\<^sub>p 1) +\<^sub>p int i)"
    apply (rule Suc.hyps[where xs="tl xs"])
      apply (case_tac [!] xs)
    using Suc by auto
  then show ?case by simp
qed

lemmas arrlist_nth = arrlist_nth_value arrlist_nth_valid

lemma case_Suc: 
  "\<forall>i < Suc n.  P i \<Longrightarrow> (\<forall>i < n . P (Suc i)) \<and> P 0"
  by simp

lemma to_arrlist:
  assumes val_heap: "\<forall>k <  length xs. v (p +\<^sub>p int k) \<and> h (p +\<^sub>p int k) = xs ! k" 
  shows "arrlist h v xs p"
  using assms
  apply (induct xs arbitrary: p)
   apply simp
  apply simp
  apply (rule conjI)
   apply (erule_tac x = 0 in allE)
   apply clarsimp
  apply (rule conjI)
   apply (erule_tac x = 0 in allE)
   apply clarsimp
  apply (drule_tac x = "p +\<^sub>p 1" in meta_spec, simp)
  apply (case_tac xs, simp)
  apply (drule case_Suc, simp)
  done


lemma arrlist_all_nth:
  "arrlist h v xs p \<longleftrightarrow>
    (\<forall>k < length xs. v (p +\<^sub>p int k) \<and> h (p +\<^sub>p int k) = xs ! k)"
  apply (intro iffI conjI allI impI)
    apply (clarsimp simp: arrlist_nth_valid)
   apply (clarsimp simp: arrlist_nth_value)
  apply (erule to_arrlist)
  done

section \<open> Word array abstraction \<close>

definition u32list :: "lifted_globals \<Rightarrow> u32 list \<Rightarrow> u32 ptr \<Rightarrow> bool" 
  where
  "u32list s xs p \<equiv> arrlist (heap_w32 s) (is_valid_w32 s) xs p"

lemmas u32list_nth =
 arrlist_nth
  [where h="heap_w32 s" and v="is_valid_w32 (s :: lifted_globals)" for s,
   simplified u32list_def[symmetric]]

lemmas u32list_all_nth =
  arrlist_all_nth
    [where h="heap_w32 s" and v="is_valid_w32 (s :: lifted_globals)" for s,
      simplified u32list_def[symmetric]]
                                 

abbreviation "w_val h w \<equiv> values_C (h w)"
abbreviation "w_len h w \<equiv> SCAST(32 signed \<rightarrow> 32) (len_C (h w))"

abbreviation "w_p s w \<equiv> w_val (heap_WordArray_u32_C s) w"
abbreviation "w_l s w \<equiv> w_len (heap_WordArray_u32_C s) w"

(* Converts a wordarray to a list *)
definition \<alpha> :: "lifted_globals \<Rightarrow> u32 list \<Rightarrow> WordArray_u32_C ptr \<Rightarrow> bool"
  where
  "\<alpha> s xs w \<equiv>
    u32list s xs (w_p s w)
    \<and> (unat (w_l s w)) = length xs
    \<and> is_valid_WordArray_u32_C s w
    \<and> 4 * length xs \<le> unat (max_word:: 32 word)"

lemma abs_length_eq:
  "\<alpha> s xs w \<Longrightarrow> unat (w_l s w) = length xs"
  by (clarsimp simp add: \<alpha>_def)

lemma \<alpha>_nth:
  fixes i :: int
  assumes
    "\<alpha> s xs w"
    "0 \<le> i" "i < length xs"
    "i = int n"
  shows "heap_w32 s ((w_val (heap_WordArray_u32_C s) w) +\<^sub>p i) = xs ! n"
    and "is_valid_w32 s ((w_val (heap_WordArray_u32_C s) w) +\<^sub>p i)"
  using u32list_nth assms
  unfolding \<alpha>_def
  by auto

lemma \<alpha>_all_nth:
  "\<alpha> s xs w \<longleftrightarrow> (unat (w_l s w)) = length xs
    \<and> is_valid_WordArray_u32_C s w
    \<and> 4 * length xs \<le> unat (max_word:: 32 word)
    \<and> (\<forall>k<length xs. is_valid_w32 s ((w_p s w) +\<^sub>p int k) \<and> heap_w32 s ((w_p s w) +\<^sub>p int k) = xs ! k)"
  apply (rule iffI)
   apply (clarsimp simp: \<alpha>_def u32list_all_nth)
  apply (clarsimp simp: \<alpha>_def u32list_all_nth)
  done
(*
lemma "unat (SCAST(32 signed \<rightarrow> 32) x) = unat x"
  using [[show_types=true]]
  apply (simp add: scast_def)
  find_theorems "word_of_int" "sint"
  apply (insert word_sint.Rep_inverse)
  apply (drule_tac x = x in meta_spec)
  apply (erule subst)
  find_theorems "sint (word_of_int _)"
  apply (subst word_sint.Abs_inverse)
   apply clarsimp
   apply (subst sints_def)
   apply clarsimp
  
  oops
*)
section \<open> refinement and frame proofs \<close>

subsection \<open> wordarray_get \<close>

lemma wordarray_get_refinement:
  "\<lbrace>\<lambda>s. \<alpha> s xs w \<rbrace>
    wordarray_get_0' (t1_C w i)
   \<lbrace>\<lambda>r s. \<alpha> s xs w \<and> r = w_get xs (unat i) \<rbrace>!"
  apply (unfold wordarray_get_0'_def)
  apply clarsimp
  apply wp
  apply (clarsimp simp: w_get_def)
  apply (safe; clarsimp simp: uint_nat word_le_nat_alt \<alpha>_nth abs_length_eq)
  apply (simp_all add: \<alpha>_def)
  done

lemma wordarray_get_frame:
  "\<lbrace>\<lambda>s. state = s \<and> \<alpha> s xs w \<rbrace>
    wordarray_get_0' (t1_C w i)
   \<lbrace>\<lambda>r s. frame_WordArray_u32_C_ptr state {} s {} {} \<and> 
         frame_word32_ptr state {} s {} {}\<rbrace>!"
  apply(unfold wordarray_get_0'_def)
  apply(clarsimp)
  apply(wp)
  apply (safe; clarsimp simp: uint_nat word_le_nat_alt frame_triv \<alpha>_nth abs_length_eq)
  apply (simp add: \<alpha>_def)
  done
  
subsection \<open> wordarray_length \<close>

lemma wordarray_length_refinement:
  "\<lbrace>\<lambda>s. \<alpha> s xs w\<rbrace>
    wordarray_length_0' w
   \<lbrace>\<lambda>r s. \<alpha> s xs w \<and> (unat r) = w_length xs\<rbrace>!"
  apply(unfold wordarray_length_0'_def)
  apply(unfold w_length_def)
  apply(clarsimp)
  apply(wp)
  by (clarsimp simp: \<alpha>_def)


lemma wordarray_length_frame:
  "\<lbrace>\<lambda>s. state = s \<and> \<alpha> s xs w \<rbrace>
    wordarray_length_0' w
   \<lbrace>\<lambda>r s. frame_WordArray_u32_C_ptr state {} s {} {} \<and> 
         frame_word32_ptr state {} s {} {}\<rbrace>!"
  apply(unfold wordarray_length_0'_def)
  apply(clarsimp)
  apply(wp)
  apply (clarsimp simp: frame_triv \<alpha>_def)
  done

subsection \<open> wordarray_put2 \<close>

lemma wordarray_same_address: 
  "\<lbrakk>\<alpha> s xs w; n < length xs; m < length xs\<rbrakk> \<Longrightarrow>
    ((w_val (heap_WordArray_u32_C s) w) +\<^sub>p int n = (w_val (heap_WordArray_u32_C s) w) +\<^sub>p int m)
     = (n = m)"
  apply (simp add: \<alpha>_def)
  using distinct_indices apply force
  done

lemma wordarray_distinct_address: 
  "\<lbrakk>\<alpha> s xs w; n < length xs; m < length xs\<rbrakk> \<Longrightarrow> 
    (w_val (heap_WordArray_u32_C s) w) +\<^sub>p int n \<noteq> (w_val (heap_WordArray_u32_C s) w) +\<^sub>p int m
    \<longrightarrow> n \<noteq> m"
  apply (intro allI impI)
  apply clarsimp
  done

(*(heap_w32_update (\<lambda>a b. if b = values_C (heap_WordArray_u32_C state w) +\<^sub>p uint i then v else a b) state)*)
lemma wordarray_put2_frame:
  "\<lbrace>\<lambda>s. state = s \<and> \<alpha> s xs w \<rbrace>
    wordarray_put2_0' (t2_C w i v)
   \<lbrace>\<lambda>r s. frame_WordArray_u32_C_ptr state {} s {} {} \<and> 
         frame_word32_ptr state { (w_p s w) +\<^sub>p uint i} s {(w_p s w) +\<^sub>p uint i } {} \<rbrace>!"
  apply (unfold wordarray_put2_0'_def)
  apply clarsimp
  apply wp
  apply clarsimp
  apply (rule conjI; clarsimp simp: uint_nat word_less_def abs_length_eq \<alpha>_nth)
   apply (simp add: frame_WordArray_u32_C_ptr_def frame_word32_ptr_def \<alpha>_def)
  apply (simp add: frame_triv \<alpha>_def)
  done
  
lemma wordarray_put2_refinement:
  "\<lbrace>\<lambda>s. \<alpha> s xs w \<rbrace>
    wordarray_put2_0' (t2_C w i v)
   \<lbrace>\<lambda>r s. \<alpha> s (w_put xs (unat i) v) r\<rbrace>!"
  apply (unfold wordarray_put2_0'_def w_put_def)
  apply clarsimp
  apply wp
  apply (clarsimp simp: uint_nat)
  apply (rule conjI)
   apply (clarsimp simp: word_less_nat_alt abs_length_eq)
   apply (rule conjI)
    apply (simp (no_asm) add: \<alpha>_def u32list_all_nth)
    apply (rule conjI)
     apply clarsimp
     apply (rule conjI)
      apply (clarsimp simp: wordarray_same_address \<alpha>_nth)
     apply (clarsimp simp: wordarray_distinct_address \<alpha>_nth)
    apply (simp add: \<alpha>_def)
   apply (clarsimp simp: \<alpha>_nth \<alpha>_def)
  apply (clarsimp simp: not_less word_le_nat_alt \<alpha>_def)
  done

lemma wordarray_put_no_fail: 
  "\<alpha> s xs w \<Longrightarrow> \<not> snd (wordarray_put2_0' (t2_C w i v) s)"
  apply (monad_eq simp: wordarray_put2_0'_def)
  apply safe
   apply (simp add: \<alpha>_def)
  apply clarsimp
  apply (frule abs_length_eq)
  apply (subgoal_tac "unat i < length xs")
   apply (metis (full_types) \<alpha>_def int_unat u32list_all_nth w_length_def)
  by (simp add: word_less_nat_alt)

subsection \<open> wordarray_fold_no_break \<close>

fun fold_dispatch :: "int \<Rightarrow> t3_C \<Rightarrow> word32"
  where
  "fold_dispatch n args = (if n = sint FUN_ENUM_mul_bod 
                           then t3_C.elem_C args * t3_C.acc_C args 
                           else t3_C.elem_C args + t3_C.acc_C args)"

definition f_n
  where  
  "f_n \<equiv> (\<lambda>n a1 a2 a3. fold_dispatch (sint n) (t3_C a2 a1 a3))"

lemma unat_min: 
  "unat (min a b) = min (unat a) (unat b)"
  by (simp add: min_of_mono' word_le_nat_alt)

lemma fold_loop_inv:
  "\<lbrace>\<lambda>s. \<alpha> s xs w \<and> r = (xa, y) \<and> y < ret \<and> ret = min to (w_l s w) \<and> frm \<le> y \<and>
        xd = t3_C.elem_C_update (\<lambda>a. heap_w32 s ((w_p s w) +\<^sub>p uint y)) xa \<and> 
        w_fold xs (unat frm) (unat to) (f_n f_num) acc obsv = 
        w_fold xs (unat y) (unat to) (f_n f_num) (t3_C.acc_C xa) obsv\<rbrace> 
    dispatch_t4' (sint f_num) xd
   \<lbrace>\<lambda>xe a. \<alpha> a xs w \<and> ret = min to (w_l a w) \<and> frm \<le> y + 1 \<and>
           w_fold xs (unat frm) (unat to) (f_n f_num) acc obsv = 
           w_fold xs (unat (y + 1)) (unat to) (f_n f_num) xe obsv \<and>
           min (unat to) (length xs) - unat (y + 1) < 
           (case r of (fargs, i) \<Rightarrow> \<lambda>s. min (unat to) (length xs) - unat i) s\<rbrace>!"
  unfolding dispatch_t4'_def mul_bod'_def sum_bod'_def
  apply wp
  apply (clarsimp simp: word_less_nat_alt unatSuc2 less_is_non_zero_p1 word_le_nat_alt)
  apply (clarsimp simp: unat_min abs_length_eq)
  apply (simp add: diff_less_mono2)
  apply (case_tac "unat frm < length xs")
   apply (case_tac "unat frm < unat to")
    apply (simp add: \<alpha>_nth uint_nat)
    apply (simp (no_asm) add: f_n_def)
    apply (clarsimp simp: w_fold_step)
    apply simp_all
  by (simp add: add.commute mult.commute)

lemma wordarray_fold_refinement:
  "\<lbrace>\<lambda>s. \<alpha> s xs w \<rbrace>
   wordarray_fold_no_break_0' (t5_C w frm to f_num acc obsv)
   \<lbrace>\<lambda>r s. \<alpha> s xs w \<and> r = w_fold xs (unat frm) (unat to) (f_n f_num) acc obsv\<rbrace>!"
  unfolding wordarray_fold_no_break_0'_def
  apply wp
      apply(subst whileLoop_add_inv[where I = "\<lambda>(fargs, i) s. \<alpha> s xs w  \<and> ret = min to (w_l s w) \<and> 
                                   frm \<le> i \<and>
                                   w_fold xs (unat frm) (unat to) (f_n f_num) acc obsv =  
                                   w_fold xs (unat i) (unat to) (f_n f_num) (t3_C.acc_C fargs) obsv"
                                   and
                                   M = "\<lambda>((fargs, i), s). (min (unat to) (length xs)) -  unat i"])
      apply wp
           apply simp
           apply (rule fold_loop_inv)
          apply wp
         apply wp
        apply wp
       apply (clarsimp simp: word_less_nat_alt uint_nat \<alpha>_nth abs_length_eq unat_min)
       apply (rule conjI, simp)+
       apply (simp add: \<alpha>_def)
      apply (safe; clarsimp simp add: not_less word_le_nat_alt w_fold_def abs_length_eq)
     apply wp
    apply wp
   apply wp
  apply clarsimp 
  apply safe
    apply (simp add: min.commute min.strict_order_iff)
  using min.strict_order_iff apply fastforce
  apply (simp add: \<alpha>_def)
  done

lemma fold_loop_frame_inv:

  "\<lbrace>\<lambda>s. \<alpha> s xs w \<and> r = (xa, y) \<and> y < ret \<and> ret = min to (w_l s w) \<and> frm \<le> y \<and>
        xd = t3_C.elem_C_update (\<lambda>a. heap_w32 s ((w_p s w) +\<^sub>p uint y)) xa \<and> 
        frame_WordArray_u32_C_ptr state {} s {} A \<and> frame_word32_ptr state {} s {} B\<rbrace> 
    dispatch_t4' (sint f) xd 
   \<lbrace>\<lambda>xe a. \<alpha> a xs w \<and> ret = min to (w_l a w) \<and> frm \<le> y + 1 \<and>
           frame_WordArray_u32_C_ptr state {} a {} A \<and> frame_word32_ptr state {} a {} B \<and>
           min (unat to) (length xs) - unat (y + 1) < 
           (case r of (fargs, i) \<Rightarrow> \<lambda>s. min (unat to) (length xs) - unat i) s\<rbrace>!"
  unfolding dispatch_t4'_def sum_bod'_def mul_bod'_def
  apply wp
  apply (clarsimp simp: word_le_nat_alt unatSuc2 less_is_non_zero_p1 word_less_nat_alt)
  by (simp add: diff_less_mono2 abs_length_eq unat_min)

lemma wordarray_fold_frame:
  "\<lbrace>\<lambda>s. \<alpha> s xs w \<and> state = s \<and> w \<notin> A \<and> (\<forall>i < length xs. p +\<^sub>p i \<notin> B)\<rbrace>
    wordarray_fold_no_break_0' (t5_C w frm to f_num acc obsv)
   \<lbrace>\<lambda>r s. frame_WordArray_u32_C_ptr state {} s {} A \<and> 
         frame_word32_ptr state {} s {} B \<rbrace>!"
  unfolding wordarray_fold_no_break_0'_def
  apply wp
      apply(subst whileLoop_add_inv[where I ="\<lambda>(fargs, i) s. \<alpha> s xs w \<and> ret = min to (w_l s w) \<and>
                                          frm \<le> i \<and> frame_WordArray_u32_C_ptr state {} s {} A \<and> 
                                          frame_word32_ptr state {} s {} B" and
                                      M = "\<lambda>((fargs, i), s). (min (unat to) (length xs)) - unat i"])
      apply wp 
           apply simp
           apply (rule fold_loop_frame_inv)
          apply wp
         apply wp
        apply wp
       apply (clarsimp simp: word_less_nat_alt uint_nat \<alpha>_nth abs_length_eq unat_min)
       apply (rule conjI, simp)+
       apply (simp add: \<alpha>_def)
      apply clarsimp
     apply wp
    apply wp
   apply wp
  apply (clarsimp simp: frame_triv frame_def)
  apply safe
    apply (simp add: min.commute min.strict_order_iff)
   apply (metis min.idem min.strict_order_iff neqE)
  apply (simp add: \<alpha>_def)
  done


subsection \<open>wordarray_map\<close>

 
fun map_dispatch :: "int \<Rightarrow> t6_C \<Rightarrow> word32 \<times> unit_t_C" 
  where
  "map_dispatch n args = (if n = sint FUN_ENUM_inc then ((t6_C.elem_C args + 1), (t6_C.acc_C args)) 
                        else  ((t6_C.elem_C args + 1), (t6_C.acc_C args)))"
definition m_n 
  where 
  "m_n = (\<lambda>n a1 a2 a3. map_dispatch (sint n) (t6_C a1 a2 a3))"

lemma map_loop:
  "\<lbrace>\<lambda>s.  b = y \<and> y < ret \<and> ret = min to (w_l s w) \<and> (frm \<le> ret \<longrightarrow> y \<le> ret) \<and> 
    (ret < frm \<longrightarrow> frm = y) \<and> frm \<le> y \<and>
    \<alpha> s (fst (w_map xs (unat frm) (unat y) (m_n m_num) acc obsv)) w  \<and>
    xd = t6_C.elem_C_update (\<lambda>a. heap_w32 s ((w_p s w) +\<^sub>p uint y)) xa  \<and>
    (t6_C.acc_C xd) = snd (w_map xs (unat frm) (unat y) (m_n m_num) acc obsv) \<rbrace>
    dispatch_t8' (sint n_num) xd 
   \<lbrace>\<lambda>xe s.
    \<alpha> (heap_w32_update (\<lambda>a b. if b = values_C (heap_WordArray_u32_C s w) +\<^sub>p uint y then t7_C.p1_C xe else a b) s)
      (fst (w_map xs (unat frm) (unat (y + 1)) (m_n m_num) acc obsv)) w \<and>
    t7_C.p2_C xe = snd (w_map xs (unat frm) (unat (y + 1)) (m_n m_num) acc obsv) \<and>
    ret = min to (w_l s w) \<and>
    (frm \<le> ret \<longrightarrow> y + 1 \<le> ret) \<and> (ret < frm \<longrightarrow> frm = y + 1) \<and> frm \<le> y + 1 \<and>
    min (unat to) (length xs) - unat (y + 1) < min (unat to) (length xs) - unat b \<and>
    is_valid_w32 s (values_C (heap_WordArray_u32_C s w) +\<^sub>p uint y) \<and> is_valid_WordArray_u32_C s w\<rbrace>!"
  apply (unfold dispatch_t8'_def inc'_def)
  apply wp
  apply clarsimp
  apply (rule conjI)
   apply (subst unatSuc2)
  using less_is_non_zero_p1 apply fastforce
   apply (simp (no_asm) add: \<alpha>_def)
   apply (clarsimp simp add: u32list_all_nth)
   apply (rule conjI)
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (rule conjI)
      apply (simp add: \<alpha>_def)
      apply (metis u32list_all_nth w_map_length)
     apply (subgoal_tac "uint y = int k")
      apply (subst w_map_step)
  using word_le_nat_alt apply blast
      apply (subgoal_tac "k = unat y")
       apply simp
       apply (subst  nth_list_update_eq)
        apply (simp add: w_map_length)
       apply (simp add: m_n_def)
       apply (simp add: \<alpha>_nth(1) w_map_endpoint w_map_length)
      apply (metis int_unat nat_int.Rep_eqD)
     apply (clarsimp simp add: uint_nat word_less_nat_alt abs_length_eq w_map_length[symmetric])
     apply (metis wordarray_same_address w_map_length_same)
    apply clarsimp
    apply (rule conjI)
     apply (simp add: \<alpha>_def u32list_all_nth w_map_length)
    apply (subst w_map_step)
  using word_le_nat_alt apply blast
    apply (subgoal_tac "k \<noteq> unat y")
     apply (simp add: \<alpha>_nth(1) w_map_length)
    apply (metis int_unat)
   apply (rule conjI)
    apply (simp add: \<alpha>_def u32list_all_nth w_map_length)
   apply (simp add: \<alpha>_def u32list_all_nth w_map_length)
  apply (rule conjI)
   apply (subst unatSuc2)
  using less_is_non_zero_p1 apply fastforce
   apply (subst w_map_step)
  using word_le_nat_alt apply blast
    apply (metis Suc_le_eq abs_length_eq w_map_length unat_mono)
   apply (simp add: m_n_def)
  apply (rule conjI)
   apply clarsimp
  using inc_le apply blast
  apply (rule conjI)
   apply clarsimp
   apply (meson min_less_iff_conj not_less_iff_gr_or_eq)
  apply (rule conjI)
   apply (metis (mono_tags, hide_lams) add.commute less_is_non_zero_p1  min.strict_coboundedI2 min_def  word_le_less_eq word_overflow)
  apply (rule conjI)
   apply (subgoal_tac "length xs > unat y")
    apply (subgoal_tac "unat to > unat y")
     apply (meson diff_less_mono2 less_is_non_zero_p1 min_less_iff_conj word_less_nat_alt word_overflow)
  using unat_mono apply blast
   apply (simp add: abs_length_eq w_map_length word_less_nat_alt)
  apply (rule conjI)
   apply (subgoal_tac "unat y < length xs")
    apply (simp add: \<alpha>_nth(2) w_map_length uint_nat)
   apply (simp add: abs_length_eq w_map_length word_less_nat_alt)
  apply (simp add: \<alpha>_def)
  done

lemma wordarray_map_refinement:
  "\<lbrace>\<lambda>s. \<alpha> s xs w \<rbrace>
   wordarray_map_no_break_0' (t9_C w frm to w_num acc obsv)
   \<lbrace>\<lambda>r s. \<alpha> s (fst (w_map xs (unat frm) (unat to) (m_n m_num) acc obsv)) w \<and>
    (t10_C.p2_C r) = snd (w_map xs (unat frm) (unat to) (m_n m_num) acc obsv)\<rbrace>!"
  unfolding wordarray_map_no_break_0'_def
  apply wp
        apply(subst whileLoop_add_inv[where I ="\<lambda>(fargs, i) s. 
                              \<alpha> s (fst (w_map xs (unat frm) (unat i) (m_n m_num) acc obsv)) w \<and> 
                              (t6_C.acc_C fargs) = snd (w_map xs (unat frm) (unat i) (m_n m_num) acc obsv) \<and> 
                              ret = min to (w_l s w) \<and> (frm \<le> ret  \<longrightarrow> i \<le> ret) \<and> (frm > ret \<longrightarrow> frm = i) \<and> frm \<le> i"
                              and    
                              M = "\<lambda>((fargs, i), s). (min (unat to) (length xs)) -  unat i"])
       apply wp
            apply clarsimp
            apply (wp map_loop)
           apply wp
          apply wp
         apply wp
        apply clarsimp
        apply (rule conjI)
         apply simp         
        apply (metis (full_types) \<alpha>_def int_unat u32list_all_nth w_length_def word_less_nat_alt)
       apply clarsimp

       apply (case_tac "min to (w_l s w) < frm")
        apply (case_tac "b > to")
         apply (clarsimp simp add: w_map_def)
         apply (rule FalseE)
         apply (simp add: dual_order.strict_implies_order unat_mono)
        apply clarsimp
        apply (subgoal_tac "unat frm > length xs")
         apply (simp add: w_map_def)
        apply (metis (mono_tags, hide_lams) abs_length_eq w_map_length min_less_iff_disj unat_mono)
       apply clarsimp
       apply (subgoal_tac "frm \<le> to \<and> frm \<le> (w_l s w)")
        apply clarsimp
        apply (case_tac "b = to")
         apply simp
        apply (subgoal_tac "b < to")
         apply clarsimp
         apply (metis abs_length_eq w_map_bounds w_map_length word_le_nat_alt)
  using word_le_less_eq apply blast
       apply (simp add: min_less_iff_disj word_le_not_less)
      apply wp
     apply wp
    apply wp
   apply wp
  apply clarsimp
  apply (simp add: w_map_def)
  apply (rule conjI)
   apply (simp add: min.commute min.strict_order_iff)
   apply (simp add: \<alpha>_def)
  using min.strict_order_iff apply fastforce
  done

end (* of context *)
end

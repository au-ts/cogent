theory WordArray_C_Abstraction
  imports "Generated_ACInstall" 
begin

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

lemmas frame_C_def = frame_WordArray_u32_C_ptr_def frame_word32_ptr_def

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
end (* of context *)
end
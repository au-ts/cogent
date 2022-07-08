theory BinarySearch
  imports
    BinarySearchAsm
begin

sublocale WordArray \<subseteq> Generated_cogent_shallow _ upd.wa_abs_repr val.wa_abs_typing_v upd.wa_abs_typing_u wa_abs_upd_val
  by (unfold_locales)

context WordArray begin

thm corres_shallow_C_binarySearch_concrete

section "record simps"

fun t0_unmake
  where
"t0_unmake x = (T0.p1\<^sub>f x, T0.p2\<^sub>f x, T0.p3\<^sub>f x)" 

fun t0_make
  where
"t0_make (a, b, c) = T0.make a b c"

fun t1_make
  where
"t1_make (a, b) = T1.make a b"

fun t1_unmake
  where
"t1_unmake x = (T1.p1\<^sub>f x, T1.p2\<^sub>f x)"

lemma t0_make_simps:
  "T0.p1\<^sub>f (t0_make x) = (\<lambda>(a,b,c). a) x"
  "T0.p2\<^sub>f (t0_make x) = (\<lambda>(a,b,c). b) x"
  "T0.p3\<^sub>f (t0_make x) = (\<lambda>(a,b,c). c) x"
  apply (clarsimp split: prod.splits simp: valRel_records)+
  done

lemma t1_make_simps:
  "T1.p1\<^sub>f (t1_make x) = (\<lambda>(a,b). a) x"
  "T1.p2\<^sub>f (t1_make x) = (\<lambda>(a,b). b) x"
  apply (clarsimp split: prod.splits simp: valRel_records)+
  done

section "word simps"

lemma unat_ucast_of_nat:
  "x \<le> unat (max_word :: 32 word) \<Longrightarrow> unat (UCAST(32 \<rightarrow> 64) (of_nat (x))) = x"
  apply (clarsimp simp: max_word_def ucast_of_nat_small )
  apply (subst le_unat_uoi[where z = "4294967295"]; simp)
  done

lemma unatSuc_comm:
  "(1 :: ('a :: len8) word) + n \<noteq> 0 \<Longrightarrow> unat (n + 1) = Suc (unat n)"
  apply (drule unatSuc)
  apply (simp add: add.commute)
  done

section "midpoint lemmas"

lemma midpoint_alt:
  "a < b \<Longrightarrow> (a ::nat) + (b - a) div 2 = (a + b) div 2"
  apply (induct a)
   apply simp
  apply simp
  done

lemma midpoint_bounds_upper:
  "\<lbrakk>a < b; b \<le> d\<rbrakk> \<Longrightarrow> (a ::nat) + (b - a) div 2 < d"
  apply (induct a)
   apply simp
  apply simp
  done

section "search_stop simps"

definition search_stop0
  where
"search_stop0 = (\<lambda>ds\<^sub>0. \<not> T0.p2\<^sub>f (StepParam.acc\<^sub>f ds\<^sub>0) \<le> T0.p1\<^sub>f (StepParam.acc\<^sub>f ds\<^sub>0) \<longrightarrow> p3\<^sub>f (StepParam.acc\<^sub>f ds\<^sub>0))"

lemma search_stop0_simp:
  "Generated_Shallow_Desugar.searchStop = search_stop0"
  unfolding Generated_Shallow_Desugar.searchStop_def search_stop0_def
  apply (clarsimp simp: Let_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def valRel_records swa_get_def split: if_splits)
  done

definition search_stop1
  where
"search_stop1 = (\<lambda>a b. \<not> T0.p2\<^sub>f a \<le> T0.p1\<^sub>f a \<longrightarrow> p3\<^sub>f a)"

lemma search_stop1_simp:
  "(\<lambda>a b. search_stop0 \<lparr>StepParam.acc\<^sub>f = a, obsv\<^sub>f = b\<rparr>) = search_stop1"
  unfolding search_stop0_def search_stop1_def
  apply (clarsimp simp: Let_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def valRel_records swa_get_def split: if_splits)
  done

definition search_stop2
  where
"search_stop2 = (\<lambda>(a, b, c) (d, e). \<not> b \<le> a \<longrightarrow> c)"

lemma search_stop2_simp:
  "(\<lambda>a b. search_stop1 (t0_make a) (t1_make b)) = search_stop2"
  unfolding search_stop1_def search_stop2_def
  apply (clarsimp simp: fun_eq_iff valRel_records split: prod.splits)
  done

section "search_next simps"

lemma searchNext_simps:
  "(\<lambda>a (b, c). t0_unmake (Generated_Shallow_Desugar.searchNext \<lparr>StepParam.acc\<^sub>f = t0_make a, obsv\<^sub>f = \<lparr>T1.p1\<^sub>f = SWA b, p2\<^sub>f = c\<rparr>\<rparr>))
    = (\<lambda>(a0, a1, a2) (b, c). t0_unmake (Generated_Shallow_Desugar.searchNext \<lparr>StepParam.acc\<^sub>f = t0_make (a0, a1, a2), obsv\<^sub>f = \<lparr>T1.p1\<^sub>f = SWA b, p2\<^sub>f = c\<rparr>\<rparr>))"
  unfolding Generated_Shallow_Desugar.searchNext_def swa_get_def
  apply (clarsimp simp: Let_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def valRel_records checked_div_def  t1_make_simps t0_make_simps fun_eq_iff
                  split: if_splits)
  done

definition search_next0
  where
"search_next0 = (\<lambda>(a0, a1, a2) (b, c).
    (if (if unat (a0 + (a1 - a0) div 2) < length b then b ! unat (a0 + (a1 - a0) div 2) else 0) < c
      then (a0 + (a1 - a0) div 2 + 1, a1, a2)
     else if c < (if unat (a0 + (a1 - a0) div 2) < length b then b ! unat (a0 + (a1 - a0) div 2) else 0)
      then (a0, a0 + (a1 - a0) div 2, a2)
     else (a0 + (a1 - a0) div 2, a1, True)))"
lemma search_next_simp:
  "(\<lambda>(a0, a1, a2) (b, c). t0_unmake (Generated_Shallow_Desugar.searchNext \<lparr>StepParam.acc\<^sub>f = t0_make (a0, a1, a2), obsv\<^sub>f = \<lparr>T1.p1\<^sub>f = SWA b, p2\<^sub>f = c\<rparr>\<rparr>))
    = search_next0"
  unfolding Generated_Shallow_Desugar.searchNext_def swa_get_def search_next0_def
  apply (clarsimp simp: Let_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def valRel_records checked_div_def  t1_make_simps t0_make_simps fun_eq_iff
                  split: if_splits)
  done

definition search_next1
  where
"search_next1 = (\<lambda>(a0, a1, a2) (b, c).
    (if (if ((a0 + a1) div 2) < length b then b ! ((a0 + a1) div 2) else 0) < c
      then ((a0 + a1) div 2 + 1, a1, a2)
     else if c < (if ((a0 + a1) div 2) < length b then b ! ((a0 + a1) div 2) else 0)
      then (a0, (a0 + a1 ) div 2, a2)
     else ((a0 + a1) div 2, a1, True)))"

lemma search_next1_simp:
  "\<lbrakk>length xs \<le> unat (max_word :: 32 word); a0 < a1; unat a0 < length xs; unat a1 \<le> length xs\<rbrakk> \<Longrightarrow> 
    (\<lambda>(a0, a1, b). (unat a0, unat a1, b)) ((search_next0 ((a0) :: 32 word, a1, a2) (xs, (v :: ('a :: len8) word))))
      = search_next1 (unat a0, unat a1, a2) (xs, v)"
  apply (subgoal_tac "unat (a0 + (a1 - a0) div 2) = ((unat a0) + (unat a1)) div 2")
  unfolding search_next0_def search_next1_def
   apply (clarsimp split: prod.splits)
   apply (rule conjI; clarsimp)
    apply (subst unatSuc_comm)
     apply (subst add.commute)
     apply (rule_tac k = max_word in less_is_non_zero_p1)
     apply (subst word_less_nat_alt)
     apply simp
    apply simp
   apply (subst unatSuc_comm)
    apply (subst add.commute)
    apply (rule_tac k = max_word in less_is_non_zero_p1)
    apply (subst word_less_nat_alt)
    apply simp
   apply simp
  apply (subst unat_add_lem')
   apply (simp add: unat_div unat_sub)+
   apply (simp add: unat_div unat_sub midpoint_bounds_upper max_word_def)
  apply (simp add: unat_div unat_sub)
  apply (subst midpoint_alt; simp add: word_less_nat_alt)
  done
 
definition search_stop3
  where
"search_stop3 = (\<lambda>a (b, c). search_stop2 a (SWA b, c))"

definition search_stop4
  where
"search_stop4 = (\<lambda>(a0, a1, a2) (b, c). (\<not> (a1 :: nat) \<le> a0 \<longrightarrow> a2))"

lemma search_next1_simp2:
  "\<lbrakk>length xs \<le> unat (max_word :: 32 word); a0 < a1; unat a0 < length xs; unat a1 \<le> length xs;
    search_next0 ((a0) :: 32 word, a1, a2) (xs, (v :: ('a :: len8) word)) = (l, h, b)\<rbrakk>
      \<Longrightarrow> search_next1 (unat a0, unat a1, a2) (xs, v) = (unat l, unat h, b)"
 apply (subgoal_tac "unat (a0 + (a1 - a0) div 2) = ((unat a0) + (unat a1)) div 2")
  unfolding search_next0_def search_next1_def
   apply (clarsimp split: prod.splits)
   apply (rule conjI; clarsimp)+
    apply (subst unatSuc_comm)
     apply (subst add.commute)
     apply (rule_tac k = max_word in less_is_non_zero_p1)
     apply (subst word_less_nat_alt)
     apply simp
     apply simp
    apply (rule conjI; clarsimp)+
    apply (subst unatSuc_comm)
     apply (subst add.commute)
     apply (rule_tac k = max_word in less_is_non_zero_p1)
     apply (subst word_less_nat_alt)
     apply simp
    apply simp
   apply (rule conjI; clarsimp)+
   apply (subst unatSuc_comm)
    apply (subst add.commute)
    apply (rule_tac k = max_word in less_is_non_zero_p1)
    apply (subst word_less_nat_alt)
    apply simp
   apply simp
  apply (subst unat_add_lem')
   apply (simp add: unat_div unat_sub)+
   apply (simp add: unat_div unat_sub midpoint_bounds_upper max_word_def)
  apply (simp add: unat_div unat_sub)
  apply (subst midpoint_alt; simp add: word_less_nat_alt)
  done

section "repeat simps"

lemma repeatatm_simps:
  "repeatatm n f1 f2 \<lparr>T0.p1\<^sub>f = a, p2\<^sub>f = b, p3\<^sub>f = c\<rparr> \<lparr>T1.p1\<^sub>f = d, p2\<^sub>f = e\<rparr> 
    = t0_make (repeatatm n (\<lambda>a b. f1 (t0_make a) (t1_make b)) (\<lambda>a b. t0_unmake (f2 (t0_make a) (t1_make b))) (a,b,c) (d,e))"
  apply (induct n arbitrary: a b c)
   apply (simp add: repeatatm.simps valRel_records)
  apply (clarsimp simp: repeatatm.simps valRel_records)
  apply (erule_tac x = "T0.p1\<^sub>f (f2 \<lparr>T0.p1\<^sub>f = a, p2\<^sub>f = b, p3\<^sub>f = c\<rparr> \<lparr>T1.p1\<^sub>f = d, p2\<^sub>f = e\<rparr>)" in meta_allE)
  apply (erule_tac x = "T0.p2\<^sub>f (f2 \<lparr>T0.p1\<^sub>f = a, p2\<^sub>f = b, p3\<^sub>f = c\<rparr> \<lparr>T1.p1\<^sub>f = d, p2\<^sub>f = e\<rparr>)" in meta_allE)
  apply (erule_tac x = "T0.p3\<^sub>f (f2 \<lparr>T0.p1\<^sub>f = a, p2\<^sub>f = b, p3\<^sub>f = c\<rparr> \<lparr>T1.p1\<^sub>f = d, p2\<^sub>f = e\<rparr>)" in meta_allE)
  by (metis (mono_tags, lifting) T0.surjective old.unit.exhaust)


lemma repeatatm_simps2:
  "repeatatm n f g (a, b, c) (SWA xs, v) 
    = repeatatm n (\<lambda>a (b, c). f a (list_to_swa b, c)) (\<lambda>a (b, c). g a (list_to_swa b, c)) (a, b, c) (xs, v)"
  apply (induct n arbitrary: a b c)
   apply (simp add: repeatatm.simps)
  apply (clarsimp simp: repeatatm.simps)
  by (metis WordArray.t0_make.cases)


lemma repeatatm_nat_simp:
  "\<lbrakk>repeatatm n search_stop3 search_next0 ((i :: 32 word), j, b) (xs, (v :: ('a :: len8) word)) = (l, h, b');
    unat i < length xs; unat j \<le> length xs; length xs \<le> unat (max_word :: 32 word)\<rbrakk>
    \<Longrightarrow> repeatatm n search_stop4 search_next1 (unat i, unat j, b) (xs, v) = (unat l, unat h, b')"
  apply (induct n arbitrary: i j b)
   apply (simp add: repeatatm.simps)
  apply (simp add: repeatatm.simps)
  apply (rule conjI; clarsimp)
   apply (rotate_tac 1; subst (asm) search_stop3_def)
   apply (clarsimp simp: search_stop2_def search_stop4_def not_le word_less_nat_alt)
   apply (rotate_tac 1; subst (asm) search_stop3_def)
  apply (clarsimp simp: search_stop2_def not_le word_less_nat_alt)
  apply (subst (asm) search_stop4_def)
  apply simp
  apply (subgoal_tac "\<exists>x y z. search_next0 (i, j, False) (xs, v) = (x, y, z) \<and>  unat y \<le> length xs")
   apply (elim exE conjE)
   apply simp
   apply (drule search_next1_simp2[rotated -1]; simp?)
    apply (clarsimp simp: word_less_nat_alt not_le)
   apply (case_tac "unat x < length xs"; clarsimp?)
   apply (case_tac n; clarsimp simp: repeatatm.simps)
   apply (rule conjI; clarsimp)
    apply (subst (asm) search_stop3_def)
    apply (clarsimp simp: search_stop2_def search_stop4_def not_le word_less_nat_alt)
   apply (subst (asm) search_stop3_def)
   apply (clarsimp simp: search_stop2_def not_le word_less_nat_alt)
   apply (rotate_tac -1; subst (asm) search_stop4_def)
   apply simp
  apply (subst search_next0_def)
  apply clarsimp
  done

section "binary search nat lemmas"

lemma binary_search_range_shrink:
  "\<lbrakk>repeatatm n search_stop4 search_next1 (i, j, b) (xs, v) = (l, h, b'); 
    i < j; j \<le> length xs\<rbrakk>
    \<Longrightarrow> i \<le> l \<and> h \<le> j"
  apply (induct n arbitrary: i j b)
   apply (clarsimp simp: repeatatm.simps)
  apply (clarsimp simp: repeatatm.simps)
  apply (rotate_tac 1; subst (asm) search_stop4_def; clarsimp split: if_splits)
  apply (rotate_tac -1; subst (asm) search_next1_def; subst (asm) search_next1_def)
  apply (subst (asm) search_next1_def[symmetric])
  apply (clarsimp split: if_splits)
    apply (case_tac "Suc ((i + j) div 2) < j"; clarsimp)
     apply (elim meta_allE, erule meta_impE, assumption; simp?)
     apply clarsimp
     apply (rule_tac b = "Suc ((i + j) div 2)" in  order.trans; simp?)
    apply (case_tac n; clarsimp simp: repeatatm.simps search_stop4_def split: if_splits)
   apply (elim meta_allE, erule meta_impE, assumption; simp?)
   apply (case_tac "i < (i + j) div 2"; clarsimp)
    apply (rule_tac b = "(i + j) div 2" in  order.trans; simp?)
   apply (case_tac n; clarsimp simp: repeatatm.simps search_stop4_def split: if_splits)
    apply (case_tac n; clarsimp simp: repeatatm.simps search_stop4_def split: if_splits)
   apply arith
  apply arith
  done

lemma binary_search_correct_range:
  "\<lbrakk>repeatatm n search_stop4 search_next1 (i, j, False) (xs, v) = (l, h, b'); 
    i < j; j \<le> length xs; sorted xs\<rbrakk>
    \<Longrightarrow> (b' \<longrightarrow> xs ! l = v \<and> l < length xs) \<and> (\<not>b' \<longrightarrow>
        (l < h \<longrightarrow> (\<forall>k. (i \<le> k \<and> k < l \<longrightarrow> xs ! k < v) \<and> (h \<le> k \<and> k < j \<longrightarrow> xs ! k > v))) \<and> 
        (\<not> l < h \<longrightarrow> (\<forall>k. i \<le>k \<and> k < j \<longrightarrow> xs ! k \<noteq> v)))"
  apply (induct n arbitrary: i j)
   apply (clarsimp simp: repeatatm.simps)
   apply (rule conjI; clarsimp)
  apply (clarsimp simp: repeatatm.simps)
  apply (rotate_tac -4; subst (asm) search_stop4_def; clarsimp split: if_splits)
  apply (subst (asm) search_next1_def; subst (asm) search_next1_def)
  apply (subst (asm) search_next1_def[symmetric])
  apply (clarsimp split: if_splits)
    apply (case_tac "Suc ((i + j) div 2) < j")
     apply (elim meta_allE, erule meta_impE, assumption; simp?)
     apply clarsimp
     apply (rule conjI; clarsimp)
      apply (erule_tac x = k in allE; clarsimp)
      apply (drule binary_search_range_shrink; simp?)
      apply (clarsimp simp: not_le)
      apply (rule_tac y = "xs ! ((i + j) div 2)" in le_less_trans; simp?)
      apply (rule sorted_nth_mono; simp?)
      apply (erule_tac x = k in allE; clarsimp)
      apply (drule binary_search_range_shrink; simp?)
      apply (clarsimp simp: not_le not_less)
     apply (drule_tac i = k and j = "((i + j) div 2)" in sorted_nth_mono; simp?)
    apply (case_tac n; clarsimp simp: repeatatm.simps search_stop4_def split: if_splits)
     apply (clarsimp simp: not_le not_less)
     apply (drule_tac i = k and j = "((i + h) div 2)" in sorted_nth_mono; simp?)
    apply (drule_tac i = k and j = "((i + h) div 2)" in sorted_nth_mono; simp?)
   apply (elim meta_allE, erule meta_impE, assumption; simp?)
  apply (clarsimp simp: not_le not_less)
   apply (case_tac "i < (i + j) div 2"; clarsimp)
    apply (rule conjI; clarsimp)
     apply (drule binary_search_range_shrink; simp?)
     apply clarsimp
     apply (erule_tac x = k in allE; clarsimp)
     apply (drule_tac i = "((i + j) div 2)" and j = k in sorted_nth_mono; simp?)
    apply (drule binary_search_range_shrink; simp?)
    apply clarsimp
    apply (erule_tac x = k in allE; clarsimp)
    apply (drule_tac i = "((i + j) div 2)" and j = k in sorted_nth_mono; simp?)
   apply (case_tac n; clarsimp simp: repeatatm.simps search_stop4_def split: if_splits)
    apply (drule_tac i = "((l + j) div 2)" and j = k in sorted_nth_mono; simp?)
   apply (drule_tac i = "((l + j) div 2)" and j = k in sorted_nth_mono; simp?)
  apply (case_tac n; clarsimp simp: repeatatm.simps search_stop4_def split: if_splits)
  done

lemma binary_search_completes:
  "\<lbrakk>repeatatm n search_stop4 search_next1 (i, j, False) (xs, v) = (l, h, b'); 
    i < j; j \<le> length xs; n \<ge> j - i\<rbrakk>
    \<Longrightarrow> b' \<or> l \<ge> h"
  apply (induct n arbitrary: i j)
   apply (clarsimp simp: repeatatm.simps)
  apply (clarsimp simp: repeatatm.simps)
  apply (rotate_tac 1; subst (asm) search_stop4_def; clarsimp split: if_splits)
  apply (subst (asm) search_next1_def; subst (asm) search_next1_def)
  apply (subst (asm) search_next1_def[symmetric])
  apply (clarsimp split: if_splits)
   apply (case_tac "Suc ((i + j) div 2) < j")
     apply (elim meta_allE, erule meta_impE, assumption; simp?)
       apply (case_tac n; clarsimp simp: repeatatm.simps search_stop4_def split: if_splits)
      apply simp
     apply (case_tac "i < (i + j) div 2")
      apply (elim meta_allE, erule meta_impE, assumption; simp?)
     apply (case_tac n; clarsimp simp: repeatatm.simps search_stop4_def split: if_splits)
    apply (case_tac n; clarsimp simp: repeatatm.simps search_stop4_def split: if_splits)
   apply simp
  apply simp
  done

text "This provides a tighter bound for time complexity analysis"

lemma binary_search_completes_tight:
  "\<lbrakk>repeatatm n search_stop4 search_next1 (i, j, False) (xs, v) = (l, h, b'); 
    i < j; j \<le> length xs; 2 ^ n >  j - i\<rbrakk>
    \<Longrightarrow> b' \<or> l \<ge> h"
 apply (induct n arbitrary: i j)
   apply (clarsimp simp: repeatatm.simps)
 apply (clarsimp simp: repeatatm.simps)
  apply (rotate_tac 1; subst (asm) search_stop4_def; clarsimp split: if_splits)
  apply (subst (asm) search_next1_def; subst (asm) search_next1_def)
  apply (subst (asm) search_next1_def[symmetric])
  apply (clarsimp split: if_splits)
       apply (case_tac "Suc ((i + j) div 2) < j")
        apply (elim meta_allE, erule meta_impE, assumption; simp?)
       apply (case_tac n; clarsimp simp: repeatatm.simps search_stop4_def split: if_splits)
      apply simp
     apply (case_tac "i < (i + j) div 2")
      apply (elim meta_allE, erule meta_impE, assumption; simp?)
     apply (case_tac n; clarsimp simp: repeatatm.simps search_stop4_def split: if_splits)
    apply (case_tac n; clarsimp simp: repeatatm.simps search_stop4_def split: if_splits)
   apply simp
  apply simp
  done

section "binary search functional correctness theorem"

theorem binary_search_correct:
  "\<lbrakk>sorted xs; i = unat (Generated_Shallow_Desugar.binarySearch \<lparr>T1.p1\<^sub>f = SWA xs, p2\<^sub>f = v\<rparr>);
    length xs \<le> unat (max_word :: 32 word)\<rbrakk> \<Longrightarrow> 
   (i < length xs \<longrightarrow> xs ! i = v) \<and> 
   (\<not> i < length xs \<longrightarrow> v \<notin> set xs)"
  unfolding Generated_Shallow_Desugar.binarySearch_def swa_length_def repeat'_def swa_get_def     
  apply (clarsimp simp: Let_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def valRel_records unat_ucast_of_nat
                        search_stop0_simp search_stop1_simp repeatatm_simps 
                        search_stop2_simp t0_make_simps checked_div_def
                        t1_make_simps repeatatm_simps2 le_unat_uoi[where z = "max_word :: 32 word"]
                 split:  prod.splits;
         subst (asm) t0_unmake.simps[symmetric]; subst (asm) searchNext_simps; subst (asm) search_next_simp)
  apply (subst (asm) search_stop3_def[symmetric])
  apply (case_tac xs, clarsimp)
  apply (drule repeatatm_nat_simp, simp)
    apply (subst le_unat_uoi[where z = "max_word :: 32 word"]; simp)
   apply simp
  apply (frule binary_search_completes)
     apply (subst le_unat_uoi[where z = "max_word :: 32 word"]; simp)+
  apply (drule binary_search_correct_range)
     apply (subst le_unat_uoi[where z = "max_word :: 32 word"]; simp)+
   apply simp
  apply (thin_tac "xs = _ ")
  apply clarsimp
  apply (subst (asm) le_unat_uoi[where z = "max_word :: 32 word"], simp)
  apply (simp add: set_conv_nth)
  apply clarsimp
  apply (rename_tac k)
  apply (erule_tac x = k in allE; clarsimp)
  done

definition
  array :: "(lifted_globals \<times> WordArray_u32_C ptr) \<Rightarrow>
              (WordArray_u32_C \<times>
              abstyp \<times>
              vabstyp \<times>
              vabstyp \<times>
              32 word WordArray)"
where
  "array sp = 
    (let (s, p) = sp;
         w = heap s p;
         l = (SCAST(32 signed \<rightarrow> 32))(len_C w);
         arr = values_C w;
         xs = (map (\<lambda>i. heap_w32 s (arr +\<^sub>p int i)) [0..<(unat l)]);
         vxs = (map (\<lambda>i. VPrim (LU32 i)) xs);
         rp = RCon ''WordArray'' [RPrim (Num U32)]
    in (w,
        UWA (TPrim (Num U32)) l (ptr_val arr),
        VWA (TPrim (Num U32)) vxs,
        VWA (TPrim (Num U32)) vxs,
        SWA xs))"

abbreviation  "arr\<^sub>c \<equiv> prod.fst \<circ> array"
abbreviation  "arr\<^sub>u \<equiv> prod.fst \<circ> prod.snd \<circ> array"
abbreviation  "arr\<^sub>m \<equiv> prod.fst \<circ> prod.snd \<circ> prod.snd \<circ> array"
abbreviation  "arr\<^sub>p \<equiv> prod.fst \<circ> prod.snd \<circ> prod.snd \<circ> prod.snd \<circ> array"
abbreviation  "arr\<^sub>s \<equiv> prod.snd \<circ> prod.snd \<circ> prod.snd \<circ> prod.snd \<circ> array"
abbreviation  "arrlist \<equiv> swa_to_list \<circ> arr\<^sub>s"
abbreviation  "arrptrs s p \<equiv> map (\<lambda>i. ptr_val (values_C (arr\<^sub>c (s, p)) +\<^sub>p int i))[0..<unat((SCAST(32 signed \<rightarrow> 32))(len_C (arr\<^sub>c (s, p))))]"


definition
  inputs :: "(lifted_globals \<times> t8_C) \<Rightarrow>
                ((funtyp, atyp, ptrtyp) uval \<times>
                (funtyp, vabstyp) vval \<times>
                (funtyp, vabstyp) vval \<times>
                (32 word WordArray, 32 word) T1)"
where
  "inputs sx = 
    (let (s, x) = sx;
         p = t8_C.p1_C x;
         v = t8_C.p2_C x;
             rp = RCon ''WordArray'' [RPrim (Num U32)]
    in (URecord [(UPtr (ptr_val p) rp, RPtr rp), (UPrim (LU32 v), RPrim (Num U32))] None,
        VRecord [VAbstract (arr\<^sub>m (s, p)), VPrim (LU32 v)],
        VRecord [VAbstract (arr\<^sub>p (s, p)), VPrim (LU32 v)],
        \<lparr>T1.p1\<^sub>f = arr\<^sub>s (s, p), p2\<^sub>f = v\<rparr>))"

definition
  valid_array :: "lifted_globals \<Rightarrow>  WordArray_u32_C ptr \<Rightarrow> bool"
where
  "valid_array s p = 
    (let w = heap s p;
         l = (SCAST(32 signed \<rightarrow> 32))(len_C w);
         arr = values_C w
     in is_valid s p \<and> 
        size_of (TYPE(32 word)) * unat l \<le> unat (max_word :: 32 word) \<and>
        (\<forall>i < l. is_valid_w32 s (arr +\<^sub>p uint i)) \<and>
         (\<forall>i < l. ptr_val p \<noteq> ptr_val (arr +\<^sub>p uint i)))"

definition
  same_array :: "lifted_globals \<Rightarrow> lifted_globals \<Rightarrow> WordArray_u32_C ptr \<Rightarrow> bool"
where
  "same_array s s' p = 
    (let w = heap s p;
         l = (SCAST(32 signed \<rightarrow> 32))(len_C w);
         w' = heap s' p;
         arr = values_C w
     in valid_array s p \<and>
        valid_array s' p \<and>
        w = w' \<and>
        (\<forall>i < l. heap_w32 s (arr +\<^sub>p uint i) = heap_w32 s' (arr +\<^sub>p uint i)))"

lemma 
  "unat ((of_nat (size_of (TYPE(32 word)))) :: ptrtyp) = size_of (TYPE(32 word))"
  apply simp
  done

abbreviation  "uv\<^sub>m \<equiv> prod.fst \<circ> inputs"

abbreviation  "vv\<^sub>m \<equiv> prod.fst \<circ> prod.snd \<circ> inputs"

abbreviation  "vv\<^sub>p \<equiv> prod.fst \<circ> prod.snd \<circ> prod.snd \<circ> inputs"

abbreviation  "vv\<^sub>s \<equiv> prod.snd \<circ> prod.snd \<circ> prod.snd \<circ> inputs"

lemma inputs_uv_matches:
  "\<lbrakk>valid_array s p; \<sigma> (ptr_val p) = option.Some (UAbstract (arr\<^sub>u (s, p)));
    \<forall>p \<in> set (arrptrs s p). \<sigma> p = option.Some (UPrim (LU32 (heap_w32 s (PTR(32 word)p))))\<rbrakk> \<Longrightarrow>
   u_v_matches \<Xi> \<sigma> [uv\<^sub>m (s, t8_C p v)] [vv\<^sub>m (s, t8_C p v)]
      [Some (fst (snd (snd (snd Generated_TypeProof.binarySearch_type))))]
      (insert (ptr_val p) (set (arrptrs s p))) {}"
  apply (clarsimp simp: inputs_def
                        array_def
                        Let_def
                        Generated_TypeProof.binarySearch_type_def
                        Generated_TypeProof.abbreviated_type_defs)
  apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
               u_v_matches_empty[where \<tau>s = "[]", simplified]
               u_v_struct
               u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
               u_v_p_abs_ro[where a = "arr\<^sub>u (s, p)" and ts = "[TPrim (Num U32)]", simplified]
               u_v_prim'
               u_v_r_empty; (simp add: array_def Let_def u_v_matches.intros(1))?)
  apply (clarsimp simp: wa_abs_upd_val_def)
  apply (rule conjI)
   apply (clarsimp simp: upd.wa_abs_typing_u_def valid_array_def Let_def)
   apply (rule conjI)
    apply (rule equalityI; clarsimp simp: word_less_nat_alt array_def Let_def)
     apply (intro exI conjI; simp?)
     apply (subst le_unat_uoi[OF order.strict_implies_order]; simp?)
    apply (rule image_eqI; simp?)
   apply clarsimp
   apply (erule_tac x = "unat i" in ballE; simp?)
    apply (rule l0.upd.u_t_prim'; simp?)
   apply (clarsimp simp: word_less_nat_alt)
  apply (rule conjI)
   apply (clarsimp simp: val.wa_abs_typing_v_def valid_array_def Let_def)
   apply (rule l0.val.v_t_prim'; simp?)
  apply clarsimp
  apply (erule_tac x = "unat i" in ballE; simp?)
   apply (subst nth_map)
    apply (simp add: word_less_nat_alt)
   apply simp
   apply (rule l0.u_v_prim'; simp?)
   apply (simp add: word_less_nat_alt)
   apply (rename_tac i)
   apply (subgoal_tac "(PTR(32 word) (ptr_val (values_C (heap s p)) + 4 * i)) = (values_C (heap s p) +\<^sub>p int (unat i))")
    apply simp
   apply (cut_tac p = "values_C (heap s p)" and x = "of_nat x" in upd.ptr_val_add[where ?'a = "32 word"])
   apply (subst ptr_val_inj[symmetric])
   apply simp
  apply (simp add: word_less_nat_alt)
  done

lemma inputs_staterel_valrel:
  "\<lbrakk>valid_array s p\<rbrakk> \<Longrightarrow>
   \<exists>\<sigma>. (\<sigma>, s) \<in> upd.state_rel \<and>
      \<sigma> (ptr_val p) = option.Some (UAbstract (arr\<^sub>u (s, p))) \<and>
      (\<forall>p \<in> set (arrptrs s p). \<sigma> p = option.Some (UPrim (LU32 (heap_w32 s (PTR(32 word)p))))) \<and>
      val_rel_shallow_C rename (vv\<^sub>s (s, (t8_C p v))) (t8_C p v) (vv\<^sub>p (s, (t8_C p v))) (uv\<^sub>m (s, (t8_C p v))) \<xi>p1 \<sigma> \<Xi>"
  apply (clarsimp simp: val_rel_shallow_C_def
                        valRel_records inputs_def
                        Let_def
                        upd.val_rel_simp
                        valRel_WordArrayWord
                        ucast_id)
  apply (rule_tac x = "(\<lambda>l. if l = ptr_val p then option.Some (UAbstract (arr\<^sub>u (s, p))) 
                            else if l \<in> set (arrptrs s p)
                              then option.Some (UPrim (LU32 (heap_w32 s (PTR(32 word)l))))
                            else None)" in exI)
  apply (rule conjI)
   apply (clarsimp simp: upd.state_rel_def upd.heap_rel_def)
   apply (rule conjI;
          clarsimp simp: upd.heap_rel_ptr_meta
                         upd.heap_rel_meta_def
                         array_def
                         Let_def
                         upd.type_rel_simp
                         upd.wa_abs_repr_def
                         valid_array_def
                         upd.val_rel_simp)
   apply (rename_tac i)
   apply (erule_tac x = "of_nat i" in allE)
   apply (clarsimp simp: word_less_nat_alt)
   apply (cut_tac y = i and z = "(SCAST(32 signed \<rightarrow> 32) (len_C (heap s p)))" in le_unat_uoi; simp?)
   apply (subgoal_tac "x = values_C (heap s p) +\<^sub>p uint (of_nat i)")
    apply clarsimp
    apply assumption
   apply (cut_tac p = "values_C (heap s p)" and x = "of_nat i" in upd.ptr_val_add[where ?'a = "32 word"])
   apply (simp add: ptr_add_def )
   apply (subst ptr_val_inj[symmetric])
   apply simp
  apply (rule conjI; clarsimp simp: array_def Let_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_array_def Let_def)
   apply (rename_tac i)
   apply (erule_tac x = "of_nat i" in allE)+
   apply (cut_tac y = i and z = "(SCAST(32 signed \<rightarrow> 32) (len_C (heap s p)))" in le_unat_uoi; simp?)
   apply (clarsimp simp: word_less_nat_alt)
  apply (frule_tac v  = v and \<sigma> = "(\<lambda>l. if l = ptr_val p then option.Some (UAbstract (arr\<^sub>u (s, p))) 
                            else if l \<in> set (arrptrs s p)
                              then option.Some (UPrim (LU32 (heap_w32 s (PTR(32 word)l))))
                            else None)" in inputs_uv_matches; simp?)
   apply (clarsimp simp: valid_array_def Let_def)
   apply (rename_tac j)
   apply (erule_tac x = "of_nat j" in allE)+
   apply (clarsimp simp: word_less_nat_alt)
   apply (cut_tac y = j and z = "(SCAST(32 signed \<rightarrow> 32) (len_C (heap s p)))" in le_unat_uoi; simp?)
    apply (clarsimp simp: array_def Let_def u_v_matches.intros(1))+
  (*apply (rule_tac x = "fst (snd Generated_TypeProof.binarySearch_type)" in exI)*)
  apply (drule_tac i = 0 in  u_v_matches_proj_single'; simp?)
  apply clarsimp
  apply (clarsimp simp: inputs_def array_def Let_def)
  apply (intro exI conjI; assumption)
  done

lemma inputs_rename_monoval:
  "vv\<^sub>m sx = val.rename_val rename (val.monoval (vv\<^sub>p sx))"
  apply (clarsimp simp: rename_def inputs_def Let_def array_def split: prod.splits)
  done

lemma inputs_val_matches:
  "val.matches \<Xi> [vv\<^sub>m (s, t8_C p v)] 
      [Some (fst (snd (snd (snd Generated_TypeProof.binarySearch_type))))]"
  apply (clarsimp simp: val.matches_def
                        inputs_def
                        Let_def
                        array_def
                        Generated_TypeProof.binarySearch_type_def
                        Generated_TypeProof.abbreviated_type_defs)
  apply (intro val.v_t_record val.v_t_r_cons1 val.v_t_r_empty val.v_t_prim' val.v_t_abstract; simp?)
  apply (clarsimp simp: val.wa_abs_typing_v_def)
  apply (rule l0.val.v_t_prim'; simp?)
  done

lemma WordArray_u32_C_eq_simps:
  "x = y \<longleftrightarrow> len_C x = len_C y \<and> values_C x = values_C y"
  apply (rule iffI)
   apply clarsimp
  apply clarsimp
  by (metis WordArray_u32_C_idupdates(1))

corollary binary_search_C_correct:
  "\<lbrakk>sorted (arrlist (s, p));
    cc = upd.binarySearch' (t8_C p v);
    valid_array s p\<rbrakk> \<Longrightarrow>
   \<not> prod.snd (cc s) \<and> 
   (\<forall>r s'. (r, s') \<in> prod.fst (cc s) \<longrightarrow>
      same_array s s' p \<and>
      (unat r < length (arrlist (s, p)) \<longrightarrow> (arrlist (s, p)) ! unat r = v) \<and> 
      (\<not> unat r < length (arrlist (s, p)) \<longrightarrow> v \<notin> set (arrlist (s, p))))"
  apply (frule_tac v = v in inputs_staterel_valrel; clarsimp)
  apply (frule_tac s = s in 
      corres_shallow_C_binarySearch_concrete[rotated 1,
             OF _ inputs_val_matches[where s = s and p = p and v = v]];
      (simp add: inputs_rename_monoval[simplified])?)
  apply (clarsimp simp: corres_shallow_C_def proc_ctx_wellformed_\<Xi> \<xi>_1_\<xi>m1_matchesuv_\<Xi> upd.\<xi>_1_matchesu_\<Xi>)
  apply (erule impE)
   apply (subst inputs_rename_monoval[simplified, symmetric])
   apply (frule_tac \<sigma> = \<sigma> and v = v in inputs_uv_matches; simp?)
   apply (intro exI; assumption)
  apply clarsimp
  apply (erule_tac x = r in allE)
  apply (erule_tac x = s' in allE)
  apply clarsimp
  apply (rule conjI)
   apply (thin_tac "_ \<in> upd.state_rel")
   apply (frule_tac v = v in inputs_uv_matches; simp?)
   apply (drule u_v_matches_to_matches_ptrs)

   apply (drule (1) upd.preservation(1)[where  \<tau>s = "[]" and K = "[]", simplified, 
          OF subst_wellformed_nothing proc_ctx_wellformed_\<Xi>  _ 
             upd.\<xi>_1_matchesu_\<Xi> _ binarySearch_typecorrect', simplified, rotated 1])
   apply (clarsimp simp: Generated_TypeProof.binarySearch_type_def)
   apply (frule upd.tprim_no_pointers(1))
   apply (drule upd.tprim_no_pointers(2))
   apply clarsimp
   apply (drule upd.frame_empty)
   apply (clarsimp simp: valid_array_def same_array_def)
   apply (clarsimp simp: Let_def upd.state_rel_def upd.heap_rel_def upd.heap_rel_ptr_meta)
   apply (erule_tac x = p in allE)
   apply (clarsimp simp: upd.heap_rel_meta_def array_def Let_def type_rel_simps upd.wa_abs_repr_def val_rel_simps)
   apply (rule conjI)
    apply clarsimp
    apply (rename_tac i)
    apply (erule_tac x = "unat i" in ballE; simp?)
     apply (subgoal_tac "(PTR(32 word) (ptr_val (values_C (heap s p)) + 4 * i)) = (values_C (heap s p) +\<^sub>p uint i)")
      apply simp
      apply (erule_tac x = "values_C (heap s' p) +\<^sub>p uint i" in allE)
      apply (clarsimp simp: upd.heap_rel_meta_def array_def Let_def type_rel_simps upd.wa_abs_repr_def val_rel_simps)
     apply (simp add: ptr_add_def)
    apply (clarsimp simp: word_less_nat_alt)
   apply (rule conjI)
    apply (clarsimp simp:  WordArray_u32_C_eq_simps)
   apply clarsimp
   apply (rename_tac i)
    apply (erule_tac x = "unat i" in ballE; simp?)
     apply (subgoal_tac "(PTR(32 word) (ptr_val (values_C (heap s p)) + 4 * i)) = (values_C (heap s p) +\<^sub>p uint i)")
      apply simp
      apply (erule_tac x = "values_C (heap s' p) +\<^sub>p uint i" in allE)
      apply (clarsimp simp: upd.heap_rel_meta_def array_def Let_def type_rel_simps upd.wa_abs_repr_def val_rel_simps)
     apply (simp add: ptr_add_def)
    apply (clarsimp simp: word_less_nat_alt)
  apply (rotate_tac -1; subst (asm) val_rel_shallow_C_def)
  apply (clarsimp simp: val_rel_simps valRel_records)
  apply (erule u_v_uvprimE)
  apply (drule_tac i = "unat r" and v = v  in binary_search_correct; simp?)
   apply (clarsimp simp: inputs_def array_def Let_def unat_le_helper)+
  done
                                                                                               
end (* of context *)
end
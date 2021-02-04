(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory FunBucket
imports
  TypBucket
  L4vBucket
begin

definition count :: "'a list \<Rightarrow> ('b::len) word"
 where
"count xs \<equiv> of_nat (length xs) :: 'b word"

definition is_pow_of_2 :: "U32 \<Rightarrow> bool"
where
 "is_pow_of_2 x \<equiv> \<exists>k. x = 1 << k \<and> k < 32"

declare fun_app_def [iff]

text {* slice: Return a slice of a list, frm and to are offset from the 
beginning of the list *}
definition
  slice :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
 "slice frm to xs  \<equiv> List.drop frm $ take to xs"

lemma length_slice:
 "length (slice f t xs) = min (length xs) t - f"
 by (simp add: slice_def)

lemma slice_n_n:
 "slice n n xs = []"
 by (simp add: slice_def)

lemma slice_append: "slice f t (xs @ ys) = slice f t xs @ slice (f - min (length xs) t) (t - length xs) ys"
 by  (simp add: slice_def)

lemmas slice_simps = length_slice slice_n_n slice_append slice_def

lemma sub_mod_mask:
  "\<lbrakk>k < 32 \<rbrakk> \<Longrightarrow> (x::32 word) - x mod 2^k = x && ~~ mask k"
  apply (simp add: word_mod_2p_is_mask p2_gt_0 mask_out_sub_mask)
  done
  
lemma alignUp_not_aligned_eq2:
  " \<not> is_aligned a n \<Longrightarrow> Word_Lib.alignUp a n = ((a >> n) + 1) << n"
  apply (cases "n < size a")
   apply (subst alignUp_not_aligned_eq, assumption)
    apply (simp add: word_size)
   apply (simp add: shiftr_div_2n_w shiftl_t2n)
  apply (simp add: Word_Lib.alignUp_def power_overflow
        word_size complement_def shiftl_zero_size)
 done

lemma alignUp_not_aligned_eq3:
  "\<not> is_aligned a n \<Longrightarrow> Word_Lib.alignUp a n = (a && ~~ mask n) + (1 << n)"
  by (simp add: alignUp_not_aligned_eq2 word_shiftl_add_distrib and_not_mask) 
  
lemma alignUp_def2:
  "alignUp a sz = a + 2 ^ sz - 1 && ~~ mask sz"
  unfolding alignUp_def[unfolded complement_def]
  by (simp add: mask_def[symmetric,unfolded shiftl_t2n,simplified])

lemma align32_alignUp:
  "\<lbrakk>y = 1 << k; k < 32\<rbrakk> \<Longrightarrow> align32(x,y) = alignUp x k"
  apply (clarsimp simp: align32_def)
  apply (fold mask_def[simplified])
  apply (subst mask_def, simp)
  apply (subst add_diff_eq)
  apply (subst alignUp_def2[symmetric])
  by simp   
   
lemma align32_eq:
  "\<lbrakk>y=1<<k; k < 32\<rbrakk> \<Longrightarrow> align32(x,y) = (if y udvd x then x else x + y - (x mod y))"
  apply (simp add: align32_alignUp)
  apply safe
   apply (simp add: udvd_iff_dvd)
   apply (simp add: and_mask_dvd_nat)
   apply (simp only: is_aligned_mask[symmetric])
   apply (simp add: alignUp_idem)
  apply (subst diff_add_eq[symmetric])
  apply (subst sub_mod_mask, assumption)
  apply (subst alignUp_not_aligned_eq3)
   apply (clarsimp simp: is_aligned_def udvd_iff_dvd)
  apply clarsimp
  done

lemma align32_unchanged:
  "\<lbrakk>is_pow_of_2 a; a udvd x\<rbrakk> \<Longrightarrow> align32 (x,a) = x"
  by (clarsimp simp: is_pow_of_2_def align32_eq)

lemma alignUp_not_aligned_eq': "\<not> is_aligned x k
    \<Longrightarrow> alignUp x k = x + (2 ^ k - (x && mask k))"
  apply (subst alignUp_not_aligned_eq3, assumption)
  apply (subst mask_out_sub_mask)
  apply simp
  done

lemma al_dvd_align32:
  "\<lbrakk>is_pow_of_2 al; v < v + al\<rbrakk> \<Longrightarrow> al udvd align32 (v, al)"
  by (clarsimp simp: is_pow_of_2_def align32_alignUp 
                        udvd_iff_dvd is_aligned_def[symmetric])
  
lemma align32_le:
  "\<lbrakk>is_pow_of_2 al; v < v + al\<rbrakk> \<Longrightarrow> v \<le> align32 (v, al)"
  apply (case_tac "v=0", clarsimp simp: align32_alignUp)
  apply (clarsimp simp: align32_alignUp is_pow_of_2_def)
  apply (case_tac "is_aligned v k")
   apply (rule alignUp_ge, simp)
   apply (rule_tac x=v in alignUp_is_aligned_nz)
      apply simp
     apply simp
    apply simp
   apply simp
  apply (simp add: alignUp_not_aligned_eq')
  apply (drule word_less_sub_1)
  apply (rule word_plus_mono_right2)
   apply (subst(asm) field_simps[symmetric], assumption)
  apply (rule word_le_minus_mono_right)
    apply (clarsimp simp: lt1_neq0 is_aligned_mask)
   apply (rule order_trans, rule word_and_le1)
   apply (rule order_less_imp_le)
   apply (simp add: mask_lt_2pn)
  apply (simp add: word_1_le_power)
  done

lemma align32_ge:
  "\<lbrakk>is_pow_of_2 al; v < v + al\<rbrakk> \<Longrightarrow> align32 (v, al) \<ge> v"
   by (auto simp:align32_le)
 
lemma alignUp_greater:
  "\<lbrakk>(v::32 word) < 2^n; v \<noteq> 0\<rbrakk> \<Longrightarrow> alignUp v n = 2^n"
  apply (subst alignUp_not_aligned_eq')
   apply (clarsimp simp: aligned_small_is_0)
  apply (simp add: less_mask_eq)
  done
  
lemma mask_out_add_aligned:
  assumes al: "is_aligned p n"
  shows "p + (q && ~~ mask n) = (p + q) && ~~ mask n"
  using mask_add_aligned [OF al]
  by (simp add: mask_out_sub_mask)
  
lemma is_aligned_triv2:
  "is_aligned (2^a) a"
   apply (case_tac "word_bits\<le> a")
   apply (simp add:is_aligned_triv)+
   done
   
lemma alignUp_def3:
  "alignUp a sz = 2^ sz + (a - 1 && ~~ mask sz)" (is "?lhs = ?rhs")
   apply (simp add:alignUp_def2)
   apply (subgoal_tac "2 ^ sz + a - 1 && ~~ mask sz = ?rhs")
    apply (clarsimp simp:field_simps)
   apply (subst mask_out_add_aligned)
   apply (rule is_aligned_triv2)
   apply (simp add:field_simps)
   done

lemma mask_lower_twice:
  "n \<le> m \<Longrightarrow> (x && ~~ mask n) && ~~ mask m = x && ~~ mask m"
  apply (rule word_eqI)
  apply (simp add: word_size word_ops_nth_size)
  apply safe
  apply simp
  done
   
lemma alignUp_distance:
  "(alignUp (q :: 'a :: len word) sz) - q \<le> mask sz"
  apply (case_tac "len_of TYPE('a) \<le> sz")
   apply (simp add:alignUp_def2 mask_def power_overflow)
  apply (case_tac "is_aligned q sz")
  apply (clarsimp simp:alignUp_def2 p_assoc_help)
   apply (subst mask_out_add_aligned[symmetric],simp)+
   apply (simp add:mask_lower_twice word_and_le2)
   apply (simp add:and_not_mask)
   apply (subst le_mask_iff[THEN iffD1])
    apply (simp add:mask_def)
   apply simp
  apply (clarsimp simp:alignUp_def3)
  apply (subgoal_tac "2 ^ sz - (q - (q - 1 && ~~ mask sz)) \<le> 2 ^ sz - 1")
   apply (simp add:field_simps mask_def)
  apply (rule word_sub_mono)
   apply simp
   apply (rule ccontr)
   apply (clarsimp simp:not_le)
   apply (drule eq_refl)
   apply (drule order_trans[OF _ word_and_le2])
   apply (subgoal_tac "q \<noteq>  0")
    apply (drule minus_one_helper[rotated])
     apply simp
    apply simp
   apply (fastforce)
  apply (simp add: word_sub_le_iff)
  apply (subgoal_tac "q - 1 && ~~ mask sz = (q - 1) - (q - 1 && mask sz)")
   apply simp
   apply (rule order_trans)
    apply (rule word_add_le_mono2)
     apply (rule word_and_le1)
    apply (subst unat_plus_simple[THEN iffD1,symmetric])
     apply (simp add:not_le mask_def)
     apply (rule word_sub_1_le)
     apply simp
    apply (rule unat_lt2p)
   apply (simp add:mask_def)
  apply (simp add:mask_out_sub_mask)
  apply (rule word_sub_1_le)
  apply simp
  done   
   
lemma alignUp_nz:
  "\<lbrakk>(v :: 32 word) \<noteq> 0; v < v + 2^k; k < 32\<rbrakk> \<Longrightarrow> alignUp v k \<noteq> 0"
  apply (cut_tac v=v and al="2^k" in align32_le, simp add: is_pow_of_2_def)
    apply (rule_tac x=k in exI, simp+)
  apply (subst (asm) align32_alignUp[simplified], simp+)
  apply auto
  done
  
lemma aligned_neq_into_ineq:
  fixes x :: "'a::len word"
  assumes neq: "x \<noteq> y"
  and alx: "is_aligned x sz"
  and aly: "is_aligned y sz"
  shows "x + 2 ^ sz - 1 < y \<or> y + 2 ^ sz - 1 < x"
proof -
  note no_ov = aligned_neq_into_no_overlap [OF neq alx aly]
  note x = eqset_imp_iff[OF no_ov, where x=x]
  note y = eqset_imp_iff[OF no_ov, where x=y]
  from x y show ?thesis
   apply (simp add: is_aligned_no_overflow' alx aly)
   apply (auto simp: field_simps)
   done
qed  
  
lemma align32_upper_bound:
 "\<lbrakk>v \<le> bound; is_pow_of_2 al; al udvd bound; v < v + al\<rbrakk> \<Longrightarrow>
  align32 (v, al) \<le> bound"
  apply (case_tac "v=0")
   apply (clarsimp simp: align32_alignUp is_pow_of_2_def alignUp_def2 mask_def)
  apply (clarsimp simp: is_pow_of_2_def)
  apply (subst (asm) udvd_iff_dvd)
  apply simp
  apply (fold is_aligned_def)
  apply (subst align32_alignUp, simp+)
  apply (case_tac "is_aligned v k")
   apply (simp add: alignUp_idem)
  apply (case_tac "al > v")
   apply (subst alignUp_greater, simp+)
   apply (drule_tac a=bound in is_aligned_less_sz)
    apply clarsimp
   apply (simp add: le_def[symmetric])
  apply (simp add: le_def[symmetric])
  apply (cut_tac p=v and n=k in is_aligned_alignUp)
  apply (cut_tac q=v and sz=k in alignUp_distance)
  apply (drule word_diff_ls'(3))
   apply (drule word_less_sub_1)
   apply (simp add: mask_def word_less_sub_1)
   apply (subst diff_add_eq)
   apply (simp add: add.commute)
  apply (case_tac "v + 2^k \<le> bound")
   apply (simp add: mask_def)
   apply (cut_tac v=v and k=k in alignUp_nz, simp+)
   apply (metis (erased, hide_lams) add.commute add_diff_eq
                not_less order_trans word_le_less_eq word_less_1 word_sub_le)
  apply (subst (asm) word_not_le)
  apply (case_tac "bound = alignUp v k")
   apply simp
  apply (frule_tac x=bound and y="alignUp v k" and sz=k
                      in aligned_neq_into_ineq, assumption+)
  apply (simp add: mask_def)
  apply safe
   apply (simp add: L4vBucket.alignUp_le_greater_al)
  apply (simp add: L4vBucket.alignUp_le_greater_al)
  done

lemma align32_idempotence:
 "is_pow_of_2 y \<Longrightarrow> x < x + y \<Longrightarrow>
 align32 (align32 (x, y), y) = align32 (x, y)"
 apply (frule (1) al_dvd_align32)
 apply (erule (1) align32_unchanged)
done


end

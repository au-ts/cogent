(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory L4vBucket
imports
  "Word_Lib.Word_Lemmas"
  "CogentShallow.ShallowUtil"
begin



no_notation fun_app (infixr "$" 10)

(* Copied from HaskellLemmaBucket.thy *)
lemma is_aligned_alignUp[simp]:
  "is_aligned (alignUp p n) n"
  by (simp add: alignUp_def complement_def
                is_aligned_mask mask_def
                word_bw_assocs)

lemma alignUp_le[simp]:
  "alignUp p n \<le> p + 2 ^ n - 1"
  unfolding alignUp_def
  by (rule word_and_le2)

lemma complement_mask:
  "complement (2 ^ n - 1) = ~~ mask n"
  unfolding complement_def mask_def
  by simp
  
lemma alignUp_idem:
  fixes a :: "'a::len word"
  assumes al: "is_aligned a n"
  and   sz: "n < len_of TYPE('a)"
  shows "alignUp a n = a"
  using sz al unfolding alignUp_def 
  apply (simp add: complement_mask)
  apply (subst x_power_minus_1)
  apply (subst neg_mask_is_div)    
  apply (simp only: word_arith_nat_div  unat_word_ariths)
  apply (simp only: unat_power_lower)
  apply (subst power_mod_div)
  apply (erule is_alignedE)
  apply simp
  apply (subst unat_mult_power_lem)
   apply simp
  apply (subst unat_sub)
   apply (subst unat_arith_simps)
   apply (simp add: word_size)
  apply (simp add: word_size del: unat_1)
  apply simp
  done

lemma alignUp_not_aligned_eq:
  fixes a :: "'a :: len word"
  assumes al: "\<not> is_aligned a n"
    and   sz: "n < len_of TYPE('a)"
  shows "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n"
  using assms
  by (metis alignUp_not_aligned_eq)

lemma alignUp_ge:
  fixes a :: "'a :: len word"
  assumes sz: "n < len_of TYPE('a)"
  and nowrap: "alignUp a n \<noteq> 0"
  shows "a \<le> alignUp a n"
proof (cases "is_aligned a n")
  case True
  thus ?thesis using sz
    by (subst alignUp_idem, simp_all)
next
  case False

  have lt0: "unat a div 2 ^ n < 2 ^ (len_of TYPE('a) - n)" using sz
    apply -
    apply (subst td_gal_lt [symmetric])
     apply simp
    apply (simp add: power_add [symmetric])
    done

  have"2 ^ n * (unat a div 2 ^ n + 1) \<le> 2 ^ len_of TYPE('a)" using sz
    apply -
    apply (rule nat_le_power_trans)
    apply simp
    apply (rule Suc_leI [OF lt0])
    apply simp
    done
  moreover have "2 ^ n * (unat a div 2 ^ n + 1) \<noteq> 2 ^ len_of TYPE('a)" using nowrap sz
    apply -  
    apply (erule contrapos_nn)
    apply (subst alignUp_not_aligned_eq [OF False sz])
    apply (subst unat_arith_simps)
    apply (subst unat_word_ariths)
    apply (subst unat_word_ariths)
    apply simp
    apply (subst mult_mod_left)
    apply (simp add: unat_div field_simps power_add[symmetric] mod_mod_power
                     min.absorb2 unat_power_lower)
    done
  ultimately have lt: "2 ^ n * (unat a div 2 ^ n + 1) < 2 ^ len_of TYPE('a)" by simp
      
  have "a = a div 2 ^ n * 2 ^ n + a mod 2 ^ n" by (rule word_mod_div_equality [symmetric])
  also have "\<dots> < (a div 2 ^ n + 1) * 2 ^ n" using sz lt
    apply (simp add: field_simps)
    apply (rule word_add_less_mono1)
    apply (rule word_mod_less_divisor)
    apply (simp add: word_less_nat_alt unat_power_lower)
    apply (subst unat_word_ariths)
    apply (simp add: unat_div unat_power_lower)
    done
  also have "\<dots> =  alignUp a n"
    by (rule alignUp_not_aligned_eq [symmetric]) fact+  
  finally show ?thesis by (rule order_less_imp_le)
qed

lemma alignUp_le_greater_al:
  fixes x :: "'a :: len word"
  assumes le: "a \<le> x"
  and     sz: "n < len_of TYPE('a)"
  and     al: "is_aligned x n"
  shows   "alignUp a n \<le> x"
proof (cases "is_aligned a n")
  case True
  thus ?thesis using sz le by (simp add: alignUp_idem)
next
  case False

  hence anz: "a mod 2 ^ n \<noteq> 0" 
    by (rule not_aligned_mod_nz)
  
  from al obtain k where xk: "x = 2 ^ n * of_nat k" and kv: "k < 2 ^ (len_of TYPE('a) - n)"
    by (auto elim!: is_alignedE)
  
  hence kn: "unat (of_nat k :: 'a word) * unat ((2::'a word) ^ n) < 2 ^ len_of TYPE('a)" 
    using sz
    apply (subst unat_of_nat_eq)
     apply (erule order_less_le_trans)
     apply simp
    apply (subst mult.commute)
    apply (simp add: unat_power_lower)
    apply (rule nat_less_power_trans)
     apply simp
    apply simp
    done

  have au: "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n" 
    by (rule alignUp_not_aligned_eq) fact+
  also have "\<dots> \<le> of_nat k * 2 ^ n"
  proof (rule word_mult_le_mono1 [OF inc_le _ kn])
    show "a div 2 ^ n < of_nat k" using kv xk le sz anz
      by (simp add: alignUp_div_helper)
  
    show "(0:: 'a word) < 2 ^ n" using sz by (simp add: p2_gt_0 sz)
  qed
    
  finally show ?thesis using xk by (simp add: field_simps)
qed

lemma alignUp_is_aligned_nz:
  fixes a :: "'a :: len word"
  assumes al: "is_aligned x n"
  and     sz: "n < len_of TYPE('a)"
  and     ax: "a \<le> x"
  and     az: "a \<noteq> 0"
  shows   "alignUp (a::'a :: len word) n \<noteq> 0"
proof (cases "is_aligned a n")
  case True
  hence "alignUp a n = a" using sz by (simp add: alignUp_idem)
  thus ?thesis using az by simp
next
  case False
  hence anz: "a mod 2 ^ n \<noteq> 0" 
    by (rule not_aligned_mod_nz)

  {
    assume asm: "alignUp a n = 0"

    have lt0: "unat a div 2 ^ n < 2 ^ (len_of TYPE('a) - n)" using sz
      apply -
      apply (subst td_gal_lt [symmetric])
      apply simp
      apply (simp add: power_add [symmetric])
      done

    have leq: "2 ^ n * (unat a div 2 ^ n + 1) \<le> 2 ^ len_of TYPE('a)" using sz
      apply -
      apply (rule nat_le_power_trans)
      apply simp
      apply (rule Suc_leI [OF lt0])
      apply simp
      done    

    from al obtain k where  kv: "k < 2 ^ (len_of TYPE('a) - n)" and xk: "x = 2 ^ n * of_nat k"
      by (auto elim!: is_alignedE)

    hence "a div 2 ^ n < of_nat k" using ax sz anz
      by (rule alignUp_div_helper)

    hence r: "unat a div 2 ^ n < k" using sz
      apply (simp add: unat_div word_less_nat_alt)
      apply (subst (asm) unat_of_nat) 
      apply (subst (asm) mod_less)
      apply (rule order_less_le_trans [OF kv])
      apply (simp add: unat_power_lower)+
      done
    
    have "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n"
      by (rule alignUp_not_aligned_eq) fact+
    
    hence "\<dots> = 0" using asm by simp
    hence "unat a div 2 ^ n = 2 ^ (len_of TYPE('a) - n) - 1" using sz leq
      apply -
      apply (rule nat_diff_add)
      apply simp
      apply (subst nat_mult_eq_cancel1 [where k = "2 ^ n", symmetric])
      apply simp
      apply (subst power_add [symmetric])
      apply simp
      apply (drule unat_cong)
      apply simp
      apply (subst (asm) unat_word_ariths)
      apply (subst (asm) unat_word_ariths)
      apply (simp add: unat_div mult_mod_left power_add [symmetric] mod_mod_power
                       min.absorb2)
      apply (clarsimp simp: field_simps)
      apply (rule ccontr)
      apply (drule (1) order_le_neq_trans)
      apply (force simp add: unat_power_lower)
      done
    
    hence "2 ^ (len_of TYPE('a) - n) - 1 < k" using r
      by simp
    hence False using kv by simp
  } thus ?thesis by (clarsimp simp del: word_neq_0_conv)
qed

lemma alignUp_ar_helper:
  fixes a :: "'a :: len word"
  assumes al: "is_aligned x n"
  and     sz: "n < len_of TYPE('a)"
  and    sub: "{x..x + 2 ^ n - 1} \<subseteq> {a..b}"
  and    anz: "a \<noteq> 0"
  shows "a \<le> alignUp a n \<and> alignUp a n + 2 ^ n - 1 \<le> b"
proof 
  from al have xl: "x \<le> x + 2 ^ n - 1" by (simp add: is_aligned_no_overflow)
    
  from xl sub have ax: "a \<le> x"
    by (clarsimp elim!: range_subset_lower [where x = x])

  show "a \<le> alignUp a n"
  proof (rule alignUp_ge)
    show "alignUp a n \<noteq> 0" using al sz ax anz
      by (rule alignUp_is_aligned_nz)   
  qed fact+  
  
  show "alignUp a n + 2 ^ n - 1 \<le> b"
  proof (rule order_trans)
    from xl show tp: "x + 2 ^ n - 1 \<le> b" using sub
      by (clarsimp elim!: range_subset_upper [where x = x])
    
    from ax have "alignUp a n \<le> x"
      by (rule alignUp_le_greater_al) fact+
    hence "alignUp a n + (2 ^ n - 1) \<le> x + (2 ^ n - 1)" using xl
      apply -
      apply (erule word_plus_mono_left)
      apply (subst olen_add_eqv)
      apply (simp add: field_simps)
      done
    thus "alignUp a n + 2 ^ n - 1 \<le> x + 2 ^ n - 1"
      by (simp add: field_simps)
  qed
qed

end

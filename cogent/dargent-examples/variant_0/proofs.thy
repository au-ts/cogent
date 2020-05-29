theory proofs
  imports
    "AutoCorres.AutoCorres"
begin

install_C_file "variant_0.c"
autocorres  "variant_0.c"
context variant_0 begin

lemma ucast_and_dist: "ucast (p && q) = ucast p && ucast q"
  apply(rule word_eqI)
  apply(simp add: nth_ucast)
  using bang_conj_lt apply blast
  done

lemma ucast_or_dist: "ucast (p || q) = ucast p || ucast q"
  apply(rule word_eqI)
  apply(simp add: nth_ucast)
  using bang_conj_lt apply blast
  done

lemmas bitLemmas =
  Bit_Representation.bin_last_numeral_simps(2)
  Bit_Representation.bin_rest_numeral_simps(2)
  Bit_Representation.bintrunc_n_0
  Bit_Representation.bintrunc_numeral_simps(2)
  Bit_Representation.bintrunc_numeral_simps(5)
  Bit_Representation.bintrunc.Suc
  Bit_Representation.BIT_special_simps(1)
  Bit_Representation.BIT_special_simps(2)
  Bit_Representation.BIT_special_simps(4)
  Bits_Int.int_and_numerals(1)
  Groups.monoid_add_class.add.right_neutral
  Nat.mult_0_right
  Nat.mult_Suc_right
  Nat.One_nat_def
  Num.mult_num_simps(1)
  Num.mult_num_simps(2)
  Num.mult_num_simps(3)
  Num.pred_numeral_simps(2)
  Num.pred_numeral_simps(3)
  Word.word_bool_alg.conj_absorb
  Word.word_log_esimps(1)
  Word.word_log_esimps(9)
  Word.word_of_int_0

lemmas bitLemmas' = 
Bit_Representation.BIT_special_simps(1)
Bits_Int.int_and_numerals
Bits_Int.int_and_numerals
HOL.simp_thms(6)
Word.word_no_log_defs(3)
Word.word_of_int_0

lemmas bitLemmas'' = 
Bit_Representation.bin_last_numeral_simps(2)
Bit_Representation.bin_rest_numeral_simps(2)
Bit_Representation.bintrunc_n_0
Bit_Representation.bintrunc_numeral_simps(2)
Bit_Representation.bintrunc_numeral_simps(5)
Bit_Representation.bintrunc.Suc
Bit_Representation.BIT_bin_simps(2)
Bit_Representation.BIT_special_simps(1)
Bit_Representation.BIT_special_simps(2)
Bit_Representation.BIT_special_simps(4)
Bits_Int.int_and_numerals(1)
HOL.implies_True_equals
HOL.simp_thms(6)
Nat.One_nat_def
Num.mult_num_simps(1)
Num.mult_num_simps(2)
Num.mult_num_simps(3)
Num.pred_numeral_simps(2)
Num.pred_numeral_simps(3)
Pure.triv_forall_equality
Word.word_log_esimps(1)
Word.word_log_esimps(9)
Word.word_of_int_0
Word.word_of_int_numeral

lemma
  "\<lbrace>\<lambda>s. True \<rbrace>
      d28_set_a_A' b v
   \<lbrace>\<lambda>r s. d6_get_a_A' b s = Some (v && 0xFF) \<rbrace>"
  unfolding d6_get_a_A'_def d28_set_a_A'_def d7_get_a_A_part0'_def d29_set_a_A_part0'_def
  apply wp
  apply (simp only: oguard_def ogets_def oreturn_def obind_def)
  apply clarsimp
  apply unat_arith
  apply clarsimp
  apply(rule eq_ucast_ucast_eq)
  apply(simp only: len_bit0)
  apply(subst fun_upd_same)
  apply(simp)
  apply(simp only: BIT_special_simps word_no_log_defs int_and_numerals word_ao_absorbs word_bw_assocs word_bw_lcs word_ao_dist ucast_and_dist)
  apply(simp only: ucast_bintr len_bit0 bin_ops_same BIT_bin_simps len_num1 word_of_int_numeral)
  apply(simp only: One_nat_def)
  apply(simp only: bitLemmas bitLemmas' semiring_numeral_class.numeral_mult[symmetric] mult_num_simps)
   apply(simp only: word_of_int_numeral BIT_bin_simps numeral.simps(1) Num.arith_simps bitLemmas bitLemmas' semiring_numeral_class.numeral_mult[symmetric] mult_num_simps)
  done

lemma is_valid_heap_update: "is_valid_t1_C (heap_t1_C_update k r) = is_valid_t1_C r"
  by simp

lemmas testLemmas = 
is_valid_heap_update
Fun.comp_apply
Groups.ab_semigroup_add_class.add.commute
Groups.ab_semigroup_mult_class.mult.commute
Groups.monoid_add_class.add_0_right
Groups.monoid_add_class.add.right_neutral
HOL.True_implies_equals
Int.diff_nat_numeral
Int.nat_0
Int.nat_numeral
Lib.K_def
Nat.add_0_right
Nat.mult_0_right
Nat.mult_Suc_right
Nat.One_nat_def
Nat.plus_nat.add_0
Nat.plus_nat.add_Suc
(* Nat.Suc_eq_plus1 -- doesn't terminate *)
NonDetMonad.K_bind_def
Num.arith_simps(10)
Num.arith_simps(16)
Num.arith_simps(19)
Num.arith_simps(2)
Num.arith_simps(21)
Num.arith_simps(23)
Num.arith_simps(25)
Num.arith_simps(26)
Num.arith_simps(32)
Num.arith_simps(37)
Num.arith_simps(52)
Num.arith_simps(62)
Num.arith_simps(63)
Num.mult_num_simps(1)
Num.mult_num_simps(2)
Num.mult_num_simps(3)
Num.numeral_class.numeral_plus_numeral
Num.rel_simps(1)
Num.rel_simps(24)
Num.rel_simps(28)
Num.rel_simps(4)
Num.rel_simps(5)
Num.rel_simps(75)
Num.semiring_numeral_class.numeral_times_numeral
Option.option.inject
Power.semiring_numeral_class.power_numeral
Pure.triv_forall_equality
Type_Length.len_bit0
Type_Length.len_num1

lemma heap_heap_update: "heap_t1_C (heap_t1_C_update k r) = k (heap_t1_C r)"
  by simp

lemma
  "\<lbrace>\<lambda>s. True \<rbrace>
      d28_set_a_A' b v
   \<lbrace>\<lambda>r s. d6_get_a_A' b s = Some (v && 0xFF) \<rbrace>"
  unfolding d6_get_a_A'_def d28_set_a_A'_def d7_get_a_A_part0'_def d29_set_a_A_part0'_def
  apply wp
  apply (clarsimp simp: oguard_def ogets_def oreturn_def obind_def)
  apply unat_arith
  apply clarsimp
  apply (rule eq_ucast_ucast_eq)
   apply clarsimp
  apply (subst fun_upd_same)
  apply(simp)
  apply (simp only: BIT_special_simps word_no_log_defs int_and_numerals word_ao_absorbs word_bw_assocs word_bw_lcs word_ao_dist ucast_and_dist)
  apply(simp only: ucast_bintr len_bit0 bin_ops_same BIT_bin_simps len_num1 word_of_int_numeral)
  apply(simp only: One_nat_def)
  apply(simp only: bitLemmas bitLemmas' bitLemmas'')
  using[[simp_trace]]
  apply simp
  done

lemma
  "\<lbrace>\<lambda>s. True \<rbrace>
      d28_set_a_A' b v
   \<lbrace>\<lambda>r s. d6_get_a_A' b s = Some (v && 0xFF) \<rbrace>"
  unfolding d6_get_a_A'_def d28_set_a_A'_def d7_get_a_A_part0'_def d29_set_a_A_part0'_def
  apply wp
  apply (simp only: oguard_def ogets_def oreturn_def obind_def)
  apply(simp only: split: unat_splits option.splits if_splits)
  apply safe
     apply(simp)
  using[[simp_trace]]
    apply(simp only: testLemmas heap_heap_update)
  apply simp
    apply clarify
  apply(rule eq_ucast_ucast_eq)
   apply(simp only: len_bit0)
  apply(subst fun_upd_same)
  apply(simp only: proofs.t1_C_accupd_same)
  apply(subst Arrays.index_update)
   apply(simp only: card_bit1 card_bit0 card_num1)
  apply(simp only: BIT_special_simps word_no_log_defs int_and_numerals word_ao_absorbs word_bw_assocs word_bw_lcs word_ao_dist ucast_and_dist)
  apply(simp only: ucast_bintr len_bit0 bin_ops_same BIT_bin_simps len_num1 word_of_int_numeral)
  apply(simp only: One_nat_def)
  apply(simp only: bitLemmas bitLemmas' semiring_numeral_class.numeral_mult[symmetric] mult_num_simps)
    apply(simp only: word_of_int_numeral BIT_bin_simps numeral.simps(1) Num.arith_simps bitLemmas bitLemmas' semiring_numeral_class.numeral_mult[symmetric] mult_num_simps)
   apply simp
  apply simp
  done


end
  
end

theory proofs
  imports
    "AutoCorres.AutoCorres"
begin

install_C_file "variant_0.c"
autocorres  "variant_0.c"
context variant_0 begin

lemma ucast_and_dist: "ucast (p && q) = ucast p && ucast q"
  apply(rule word_eqI)
  apply(simp add: nth_ucast)
  using bang_conj_lt apply blast
  done

lemma ucast_or_dist: "ucast (p || q) = ucast p || ucast q"
  apply(rule word_eqI)
  apply(simp add: nth_ucast)
  using bang_conj_lt apply blast
  done

lemmas bitLemmas =
  bin_last_numeral_simps(2)
  bin_rest_numeral_simps(2)
  bintrunc_n_0
  bintrunc_numeral_simps(2)
  bintrunc_numeral_simps(5)
  bintrunc.Suc
  BIT_special_simps(1)
  BIT_special_simps(2)
  BIT_special_simps(4)
  Bits_Int.int_and_numerals(1)
  Groups.monoid_add_class.add.right_neutral
  Nat.mult_0_right
  Nat.mult_Suc_right
  Nat.One_nat_def
  Num.mult_num_simps(1)
  Num.mult_num_simps(2)
  Num.mult_num_simps(3)
  Num.pred_numeral_simps(2)
  Num.pred_numeral_simps(3)
  Word.word_bool_alg.conj_absorb
  Word.word_log_esimps(1)
  Word.word_log_esimps(9)
  Word.word_of_int_0

lemmas bitLemmas' = 
BIT_special_simps(1)
Bits_Int.int_and_numerals
Bits_Int.int_and_numerals
HOL.simp_thms(6)
Word.word_no_log_defs(3)
Word.word_of_int_0

lemmas bitLemmas'' = 
bin_last_numeral_simps(2)
bin_rest_numeral_simps(2)
bintrunc_n_0
bintrunc_numeral_simps(2)
bintrunc_numeral_simps(5)
bintrunc.Suc
BIT_bin_simps(2)
BIT_special_simps(1)
BIT_special_simps(2)
BIT_special_simps(4)
Bits_Int.int_and_numerals(1)
HOL.implies_True_equals
HOL.simp_thms(6)
Nat.One_nat_def
Num.mult_num_simps(1)
Num.mult_num_simps(2)
Num.mult_num_simps(3)
Num.pred_numeral_simps(2)
Num.pred_numeral_simps(3)
Pure.triv_forall_equality
Word.word_log_esimps(1)
Word.word_log_esimps(9)
Word.word_of_int_0
Word.word_of_int_numeral

lemma
  "\<lbrace>\<lambda>s. True \<rbrace>
      d28_set_a_A' b v
   \<lbrace>\<lambda>r s. d6_get_a_A' b s = Some (v && 0xFF) \<rbrace>"
  unfolding d6_get_a_A'_def d28_set_a_A'_def d7_get_a_A_part0'_def d29_set_a_A_part0'_def
  apply wp
  apply (simp only: oguard_def ogets_def oreturn_def obind_def)
  apply clarsimp
  apply unat_arith
  apply clarsimp
  apply(rule eq_ucast_ucast_eq)
  apply(simp only: len_bit0)
  apply(subst fun_upd_same)
  apply(simp)
  apply(simp only: BIT_special_simps word_no_log_defs int_and_numerals word_ao_absorbs word_bw_assocs word_bw_lcs word_ao_dist ucast_and_dist)
  apply(simp only: ucast_bintr len_bit0 bin_ops_same BIT_bin_simps len_num1 word_of_int_numeral)
  apply(simp only: One_nat_def)
  apply(simp only: bitLemmas bitLemmas' semiring_numeral_class.numeral_mult[symmetric] mult_num_simps)
   apply(simp only: word_of_int_numeral BIT_bin_simps numeral.simps(1) Num.arith_simps bitLemmas bitLemmas' semiring_numeral_class.numeral_mult[symmetric] mult_num_simps)
  done

lemma is_valid_heap_update: "is_valid_t1_C (heap_t1_C_update k r) = is_valid_t1_C r"
  by simp

lemmas testLemmas = 
is_valid_heap_update
Fun.comp_apply
Groups.ab_semigroup_add_class.add.commute
Groups.ab_semigroup_mult_class.mult.commute
Groups.monoid_add_class.add_0_right
Groups.monoid_add_class.add.right_neutral
HOL.True_implies_equals
Int.diff_nat_numeral
Int.nat_0
Int.nat_numeral
Lib.K_def
Nat.add_0_right
Nat.mult_0_right
Nat.mult_Suc_right
Nat.One_nat_def
Nat.plus_nat.add_0
Nat.plus_nat.add_Suc
(* Nat.Suc_eq_plus1 -- doesn't terminate *)
NonDetMonad.K_bind_def
Num.arith_simps(10)
Num.arith_simps(16)
Num.arith_simps(19)
Num.arith_simps(2)
Num.arith_simps(21)
Num.arith_simps(23)
Num.arith_simps(25)
Num.arith_simps(26)
Num.arith_simps(32)
Num.arith_simps(37)
Num.arith_simps(52)
Num.arith_simps(62)
Num.arith_simps(63)
Num.mult_num_simps(1)
Num.mult_num_simps(2)
Num.mult_num_simps(3)
Num.numeral_class.numeral_plus_numeral
Num.rel_simps(1)
Num.rel_simps(24)
Num.rel_simps(28)
Num.rel_simps(4)
Num.rel_simps(5)
Num.rel_simps(75)
Num.semiring_numeral_class.numeral_times_numeral
Option.option.inject
Power.semiring_numeral_class.power_numeral
Pure.triv_forall_equality
Type_Length.len_bit0
Type_Length.len_num1

lemma heap_heap_update: "heap_t1_C (heap_t1_C_update k r) = k (heap_t1_C r)"
  by simp

lemma
  "\<lbrace>\<lambda>s. True \<rbrace>
      d28_set_a_A' b v
   \<lbrace>\<lambda>r s. d6_get_a_A' b s = Some (v && 0xFF) \<rbrace>"
  unfolding d6_get_a_A'_def d28_set_a_A'_def d7_get_a_A_part0'_def d29_set_a_A_part0'_def
  apply wp
  apply (clarsimp simp: oguard_def ogets_def oreturn_def obind_def)
  apply unat_arith
  apply clarsimp
  apply (rule eq_ucast_ucast_eq)
   apply clarsimp
  apply (subst fun_upd_same)
  apply(simp)
  apply (simp only: BIT_special_simps word_no_log_defs int_and_numerals word_ao_absorbs word_bw_assocs word_bw_lcs word_ao_dist ucast_and_dist)
  apply(simp only: ucast_bintr len_bit0 bin_ops_same BIT_bin_simps len_num1 word_of_int_numeral)
  apply(simp only: One_nat_def)
  apply(simp only: bitLemmas bitLemmas' bitLemmas'')
  using[[simp_trace]]
  apply simp
  done

lemma
  "\<lbrace>\<lambda>s. True \<rbrace>
      d28_set_a_A' b v
   \<lbrace>\<lambda>r s. d6_get_a_A' b s = Some (v && 0xFF) \<rbrace>"
  unfolding d6_get_a_A'_def d28_set_a_A'_def d7_get_a_A_part0'_def d29_set_a_A_part0'_def
  apply wp
  apply (simp only: oguard_def ogets_def oreturn_def obind_def)
  apply(simp only: split: unat_splits option.splits if_splits)
  apply safe
     apply(simp)
  using[[simp_trace]]
    apply(simp only: testLemmas heap_heap_update)
  apply simp
    apply clarify
  apply(rule eq_ucast_ucast_eq)
   apply(simp only: len_bit0)
  apply(subst fun_upd_same)
  apply(simp only: proofs.t1_C_accupd_same)
  apply(subst Arrays.index_update)
   apply(simp only: card_bit1 card_bit0 card_num1)
  apply(simp only: BIT_special_simps word_no_log_defs int_and_numerals word_ao_absorbs word_bw_assocs word_bw_lcs word_ao_dist ucast_and_dist)
  apply(simp only: ucast_bintr len_bit0 bin_ops_same BIT_bin_simps len_num1 word_of_int_numeral)
  apply(simp only: One_nat_def)
  apply(simp only: bitLemmas bitLemmas' semiring_numeral_class.numeral_mult[symmetric] mult_num_simps)
    apply(simp only: word_of_int_numeral BIT_bin_simps numeral.simps(1) Num.arith_simps bitLemmas bitLemmas' semiring_numeral_class.numeral_mult[symmetric] mult_num_simps)
   apply simp
  apply simp
  done


end
  
end

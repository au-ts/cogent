theory Test
  imports "AutoCorres.AutoCorres"
begin


lemma mask_31: "(0x7FFFFFFF :: 32 word) = mask 31"
  by (simp add: mask_def)

lemma not_mask_31: "(0x80000000 :: 32 word) = ~~ (mask 31)"
  by (simp add: mask_def)

lemma mask_1: "(0x00000001 :: 32 word) = mask 1"
  by (simp add: mask_def)

lemma not_mask_1: "(0xFFFFFFFE :: 32 word) = ~~ (mask 1)"
  by (simp add: mask_def)

lemma lshift1_mask31_eq_not_mask1: "(mask 31 :: 32 word) << Suc 0 = ~~ (mask 1)"
  by (simp add: mask_def)

lemma
  fixes v :: "32 word"
  shows
  "(b0 && 1 || (v && 0x7FFFFFFF << Suc 0) >> Suc 0) && 0x7FFFFFFF ||
   ((b1 && 0xFFFFFFFE || (v >> 31) && 1) && 1 << 31) =
    v"
  apply (simp add:
      shiftl_over_and_dist shiftr_over_or_dist
      mask_31 not_mask_31
      mask_1 not_mask_1
      lshift1_mask31_eq_not_mask1
      mask_shift and_mask2
      word_bits_conv word_bits_size
      word_bool_alg.conj_disj_distrib2
      word_bool_alg.disj.assoc
      word_bool_alg.conj.assoc)
  apply (simp add: shiftr_over_and_dist mask_shiftl_decompose and_not_mask[symmetric] mask_or_not_mask)
  done

end
(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory PleSle
imports
  "../impl/BilbyFs_Shallow_Desugar_Tuples"
  "../adt/WordArrayT"
  "../adt/ArrayT"
  "../adt/BufferT"
  "HOL-Eisbach.Eisbach"
begin

text{* axioms and lemmas that are *not* specific to 32 word. -> should be refactored.*}
axiomatization
where
 u32_to_u8_is_ucast:
  "u32_to_u8 = ucast"
and
 u64_to_u8_is_ucast:
  "u64_to_u8 = ucast"
and
 u64_to_u32_is_ucast:
  "u64_to_u32 = ucast"
and
 u16_to_u8_is_ucast:
  "u16_to_u8 = ucast"
  
lemmas less_to_le = order_class.order.strict_implies_order

lemma test_bit_out_of_bounds:
  "\<lbrakk>n \<ge> 8\<rbrakk> \<Longrightarrow> ((w :: 8 word) !! n) = False"
  by (auto dest!: test_bit_size simp:word_size)
  
lemma mod_range_eq:
  "\<lbrakk>n \<ge> (a::nat)*8; (n::nat) < (a+1)*8\<rbrakk> \<Longrightarrow> n mod 8 = n - (a*8)"
  by (simp add: div_nat_eqI modulo_nat_def mult.commute)
  
lemma range_le:
  "\<lbrakk>(n :: nat) \<ge> (a::nat)*8; n < (a+1)*8\<rbrakk> \<Longrightarrow>
      n - (a*8) < 8"
  by simp
  
lemma div_range_le:
  "\<lbrakk>n < (a*8)\<rbrakk> \<Longrightarrow> (n :: nat) div 8 < a"
  by auto

lemma take_decomp:
  "length l \<ge> n \<Longrightarrow> n > 0 \<Longrightarrow> (take n l) = ((hd l) # (take (n - 1) (tl l)))"
  by (induct l) (simp add: take_Cons split: nat.split)+
  
lemma take_drop_decomp:
  "k < length l \<Longrightarrow> length (List.drop k l) \<ge> n \<Longrightarrow> n > 0 
    \<Longrightarrow> take n (List.drop k l) = (l ! k) # take (n - 1) (List.drop (k + 1) l)"
  by (simp add: take_decomp hd_drop_conv_nth drop_Suc[symmetric] drop_tl[symmetric])

lemma elem_take_n:
 "i<n \<Longrightarrow> (take n xs ! i) = xs ! i"
 by simp
  
lemma take_n_eq_simp:
 "take len ys = take len xs \<Longrightarrow>
  idx < len \<Longrightarrow>
    ys !idx = xs !idx"
by (metis elem_take_n)

 lemma take_n_and_len'_eq_simp:
 "take len ys = take len xs \<Longrightarrow>
  idx < len' \<Longrightarrow>
  len' \<le> len \<Longrightarrow>
    ys !idx = xs !idx"
by (erule take_n_eq_simp) simp

lemma drop_n_then_nth_eq:
 assumes "n + i \<le> length xs"
 assumes "n + i \<le> length ys"
 assumes "ys ! (n + i) = xs ! (n + i)"
 shows "List.drop n ys ! (0 + i) = List.drop n xs ! (0 + i)"
 using assms by auto
 
 lemma drop_n_then_nth_eq_wo_0:
 assumes "n + i \<le> length xs"
 assumes "n + i \<le> length ys"
 assumes "ys ! (n + i) = xs ! (n + i)"
 shows "List.drop n ys ! i = List.drop n xs ! i"
 using assms by auto

lemma plus_no_overflow_unat_lift: 
  "(a::'a::len word )  < a + b \<Longrightarrow>  unat (a+b) = unat a + unat b"
  by unat_arith


method handle_wa_mod for offs :: "U32" =
(rule wordarray_modify_ret[where index=offs, simplified Let_def],
  simp_all add: wordarray_make ArrA.defs ElemAO.defs  ElemA.defs
   setu8_def[unfolded tuple_simps sanitizers], unat_arith)

lemma take_list_update:
  "i < length xs
    \<Longrightarrow> take n (xs[i := x]) = (if i < n then (take n xs)[i := x] else take n xs)"
  by (induct xs arbitrary: n i, simp_all add: take_Cons split: nat.split)

lemma drop_list_update:
  "i < length xs
    \<Longrightarrow> List.drop n (xs[i := x]) = (if i < n then List.drop n xs else (List.drop n xs)[i - n := x])"
  by (induct xs arbitrary: n i, simp_all add: drop_Cons split: nat.split)

definition ple16 :: "8 word list \<Rightarrow> 32 word \<Rightarrow> 16 word"
where
  "ple16 data offs \<equiv> word_rcat (rev (take 2 (List.drop (unat offs) data)))"
  
definition sle16 :: "U16 \<Rightarrow> U8 list"
where
  "sle16 \<equiv> rev \<circ> word_rsplit"
  
lemma deserialise_le16_ret:
assumes valid_offs:
  "unat offs + 1 < length (\<alpha>wa $ data\<^sub>f buf)"
assumes no_ovf:
  "offs < offs + 2"
shows
  "deserialise_le16 (buf, offs) = (ple16 (\<alpha>wa $ data\<^sub>f buf) offs)"
using valid_offs
  apply (subgoal_tac "(\<forall>i\<in>{0..1}. unat (offs+i) < length (\<alpha>wa (data\<^sub>f buf)))")
   prefer 2
   apply unat_arith
  apply (clarsimp simp: wordarray_get_ret[where arr="data\<^sub>f buf"] ple16_def 
                        deserialise_le16_def)
  apply (subgoal_tac "(unat (offs + 1) > 0)")
   prefer 2
   apply (drule_tac x=1 in bspec, simp)
   using no_ovf apply unat_arith
   apply auto[1]
  apply (subst take_drop_decomp, (simp+))+
  apply (subst unatSuc[symmetric], (simp add: unat_gt_0[symmetric] add.commute[where b=offs]))+
  apply (rule trans, rule word_rcat_rsplit[symmetric])
  apply (rule arg_cong[where f=word_rcat])
  apply (subst word_rsplit_upt[where n=2], simp add: word_size)
   apply simp
  apply (simp add: upt_rec shiftr_over_or_dist shiftl_shiftr1 shiftl_shiftr2 word_size)
  apply (safe intro!: word_eqI, simp_all add: word_size word_ops_nth_size nth_ucast
        nth_shiftr nth_shiftl add.commute[where b=offs] test_bit_out_of_bounds)
  done

lemma serial_le16_helper:
 "unat offs + 2 < length (\<alpha>wa (data\<^sub>f buf)) \<Longrightarrow>
   [u16_to_u8 v, u16_to_u8 (v >> 8)]
 = sle16 v"
  apply (clarsimp simp: u16_to_u8_is_ucast sle16_def)
  apply (subst word_rsplit_upt[where n=2])
    apply ((simp add: word_size upt_rec)+)[2]
   apply (simp add: upt_rec)
  done
  
lemma serialise_le16_ret:
  assumes no_overflow: "offs < offs + 2"
  and valid_offs:
   "unat offs + 2 < length (\<alpha>wa (data\<^sub>f buf))"
shows
  "(serialise_le16 (buf, offs, v)) =
  buf\<lparr>data\<^sub>f:=WordArrayT.make (buf_sub_slice buf offs (offs+2) (sle16 v))\<rparr>"
proof -
  have unat_plus:
    "\<And>n. n \<le> 2 \<longrightarrow> unat (offs + n) = unat offs + unat n"
    using no_overflow valid_offs
    by clarsimp unat_arith
  show ?thesis
  using valid_offs
  apply (simp add: serialise_le16_def[unfolded sanitizers] serialise_u8_def[unfolded sanitizers] Let_def)
  apply (handle_wa_mod "offs")
  apply (handle_wa_mod "offs+1")
  apply (simp add: serial_le16_helper[OF valid_offs, where v=v,symmetric])
  apply (rule arg_cong[where f="\<lambda>v. Buffer.data\<^sub>f_update v buf"])
  apply (rule ext)
  apply (rule arg_cong[where f="WordArrayT.make"])
  
  apply (simp add: buf_sub_slice_def)
  apply (rule trans, rule_tac n="unat offs" in append_take_drop_id[symmetric],
    rule arg_cong2[where f=append])
   apply (simp add: unat_plus order_le_less_trans[OF _ valid_offs] take_list_update)
  apply (simp add: unat_plus)
    apply (cut_tac valid_offs, simp)
   apply (simp add: max_absorb1)
   apply clarsimp
   apply (simp add: list_eq_iff_nth_eq)
   apply (rule conjI)
    using valid_offs
    apply (simp add: nth_Cons split: nat.split)
  using valid_offs
  apply (clarsimp simp only:)
  apply (subst nth_list_update, unat_arith) +
  apply clarsimp
  apply (rule arg_cong[where f="nth (\<alpha>wa (data\<^sub>f buf))"])
   apply simp
 done
qed

lemma ple16_take:
 assumes offs:"offs < offs+2"
 assumes ntake:"unat (offs + 2) \<le> ntake"
 shows   "ple16 (take ntake ys) offs = ple16 ys offs"
 apply (simp add: ple16_def)
 apply (rule arg_cong[where f="word_rcat"])
 apply (rule arg_cong[where f="rev"])
  apply (subst list_eq_iff_nth_eq)
  using offs ntake less_to_le[OF offs, simplified unat_plus_simple]
  apply fastforce
 done
 
lemma ple16_append:
  assumes no_overflow: "offs < offs + 2" 
  assumes len_ys: "unat (offs + 2) \<le> length ys"
  shows   "ple16 (ys@zs) offs = ple16 ys offs"
  using plus_no_overflow_unat_lift[OF no_overflow]  len_ys
  by (simp add: ple16_def)
  
lemma ple16_append_Cons:
  assumes no_overflow: "offs < offs + 2"
  assumes len_ys: "unat (offs + 2) \<le> length (v#ys)"
  shows   "ple16 (v#ys@zs) offs = ple16 (v#ys) offs"
proof -
  have unat_nth_simp_Cons: "\<And> n xs ys . 
    unat n < Suc (length xs) \<Longrightarrow> (v#xs@ys)!(unat n) = (v#xs)!(unat n)"
  by (case_tac "0 < unat n") (fastforce simp: nth_append) +
  show ?thesis
  apply(subgoal_tac "unat offs < Suc (length ys)")
   apply(rule ple16_append[where ys = "v#ys" and zs = "zs" and offs="offs", 
       simplified List.append.append_Cons])
    using no_overflow apply clarsimp
   using len_ys apply clarsimp
  using assms by unat_arith
qed

definition ple64 :: "8 word list \<Rightarrow> 32 word \<Rightarrow> 64 word"
where
  "ple64 data offs \<equiv> word_rcat (rev (take 8 (List.drop (unat offs) data)))"

definition ple32 :: "8 word list \<Rightarrow> 32 word \<Rightarrow> 32 word"
where
  "ple32 data offs \<equiv> word_rcat (rev (take 4 (List.drop (unat offs) data)))"

definition sle32 :: "U32 \<Rightarrow> U8 list"
where
  "sle32 \<equiv> rev \<circ> word_rsplit"

lemma deserialise_le32_ret:
assumes valid_offs:
  "unat offs + 3 < length (\<alpha>wa $ data\<^sub>f buf)"
assumes no_ovf:
  "offs < offs + 3"
shows
  "deserialise_le32 (buf, offs) = (ple32 (\<alpha>wa $ data\<^sub>f buf) offs)"
using valid_offs
  apply (subgoal_tac "(\<forall>i\<in>{0..3}. unat (offs+i) < length (\<alpha>wa (data\<^sub>f buf)))")
   prefer 2
   apply unat_arith
  apply (clarsimp simp: wordarray_get_ret[where arr="data\<^sub>f buf"] ple32_def 
                        deserialise_le32_def)
  apply (subgoal_tac "\<forall>j\<in>{1..3}. (unat (offs + j) > 0)")
   prefer 2
   apply clarsimp
   apply (drule_tac x=j in bspec, simp)
   using no_ovf apply unat_arith
   apply auto[1]
  apply (subst take_drop_decomp, (simp+))+
  apply (subst unatSuc[symmetric], (simp add: unat_gt_0[symmetric] add.commute[where b=offs]))+
  apply simp
  apply (rule trans, rule word_rcat_rsplit[symmetric])
  apply (rule arg_cong[where f=word_rcat])
  apply (subst word_rsplit_upt[where n=4], simp add: word_size)
   apply simp
  apply (simp add: upt_rec shiftr_over_or_dist shiftl_shiftr1 shiftl_shiftr2 word_size)
  apply (safe intro!: word_eqI, simp_all add: word_size word_ops_nth_size nth_ucast
        nth_shiftr nth_shiftl add.commute[where b=offs] test_bit_out_of_bounds)
  done

lemma deserialise_le32_ret':
assumes valid_offs:
  "offs + 3 < wordarray_length (data\<^sub>f buf)"
assumes no_ovf:
  "offs < offs + 3"
shows
  "deserialise_le32 (buf, offs) = (ple32 (\<alpha>wa $ data\<^sub>f buf) offs)"
using valid_offs
  apply (subgoal_tac "(\<forall>i\<in>{0..3}. unat (offs+i) < length (\<alpha>wa (data\<^sub>f buf)))")
  prefer 2
   apply clarsimp
   apply (rule order.strict_trans2[OF _ wordarray_length_leq_length])
   using no_ovf apply unat_arith
  apply (clarsimp simp: wordarray_get_ret[where arr="data\<^sub>f buf"] ple32_def 
                        deserialise_le32_def)
  apply (subgoal_tac "\<forall>j\<in>{1..3}. (unat (offs + j) > 0)")
   prefer 2
   apply clarsimp
   apply (drule_tac x=j in bspec, simp)
   using no_ovf apply unat_arith
   apply (frule_tac x=3 in bspec, simp)
   apply (cut_tac plus_no_overflow_unat_lift[OF no_ovf])
  apply (subst take_drop_decomp, (simp+))+
  apply (subst unatSuc[symmetric], (simp add: unat_gt_0[symmetric] add.commute[where b=offs]))+
  apply simp
  apply (rule trans, rule word_rcat_rsplit[symmetric])
  apply (rule arg_cong[where f=word_rcat])
  apply (subst word_rsplit_upt[where n=4], simp add: word_size)
   apply simp
  apply (simp add: upt_rec shiftr_over_or_dist shiftl_shiftr1 shiftl_shiftr2 word_size)
  apply (clarsimp simp: wordarray_get_ret)
  apply (safe intro!: word_eqI, simp_all add: word_size word_ops_nth_size nth_ucast
        nth_shiftr nth_shiftl add.commute[where b=offs] test_bit_out_of_bounds)
  done


lemma serial_le32_helper:
 "unat offs + 4 < length (\<alpha>wa (data\<^sub>f buf)) \<Longrightarrow>
   [u32_to_u8 v, u32_to_u8 (v >> 8), u32_to_u8 (v >> 16), u32_to_u8 (v >> 24)]
 = sle32 v"
  apply (clarsimp simp: u32_to_u8_is_ucast sle32_def)
  apply (subst word_rsplit_upt[where n=4])
    apply ((simp add: word_size upt_rec)+)[2]
   apply (simp add: upt_rec)
  done
  
lemma serialise_le32_ret:
  assumes no_overflow: "offs < offs + 4"
  and valid_offs:
   "unat offs + 4 < length (\<alpha>wa (data\<^sub>f buf))"
  notes  wa_modify_ret = wordarray_modify_ret[rotated - 1, simplified Let_def]
shows
  "(serialise_le32 (buf, offs, v)) =
  buf\<lparr>data\<^sub>f:=WordArrayT.make (buf_sub_slice buf offs (offs+4) (sle32 v))\<rparr>"
proof -
  have unat_plus:
    "\<And>n. n \<le> 4 \<longrightarrow> unat (offs + n) = unat offs + unat n"
    using no_overflow valid_offs
    by unat_arith auto
  show ?thesis
  using valid_offs
  apply (simp add: serialise_le32_def[unfolded sanitizers] serialise_u8_def[unfolded sanitizers] Let_def)
  apply (handle_wa_mod "offs")
  apply (handle_wa_mod "offs+1")
  apply (handle_wa_mod "offs+2")
  apply (handle_wa_mod "offs+3")
  apply (simp add: serial_le32_helper[OF valid_offs, where v=v,symmetric])
  apply (rule arg_cong[where f="\<lambda>v. Buffer.data\<^sub>f_update v buf"])
  apply (rule ext)
  apply (rule arg_cong[where f="WordArrayT.make"])
  
  apply (simp add: buf_sub_slice_def)
  apply (rule trans, rule_tac n="unat offs" in append_take_drop_id[symmetric],
    rule arg_cong2[where f=append])
   apply (simp add: unat_plus order_le_less_trans[OF _ valid_offs] take_list_update)
  apply (simp add: unat_plus)
    apply (cut_tac valid_offs, simp)
   apply (simp add: max_absorb1)
   apply (simp add: list_eq_iff_nth_eq)
   apply (rule conjI)
    using valid_offs
    apply (simp add: nth_Cons split: nat.split)
  using valid_offs
  apply (clarsimp simp only:)
  apply (subst nth_list_update, unat_arith) +
  apply force
 done
qed

lemma ple32_take:
 assumes offs:"offs < offs+4"
 assumes ntake:"unat (offs + 4) \<le> ntake"
 shows   "ple32 (take ntake ys) offs = ple32 ys offs"
  apply (simp add: ple32_def)
  apply (rule arg_cong[where f="word_rcat"])
  apply (rule arg_cong[where f="rev"])
  apply (subst list_eq_iff_nth_eq)
  using offs ntake less_to_le[OF offs, simplified unat_plus_simple]
  apply fastforce
 done
 
lemma plus4_offs_ntake:
  fixes offs ::U32
  assumes "unat (offs + 4) \<le> ntake"
  assumes offs_overflow: " (offs) <  ((offs+4))"
  assumes "n \<in> {0,1,2,3}"
  shows "unat (offs+n) < ntake"
  using assms apply (clarsimp)
  apply (erule disjE, unat_arith, fastforce?)+
  apply simp
  apply unat_arith
 done
 
lemma ple32_append:
  assumes no_overflow: "offs < offs+4" 
  assumes len_ys: "unat (offs + 4) \<le> length ys"
  shows   "ple32 (ys@zs) offs = ple32 ys offs"
  using plus_no_overflow_unat_lift[OF no_overflow]  len_ys
  by (simp add: ple32_def)
  
lemma ple32_append_Cons:
  assumes no_overflow: "offs < offs+4"
  assumes len_ys: "unat (offs + 4) \<le> length (v#ys)"
  shows   "ple32 (v#ys@zs) offs = ple32 (v#ys) offs"
proof -
  have unat_nth_simp_Cons: "\<And> n xs ys . 
    unat n < Suc (length xs) \<Longrightarrow> (v#xs@ys)!(unat n) = (v#xs)!(unat n)"
  by (case_tac "0 < unat n") (fastforce simp: nth_append) +
  show ?thesis
  apply(subgoal_tac "unat offs < Suc (length ys)")
   apply(rule ple32_append[where ys = "v#ys" and zs = "zs" and offs="offs", simplified List.append.append_Cons])
    using no_overflow apply clarsimp
   using len_ys apply clarsimp
  using assms by unat_arith
qed

  
definition sle64 :: "U64 \<Rightarrow> U8 list"
where
  "sle64 \<equiv> rev \<circ> word_rsplit"

lemma deserialise_le64_ret:
assumes valid_offs:
  "unat offs + 8 \<le> length (\<alpha>wa $ data\<^sub>f buf)"
assumes no_ovf:
  "offs \<le> offs + 8"
shows
  "deserialise_le64 (buf, offs) = (ple64 (\<alpha>wa $ data\<^sub>f buf) offs)"
using valid_offs
  apply (subgoal_tac "(\<forall>i\<in>{0..7}. unat (offs+i) < length (\<alpha>wa (data\<^sub>f buf)))")
   prefer 2
   apply unat_arith
  apply (clarsimp simp: wordarray_get_ret[where arr="data\<^sub>f buf"] ple64_def 
                        deserialise_le64_def)
  apply (subgoal_tac "\<forall>j\<in>{1..7}. (unat (offs + j) > 0)")
   prefer 2
   apply clarsimp
   apply (drule_tac x=j in bspec, simp)
   using no_ovf apply unat_arith
   apply auto[1]
  apply (subst take_drop_decomp, (simp+))+
  apply (subst unatSuc[symmetric], (simp add: unat_gt_0[symmetric] add.commute[where b=offs])[1])+
  apply simp
  apply (rule trans, rule word_rcat_rsplit[symmetric])
  apply (rule arg_cong[where f=word_rcat])
  apply (subst word_rsplit_upt[where n=8], simp add: word_size)
   apply simp
  apply (simp add: upt_rec shiftr_over_or_dist shiftl_shiftr1 shiftl_shiftr2 word_size)
  apply (safe intro!: word_eqI, simp_all add: word_size word_ops_nth_size nth_ucast
        nth_shiftr nth_shiftl add.commute[where b=offs] test_bit_out_of_bounds)
  done

lemma word_leq_plus:"\<lbrakk>(a::('a::len) word) \<le> a + b; c < b\<rbrakk> \<Longrightarrow> a \<le> a + c"
by (metis order_less_imp_le word_random)

lemma plus_le_bound_unat_lift:
  "\<lbrakk> (x::('a::len) word) \<le> x + j; i < j \<rbrakk> \<Longrightarrow> unat (x + i) = unat x + unat i"
  apply (drule word_leq_plus; simp?)
  apply (clarsimp simp: unat_plus_simple)
  done

lemma deserialise_le64_ret':
assumes valid_offs:
  "offs + 8 \<le> wordarray_length (data\<^sub>f buf)"
assumes no_ovf:
  "offs \<le> offs + 8"
shows
  "deserialise_le64 (buf, offs) = (ple64 (\<alpha>wa $ data\<^sub>f buf) offs)"
using valid_offs
  apply (subgoal_tac "(\<forall>i\<in>{0..7}. unat (offs+i) < length (\<alpha>wa (data\<^sub>f buf)))")
  prefer 2
   apply clarsimp
   apply (rule order.strict_trans2[OF _ wordarray_length_leq_length])
   apply (cut_tac i = i in plus_le_bound_unat_lift[OF no_ovf], unat_arith)
   apply (cut_tac no_ovf; clarsimp simp: unat_plus_simple)
   apply (clarsimp simp: word_le_nat_alt)
  apply (clarsimp simp: wordarray_get_ret[where arr="data\<^sub>f buf"] ple64_def 
                        deserialise_le64_def)
  apply (subgoal_tac "\<forall>j\<in>{1..7}. (unat (offs + j) > 0)")
   prefer 2
   apply clarsimp
   apply (drule_tac x=j in bspec, simp)
   using no_ovf apply unat_arith
   apply auto[1]
  apply (subgoal_tac "unat offs + 8 \<le> length (\<alpha>wa $ data\<^sub>f buf)")
   apply (subst take_drop_decomp, (simp+))+
   apply (subst unatSuc[symmetric], (simp add: unat_gt_0[symmetric] add.commute[where b=offs])[1])+
   apply simp
   apply (rule trans, rule word_rcat_rsplit[symmetric])
   apply (rule arg_cong[where f=word_rcat])
   apply (subst word_rsplit_upt[where n=8], simp add: word_size)
    apply simp
   apply (simp add: upt_rec shiftr_over_or_dist shiftl_shiftr1 shiftl_shiftr2 word_size)
   apply (clarsimp simp: wordarray_get_ret)
   apply (safe intro!: word_eqI, simp_all add: word_size word_ops_nth_size nth_ucast
        nth_shiftr nth_shiftl add.commute[where b=offs] test_bit_out_of_bounds)
   apply (rule order.trans[OF _ wordarray_length_leq_length])
  apply (cut_tac no_ovf; clarsimp simp: unat_plus_simple; clarsimp simp: word_le_nat_alt)
  done

lemma serial_le64_helper:
 "unat offs + 8 < length (\<alpha>wa (data\<^sub>f buf)) \<Longrightarrow>
   [u64_to_u8 v, u64_to_u8 (v >> 8), u64_to_u8 (v >> 16), u64_to_u8 (v >> 24),
    u64_to_u8 (v >> 32),  u64_to_u8 (v >> 40), u64_to_u8 (v >> 48), u64_to_u8 (v >> 56)]
 = sle64 v"
  apply (clarsimp simp: u64_to_u8_is_ucast sle64_def)
  apply (subst word_rsplit_upt[where n=8])
    apply ((simp add: word_size upt_rec)+)[2]
   apply (simp add: upt_rec)
  done

lemma serialise_le64_ret:
  assumes no_overflow: "offs < offs + 8"
  and valid_offs:
   "unat offs + 8 < length (\<alpha>wa (data\<^sub>f buf))"
shows
  "(serialise_le64 (buf, offs, v)) =
  buf\<lparr>data\<^sub>f:=WordArrayT.make (buf_sub_slice buf offs (offs+8) (sle64 v))\<rparr>"
proof -
  have unat_plus:
    "\<And>n. n \<le> 8 \<longrightarrow> unat (offs + n) = unat offs + unat n"
    using no_overflow valid_offs
    by unat_arith auto
  show ?thesis

  apply (simp add: serialise_le64_def[unfolded sanitizers] serialise_u8_def[unfolded sanitizers] Let_def)
  using valid_offs apply -
  apply (handle_wa_mod "offs")
  apply (handle_wa_mod "offs+1")
  apply (handle_wa_mod "offs+2")
  apply (handle_wa_mod "offs+3")
  apply (handle_wa_mod "offs+4")
  apply (handle_wa_mod "offs+5")
  apply (handle_wa_mod "offs+6")
  apply (handle_wa_mod "offs+7")
  apply (simp add: serial_le64_helper[OF valid_offs, where v=v,symmetric])
  apply (rule arg_cong[where f="\<lambda>v. Buffer.data\<^sub>f_update v buf"])
  apply (rule ext)
  apply (rule arg_cong[where f="WordArrayT.make"])
  
  apply (simp add: buf_sub_slice_def)
  apply (rule trans, rule_tac n="unat offs" in append_take_drop_id[symmetric],
    rule arg_cong2[where f=append])
   apply (simp add: unat_plus order_le_less_trans[OF _ valid_offs] take_list_update)
  apply (simp add: unat_plus)
    apply (cut_tac valid_offs, simp)
   apply (simp add: max_absorb1)
   apply (simp add: list_eq_iff_nth_eq)
   apply (rule conjI)
    using valid_offs
    apply (simp add: nth_Cons split: nat.split)
  using valid_offs
  apply (clarsimp simp only:)
  apply (subst nth_list_update, unat_arith) +
  apply force
 done
qed

lemma ple64_take:
 assumes offs:"offs < offs+8"
 assumes ntake:"unat (offs + 8) \<le> ntake"
 shows   "ple64 (take ntake ys) offs = ple64 ys offs"
  apply (simp add: ple64_def)
  apply (rule arg_cong[where f="word_rcat"])
  apply (rule arg_cong[where f="rev"])
  apply (subst list_eq_iff_nth_eq)
  using offs ntake less_to_le[OF offs, simplified unat_plus_simple]
  apply fastforce
 done
 
lemma ple64_append:
  assumes no_overflow: "offs < offs + 8" 
  assumes len_ys: "unat (offs + 8) \<le> length ys"
  shows   "ple64 (ys@zs) offs = ple64 ys offs"
  using plus_no_overflow_unat_lift[OF no_overflow]  len_ys
  by (simp add: ple64_def)
  
lemma ple64_append_Cons:
  assumes no_overflow: "offs < offs + 8"
  assumes len_ys: "unat (offs + 8) \<le> length (v#ys)"
  shows   "ple64 (v#ys@zs) offs = ple64 (v#ys) offs"
proof -
  have unat_nth_simp_Cons: "\<And> n xs ys . 
    unat n < Suc (length xs) \<Longrightarrow> (v#xs@ys)!(unat n) = (v#xs)!(unat n)"
  by (case_tac "0 < unat n") (fastforce simp: nth_append) +
  show ?thesis
  apply(subgoal_tac "unat offs < Suc (length ys)")
   apply(rule ple64_append[where ys = "v#ys" and zs = "zs" and offs="offs", simplified List.append.append_Cons])
    using no_overflow apply clarsimp
   using len_ys apply clarsimp
  using assms by unat_arith
qed
end

(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory OstoreR
imports
  "../spec/OstoreS"
  "../spec/OstoreInvS"
  "../spec/TransS"
  "BilbyFsConsts.BilbyFs_Shallow_Desugar_Tuples"
  "../adt/BufferT"
  "../spec/SerialS"
  "HOL-Library.Sublist"
  (* "~~/src/HOL/Word/WordBitwise" *)
  "HOL-Library.Multiset"
begin

lemma take_list_update:
  "i < length xs
    \<Longrightarrow> take n (xs[i := x]) = (if i < n then (take n xs)[i := x] else take n xs)"
  by (induct xs arbitrary: n i, simp_all add: take_Cons split: nat.split)

lemma drop_list_update:
  "i < length xs
    \<Longrightarrow> drop n (xs[i := x]) = (if i < n then drop n xs else (drop n xs)[i - n := x])"
  by (induct xs arbitrary: n i, simp_all add: drop_Cons split: nat.split)

lemma is_set_0[simp]:
 "\<not>is_set (0, x)"
 "\<not>is_set (ostoreWriteNone, x)"
by (simp add: ostoreWriteNone_def is_set_def)+

lemma padding_to_eq_align32_simp:
  "\<not> no_summary\<^sub>f mount_st \<Longrightarrow> 
  padding_to (mount_st, ostore_st, ostoreWriteNone) =
   align32 (used\<^sub>f ostore_st, io_size\<^sub>f (super\<^sub>f mount_st))"
unfolding  padding_to_def[unfolded tuple_simps sanitizers]
 by (simp add: ostoreWriteNone_def Let_def)

lemma padding_to_ret:
  "\<lbrakk> P (if is_set(osw,ostoreWriteNewEb) then
          if no_summary\<^sub>f mount_st \<or> used\<^sub>f ostore_st = eb_size\<^sub>f (super\<^sub>f mount_st) then
            eb_size\<^sub>f (super\<^sub>f mount_st)
          else
            eb_size\<^sub>f (super\<^sub>f mount_st) -
                    serialise_size_summary_Obj_with_extra (summary\<^sub>f ostore_st, 0)
        else align32 (used\<^sub>f ostore_st, io_size\<^sub>f (super\<^sub>f mount_st)))  \<rbrakk> \<Longrightarrow> 
    P (padding_to (mount_st, ostore_st, osw))"
  unfolding padding_to_def[unfolded sanitizers tuple_simps]   
  by (fastforce simp: Let_def ostoreWriteNewEb_def) 

lemma word_le_diff:
 "(a::U32) < a + b \<Longrightarrow>
   a + b \<le> c \<Longrightarrow>
   a \<le> c - b"
  by (unat_arith)

lemma os_sum_sz_simp:
  "serialise_size_summary_Obj_with_extra (summary\<^sub>f ostore_st, 0) = os_sum_sz ostore_st"
by (simp add: os_sum_sz_def serialise_size_summary_Obj_def
    serialise_size_summary_Obj_with_extra_def bilbyFsObjHeaderSize_def)

lemma padding_to_eb_fullE:
  "inv_ostore mount_st ostore_st \<Longrightarrow>
   inv_mount_st mount_st \<Longrightarrow>
   used\<^sub>f ostore_st = eb_size\<^sub>f (super\<^sub>f mount_st) \<Longrightarrow>
  (used\<^sub>f ostore_st = eb_size\<^sub>f (super\<^sub>f mount_st) \<Longrightarrow>
  P (eb_size\<^sub>f (super\<^sub>f mount_st)))
 \<Longrightarrow> P (padding_to (mount_st, ostore_st, osw))"
  apply (rule padding_to_ret)
  apply (case_tac "is_set (osw, ostoreWriteNewEb)")
   apply simp
  apply clarsimp
  apply (clarsimp simp:inv_mount_st_def Let_def)
  apply (simp add: align32_unchanged)
 done

lemma sync_offs_le_padding_to:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  shows
  "sync_offs\<^sub>f ostore_st \<le> padding_to (mount_st, ostore_st, ostoreWriteNone)"
  apply (case_tac "used\<^sub>f ostore_st = eb_size\<^sub>f (super\<^sub>f mount_st)")
   apply (erule padding_to_eb_fullE[OF inv_ostore inv_mount_st])
    using inv_ostore apply (fastforce simp: inv_ostore_def)
   apply (simp add: padding_to_def)
   
   using inv_ostore_sync_offsD[OF inv_ostore] align32_le[where v="used\<^sub>f ostore_st" and al="io_size\<^sub>f (super\<^sub>f mount_st)"]
   inv_mount_st inv_ostore_used_no_overflowD[OF inv_ostore] apply (clarsimp simp: inv_mount_st_def Let_def)
    apply unat_arith+
 done

lemma used_le_padding_to:
assumes inv_ostore: "inv_ostore mount_st ostore_st"
assumes inv_mount_st: "inv_mount_st mount_st"
shows
"used\<^sub>f ostore_st \<le> padding_to (mount_st, ostore_st, ostoreWriteNone)"
  apply (case_tac "used\<^sub>f ostore_st = eb_size\<^sub>f (super\<^sub>f mount_st)")
   apply (erule padding_to_eb_fullE[OF inv_ostore inv_mount_st])
  apply (rule inv_ostore_usedD[OF inv_ostore])
  apply (simp add: padding_to_def)
  apply (rule align32_le)
   using inv_mount_st
   apply (fastforce simp: inv_mount_st_def Let_def)
  using inv_mount_st inv_ostore_used_no_overflowD[OF inv_ostore]
  apply (clarsimp simp add: inv_mount_st_def Let_def) 
 done

lemma padding_to_le_length_wbuf:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  shows
 "unat (padding_to (mount_st, ostore_st, ostoreWriteNone)) \<le> length (\<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st)))"
   apply (simp add: padding_to_def[unfolded tuple_simps sanitizers] ostoreWriteNone_def)
  using align32_upper_bound[where bound="eb_size\<^sub>f (super\<^sub>f mount_st)" and v="used\<^sub>f ostore_st" and
                                  al="io_size\<^sub>f (super\<^sub>f mount_st)"]
  using inv_mount_st[simplified inv_mount_st_def Let_def] apply clarsimp
  using inv_ostore_usedD[OF inv_ostore] apply simp
  using inv_ostore_used_no_overflowD[OF inv_ostore] apply simp
  using inv_ostore_eb_size_wbuf_eqD[OF inv_ostore]
  apply unat_arith
 done

lemma take_eq_strenghen:
 assumes "take m xs = take m ys"
 and "n \<le> m"
shows
 "take n xs =  take n ys"
using assms by (metis min.absorb_iff2 min.commute take_take)

lemma inv_ostore_bound_le_lenD:
 "inv_ostore mount_st ostore_st \<Longrightarrow>
 unat (bound\<^sub>f (wbuf\<^sub>f ostore_st)) \<le> length (\<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st)))"
 apply (clarsimp simp: inv_ostore_def buf_simps wordarray_length_ret)
 using wordarray_length_ret[where arr="data\<^sub>f (wbuf\<^sub>f ostore_st)"]
 apply simp
done

lemma prepare_memset_get_obj_eq:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and inv_mount_st: "inv_mount_st mount_st"
  and pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"


  shows
  "\<And>v. is_valid_addr mount_st ostore_st v \<Longrightarrow>
    ostore_get_obj (ostore_st \<lparr>wbuf\<^sub>f := buf_memset (wbuf\<^sub>f ostore_st, used\<^sub>f ostore_st, pad_to - used\<^sub>f ostore_st, bilbyFsPadByte),
                           used\<^sub>f := pad_to\<rparr>) v = ostore_get_obj ostore_st  v"
  apply (clarsimp simp: ostore_get_obj_def)
  apply (rule_tac f="\<lambda>x. pObj x (ObjAddr.offs\<^sub>f v)" in arg_cong)
  apply (rule_tac m="unat $ used\<^sub>f ostore_st" in take_eq_strenghen)
   using wordarray_length_ret[where arr="data\<^sub>f (wbuf\<^sub>f ostore_st)", symmetric]
        inv_ostore_wbuf_boundD[OF inv_ostore]
        inv_ostore_usedD[OF inv_ostore]
        inv_ostore_wbuf_lengthD[OF inv_ostore ]
        inv_mount_st[simplified inv_mount_st_def]
   unfolding is_valid_addr_def 
   apply (subst buf_memset_eq[OF inv_ostore_bound_le_lenD[OF inv_ostore]])
    using used_le_padding_to[OF inv_ostore inv_mount_st]
    apply (simp add: pad_to)
   apply (fastforce simp:  buf_memset_eq word_le_nat_alt buf_simps wordarray_make
          is_valid_addr_def Let_def pad_to min_absorb1)
  apply (unat_arith)
 done

lemma inv_ostore_index_padding_bytes:
assumes inv_ostore: "inv_ostore mount_st ostore_st"
and inv_mount_st: "inv_mount_st mount_st"
and pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
shows
"inv_ostore_index mount_st
                 (ostore_st \<lparr>wbuf\<^sub>f := buf_memset (wbuf\<^sub>f ostore_st, used\<^sub>f ostore_st, pad_to - used\<^sub>f ostore_st, bilbyFsPadByte),
                             used\<^sub>f := pad_to\<rparr>)"
 (is "inv_ostore_index mount_st ?ostore_st")
proof -
   have index_unchanged:
     "index_st\<^sub>f ?ostore_st = index_st\<^sub>f ostore_st" by simp
   also have inv_ostore_index:
     "inv_ostore_index mount_st ostore_st"
     using inv_ostore by (simp add: inv_ostore_def)
   moreover have pad_to_ge_used:
     "used\<^sub>f ostore_st \<le> pad_to"
     by (subst pad_to, rule used_le_padding_to[OF inv_ostore inv_mount_st])
   moreover have is_valid_addr:
     "\<And>v. is_valid_addr mount_st ostore_st v \<Longrightarrow>
            is_valid_addr mount_st ?ostore_st v"
     apply (clarsimp simp: is_valid_addr_def pad_to)
     apply (case_tac "used\<^sub>f ostore_st = eb_size\<^sub>f (super\<^sub>f mount_st)")
      apply (erule (1) padding_to_eb_fullE[OF inv_ostore inv_mount_st])
     apply (cut_tac used_le_padding_to[OF inv_ostore inv_mount_st])
     apply (unat_arith)
    done
   moreover have get_obj_eq:
    "\<And>v. is_valid_addr mount_st ostore_st v \<Longrightarrow>
      ostore_get_obj ?ostore_st v = ostore_get_obj ostore_st  v"
     using prepare_memset_get_obj_eq[OF inv_ostore inv_mount_st pad_to] .

  ultimately show ?thesis
   unfolding inv_ostore_index_def
    by (clarsimp simp: Let_def)
qed

lemma map_eq_iff_nth_eq:
  "(map f xs = map g ys) = (length xs = length ys \<and> (\<forall>i\<in>{0..<length xs}. f (xs!i) = g (ys!i)))"
by (auto simp: list_eq_iff_nth_eq[where xs="map f xs"] dest: map_eq_imp_length_eq)


text {* Adding padding does not add any object to the ostore_log_objects,
Should probably also have a lemma to prove that the snd part of list_trans on all erase-blocks
is unchanged. That lemma can be used to prove this one almost trivially as  ostore_log_objects only used snd
part of the "EbLog list".
 *}

lemma length_pollute_buf:
"length (pollute_buf n xs) = length xs"
 by (simp add: pollute_buf_def)

lemma buf_slice_buf_memset_is_append_padding:
  notes list_trans.simps[simp del]

  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and     frm: "frm \<in> {0, (sync_offs\<^sub>f ostore_st)}"

 notes   pad_to' = pad_to[simplified padding_to_eq_align32_simp[OF inv_mount_st_no_summaryD[OF inv_mount_st]]]

shows
 "buf_slice (buf_memset (wbuf\<^sub>f ostore_st, used\<^sub>f ostore_st, pad_to - used\<^sub>f ostore_st, bilbyFsPadByte))
            frm pad_to =
 buf_slice (wbuf\<^sub>f ostore_st) frm (used\<^sub>f ostore_st) @ padding (unat pad_to - unat (used\<^sub>f ostore_st))"
  using inv_ostore_sync_offsD[OF inv_ostore,simplified word_le_nat_alt]
      inv_ostore_buf_bound_eqD[OF inv_ostore]
      inv_ostore_used_len_wbufD[OF inv_ostore inv_mount_st]
 apply (subst buf_memset_eq[OF inv_ostore_bound_le_lenD[OF inv_ostore]])
  using used_le_padding_to[OF inv_ostore inv_mount_st]
  apply (simp add: pad_to)
  apply (subgoal_tac "unat (align32 (used\<^sub>f ostore_st, io_size\<^sub>f (super\<^sub>f mount_st))) \<le> length (\<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st)))")
   apply (subgoal_tac "0 < io_size\<^sub>f (super\<^sub>f mount_st)")
    apply (case_tac "frm = sync_offs\<^sub>f ostore_st")
     using inv_mount_st[simplified inv_mount_st_def Let_def] inv_ostore_used_no_overflowD[OF inv_ostore]
     apply (clarsimp simp add:  pad_to' buf_simps  wordarray_make  unat_arith_simps(4-5)
       min_absorb1 min_absorb2  align32_le[simplified word_le_nat_alt] padding_def)
    using frm inv_mount_st[simplified inv_mount_st_def Let_def] inv_ostore_used_no_overflowD[OF inv_ostore]
     apply (clarsimp simp add: buf_memset_eq pad_to' buf_simps  wordarray_make  unat_arith_simps(4-5)
       min_absorb1 min_absorb2  align32_le[simplified word_le_nat_alt] padding_def)
    using frm inv_mount_st[simplified inv_mount_st_def Let_def]
     apply (clarsimp, unat_arith)
  using align32_upper_bound inv_ostore_eb_size_wbuf_eqD[OF inv_ostore, symmetric] inv_mount_st
      inv_ostore_used_no_overflowD[OF inv_ostore]
  apply (simp only: unat_arith_simps, fastforce simp add: inv_mount_st_def Let_def)
 done


lemma inv_ostore_valid_list_trans_wbuf:
assumes inv_ostore: "inv_ostore mount_st ostore_st"
assumes used_gt_zero: "0 < used\<^sub>f ostore_st"
assumes sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
shows
  "valid_list_trans (buf_take (wbuf\<^sub>f  ostore_st) (used\<^sub>f ostore_st))"
  using inv_bufsD[OF inv_ostore, simplified used_gt_zero sync_lt_used]
     apply (clarsimp simp add: valid_list_trans_no_pad_def buf_slice_0_eq_buf_take)
  apply (simp add: buf_take_buf_slice_adjacent[OF order.strict_implies_order[OF sync_lt_used],symmetric])
  apply (erule (1)  valid_list_trans_append)
 done

lemma snd_list_trans_memset:
notes list_trans.simps[simp del]
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and     used_gt_zero: "0 < used\<^sub>f ostore_st"
  and     sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
  and     frm: "frm \<in> {0, (sync_offs\<^sub>f ostore_st)}"

  notes   pad_to' = pad_to[simplified padding_to_eq_align32_simp[OF inv_mount_st_no_summaryD[OF inv_mount_st]]]

shows
 "prod.snd (list_trans_no_pad
          (buf_slice (buf_memset (wbuf\<^sub>f ostore_st, used\<^sub>f ostore_st, pad_to - used\<^sub>f ostore_st, bilbyFsPadByte))
            frm pad_to)) =
 prod.snd (list_trans_no_pad (buf_slice (wbuf\<^sub>f ostore_st) frm (used\<^sub>f ostore_st)))"
proof -
 have sync_le_used: "sync_offs\<^sub>f ostore_st \<le> used\<^sub>f ostore_st" using sync_lt_used by unat_arith
show ?thesis
using buf_slice_buf_memset_is_append_padding[OF inv_ostore inv_mount_st pad_to, where frm=frm]
  apply simp
  apply (case_tac "frm = 0")
  using frm apply (simp add: buf_slice_0_eq_buf_take)
   apply (rule snd_list_trans_no_pad_padding_unchanged)
   apply (rule inv_ostore_valid_list_trans_wbuf[OF inv_ostore used_gt_zero sync_lt_used])
  using frm apply simp
  apply (rule snd_list_trans_no_pad_padding_unchanged)
  using inv_bufsD[OF inv_ostore, simplified sync_lt_used]
  apply (simp add: valid_list_trans_no_pad_def)
  done
qed

lemma ostore_log_objects_padding_bytes:
notes list_trans.simps [simp del]
assumes inv_ostore: "inv_ostore mount_st ostore_st"
assumes inv_mount_st: "inv_mount_st mount_st"
assumes pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
assumes padsz: "padsz = unat (used\<^sub>f ostore_st) - unat pad_to"
assumes used_gt_zero: "0 < used\<^sub>f ostore_st"
assumes sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
shows
 "ostore_log_objects (list_eb_log_wbuf (ostore_st \<lparr>wbuf\<^sub>f :=
    buf_memset (wbuf\<^sub>f ostore_st, used\<^sub>f ostore_st, pad_to - used\<^sub>f ostore_st, bilbyFsPadByte), used\<^sub>f := pad_to\<rparr>))
       =
    ostore_log_objects (list_eb_log_wbuf ostore_st)"
 (is "ostore_log_objects (list_eb_log_wbuf ?ostore_st) =
      ostore_log_objects (list_eb_log_wbuf ostore_st)")
proof -
  have len_eq: "length (list_eb_log_wbuf ?ostore_st) = length (list_eb_log_wbuf ostore_st)"
    by (simp add: list_eb_log_wbuf_def list_eb_log_def)
  have pad_to_gt_0: "pad_to > 0"
    using used_le_padding_to[OF inv_ostore inv_mount_st] pad_to used_gt_zero
    by unat_arith
  have pad_to': "pad_to =  align32 (used\<^sub>f ostore_st, io_size\<^sub>f (super\<^sub>f mount_st))"
  using pad_to by (simp add: padding_to_def[unfolded tuple_simps sanitizers] ostoreWriteNone_def)
  have val_xs: "valid_list_trans (buf_slice (wbuf\<^sub>f ostore_st) 0 (sync_offs\<^sub>f ostore_st))"
     using inv_bufsD[OF inv_ostore] used_gt_zero
     by (clarsimp simp: buf_slice_0_eq_buf_take valid_list_trans_no_pad_def)
  have val_ys: "valid_list_trans (buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st))"
     using inv_bufsD[OF inv_ostore] sync_lt_used
     by (clarsimp simp: valid_list_trans_no_pad_def)

  have sync_le_used: "sync_offs\<^sub>f ostore_st \<le> used\<^sub>f ostore_st" using sync_lt_used by simp

  have valid_list_trans_till_used: "valid_list_trans (buf_slice (wbuf\<^sub>f ostore_st) 0 (used\<^sub>f ostore_st))"
   using inv_bufsD[OF inv_ostore] used_gt_zero sync_lt_used
   apply (clarsimp simp add: unat_arith_simps  valid_list_trans_no_pad_def)
   using valid_list_trans_append[where xs="buf_take (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st)" and
     ys="buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st)"]
    buf_take_buf_slice_adjacent[OF sync_le_used]
   apply (simp add: buf_simps Let_def)
  done

  have snd_list_trans_no_pad:
    "prod.snd (list_trans_no_pad (buf_slice (wbuf\<^sub>f ostore_st) 0 (used\<^sub>f ostore_st))) \<noteq> []"
   using inv_bufsD[OF inv_ostore] used_gt_zero sync_lt_used
   apply (clarsimp simp add: unat_arith_simps  valid_list_trans_no_pad_def del: notI)
   apply (drule (1) list_trans_no_pad_append)
   apply (simp only: length_greater_0_conv[symmetric] buf_slice_0_eq_buf_take )
   using buf_take_buf_slice_adjacent[OF sync_le_used, where b="(wbuf\<^sub>f ostore_st)",symmetric]
   apply simp
   using list_trans_no_pad_append val_ys  by fastforce

  have buf_slice_not_Nil: "\<And>xs. buf_slice (wbuf\<^sub>f ostore_st) 0 (used\<^sub>f ostore_st)@ xs \<noteq> []"
   using inv_ostore_eb_size_wbuf_eqD[OF inv_ostore] inv_mount_st[simplified inv_mount_st_def Let_def] used_gt_zero
   by (clarsimp simp add:  buf_slice_def slice_def unat_arith_simps)
  have prod_eq: "\<And>x y z. x = (y,z) = (prod.fst x = y \<and> prod.snd x = z)" by auto
  have opt_eq: "\<And>i. i < length (list_eb_log_wbuf  ostore_st) \<Longrightarrow> (list_eb_log_wbuf ?ostore_st ! i) = [] = ((list_eb_log_wbuf ostore_st ! i) = [])"
   apply (simp add: list_eb_log_wbuf_def list_eb_log_def used_gt_zero  
            buf_slice_buf_memset_is_append_padding[OF inv_ostore
                        inv_mount_st pad_to, where frm=0, simplified])
   apply (case_tac "i \<noteq> unat (wbuf_eb\<^sub>f ostore_st)- unat bilbyFsFirstLogEbNum")
   using snd_list_trans_padding_unchanged[OF valid_list_trans_till_used, where n="(unat pad_to - unat (used\<^sub>f ostore_st))"]
          snd_list_trans_no_pad
   apply (simp add: list_trans_no_pad_def prod.case_eq_if)+
   done
  {
   fix i
   assume i_range: "i < length (list_eb_log_wbuf ostore_st)"
   and not_none: "list_eb_log_wbuf ostore_st ! i \<noteq> []"
   have "list_eb_log_wbuf ?ostore_st ! i = list_eb_log_wbuf ostore_st ! i"
   proof -
     have "list_eb_log_wbuf ?ostore_st ! i \<noteq> []"
      using opt_eq i_range not_none by simp
     thus ?thesis
     proof cases
       assume cur_eb: "i = unat (wbuf_eb\<^sub>f ostore_st) - unat bilbyFsFirstLogEbNum"
       have i_in_range: "i < length ((drop (unat bilbyFsFirstLogEbNum) (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))))"
         using inv_ubi_volD[OF inv_ostore, simplified inv_ubi_vol_def]  cur_eb
         inv_ostore[simplified inv_ostore_def] by unat_arith
       show ?thesis
       using i_in_range 
       apply (simp add: list_eb_log_wbuf_def list_eb_log_def  cur_eb)
       using buf_slice_buf_memset_is_append_padding[OF inv_ostore inv_mount_st pad_to, where frm=0, simplified]
       apply simp
       apply (rule snd_list_trans_no_pad_padding_unchanged[OF valid_list_trans_till_used])
       done
     next
       assume cur_eb: "i \<noteq> unat (wbuf_eb\<^sub>f ostore_st) - unat bilbyFsFirstLogEbNum"
       show ?thesis
         using cur_eb len_eq by - (clarsimp simp: buf_memset_eq wordarray_make list_eb_log_wbuf_def list_eb_log_def )
     qed
   qed
  } note list_eb_log_wbuf = this
  have "list_eb_log_wbuf ?ostore_st = list_eb_log_wbuf ostore_st"
   apply (simp add: list_eb_log_wbuf_def)
   using list_eb_log_wbuf
   apply (simp add: list_eb_log_wbuf_def)
   using snd_list_trans_memset[OF inv_ostore inv_mount_st pad_to used_gt_zero sync_lt_used, where frm=0, simplified ]
   apply (simp only:)
   done
  thus ?thesis
    unfolding ostore_log_objects_def by simp
qed

lemma inv_ostore_fsm_padding_bytes:
assumes inv_ostore: "inv_ostore mount_st ostore_st"
assumes inv_mount_st: "inv_mount_st mount_st"
assumes pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
assumes used_gt_zero: "0 < used\<^sub>f ostore_st"
assumes sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
shows
 "inv_ostore_fsm mount_st
     (ostore_st
      \<lparr>wbuf\<^sub>f := buf_memset (wbuf\<^sub>f ostore_st, used\<^sub>f ostore_st, pad_to - used\<^sub>f ostore_st, bilbyFsPadByte),
         used\<^sub>f := pad_to\<rparr>)"
(is "inv_ostore_fsm mount_st ?ostore_st")
proof -
  obtain padsz::nat where pad_sz: "padsz = unat (used\<^sub>f ostore_st) - unat pad_to" by simp
  have inv_fsm:"inv_ostore_fsm mount_st ostore_st" using inv_ostore_fsmD[OF inv_ostore] .
  {
    fix oid :: ObjId and gimnode :: GimNode\<^sub>T
    assume "oid \<in> dom (\<alpha>_fsm_gim (gim\<^sub>f (fsm_st\<^sub>f ?ostore_st)))"
    and  "(\<alpha>_fsm_gim $ gim\<^sub>f (fsm_st\<^sub>f ?ostore_st)) oid = option.Some gimnode"
    hence "unat (GimNode.count\<^sub>f gimnode) = (card {x \<in> set (ostore_log_objects (list_eb_log_wbuf ostore_st)).
                 oid_is_deleted_by (get_obj_oid x) oid}) = (unat (GimNode.count\<^sub>f gimnode) =
            card {x \<in> set (ostore_log_objects (list_eb_log_wbuf ?ostore_st)).
                  oid_is_deleted_by (get_obj_oid x) oid})
            "
    using ostore_log_objects_padding_bytes[OF inv_ostore inv_mount_st pad_to pad_sz used_gt_zero sync_lt_used] by simp
  } note gim_eq = this
 show ?thesis
  using inv_fsm unfolding inv_ostore_fsm_def by (fastforce simp: gim_eq dom_def)
qed

lemma prepare_wbuf_memset_\<alpha>_updates_eq:
  assumes inv: "inv_ostore mount_st ostore_st"
  and inv_mount_st: "inv_mount_st mount_st"
  and pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and sync_not_eq_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
  shows
  "\<alpha>_updates (ostore_st\<lparr>wbuf\<^sub>f := buf_memset (wbuf\<^sub>f ostore_st, used\<^sub>f ostore_st,  pad_to - used\<^sub>f ostore_st, bilbyFsPadByte), used\<^sub>f := pad_to\<rparr>) = \<alpha>_updates ostore_st"
  apply (simp add: \<alpha>_updates_def del: list_trans.simps)
  apply (rule arg_cong[where f="map ostore_update"])
  using buf_slice_buf_memset_is_append_padding[OF inv inv_mount_st,folded bilbyFsPadByte_def, where frm="(sync_offs\<^sub>f ostore_st)",simplified]
     pad_to[unfolded tuple_simps sanitizers, simplified padding_to_def Let_def ostoreWriteNone_def]
  apply (simp add:  padding_to_def Let_def ostoreWriteNone_def del: list_trans.simps)
  apply (drule meta_spec[where x=pad_to])
  apply (simp del: list_trans.simps)
  apply (rule snd_list_trans_no_pad_padding_unchanged)
  using inv_bufsD[OF inv] sync_not_eq_used
  apply (clarsimp simp add: valid_list_trans_no_pad_def)
 done

definition
  buf_prepared :: "OstoreState\<^sub>T \<Rightarrow> U32 \<Rightarrow> U32 \<Rightarrow> Obj\<^sub>T \<Rightarrow> U8 list"
where
 "buf_prepared ostore_st pad_from pad_to pobj \<equiv>
   if pad_to - pad_from < bilbyFsObjHeaderSize then
     buf_memset' (wbuf\<^sub>f ostore_st) pad_from (pad_to - pad_from) bilbyFsPadByte
   else
     buf_sub_slice (wbuf\<^sub>f ostore_st) pad_from pad_to (sObj pobj)"

lemma buf_prepared_n_n:
 "buf_prepared ostore_st n n pobj = (\<alpha>wa $ data\<^sub>f $ wbuf\<^sub>f ostore_st)"
  by (simp add: buf_prepared_def bilbyFsObjHeaderSize_def buf_sub_slice_def buf_simps padding_def)

definition
  prepared_pad_obj_no_crc :: "OstoreState\<^sub>T \<Rightarrow> U32 \<Rightarrow> Obj\<^sub>T"
where
 "prepared_pad_obj_no_crc ostore_st pad_to \<equiv>
   opad\<^sub>f ostore_st
       \<lparr>Obj.sqnum\<^sub>f := OstoreState.next_sqnum\<^sub>f ostore_st,
        Obj.len\<^sub>f := pad_to - used\<^sub>f ostore_st,
        trans\<^sub>f := bilbyFsTransCommit \<rparr>"

definition
  prepared_pad_obj :: "OstoreState\<^sub>T \<Rightarrow> U32 \<Rightarrow> U32 \<Rightarrow> Obj\<^sub>T"
where
 "prepared_pad_obj ostore_st pad_to crc \<equiv>
  let opad = prepared_pad_obj_no_crc ostore_st pad_to
  in  opad \<lparr> crc\<^sub>f := crc \<rparr>"

lemma padding_to_io_size_no_overflow:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and inv_mount_st: "inv_mount_st mount_st"

  notes pad_simps = padding_to_def[unfolded tuple_simps sanitizers] ostoreWriteNone_def

  shows
 "padding_to (mount_st, ostore_st, ostoreWriteNone)
    < padding_to (mount_st, ostore_st, ostoreWriteNone) + io_size\<^sub>f (super\<^sub>f mount_st)"
proof -
  have pad_to_le_max_eb_sz: "padding_to (mount_st, ostore_st, ostoreWriteNone) \<le> bilbyFsMaxEbSize"
  using align32_upper_bound[where v="used\<^sub>f ostore_st" and al="io_size\<^sub>f (super\<^sub>f mount_st)" and bound="eb_size\<^sub>f (super\<^sub>f mount_st)"]
        inv_ostore_eb_size_wbuf_eqD[OF inv_ostore]
        inv_mount_st[simplified inv_mount_st_def Let_def]
        inv_ostore_usedD[OF inv_ostore]
        inv_ostore_used_no_overflowD[OF inv_ostore]
     by (clarsimp simp: pad_simps) unat_arith

  have iosz_gt_0: "0 < io_size\<^sub>f (super\<^sub>f mount_st)"
  and  iosz_lt_max_eb_sz: "io_size\<^sub>f (super\<^sub>f mount_st) \<le> bilbyFsMaxEbSize"
    using inv_mount_st[simplified inv_mount_st_def Let_def]
    by (clarsimp, unat_arith)+

  have "bilbyFsMaxEbSize < bilbyFsMaxEbSize + io_size\<^sub>f (super\<^sub>f mount_st)"
   using  iosz_lt_max_eb_sz and iosz_gt_0
   by (simp add: unat_arith_simps bilbyFsMaxEbSize_def)
  thus ?thesis
  using pad_to_le_max_eb_sz by (simp add: pad_simps) unat_arith
qed

lemma buf_memset_bound_eq:
   "unat (buf_bound buf) \<le> length (\<alpha>wa (data\<^sub>f buf)) \<Longrightarrow>
    offs \<le> offs + len \<Longrightarrow> buf_bound (buf_memset (buf, offs, len, v)) = buf_bound buf"
  apply (subst buf_memset_eq[OF])
apply (simp add: buf_bound_def)+
done

lemma inv_ostore_padding_bytes_preserved:
assumes inv_ostore: "inv_ostore mount_st ostore_st"
assumes inv_mount_st: "inv_mount_st mount_st"
assumes pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
assumes used_gt_zero: "0 < used\<^sub>f ostore_st"
assumes sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
shows "inv_ostore mount_st (ostore_st \<lparr>wbuf\<^sub>f :=buf_memset(wbuf\<^sub>f ostore_st, used\<^sub>f ostore_st, pad_to - used\<^sub>f ostore_st, bilbyFsPadByte), used\<^sub>f := pad_to\<rparr>)"
  (is "inv_ostore mount_st ?ostore_st")
proof -
  have pad_to': "pad_to =  align32 (used\<^sub>f ostore_st, io_size\<^sub>f (super\<^sub>f mount_st))"
    using pad_to by (simp add: padding_to_def[unfolded tuple_simps sanitizers] ostoreWriteNone_def)
  have "sync_offs\<^sub>f ostore_st \<le> padding_to (mount_st, ostore_st, ostoreWriteNone)"
   using  sync_offs_le_padding_to[OF inv_ostore inv_mount_st ] .
  moreover have "eb_size\<^sub>f (super\<^sub>f mount_st) = buf_length (wbuf\<^sub>f ?ostore_st)"
  apply (simp add: pad_to)
  apply (subst buf_memset_length_eq[OF inv_ostore_bound_le_lenD[OF inv_ostore]])
    apply simp
    using used_le_padding_to[OF inv_ostore inv_mount_st] apply simp
   using inv_ostore by (fastforce simp: buf_memset_length_eq  inv_ostore_def )
  moreover have "inv_ostore_summary mount_st ?ostore_st"
    by (simp add: inv_ostore_summary_def)
  moreover have "inv_ostore_index mount_st ?ostore_st"
    by (rule inv_ostore_index_padding_bytes[OF inv_ostore inv_mount_st pad_to])
  moreover have "inv_ostore_index_gim_disjoint ?ostore_st"
    using inv_ostore by (clarsimp simp: inv_ostore_def inv_ostore_index_gim_disjoint_def) 
  moreover have "inv_ostore_fsm mount_st ?ostore_st" 
    using inv_ostore_fsm_padding_bytes[OF inv_ostore inv_mount_st pad_to used_gt_zero sync_lt_used] .
  moreover hence "buf_bound (wbuf\<^sub>f ?ostore_st) = buf_length (wbuf\<^sub>f ?ostore_st)"
  apply (simp add: pad_to)
  apply (subst buf_memset_length_eq[OF inv_ostore_bound_le_lenD[OF inv_ostore], simplified ])
   using used_le_padding_to[OF inv_ostore inv_mount_st]
    apply simp
  apply (subst buf_memset_bound_eq)
  using inv_ostore_bound_le_lenD[OF inv_ostore] apply (simp add: buf_simps)
  apply simp
   using used_le_padding_to[OF inv_ostore inv_mount_st]
    apply simp


using inv_ostore
   by (fastforce  simp add:   inv_ostore_def buf_simps intro: )
  moreover have inv_bufs: "inv_bufs mount_st ?ostore_st" 
    using inv_ostore apply (clarsimp simp: inv_ostore_def inv_bufs_def Let_def)
    apply (rule conjI)

    apply (subst buf_memset_eq)
         using inv_ostore_bound_le_lenD[OF inv_ostore] apply (simp add: buf_simps)
    using used_le_padding_to[OF inv_ostore inv_mount_st] apply (simp add: pad_to)

    apply (simp add: buf_simps )
    using inv_ostore_sync_offsD[OF inv_ostore,simplified word_le_nat_alt]
      inv_ostore_buf_bound_eqD[OF inv_ostore]
      inv_ostore_used_len_wbufD[OF inv_ostore inv_mount_st]
      inv_ostore_eb_size_wbuf_eqD[OF inv_ostore]
    apply (simp add: min_absorb1 min_absorb2 inv_mount_st inv_mount_st_def
        Let_def wordarray_make)
    using buf_slice_buf_memset_is_append_padding[OF inv_ostore inv_mount_st pad_to, where frm="sync_offs\<^sub>f ostore_st"]
     using inv_ostore_bound_le_lenD[OF inv_ostore] apply (simp add: )
    using used_le_padding_to[OF inv_ostore inv_mount_st]
    apply (simp add: pad_to )
    apply (rule padding_to_ret, simp add: ostoreWriteNone_def )
    using inv_mount_st[simplified Let_def inv_mount_st_def]
    apply clarsimp
    apply (drule align32_le[where v="used\<^sub>f ostore_st" and al="io_size\<^sub>f (super\<^sub>f mount_st)"])
     using inv_ostore_used_no_overflowD[OF inv_ostore] apply simp
    apply (rule conjI)
     apply (rule impI)
     apply (rule valid_list_trans_no_pad_append_padding)
     apply (erule (1) impE[OF _  sync_lt_used])
    apply (erule impE[OF _  used_gt_zero])
    apply (simp only: buf_slice_0_eq_buf_take[symmetric])
    apply (subst  buf_slice_out_of_buf_memset)
         apply simp
        apply simp
       using used_le_padding_to[OF inv_ostore inv_mount_st] apply fastforce
      using inv_ostore_usedD[OF inv_ostore]
            inv_ostore_wbuf_boundD[OF inv_ostore]
            apply (simp add: buf_simps)
     using inv_ostore_usedD[OF inv_ostore]
           inv_ostore_wbuf_boundD[OF inv_ostore]
           inv_ostore_eb_size_wbuf_eqD[OF inv_ostore]
           apply (fastforce simp add: buf_simps)
   apply simp
     apply (clarsimp simp: sync_lt_used valid_list_trans_no_pad_def)
     apply (simp add: snd_list_trans_no_pad_padding_unchanged)
   done
   moreover have get_obj_eq:
    "\<And>v. is_valid_addr mount_st ostore_st v \<Longrightarrow>
      ostore_get_obj ?ostore_st v = ostore_get_obj ostore_st  v"
     using prepare_memset_get_obj_eq[OF inv_ostore inv_mount_st pad_to] .

   hence runtime_eq: "\<alpha>_ostore_runtime ?ostore_st = \<alpha>_ostore_runtime ostore_st"
    using inv_ostore_indexD[OF inv_ostore]
    by (fastforce simp add: \<alpha>_ostore_runtime_def option.case_eq_if inv_ostore_index_def Let_def)

   have \<alpha>_updates_eq: "\<alpha>_updates ?ostore_st = \<alpha>_updates ostore_st"
    using prepare_wbuf_memset_\<alpha>_updates_eq[OF inv_ostore inv_mount_st pad_to sync_lt_used] .
   have \<alpha>_ostore_medium_eq: "\<alpha>_ostore_medium ?ostore_st = \<alpha>_ostore_medium ostore_st"
    by (simp add: \<alpha>_ostore_medium_def abstract_mount_\<alpha>_ostore_def Let_def list_eb_log_def)
   then have uptodate_eq: "\<alpha>_ostore_uptodate ?ostore_st = \<alpha>_ostore_uptodate ostore_st"
    by (simp add: \<alpha>_ostore_medium_eq \<alpha>_updates_eq \<alpha>_ostore_uptodate_def)
  moreover have "\<alpha>_ostore_runtime ?ostore_st = \<alpha>_ostore_uptodate ?ostore_st"
   using inv_ostore
   by (simp add: runtime_eq uptodate_eq inv_ostore_def)
  moreover have "pad_to  \<le> buf_length (wbuf\<^sub>f ?ostore_st)"
    using inv_mount_st[simplified inv_mount_st_def Let_def]
      inv_ostore[simplified inv_ostore_def]
    using align32_upper_bound[where v="used\<^sub>f ostore_st" and al="io_size\<^sub>f (super\<^sub>f mount_st)" and bound="eb_size\<^sub>f (super\<^sub>f mount_st)"]
    inv_ostore[simplified inv_ostore_def]  inv_mount_st[simplified Let_def inv_mount_st_def]
    inv_ostore_eb_size_wbuf_eqD[OF inv_ostore]
    apply (simp add: pad_to')
    apply (subst buf_memset_length_eq)
         using inv_ostore_bound_le_lenD[OF inv_ostore] apply (simp add: buf_simps)
    using used_le_padding_to[OF inv_ostore inv_mount_st] apply (simp add: pad_to' pad_to padding_to_def[unfolded tuple_simps sanitizers] ostoreWriteNone_def)
   by (clarsimp simp: pad_to' buf_memset_length_eq)
  moreover have "inv_log (list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ?ostore_st))) (prod.snd (list_trans_no_pad
     (buf_slice (buf_memset (wbuf\<^sub>f ostore_st, used\<^sub>f ostore_st, pad_to - used\<^sub>f ostore_st, bilbyFsPadByte)) (sync_offs\<^sub>f ostore_st) pad_to)))"
     using snd_list_trans_no_pad_padding_unchanged
     using snd_list_trans_memset[OF inv_ostore inv_mount_st pad_to used_gt_zero sync_lt_used, where frm="sync_offs\<^sub>f ostore_st",simplified]
     apply simp
     using inv_logD[OF inv_ostore, folded inv_log_def] by simp

  moreover have "used\<^sub>f ?ostore_st < used\<^sub>f ?ostore_st + io_size\<^sub>f (super\<^sub>f mount_st)"
    using padding_to_io_size_no_overflow[OF inv_ostore inv_mount_st]
    by (clarsimp simp: inv_ostore_def pad_to)
    

  ultimately show ?thesis
    using inv_ostore by (clarsimp simp: pad_to inv_ostore_def inv_bufs inv_flash_def)
qed

lemma take_n_m_padding:
 "m \<le> n \<Longrightarrow> n \<le> length xs \<Longrightarrow> 
  take n (take m xs @ padding (n - m) @ ys) = take m xs @ padding (n - m)"
 by (simp add: min_absorb1 min_absorb2 padding_def )
 
lemma safe_add64:
  assumes err: "a > a + b \<Longrightarrow> P (Error ())"
  and     suc: "a \<le> a+b \<Longrightarrow> P (Success (a+b))"
  shows
   "P (safe_add64 (a,b))"
 unfolding safe_add64_def[unfolded tuple_simps sanitizers]
  apply (simp add: Let_def)
  apply safe
    apply (rule err, simp)
   apply (rule err)
(* FIX Cogent code only one check is needed *)
   apply (unat_arith)
  apply (rule suc)
  apply unat_arith
 done

lemmas ElemX_simps = ElemA.defs ElemAO.defs ElemB.defs

lemma fsm_mark_ebnum_dirty:
  assumes inv_fsm_st: "inv_fsm_st mount_st fsm_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     ebnum_range: "ebnum \<ge> bilbyFsFirstLogEbNum \<and> ebnum < nb_eb\<^sub>f (super\<^sub>f mount_st)"
  and     suc: "P (fsm_st
       \<lparr>dirty_space\<^sub>f :=
          WordArrayT.make
           ((\<alpha>wa (dirty_space\<^sub>f fsm_st))[unat ebnum := \<alpha>wa (dirty_space\<^sub>f fsm_st) ! unat ebnum + len])\<rparr>)"
  shows
  "P (fsm_mark_ebnum_dirty (fsm_st, ebnum, len))"
  unfolding fsm_mark_ebnum_dirty_def[unfolded tuple_simps sanitizers]
  apply (simp add: )
  apply (rule wordarray_modify_ret)
  using inv_fsm_st[simplified inv_fsm_st_def] ebnum_range apply (clarsimp, unat_arith)
  apply (simp add: suc  ArrA.make_def wordarray_make 
        mark_dirty_modifier_def[unfolded tuple_simps sanitizers] ElemX_simps)
 done

lemma fsm_mark_dirty_ret: (* This a specialise lemma for fsm_mark_diry when oid = nilObjId
 *)
  assumes inv_fsm_st: "inv_fsm_st mount_st fsm_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     ebnum_range: "ebnum\<^sub>f oaddr \<ge> bilbyFsFirstLogEbNum \<and> ebnum\<^sub>f oaddr < nb_eb\<^sub>f (super\<^sub>f mount_st)"
  and     suc: "\<And>ex. P(ex, fsm_st
          \<lparr>dirty_space\<^sub>f :=
             WordArrayT.make
              ((\<alpha>wa (dirty_space\<^sub>f fsm_st))
               [unat (ObjAddr.ebnum\<^sub>f oaddr) :=
                  \<alpha>wa (dirty_space\<^sub>f fsm_st) ! unat (ObjAddr.ebnum\<^sub>f oaddr) + ObjAddr.len\<^sub>f oaddr])\<rparr>,
          gimpool)"
  shows
  "P (fsm_mark_dirty (ex, mount_st, fsm_st, gimpool, nilObjId, oaddr))"
  unfolding fsm_mark_dirty_def[unfolded tuple_simps sanitizers]
  apply (simp add:)
  apply (rule fsm_mark_ebnum_dirty[OF inv_fsm_st inv_mount_st])
   using ebnum_range apply (simp)
  using ebnum_range apply (simp add: nilObjId_def Let_def suc[where ex=ex])
done

lemma offs_pl_padding_to_le_eb_size:
 assumes inv_ostore: "inv_ostore mount_st ostore_st"
 and inv_mount_st: "inv_mount_st mount_st"
 and sync_neq_used: "sync_offs\<^sub>f ostore_st \<noteq> used\<^sub>f ostore_st"
 and var: "var \<in> {sync_offs\<^sub>f ostore_st, used\<^sub>f ostore_st}"
 shows
 "unat var + unat (padding_to (mount_st, ostore_st, ostoreWriteNone) - var)
         \<le> unat (eb_size\<^sub>f (super\<^sub>f mount_st))"
proof -
  have pow_of_2: "is_pow_of_2 (io_size\<^sub>f (super\<^sub>f mount_st))"
    using inv_mount_st by (simp add: inv_mount_st_def Let_def)

  have not_0: "0 < io_size\<^sub>f (super\<^sub>f mount_st)"
    using inv_mount_st by (simp add: inv_mount_st_def Let_def) unat_arith

  have iosize_dvd_ebsize: "io_size\<^sub>f (super\<^sub>f mount_st) udvd eb_size\<^sub>f (super\<^sub>f mount_st)"
    using inv_mount_st by (simp add: inv_mount_st_def Let_def)
  show ?thesis
  using inv_ostore_usedD[OF inv_ostore] iosize_dvd_ebsize
        align32_ge[OF pow_of_2 , where v="used\<^sub>f ostore_st"]
        align32_upper_bound[OF _ pow_of_2, where v="used\<^sub>f ostore_st" and bound="eb_size\<^sub>f  (super\<^sub>f mount_st)"]
        inv_ostore_sync_offsD[OF inv_ostore] inv_ostore_used_no_overflowD[OF inv_ostore]
  apply (case_tac "var = sync_offs\<^sub>f ostore_st", simp_all  add: var padding_to_def[unfolded tuple_simps sanitizers] ostoreWriteNone_def)
  using var
  by unat_arith+
qed


definition
  prepared_fsm_padding_obj :: "OstoreState\<^sub>T \<Rightarrow> U32 \<Rightarrow> FsmState\<^sub>T"
where
 "prepared_fsm_padding_obj ostore_st pad_to \<equiv>
   if \<not> (pad_to - used\<^sub>f ostore_st < bilbyFsObjHeaderSize) then
    fsm_st\<^sub>f ostore_st \<lparr>dirty_space\<^sub>f :=
      WordArrayT.make ((\<alpha>wa (dirty_space\<^sub>f (fsm_st\<^sub>f ostore_st)))
      [unat (wbuf_eb\<^sub>f ostore_st) := \<alpha>wa (dirty_space\<^sub>f (fsm_st\<^sub>f ostore_st)) ! unat (wbuf_eb\<^sub>f ostore_st)
        + (pad_to - used\<^sub>f ostore_st)])\<rparr>
  else fsm_st\<^sub>f ostore_st"

lemma update_obj_pad_ret:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     oaddr_range: "bilbyFsFirstLogEbNum \<le> ObjAddr.ebnum\<^sub>f oaddr \<and> ObjAddr.ebnum\<^sub>f oaddr < nb_eb\<^sub>f (super\<^sub>f mount_st)"
  and     suc: "\<And>ex v. P (ex, ostore_st
   \<lparr>fsm_st\<^sub>f := fsm_st\<^sub>f ostore_st
      \<lparr>dirty_space\<^sub>f :=
         WordArrayT.make
          ((\<alpha>wa (dirty_space\<^sub>f (fsm_st\<^sub>f ostore_st)))
           [unat (ebnum\<^sub>f oaddr) := \<alpha>wa (dirty_space\<^sub>f (fsm_st\<^sub>f ostore_st)) ! unat (ebnum\<^sub>f oaddr) +
              ObjAddr.len\<^sub>f oaddr])\<rparr>,
      OstoreState.oaddr\<^sub>f :=v\<rparr>)"
  shows
  "P (update_obj_pad (ex, mount_st, ostore_st, oaddr))"
 unfolding update_obj_pad_def[unfolded tuple_simps sanitizers, folded nilObjId_def]
  apply (simp add:)
  apply (rule fsm_mark_dirty_ret[OF _ inv_mount_st])
     using inv_fsm_stD[OF inv_ostore] apply (simp add: inv_fsm_st_def)
    using inv_ostore[simplified  inv_ostore_def] apply (simp)
   using  oaddr_range apply simp
  apply simp
  apply (rule suc)
 done

lemma ostore_get_obj_eq_padding_obj:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and inv_mount_st: "inv_mount_st mount_st"
  and pad_to: "pad_to = padding_to (mount_st, ostore_st, osw)"
  shows
  "\<And>v. is_valid_addr mount_st ostore_st v \<Longrightarrow>
    ostore_get_obj (ostore_st \<lparr>wbuf\<^sub>f := wbuf\<^sub>f ostore_st
            \<lparr>data\<^sub>f := WordArrayT.make (buf_sub_slice (wbuf\<^sub>f ostore_st) (used\<^sub>f ostore_st) pad_to (sObj obj'))\<rparr>,
             opad\<^sub>f := obj', used\<^sub>f := pad_to,
             OstoreState.next_sqnum\<^sub>f := OstoreState.next_sqnum\<^sub>f ostore_st + 1,
              fsm_st\<^sub>f := fsm_st, OstoreState.oaddr\<^sub>f:= oaddr\<rparr>) v = ostore_get_obj ostore_st  v"
  apply (clarsimp simp: ostore_get_obj_def)
  apply (rule_tac f="\<lambda>x. pObj x (ObjAddr.offs\<^sub>f v)" in arg_cong)
  apply (rule_tac m="unat $ used\<^sub>f ostore_st" in take_eq_strenghen)
   using wordarray_length_ret[where arr="data\<^sub>f (wbuf\<^sub>f ostore_st)", symmetric]
        inv_ostore_wbuf_boundD[OF inv_ostore]
        inv_ostore_usedD[OF inv_ostore]
        inv_ostore_wbuf_lengthD[OF inv_ostore ]
        inv_mount_st[simplified inv_mount_st_def]
   unfolding is_valid_addr_def
   apply (clarsimp simp: wordarray_make pad_to buf_length_def )
   apply (subst take_n_buf_sub_slice_n)
    apply unat_arith
   apply simp
  apply unat_arith
 done

lemma inv_ostore_index_padding_obj:
assumes inv_ostore: "inv_ostore mount_st ostore_st"
and inv_mount_st: "inv_mount_st mount_st"
and pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
shows
"inv_ostore_index mount_st
  (ostore_st \<lparr>wbuf\<^sub>f := wbuf\<^sub>f ostore_st
         \<lparr>data\<^sub>f := WordArrayT.make (buf_sub_slice (wbuf\<^sub>f ostore_st) (used\<^sub>f ostore_st) pad_to (sObj obj'))\<rparr>,
         opad\<^sub>f := obj', used\<^sub>f := pad_to,
         OstoreState.next_sqnum\<^sub>f := OstoreState.next_sqnum\<^sub>f ostore_st + 1,
         fsm_st\<^sub>f := fsm_st,
         OstoreState.oaddr\<^sub>f := oaddr\<rparr>)"
 (is "inv_ostore_index mount_st ?ostore_st")
proof -
   have index_unchanged:
     "index_st\<^sub>f ?ostore_st = index_st\<^sub>f ostore_st" by simp
   also have inv_ostore_index:
     "inv_ostore_index mount_st ostore_st"
     using inv_ostore by (simp add: inv_ostore_def)
   moreover have pad_to_ge_used:
     "used\<^sub>f ostore_st \<le> pad_to"
     by (subst pad_to, rule used_le_padding_to[OF inv_ostore inv_mount_st])
   moreover have is_valid_addr:
     "\<And>v. is_valid_addr mount_st ostore_st v \<Longrightarrow>
            is_valid_addr mount_st ?ostore_st v"
     apply (clarsimp simp: is_valid_addr_def pad_to)
     apply (case_tac "used\<^sub>f ostore_st = eb_size\<^sub>f (super\<^sub>f mount_st)")
      apply (erule (1) padding_to_eb_fullE[OF inv_ostore inv_mount_st])
     apply (cut_tac used_le_padding_to[OF inv_ostore inv_mount_st])
     apply (unat_arith)
    done
   moreover have get_obj_eq:
    "\<And>v. is_valid_addr mount_st ostore_st v \<Longrightarrow>
      ostore_get_obj ?ostore_st v = ostore_get_obj ostore_st  v"
     using ostore_get_obj_eq_padding_obj[OF inv_ostore inv_mount_st pad_to,
          where fsm_st=fsm_st and oaddr=oaddr] by simp

  ultimately show ?thesis
   unfolding inv_ostore_index_def
    by (clarsimp simp: Let_def)
qed

lemmas ostore_update_padding_obj' = ostore_update_padding_obj_def[unfolded tuple_simps sanitizers]

lemma snd_list_trans_sObj_eq_sObj:
  assumes valid_obj: "valid_pad_obj obj"
  notes Obj_inverse[where xs=Nil, simplified, simp]
  shows
 "valid_list_trans (sObj obj) \<Longrightarrow>
   prod.snd (list_trans (sObj obj)) = [[obj]]"
   using valid_obj apply (clarsimp simp: valid_pad_obj_def  simp del: list_trans.simps)
  apply (erule valid_list_trans.elims)
  apply (clarsimp split: if_splits)
   apply (erule valid_trans.elims)
   apply (rename_tac x xs)
   apply (drule sym[where s="sObj obj"], clarsimp simp add: Let_def is_valid_ObjTrans split:if_splits)
    using is_valid_ObjHeader_length_sObj[OF valid_obj]
    apply (drule_tac t="x#xs" in sym, simp)
   apply (drule_tac t="x#xs" in sym, simp)
   apply (frule is_valid_ObjHeader_length_sObj[OF valid_obj], simp)
  apply (erule valid_trans.elims, clarsimp simp add: is_valid_ObjTrans split: if_splits)
   apply (rename_tac x xs)
   apply (drule_tac t="x#xs" in sym, simp)
   apply (frule is_valid_ObjHeader_length_sObj[OF valid_obj], simp)
  apply (rename_tac x xs)
  apply (drule_tac t="x#xs" in sym, simp)
  apply (frule is_valid_ObjHeader_length_sObj[OF valid_obj], simp)
 done


lemma valid_commit_pad_obj:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and     obj: "\<exists>crc. obj = ostore_update_padding_obj
        (opad\<^sub>f ostore_st, OstoreState.next_sqnum\<^sub>f ostore_st,
         pad_to - used\<^sub>f ostore_st - bilbyFsObjHeaderSize)
       \<lparr>crc\<^sub>f :=crc\<rparr>"
  and     padding_obj: "\<not> (pad_to - used\<^sub>f ostore_st < bilbyFsObjHeaderSize)"
 shows
  "is_valid_ObjCommit obj (sObj obj)"
    using obj
    apply (clarsimp simp: is_valid_ObjTrans)
    apply safe
     apply (erule ssubst)
     apply (simp add: is_valid_ObjHeader_def )

     using  inv_opadD[OF inv_ostore]
           inv_ostore_eb_size_wbuf_eqD[OF inv_ostore] inv_mount_st[simplified inv_mount_st_def Let_def] 
     apply (clarsimp simp: ostore_update_padding_obj' buf_sub_slice_length bilbyFsTransCommit_def)
     apply (rule conjI)
      apply (subst length_sObj)
      using obj apply clarsimp
       apply (drule arg_cong[ where f=Obj.len\<^sub>f, simplified ostore_update_padding_obj' Let_def prod.case_eq_if])
       using padding_obj
       apply (simp add: bilbyFsObjHeaderSize_def) 
      using padding_obj
      apply (clarsimp simp add: bilbyFsObjHeaderSize_def)
     apply (simp add: is_valid_Obj_def)
    apply (simp)
   apply (simp add: is_len_and_type_ok_def otype_simps)
   using padding_obj apply (simp add: bilbyFsObjHeaderSize_def )
  using inv_opadD[OF inv_ostore]
  apply (subst  Obj_inverse[where xs=Nil, simplified])
     apply (clarsimp simp: ostore_update_padding_obj'
            Obj_inverse[where xs=Nil, simplified] bilbyFsTransCommit_def is_valid_Obj_def)+
 done

lemma snd_list_trans_no_pad_padding_obj:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and     sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
  and     obj: "\<exists>crc. obj = ostore_update_padding_obj
        (opad\<^sub>f ostore_st, OstoreState.next_sqnum\<^sub>f ostore_st,
         pad_to - used\<^sub>f ostore_st - bilbyFsObjHeaderSize)
       \<lparr>crc\<^sub>f :=crc\<rparr>"
  and     padding_obj: "\<not> (pad_to - used\<^sub>f ostore_st < bilbyFsObjHeaderSize)"
  and     valid_list_trans_pad_obj: "valid_list_trans (sObj obj)"

  notes   pad_to' = pad_to[simplified padding_to_eq_align32_simp[OF inv_mount_st_no_summaryD[OF inv_mount_st]]]
  shows
   "prod.snd (list_trans_no_pad
          (buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st) @
           sObj obj)) =
    prod.snd (list_trans_no_pad
          (buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st)))"
    using obj length_sObj[where obj=obj]  apply (simp add: ostore_update_padding_obj' )
     apply (erule meta_impE)
      apply (fold bilbyFsObjHeaderSize_def)
      using padding_obj apply clarsimp
       apply (drule arg_cong[where f="Obj.len\<^sub>f"], simp)
     apply (subst list_trans_no_pad_append[symmetric])
       using inv_bufsD[OF inv_ostore, simplified sync_lt_used] apply (simp add: valid_list_trans_no_pad_def)
      using valid_list_trans_pad_obj  apply (simp add: obj ostore_update_padding_obj')
     using snd_list_trans_sObj_eq_sObj[OF _ valid_list_trans_pad_obj]
           inv_opadD[OF inv_ostore]
           inv_ostore_valid_pad_objD[OF inv_ostore] 
      apply (simp add: obj ostore_update_padding_obj' list_trans_no_pad_def 
                        prod.case_eq_if valid_pad_obj_def is_valid_Obj_def
                  del:list_trans.simps)
       apply clarsimp
     done

lemma  len_sObj:
 assumes valid_hdr:  "is_valid_ObjHeader obj (sObj obj)"
  and     obj: "\<exists>crc. obj = ostore_update_padding_obj
        (opad\<^sub>f ostore_st, OstoreState.next_sqnum\<^sub>f ostore_st,
         pad_to - used\<^sub>f ostore_st - bilbyFsObjHeaderSize)
       \<lparr>crc\<^sub>f :=crc\<rparr>"
  and   valid_pad_obj: "valid_pad_obj obj"
 shows
  "unat (pad_to - used\<^sub>f ostore_st) = length (sObj obj)"
     using is_valid_ObjHeader_len_facts[OF valid_hdr] valid_pad_obj apply (clarsimp simp: is_valid_ObjHeader_def valid_pad_obj_def length_sObj )
     using obj apply clarsimp
     apply (drule arg_cong[where f="Obj.len\<^sub>f"])
     apply (simp add: ostore_update_padding_obj' bilbyFsObjHeaderSize_def)
    done

lemma len_sObj':
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and     valid_hdr:  "is_valid_ObjHeader obj (sObj obj)"
  and     obj: "\<exists>crc. obj = ostore_update_padding_obj
        (opad\<^sub>f ostore_st, OstoreState.next_sqnum\<^sub>f ostore_st,
         pad_to - used\<^sub>f ostore_st - bilbyFsObjHeaderSize)
       \<lparr>crc\<^sub>f :=crc\<rparr>"
  and   valid_pad_obj: "valid_pad_obj obj"
 shows
 "unat pad_to - unat (used\<^sub>f ostore_st) = length (sObj obj)"
 using len_sObj[OF valid_hdr obj valid_pad_obj] used_le_padding_to[OF inv_ostore inv_mount_st] pad_to
  by (clarsimp simp: valid_pad_obj_def) unat_arith

lemma valid_list_trans_pad_obj: 
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and     sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
  and     obj: "\<exists>crc. obj = ostore_update_padding_obj
        (opad\<^sub>f ostore_st, OstoreState.next_sqnum\<^sub>f ostore_st,
         pad_to - used\<^sub>f ostore_st - bilbyFsObjHeaderSize)
       \<lparr>crc\<^sub>f :=crc\<rparr>"
  and   valid_pad_obj: "valid_pad_obj obj"
  and     padding_obj: "\<not> (pad_to - used\<^sub>f ostore_st < bilbyFsObjHeaderSize)"

  notes   pad_to' = pad_to[simplified padding_to_eq_align32_simp[OF inv_mount_st_no_summaryD[OF inv_mount_st]]]
  and     invs_pad_to = inv_ostore inv_mount_st pad_to
  and     padding_obj_unat = padding_obj[simplified word_less_nat_alt]
  and    valid_commit_pad_obj = valid_commit_pad_obj[OF invs_pad_to obj padding_obj]
  and    valid_hdr = valid_commit_pad_obj[OF invs_pad_to obj padding_obj, simplified is_valid_ObjTrans, THEN conjunct1]
  shows
  "valid_list_trans (sObj obj)"
  using obj
  apply clarify
  apply (drule sym[where s=obj], simp)
  apply (drule arg_cong[where f=Obj.len\<^sub>f])
  apply (simp add: ostore_update_padding_obj')
  apply (case_tac "sObj obj")
   using is_valid_ObjHeader_length_sObj[OF valid_pad_obj] valid_commit_pad_obj[simplified is_valid_ObjTrans]
        padding_obj_unat
   apply (clarsimp simp add: bilbyFsObjHeaderSize_def)
   apply simp
  apply (drule sym[where s="sObj obj" ], simp)
  using is_valid_ObjCommit_trans_len[OF valid_pad_obj valid_commit_pad_obj]
  using is_valid_ObjHeader_length_sObj[OF valid_pad_obj valid_hdr] obj
  apply (clarsimp simp: ostore_update_padding_obj')
   apply (drule arg_cong[where f=Obj.len\<^sub>f])
   apply simp
   apply (simp add: bilbyFsObjHeaderSize_def)
  apply (simp add: no_pad_Nil)
  apply (drule sym[where t="sObj obj"])
  apply (simp only:)
  apply (subst valid_trans.simps)
  apply (drule sym[where s="sObj obj"])
  using valid_pad_obj[simplified valid_pad_obj_def] valid_commit_pad_obj Obj_inverse[where xs=Nil, simplified, where obj=obj, symmetric]
  apply (simp add: is_valid_ObjTrans)
 done

lemma valid_list_trans_buf_take_sync_offs:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and     used_gt_zero: "0 < used\<^sub>f ostore_st"
  and     sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"

  shows
   "valid_list_trans (buf_take (wbuf\<^sub>f ostore_st \<lparr>data\<^sub>f := WordArrayT.make
       (buf_sub_slice (wbuf\<^sub>f ostore_st) (used\<^sub>f ostore_st) pad_to (sObj obj))\<rparr>)
       (sync_offs\<^sub>f ostore_st))"
     apply (simp add: buf_take_def wordarray_make)
     apply (subst take_n_buf_sub_slice_m)
      using inv_ostore_used_len_wbufD[OF inv_ostore inv_mount_st] apply simp
     using sync_lt_used apply simp
     using inv_bufsD[OF inv_ostore] used_gt_zero apply (simp add: valid_list_trans_no_pad_def buf_simps)
   done

lemma  padding_to_le_eb_size:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  shows
  "padding_to (mount_st, ostore_st, ostoreWriteNone) \<le> eb_size\<^sub>f (super\<^sub>f mount_st)"
    apply (simp add: padding_to_eq_align32_simp[OF inv_mount_st_no_summaryD[OF inv_mount_st]])
    apply (rule align32_upper_bound)
    using inv_mount_st[simplified inv_mount_st_def Let_def]
          inv_ostore_usedD[OF inv_ostore]
          inv_ostore_used_no_overflowD[OF inv_ostore]
    apply simp+
    done

lemma padding_to_le_len_wbuf:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"

  notes   pad_simps =  padding_to_eq_align32_simp[OF inv_mount_st_no_summaryD[OF inv_mount_st]]

  shows
 "unat pad_to \<le> length (\<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st)))"
  using padding_to_le_eb_size[OF assms(1,2), simplified pad_to pad_simps]
  using inv_mount_st apply (clarsimp simp: inv_mount_st_def Let_def pad_to pad_simps)
  using inv_ostore_eb_size_wbuf_eqD[OF inv_ostore] apply (unat_arith)
 done

lemma valid_list_trans_buf_slice_sync_offs_pad_to:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and     used_gt_zero: "0 < used\<^sub>f ostore_st"
  and     sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"

  and     valid_hdr: "is_valid_ObjHeader obj (sObj obj)"
  and     obj: "\<exists>crc. obj = ostore_update_padding_obj
        (opad\<^sub>f ostore_st, OstoreState.next_sqnum\<^sub>f ostore_st,
         pad_to - used\<^sub>f ostore_st - bilbyFsObjHeaderSize)
       \<lparr>crc\<^sub>f :=crc\<rparr>"
  and   valid_pad_obj: "valid_pad_obj obj"
  and     padding_obj: "\<not> (pad_to - used\<^sub>f ostore_st < bilbyFsObjHeaderSize)"

  notes   pad_to' = pad_to[simplified padding_to_eq_align32_simp[OF inv_mount_st_no_summaryD[OF inv_mount_st]]]
  notes sync_le_used = order_less_imp_le[OF sync_lt_used]
  and   invs = inv_ostore inv_mount_st
  shows
   " valid_list_trans (buf_slice (wbuf\<^sub>f ostore_st \<lparr>data\<^sub>f :=
       WordArrayT.make (buf_sub_slice (wbuf\<^sub>f ostore_st) (used\<^sub>f ostore_st) pad_to (sObj obj))\<rparr>)
       (sync_offs\<^sub>f ostore_st) pad_to)"
     apply (simp add: buf_slice_def wordarray_make)
     apply (subst slice_buf_sub_slice[OF sync_le_used])
      using used_le_padding_to[OF invs] apply (simp add: pad_to)
      using padding_to_le_length_wbuf[OF invs] apply (simp add: pad_to)
      using len_sObj[OF valid_hdr  obj valid_pad_obj] apply simp
     apply (rule valid_list_trans_append)


     using inv_bufsD[OF inv_ostore] sync_lt_used
     apply (simp add: valid_list_trans_no_pad_def)

     using len_sObj'[OF invs pad_to valid_hdr obj valid_pad_obj]
           valid_list_trans_pad_obj[OF  invs pad_to sync_lt_used obj valid_pad_obj padding_obj ]
     apply simp
    done

lemma snd_list_trans_no_pad_padding_obj_sync_pad_to:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and     used_gt_zero: "0 < used\<^sub>f ostore_st"
  and     sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
  and     valid_hdr: "is_valid_ObjHeader obj (sObj obj)"
  and     obj: "\<exists>crc. obj = ostore_update_padding_obj
        (opad\<^sub>f ostore_st, OstoreState.next_sqnum\<^sub>f ostore_st,
         pad_to - used\<^sub>f ostore_st - bilbyFsObjHeaderSize)
       \<lparr>crc\<^sub>f :=crc\<rparr>"
  and     valid_pad_obj: "valid_pad_obj obj"
  and     padding_obj: "\<not> (pad_to - used\<^sub>f ostore_st < bilbyFsObjHeaderSize)"

  notes   pad_to' = pad_to[simplified padding_to_eq_align32_simp[OF inv_mount_st_no_summaryD[OF inv_mount_st]]]
  and     sync_le_used = order_less_imp_le[OF sync_lt_used]
  and     invs = inv_ostore inv_mount_st
  and     valid_list_trans_pad_obj = valid_list_trans_pad_obj[OF invs pad_to sync_lt_used obj valid_pad_obj padding_obj]
  and     snd_list_trans_no_pad_padding_obj = snd_list_trans_no_pad_padding_obj[OF invs pad_to sync_lt_used obj padding_obj ]

  shows
    "prod.snd (list_trans_no_pad (buf_slice (wbuf\<^sub>f ostore_st \<lparr>data\<^sub>f :=
      WordArrayT.make (buf_sub_slice (wbuf\<^sub>f ostore_st) (used\<^sub>f ostore_st) pad_to (sObj obj))\<rparr>)
       (sync_offs\<^sub>f ostore_st) pad_to)) =
    prod.snd (list_trans_no_pad (buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st)))"
   apply (simp add: buf_slice_def wordarray_make)
   apply (subst  slice_buf_sub_slice[OF sync_le_used])
      using used_le_padding_to[OF invs] apply (simp add: pad_to)
      using padding_to_le_length_wbuf[OF invs] apply (simp add: pad_to)
      using len_sObj[OF valid_hdr  obj valid_pad_obj] apply simp
     using len_sObj'[OF invs pad_to valid_hdr obj valid_pad_obj] buf_slice_def
     using  snd_list_trans_no_pad_padding_obj[OF  valid_list_trans_pad_obj]
   by simp


lemma snd_list_trans_no_pad_all_padding_obj:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and     used_gt_zero: "0 < used\<^sub>f ostore_st"
  and     sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
  and     valid_hdr: "is_valid_ObjHeader obj (sObj obj)"
  and     obj: "\<exists>crc. obj = ostore_update_padding_obj
        (opad\<^sub>f ostore_st, OstoreState.next_sqnum\<^sub>f ostore_st,
         pad_to - used\<^sub>f ostore_st - bilbyFsObjHeaderSize)
       \<lparr>crc\<^sub>f :=crc\<rparr>"
  and     valid_pad_obj: "valid_pad_obj obj"
  and     padding_obj: "\<not> (pad_to - used\<^sub>f ostore_st < bilbyFsObjHeaderSize)"

  notes pad_to' = pad_to[simplified padding_to_eq_align32_simp[OF inv_mount_st_no_summaryD[OF inv_mount_st]]]
  and   sync_le_used = order_less_imp_le[OF sync_lt_used]
  and   invs = inv_ostore inv_mount_st
  and   valid_list_trans_pad_obj = valid_list_trans_pad_obj[OF invs pad_to sync_lt_used obj valid_pad_obj padding_obj]
  and   snd_list_trans_no_pad_padding_obj = snd_list_trans_no_pad_padding_obj[OF invs pad_to sync_lt_used obj  padding_obj ]
  and   invs_pad_offs =  inv_ostore inv_mount_st pad_to used_gt_zero sync_lt_used 

  shows
 "prod.snd (list_trans_no_pad
            (buf_slice
             (wbuf\<^sub>f ostore_st
              \<lparr>data\<^sub>f :=
                WordArrayT.make
                 (buf_sub_slice (wbuf\<^sub>f ostore_st) (used\<^sub>f ostore_st) pad_to (sObj obj))\<rparr>)
            0 pad_to)) =
    prod.snd (list_trans_no_pad (buf_slice (wbuf\<^sub>f ostore_st) 0 (used\<^sub>f ostore_st)))"
   apply (simp add: buf_slice_0_eq_buf_take)
   apply (subst buf_take_buf_slice_adjacent[symmetric, where st="sync_offs\<^sub>f ostore_st" and ?end="used\<^sub>f ostore_st"])
    using sync_lt_used apply simp
   apply (subst buf_take_buf_slice_adjacent[symmetric, where st="sync_offs\<^sub>f ostore_st" and ?end="pad_to"])
    using sync_offs_le_padding_to[OF invs] apply (simp add: pad_to)
   apply (subst list_trans_no_pad_append[symmetric])
   using valid_list_trans_buf_take_sync_offs[OF invs_pad_offs] apply (simp)
   using valid_list_trans_buf_slice_sync_offs_pad_to[OF invs_pad_offs valid_hdr obj valid_pad_obj padding_obj]
   apply simp
   apply (subst list_trans_no_pad_append[symmetric])
    using inv_bufsD[OF inv_ostore] used_gt_zero apply (simp add: valid_list_trans_no_pad_def)
    using inv_bufsD[OF inv_ostore] sync_lt_used apply (simp add: valid_list_trans_no_pad_def)
    apply (simp add: buf_slice_def wordarray_make)
    apply (subst  slice_buf_sub_slice[OF sync_le_used])
      using used_le_padding_to[OF invs] apply (simp add: pad_to)
      using padding_to_le_length_wbuf[OF invs] apply (simp add: pad_to)
      using len_sObj[OF valid_hdr obj valid_pad_obj] apply simp
    apply (subst buf_take_def, simp add: wordarray_make)
    apply (subst  take_n_buf_sub_slice_m[OF _ sync_le_used])
     using inv_ostore_used_len_wbufD[OF inv_ostore inv_mount_st] apply simp
    apply (simp add: buf_take_def len_sObj')
    using len_sObj'[OF invs pad_to valid_hdr obj valid_pad_obj] snd_list_trans_no_pad_padding_obj [OF valid_list_trans_pad_obj ]
    apply (simp add: buf_slice_def)
    done

lemma \<alpha>_updates_padding_objeq:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and     used_eq_pad_to: "used = pad_to"
  and     sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
  and     valid_hdr: "is_valid_ObjHeader obj (sObj obj)"
  and     obj: "\<exists>crc. obj = ostore_update_padding_obj
        (opad\<^sub>f ostore_st, OstoreState.next_sqnum\<^sub>f ostore_st,
         pad_to - used\<^sub>f ostore_st - bilbyFsObjHeaderSize)
       \<lparr>crc\<^sub>f :=crc\<rparr>"
  and     valid_pad_obj: "valid_pad_obj obj"
  and     padding_obj: "\<not> (pad_to - used\<^sub>f ostore_st < bilbyFsObjHeaderSize)"

  notes invs = inv_ostore inv_mount_st  
  and   sync_le_used = order_less_imp_le[OF sync_lt_used]
  and   snd_list_trans_no_pad_padding_obj = snd_list_trans_no_pad_padding_obj[OF invs pad_to sync_lt_used obj  padding_obj ]
  and   valid_list_trans_pad_obj = valid_list_trans_pad_obj[OF invs pad_to sync_lt_used obj valid_pad_obj padding_obj]

  shows
 "\<alpha>_updates (ostore_st \<lparr>wbuf\<^sub>f := wbuf\<^sub>f ostore_st
            \<lparr>data\<^sub>f := WordArrayT.make (buf_sub_slice (wbuf\<^sub>f ostore_st) (used\<^sub>f ostore_st) pad_to (sObj obj))\<rparr>,
             opad\<^sub>f := obj, used\<^sub>f := used,
             OstoreState.next_sqnum\<^sub>f := OstoreState.next_sqnum\<^sub>f ostore_st + 1,
             fsm_st\<^sub>f := fsm_st,
             OstoreState.oaddr\<^sub>f := oaddr\<rparr>) = \<alpha>_updates ostore_st"
    apply (simp add: \<alpha>_updates_def)
    apply (rule arg_cong[where f="map ostore_update"])
    apply (simp add: buf_slice_def wordarray_make)
    apply (simp add: used_eq_pad_to)
    apply (subst slice_buf_sub_slice[OF sync_le_used])
      using used_le_padding_to[OF invs] apply (simp add: pad_to)
      using padding_to_le_length_wbuf[OF invs] apply (simp add: pad_to)
      using len_sObj[OF valid_hdr  obj valid_pad_obj] apply simp

    using len_sObj'[OF invs pad_to valid_hdr obj valid_pad_obj]  snd_list_trans_no_pad_padding_obj[OF valid_list_trans_pad_obj]
    apply (simp add:  len_sObj' buf_slice_def)
    done

lemmas Obj_ext_eq_expand = trans[OF _ Obj.ext_inject,
    OF arg_cong2[where f="(=)"], OF refl Obj.surjective]

lemma inv_ostore_preserved_padding_obj:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and     used_gt_zero: "0 < used\<^sub>f ostore_st"
  and     sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
  and     obj: "\<exists>crc. obj = ostore_update_padding_obj
        (opad\<^sub>f ostore_st, OstoreState.next_sqnum\<^sub>f ostore_st,
         pad_to - used\<^sub>f ostore_st - bilbyFsObjHeaderSize)
       \<lparr>crc\<^sub>f :=crc\<rparr>"
  and     valid_pad_obj: "valid_pad_obj obj"

  and     padding_obj: "\<not> (pad_to - used\<^sub>f ostore_st < bilbyFsObjHeaderSize)"
  and     used_eq_pad_to: "used = pad_to"
  and     fsm_st: "fsm_st \<in> {fsm_st\<^sub>f ostore_st, prepared_fsm_padding_obj ostore_st pad_to}"

  notes   pad_to' = pad_to[simplified padding_to_eq_align32_simp[OF inv_mount_st_no_summaryD[OF inv_mount_st]]]

  shows "inv_ostore mount_st
        (ostore_st \<lparr>wbuf\<^sub>f := wbuf\<^sub>f ostore_st
            \<lparr>data\<^sub>f := WordArrayT.make (buf_sub_slice (wbuf\<^sub>f ostore_st) (used\<^sub>f ostore_st) pad_to (sObj obj))\<rparr>,
             opad\<^sub>f := obj, used\<^sub>f := used,
             OstoreState.next_sqnum\<^sub>f := OstoreState.next_sqnum\<^sub>f ostore_st + 1,
             fsm_st\<^sub>f := fsm_st,
             OstoreState.oaddr\<^sub>f := oaddr\<rparr>)"
        (is "inv_ostore mount_st ?ostore_st")
proof -
  note invs = inv_ostore inv_mount_st
  and invs_pad_to =  inv_ostore inv_mount_st pad_to
  and invs_pad_offs = inv_ostore inv_mount_st pad_to used_gt_zero sync_lt_used 
  and snd_list_trans_no_pad_padding_obj = snd_list_trans_no_pad_padding_obj[OF invs_pad_to sync_lt_used obj padding_obj ]
  note valid_hdr = valid_commit_pad_obj[OF invs_pad_to obj padding_obj, simplified is_valid_ObjTrans, THEN conjunct1]
  and valid_list_trans_pad_obj = valid_list_trans_pad_obj[OF invs_pad_to sync_lt_used obj valid_pad_obj padding_obj]
  note snd_list_trans_no_pad_all_padding_obj = snd_list_trans_no_pad_all_padding_obj[OF invs_pad_offs valid_hdr obj valid_pad_obj padding_obj]
  note snd_list_trans_no_pad_padding_obj_sync_pad_to = snd_list_trans_no_pad_padding_obj_sync_pad_to[OF invs_pad_offs valid_hdr obj valid_pad_obj padding_obj]
  note \<alpha>_updates_padding_objeq = \<alpha>_updates_padding_objeq[OF invs pad_to used_eq_pad_to sync_lt_used valid_hdr obj valid_pad_obj padding_obj]
  note valid_list_trans_buf_slice_sync_offs_pad_to = valid_list_trans_buf_slice_sync_offs_pad_to[OF invs_pad_offs valid_hdr obj valid_pad_obj padding_obj]
  and pad_simps = padding_to_eq_align32_simp[OF inv_mount_st_no_summaryD[OF inv_mount_st]]
  note len_sObj' = len_sObj'[OF invs pad_to valid_hdr obj ]
                       
  have sync_le_pad_to: "sync_offs\<^sub>f ostore_st \<le> pad_to"
    using sync_offs_le_padding_to[OF invs] by (simp add: pad_to)

  moreover have "wordarray_length (data\<^sub>f (wbuf\<^sub>f ?ostore_st)) =  eb_size\<^sub>f (super\<^sub>f mount_st)"
    apply (simp)
    apply (subst word_unat.Rep_inject [symmetric])
    apply (subst wordarray_length_ret)
    apply (subst wordarray_make)
    apply (subst buf_sub_slice_length)
    using inv_ostore_eb_size_wbuf_eqD[OF inv_ostore] by simp

   moreover have get_obj_eq:
    "\<And>v. is_valid_addr mount_st ostore_st v \<Longrightarrow>
      ostore_get_obj ?ostore_st v = ostore_get_obj ostore_st  v"  
      using ostore_get_obj_eq_padding_obj[OF inv_ostore inv_mount_st pad_to] used_eq_pad_to by simp

   hence runtime_eq: "\<alpha>_ostore_runtime ?ostore_st = \<alpha>_ostore_runtime ostore_st"
    using inv_ostore_indexD[OF inv_ostore]
    by (fastforce simp add: \<alpha>_ostore_runtime_def option.case_eq_if inv_ostore_index_def Let_def)

   have sync_le_used: "sync_offs\<^sub>f ostore_st \<le> used\<^sub>f ostore_st" using sync_lt_used by simp

   have used_le_pad_to: "used\<^sub>f ostore_st \<le> pad_to"
    using used_le_padding_to[OF invs] by (simp add: pad_to)

   have len_sObj_ge_hdr_size: "unat bilbyFsObjHeaderSize \<le> length (sObj obj)"
   using len_sObj
     using len_sObj[OF valid_hdr obj valid_pad_obj, symmetric] len_sObj' padding_obj by unat_arith

   have \<alpha>_ostore_medium_eq: "\<alpha>_ostore_medium ?ostore_st = \<alpha>_ostore_medium ostore_st"
    by (simp add: \<alpha>_ostore_medium_def abstract_mount_\<alpha>_ostore_def Let_def list_eb_log_def)
   then have uptodate_eq: "\<alpha>_ostore_uptodate ?ostore_st = \<alpha>_ostore_uptodate ostore_st"
    by (simp add: \<alpha>_ostore_medium_eq \<alpha>_updates_padding_objeq \<alpha>_ostore_uptodate_def)

  moreover have "\<alpha>_ostore_runtime ?ostore_st = \<alpha>_ostore_uptodate ?ostore_st"
   using inv_ostore
   by (simp add: runtime_eq uptodate_eq inv_ostore_def)

  moreover have "inv_ostore_summary mount_st ?ostore_st"
    by (simp add: inv_ostore_summary_def)

  moreover have "inv_ostore_index mount_st ?ostore_st"
    using inv_ostore_index_padding_obj[OF inv_ostore inv_mount_st pad_to] used_eq_pad_to by simp
  moreover have "inv_ostore_index_gim_disjoint ?ostore_st"
     using inv_ostore fsm_st
     by (fastforce simp: prepared_fsm_padding_obj_def inv_ostore_def inv_ostore_index_gim_disjoint_def)
      
  moreover have inv_ostore_fsm: "inv_ostore_fsm mount_st ?ostore_st"
    apply (simp add: inv_ostore_fsm_def used_eq_pad_to)
    apply (rule conjI)
     using inv_ostore_fsmD[OF inv_ostore, simplified inv_ostore_fsm_def]
          padding_obj fsm_st
     apply (fastforce simp add:  prepared_fsm_padding_obj_def)
    apply (rule conjI)
     using inv_ostore_fsmD[OF inv_ostore, simplified inv_ostore_fsm_def Let_def]
     apply (case_tac "fsm_st = fsm_st\<^sub>f ostore_st", simp)
      using snd_list_trans_no_pad_all_padding_obj
      apply (simp add: list_eb_log_wbuf_def )
      using snd_list_trans_no_pad_all_padding_obj fsm_st
     apply (clarsimp simp add: padding_obj list_eb_log_wbuf_def prepared_fsm_padding_obj_def)
      using inv_ostore_fsmD[OF inv_ostore, simplified inv_ostore_fsm_def] fsm_st
    apply (fastforce simp add: padding_obj prepared_fsm_padding_obj_def)
  done

  moreover have "inv_bufs mount_st ?ostore_st"
    using inv_ostore_sync_offsD[OF inv_ostore] inv_ostore_used_len_wbufD[OF invs]
            sync_lt_used used_gt_zero
    apply (simp add: inv_bufs_def Let_def pad_to' buf_take_def wordarray_make take_n_buf_sub_slice_m used_eq_pad_to)
    apply safe
    apply (simp_all add: inv_ostore[simplified Let_def inv_ostore_def]inv_bufsD[OF inv_ostore, simplified buf_take_def])
    apply (simp add: valid_list_trans_no_pad_def) 
     apply (rule conjI)
     using valid_list_trans_buf_slice_sync_offs_pad_to[simplified pad_to'] apply simp
     apply (simp add: buf_slice_def wordarray_make)
     apply (subst slice_buf_sub_slice[OF sync_le_used])
        using used_le_padding_to[OF invs] apply (simp add: padding_to_eq_align32_simp[OF inv_mount_st_no_summaryD[OF inv_mount_st]])
        using padding_to_le_length_wbuf[OF invs] apply (simp add: pad_simps) 
      using used_le_padding_to[OF inv_ostore inv_mount_st]
      apply (simp add: pad_to' pad_to pad_simps len_sObj'[OF valid_pad_obj, symmetric])
      apply unat_arith
     apply (subst list_trans_no_pad_append[symmetric])
       using inv_bufsD[OF inv_ostore] used_gt_zero len_sObj'[symmetric]
       apply (simp add: valid_list_trans_no_pad_def )
   using padding_obj len_sObj'[OF valid_pad_obj] pad_to' valid_list_trans_pad_obj apply simp
   using inv_bufsD[OF inv_ostore] sync_lt_used apply (simp add: valid_list_trans_no_pad_def)
   using inv_bufsD[OF inv_ostore] used_gt_zero apply (simp add: valid_list_trans_no_pad_def buf_take_def)
   apply (simp add: buf_slice_def wordarray_make)
    apply (subst slice_buf_sub_slice[OF sync_le_used used_le_pad_to[simplified pad_to']])
     using padding_to_le_length_wbuf[OF invs, simplified pad_simps] apply simp
      using len_sObj[OF valid_hdr obj valid_pad_obj, symmetric]  apply (simp add: pad_to')
     using len_sObj'[OF valid_pad_obj]  apply (simp add: pad_to')
     apply (subst slice_buf_sub_slice[OF sync_le_used used_le_pad_to[simplified pad_to']])
      using padding_to_le_length_wbuf[OF invs] apply (simp add: pad_simps)
     using len_sObj[OF valid_hdr obj valid_pad_obj]  apply (simp add: pad_to')
     using snd_list_trans_no_pad_padding_obj[OF valid_list_trans_pad_obj] apply simp
     using inv_bufsD[OF inv_ostore]  apply (clarsimp simp add: valid_list_trans_no_pad_def buf_take_def)
   done

  moreover have "inv_fsm_st mount_st (fsm_st\<^sub>f ?ostore_st)"
    proof cases
     assume "fsm_st = fsm_st\<^sub>f ostore_st"
       thus ?thesis
         using inv_fsm_stD[OF inv_ostore]  by(simp add: inv_fsm_st_def)
     next
     assume "fsm_st \<noteq> fsm_st\<^sub>f ostore_st"
     hence  "fsm_st = prepared_fsm_padding_obj ostore_st pad_to"
      using fsm_st by simp
     thus ?thesis
      using inv_fsm_stD[OF inv_ostore]
      by (simp add: padding_obj prepared_fsm_padding_obj_def
        inv_fsm_st_def wordarray_make)
    qed
  moreover have "inv_flash (list_eb_log_wbuf ?ostore_st) " by (simp add: inv_flash_def)
  moreover have "inv_log (list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st)))
     (prod.snd (list_trans_no_pad (buf_slice (wbuf\<^sub>f ?ostore_st) (sync_offs\<^sub>f ostore_st) (pad_to))))"
     using snd_list_trans_no_pad_padding_obj_sync_pad_to
           inv_logD[OF inv_ostore, folded inv_log_def] 
     by simp

  moreover have "inv_opad obj"
    using inv_opadD[OF inv_ostore]  obj padding_obj
    by clarsimp (simp add: inv_opad_def ostore_update_padding_obj' bilbyFsTransCommit_def
            bilbyFsObjHeaderSize_def)

  ultimately  show ?thesis
  using padding_to_io_size_no_overflow[OF inv_ostore inv_mount_st]
        inv_ostore inv_opadD[OF inv_ostore]
        padding_to_le_eb_size[OF invs]
  apply (clarsimp simp add: inv_ostore_def  pad_to buf_simps used_eq_pad_to)
  done
qed

lemma opad_is_valid_ObjHeader:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     padding_obj: "\<not> pad_to - used\<^sub>f ostore_st < bilbyFsObjHeaderSize"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"

  notes pad_simps = padding_to_eq_align32_simp[OF inv_mount_st_no_summaryD[OF inv_mount_st]]
  notes pad_to' = pad_to[simplified pad_simps]
  and   ostore_update_padding_obj' = ostore_update_padding_obj_def[unfolded tuple_simps sanitizers]

  shows
    "is_valid_ObjHeader
     (ostore_update_padding_obj
       (opad\<^sub>f ostore_st, OstoreState.next_sqnum\<^sub>f ostore_st,
        pad_to - used\<^sub>f ostore_st - bilbyFsObjHeaderSize))
     (drop (unat (used\<^sub>f ostore_st)) (\<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st))))"
  using inv_opadD[OF inv_ostore] padding_obj inv_ostore_eb_size_wbuf_eqD[OF inv_ostore]
        inv_ostore_usedD[OF inv_ostore] inv_mount_st[simplified inv_mount_st_def Let_def]
        used_le_padding_to[OF inv_ostore inv_mount_st]
        apply (clarsimp simp add: is_valid_ObjHeader_def bilbyFsTransCommit_def 
              ostore_update_padding_obj' bilbyFsObjHeaderSize_def pad_to' word_le_nat_alt)
  apply (thin_tac _)+
  apply safe
   using padding_to_le_length_wbuf[OF inv_ostore inv_mount_st]
        inv_ostore_used_len_wbufD[OF inv_ostore inv_mount_st]
        used_le_padding_to[OF inv_ostore inv_mount_st]
        padding_obj
   apply (simp add: bilbyFsObjHeaderSize_def le_def pad_to pad_to'
            padding_to_def[unfolded tuple_simps sanitizers], unat_arith)
  using pad_to padding_obj apply (simp add: otype_simps is_len_and_type_ok_def
     bilbyFsObjHeaderSize_def padding_to_def[unfolded tuple_simps sanitizers])
 done

lemma inv_step_padding_obj:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and     used_gt_zero: "0 < used\<^sub>f ostore_st"
  and     sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
  and     obj: "\<exists>crc. obj = ostore_update_padding_obj
        (opad\<^sub>f ostore_st, OstoreState.next_sqnum\<^sub>f ostore_st,
         pad_to - used\<^sub>f ostore_st - bilbyFsObjHeaderSize)
       \<lparr>crc\<^sub>f :=crc\<rparr>"
  and     valid_pad_obj: "valid_pad_obj obj"
  and     padding_obj: "\<not> (pad_to - used\<^sub>f ostore_st < bilbyFsObjHeaderSize)"
  and     used_eq_pad_to: "used = pad_to"
  and     fsm_st: "fsm_st \<in> {fsm_st\<^sub>f ostore_st, prepared_fsm_padding_obj ostore_st pad_to}"
  and     inv_step: "inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st)"

  notes invs = inv_ostore inv_mount_st
  and   pad_to' = pad_to[simplified padding_to_eq_align32_simp[OF inv_mount_st_no_summaryD[OF inv_mount_st]]]
  and    valid_hdr = valid_commit_pad_obj[OF invs pad_to obj padding_obj, simplified is_valid_ObjTrans, THEN conjunct1]

  shows "inv_\<alpha>_ostore (\<alpha>_ostore_uptodate (ostore_st \<lparr>wbuf\<^sub>f := wbuf\<^sub>f ostore_st
      \<lparr>data\<^sub>f := WordArrayT.make (buf_sub_slice (wbuf\<^sub>f ostore_st) (used\<^sub>f ostore_st) pad_to (sObj obj))\<rparr>,
       opad\<^sub>f := obj, used\<^sub>f := used,
       OstoreState.next_sqnum\<^sub>f := OstoreState.next_sqnum\<^sub>f ostore_st + 1,
       fsm_st\<^sub>f := fsm_st,
       OstoreState.oaddr\<^sub>f := oaddr\<rparr>))"
  apply (clarsimp simp add: inv_\<alpha>_ostore_def \<alpha>_ostore_uptodate_def)
  apply (simp add: \<alpha>_updates_padding_objeq[OF inv_ostore inv_mount_st pad_to used_eq_pad_to sync_lt_used valid_hdr obj valid_pad_obj  padding_obj])
  using inv_step apply (clarsimp simp add: inv_\<alpha>_ostore_def \<alpha>_ostore_uptodate_def)
  apply (rename_tac oid obj')
  apply (erule_tac x=oid in allE)
  apply (erule_tac x=obj' in allE)
  apply (simp add: \<alpha>_ostore_medium_def abstract_mount_\<alpha>_ostore_def)
done

lemma prepare_wbuf_ret:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and inv_mount_st: "inv_mount_st mount_st"
  and inv_step: "inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st)"
  and pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and used_gt_zero: "0 < used\<^sub>f ostore_st"
  and sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
  and err:                    
   "\<And>ex'.  P ((ex',ostore_st), Error eOverflow)"
  and suc:
  "\<And>ex' ostore_st'. \<lbrakk>
     inv_ostore mount_st ostore_st';
     inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st');
     \<exists>len sqnum crc oaddr nxtsqnum. ostore_st' =
       ostore_st\<lparr>wbuf\<^sub>f := wbuf\<^sub>f ostore_st\<lparr>data\<^sub>f:=WordArrayT.make $
         buf_prepared ostore_st (used\<^sub>f ostore_st) pad_to (prepared_pad_obj ostore_st pad_to crc)\<rparr>,
         used\<^sub>f := pad_to,
         fsm_st\<^sub>f := prepared_fsm_padding_obj ostore_st pad_to,
         OstoreState.oaddr\<^sub>f:= oaddr, 
         OstoreState.next_sqnum\<^sub>f:= nxtsqnum,
         opad\<^sub>f:=opad\<^sub>f ostore_st \<lparr>Obj.len\<^sub>f:=len, Obj.sqnum\<^sub>f := sqnum, Obj.crc\<^sub>f := crc\<rparr>\<rparr>;
     OstoreState.next_sqnum\<^sub>f ostore_st \<le> OstoreState.next_sqnum\<^sub>f ostore_st'
     \<rbrakk>
     \<Longrightarrow>  P ((ex',ostore_st'), Success ())"
  notes pad_simps = padding_to_eq_align32_simp[OF inv_mount_st_no_summaryD[OF inv_mount_st]]
  notes pad_to' = pad_to[simplified pad_simps]
  and   ostore_update_padding_obj' = ostore_update_padding_obj_def[unfolded tuple_simps sanitizers]
  shows "P (prepare_wbuf (ex, mount_st, ostore_st, pad_to))"
 proof cases
  assume no_padding_obj: "pad_to - used\<^sub>f ostore_st < bilbyFsObjHeaderSize"
  let ?wbuf = "buf_memset (wbuf\<^sub>f ostore_st, used\<^sub>f ostore_st,  pad_to - used\<^sub>f ostore_st, bilbyFsPadByte)"
  let ?ostore_st = "ostore_st\<lparr>wbuf\<^sub>f := ?wbuf, used\<^sub>f := pad_to\<rparr>"
  have bound: "unat (bound\<^sub>f (wbuf\<^sub>f ostore_st)) \<le> length (\<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st)))"
   using  inv_ostore_bound_le_lenD[OF inv_ostore] by simp
  have index_unchanged: "index_st\<^sub>f ?ostore_st = index_st\<^sub>f ostore_st" by simp
  have list_eb_log_eq: "list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ?ostore_st)) = list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))"
   by (simp add: list_eb_log_def)
  have pad_to_le: "unat pad_to \<le> length (\<alpha>wa $ data\<^sub>f $ wbuf\<^sub>f ostore_st)"
  using align32_upper_bound[where v="used\<^sub>f ostore_st" and al="io_size\<^sub>f (super\<^sub>f mount_st)" and bound="eb_size\<^sub>f (super\<^sub>f mount_st)"]
    inv_ostore[simplified inv_ostore_def]  inv_mount_st[simplified Let_def inv_mount_st_def]
    inv_ostore_eb_size_wbuf_eqD[OF inv_ostore]
   by (simp add : pad_to')  unat_arith

  have used_le_pad_to: "used\<^sub>f ostore_st \<le>  pad_to"
   using align32_le[where v="used\<^sub>f ostore_st" and al="io_size\<^sub>f (super\<^sub>f mount_st)"] inv_mount_st[simplified inv_mount_st_def Let_def]
          pad_to' inv_ostore_used_no_overflowD[OF inv_ostore]
   by simp
  have unat_used_le_pad_to: "unat (used\<^sub>f ostore_st) \<le> unat pad_to" using used_le_pad_to by unat_arith
  have \<alpha>_updates_eq: "\<alpha>_updates ?ostore_st = \<alpha>_updates ostore_st"
   by (rule prepare_wbuf_memset_\<alpha>_updates_eq[OF inv_ostore inv_mount_st pad_to sync_lt_used])
  have \<alpha>_medium_eq: "\<alpha>_ostore_medium ?ostore_st = \<alpha>_ostore_medium ostore_st"
   by (simp add: \<alpha>_ostore_medium_def abstract_mount_\<alpha>_ostore_def list_eb_log_eq)
  have inv_step': "inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ?ostore_st)"
   using inv_step
   by (clarsimp simp add: \<alpha>_ostore_uptodate_def Let_def \<alpha>_medium_eq \<alpha>_updates_eq)
  have inv_ostore': "inv_ostore mount_st ?ostore_st"
   using inv_ostore_padding_bytes_preserved[OF inv_ostore inv_mount_st pad_to used_gt_zero sync_lt_used] .
  show ?thesis
  unfolding prepare_wbuf_def[unfolded tuple_simps sanitizers]
  apply (fold bilbyFsObjHeaderSize_def)
  using no_padding_obj apply (simp add: pad_to')
  apply (rule suc)
      apply (fold bilbyFsPadByte_def)
  using inv_ostore'  apply (simp add: pad_to padding_to_def ostoreWriteNone_def)
     apply(fastforce intro: subst[where P=\<open>inv_ostore mount_st\<close>,rotated])
  using inv_step' apply (simp add: pad_to padding_to_def ostoreWriteNone_def)
    apply (fastforce intro: subst[where P=\<open>\<lambda>x. inv_\<alpha>_ostore (\<alpha>_ostore_uptodate x)\<close>,rotated])
   apply (rule_tac x="Obj.len\<^sub>f (opad\<^sub>f ?ostore_st)" in exI)
   apply (rule_tac x="Obj.sqnum\<^sub>f (opad\<^sub>f ?ostore_st)" in exI)
   apply (rule_tac x="Obj.crc\<^sub>f (opad\<^sub>f ?ostore_st)" in exI)
   apply (rule_tac x="(OstoreState.oaddr\<^sub>f ?ostore_st)" in exI)
   apply (rule_tac x="(OstoreState.next_sqnum\<^sub>f ?ostore_st)" in exI)
      apply (subst buf_memset_eq)
         using bound apply simp
        using used_le_padding_to[OF inv_ostore inv_mount_st] apply (simp add: pad_to' pad_simps)
   apply (fastforce simp add: pad_to padding_to_def 
           ostoreWriteNone_def buf_prepared_def prepared_fsm_padding_obj_def)
  apply simp
 done

 next
  assume padding_obj: "\<not> (pad_to - used\<^sub>f ostore_st < bilbyFsObjHeaderSize)"

  have pad_to_upd:
    "used\<^sub>f ostore_st +
     Obj.len\<^sub>f (ostore_update_padding_obj(opad\<^sub>f ostore_st, OstoreState.next_sqnum\<^sub>f ostore_st,
               pad_to - used\<^sub>f ostore_st - bilbyFsObjHeaderSize))
      = pad_to"
    by (simp add: ostore_update_padding_obj' pad_to pad_simps bilbyFsObjHeaderSize_def)

  have dummy_upds: "\<And>x. x = x\<lparr>fsm_st\<^sub>f := fsm_st\<^sub>f x, OstoreState.oaddr\<^sub>f := OstoreState.oaddr\<^sub>f x\<rparr>"
   by simp

  have dummy_upds': "\<And>x a b c d. x\<lparr>OstoreState.next_sqnum\<^sub>f := a, used\<^sub>f := b, opad\<^sub>f := c, wbuf\<^sub>f := d\<rparr> = x\<lparr>wbuf\<^sub>f := d, opad\<^sub>f := c, used\<^sub>f := b, OstoreState.next_sqnum\<^sub>f := a, fsm_st\<^sub>f := fsm_st\<^sub>f x, OstoreState.oaddr\<^sub>f := OstoreState.oaddr\<^sub>f x\<rparr>"
    by simp

  have ostore_upds_reorder: "\<And>x a b c d e f. x\<lparr>OstoreState.next_sqnum\<^sub>f := a, used\<^sub>f := b, opad\<^sub>f := c, wbuf\<^sub>f := d, fsm_st\<^sub>f := e, OstoreState.oaddr\<^sub>f := f\<rparr> = x\<lparr>wbuf\<^sub>f := d, opad\<^sub>f := c, used\<^sub>f := b, OstoreState.next_sqnum\<^sub>f := a, fsm_st\<^sub>f := e, OstoreState.oaddr\<^sub>f := f\<rparr>" by simp

  from padding_obj show ?thesis
    unfolding prepare_wbuf_def[unfolded tuple_simps sanitizers, folded bilbyFsObjHeaderSize_def]
    apply (simp add: Let_def)
    apply (rule safe_add64)
     apply (simp add: Let_def, fold eOverflow_def )
     apply (simp add: err)
    apply (simp add: Let_def )
    apply (rule serialise_Obj_ret)
        apply (simp add:  pad_to' bilbyFsObjHeaderSize_def ostore_update_padding_obj')
        using used_le_padding_to[OF inv_ostore inv_mount_st] apply (simp add: pad_simps) 
       using opad_is_valid_ObjHeader[OF inv_ostore inv_mount_st padding_obj pad_to] apply simp
      using inv_opadD[OF inv_ostore] apply (clarsimp simp add: ostore_update_padding_obj' )
      using inv_opadD[OF inv_ostore] apply (clarsimp simp add: ostore_update_padding_obj' )
       using inv_ostore_eb_size_wbuf_eqD[OF inv_ostore]
             inv_ostore_wbuf_boundD[OF inv_ostore]
             padding_to_le_eb_size[OF inv_ostore inv_mount_st]
             apply (clarsimp simp add: pad_to buf_simps ostore_update_padding_obj' bilbyFsObjHeaderSize_def)
      apply (rename_tac buf')
      apply (simp add: prod.case_eq_if)
       apply (rule update_obj_pad_ret[OF _ inv_mount_st])
       apply (rule ssubst[OF dummy_upds'])
       apply (rule inv_ostore_preserved_padding_obj[OF inv_ostore inv_mount_st _ used_gt_zero sync_lt_used])
          using pad_to_upd apply (simp add: pad_to)
         apply (simp add: ostore_update_padding_obj' pad_to pad_simps bilbyFsObjHeaderSize_def)
         apply (rule_tac x="crc\<^sub>f (opad\<^sub>f ostore_st)" in exI)
         apply simp

         using inv_ostore_valid_pad_objD[OF inv_ostore] apply (clarsimp simp:ostore_update_padding_obj' valid_pad_obj_def is_valid_Obj_def)
        apply (simp add: ostore_update_padding_obj' bilbyFsObjHeaderSize_def)
       using inv_opadD[OF inv_ostore] apply (clarsimp simp add:  ostore_update_padding_obj' bilbyFsObjHeaderSize_def)
      using inv_ostore_wbuf_eb_rangeD[OF inv_ostore]
      apply (simp add: ostore_update_padding_obj' pad_to pad_simps bilbyFsObjHeaderSize_def)
     using inv_ostore_wbuf_eb_rangeD[OF inv_ostore] apply simp

    apply (rule suc)
      apply simp thm inv_ostore_preserved_padding_obj[OF inv_ostore 
                    inv_mount_st _ used_gt_zero sync_lt_used]
     apply(subst ostore_upds_reorder)
     apply (rule inv_ostore_preserved_padding_obj[OF inv_ostore 
                    inv_mount_st _ used_gt_zero sync_lt_used])
           using pad_to_upd apply (simp add: pad_to)
          apply (simp add: ostore_update_padding_obj' pad_to pad_simps bilbyFsObjHeaderSize_def)
          apply (rule_tac x="crc\<^sub>f (opad\<^sub>f ostore_st)" in exI)
          apply simp
         apply (simp add: ostore_update_padding_obj' bilbyFsObjHeaderSize_def)
         using inv_ostore_valid_pad_objD[OF inv_ostore] apply (clarsimp simp:ostore_update_padding_obj' valid_pad_obj_def is_valid_Obj_def)
       using inv_opadD[OF inv_ostore] apply (clarsimp simp add:  ostore_update_padding_obj' bilbyFsObjHeaderSize_def)
      using inv_ostore_wbuf_eb_rangeD[OF inv_ostore]
      apply (simp add: ostore_update_padding_obj' pad_to pad_simps bilbyFsObjHeaderSize_def)
     using padding_obj apply (simp add: prepared_fsm_padding_obj_def pad_simps bilbyFsObjHeaderSize_def pad_to' ostore_update_padding_obj')
       apply simp
     apply(subst ostore_upds_reorder)
    apply (rule inv_step_padding_obj[OF inv_ostore inv_mount_st _  used_gt_zero sync_lt_used ])
          using pad_to_upd apply (simp add: pad_to)
         apply (rule_tac x="crc\<^sub>f (opad\<^sub>f ostore_st)" in exI)
         using pad_to_upd apply (clarsimp simp add: pad_to ostore_update_padding_obj_def Let\<^sub>d\<^sub>s_def)
        using inv_ostore_valid_pad_objD[OF inv_ostore] apply (clarsimp simp: valid_pad_obj_def ostore_update_padding_obj' is_valid_Obj_def)
       using pad_to_upd apply (clarsimp simp add: pad_to ostore_update_padding_obj')
      using pad_to_upd apply (clarsimp simp add: pad_to ostore_update_padding_obj')
     using pad_to_upd apply (clarsimp simp add: pad_to ostore_update_padding_obj' prepared_fsm_padding_obj_def)
    using inv_step apply simp
   apply simp
  using [[goals_limit=1]]
   apply (rule_tac x="pad_to - used\<^sub>f ostore_st" in exI)
      apply (rule_tac x="OstoreState.next_sqnum\<^sub>f ostore_st" in exI)
      apply (rule_tac x="crc\<^sub>f (opad\<^sub>f ostore_st)" in exI)
      apply (rule_tac x="v" in exI)
      apply (rule_tac x="OstoreState.next_sqnum\<^sub>f ostore_st + 1" in exI)
      apply simp
     apply (simp add: prepared_fsm_padding_obj_def buf_prepared_def padding_obj pad_to_upd)
     apply (simp add: ostore_update_padding_obj' prepared_pad_obj_def Let_def
         bilbyFsObjHeaderSize_def prepared_pad_obj_no_crc_def bilbyFsTransCommit_def  )
 (* FIX Cogent code, currently it updates the otype field but shouldn't because
    the type of opad is part of the invariant *)
      using inv_opadD[OF inv_ostore] apply (clarsimp simp: bilbyFsTransCommit_def)
      using inv_ostore_wbuf_eb_rangeD[OF inv_ostore]
       apply (subst ostore_upds_reorder)
      sorry
  qed

definition
  sync_summary_serial :: "OstoreState\<^sub>T \<Rightarrow> (Obj\<^sub>T \<times> Buffer\<^sub>T \<times> U32)"
where
 "sync_summary_serial ostore_st \<equiv>
   serialise_ObjSummary_crc
     (wbuf\<^sub>f ostore_st, used\<^sub>f ostore_st, sum_obj\<^sub>f ostore_st
      \<lparr>Obj.sqnum\<^sub>f := OstoreState.next_sqnum\<^sub>f ostore_st, Obj.offs\<^sub>f := used\<^sub>f ostore_st,
         trans\<^sub>f := bilbyFsTransCommit,
         Obj.len\<^sub>f := serialise_size_summary_Obj_with_extra (summary\<^sub>f ostore_st, 0)\<rparr>,
      summary\<^sub>f ostore_st\<lparr>sum_offs\<^sub>f := used\<^sub>f ostore_st\<rparr>)"

lemma ostore_sync_summary_if_eb_new_ret:
  "inv_ostore mount_st ostore_st \<Longrightarrow>
   inv_mount_st mount_st \<Longrightarrow>
   inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st) \<Longrightarrow>
   (\<And>ex'. P ((ex', ostore_st), R.Success ())) \<Longrightarrow>
  P (ostore_sync_summary_if_eb_new (ex, mount_st, ostore_st, ostoreWriteNone))"
 by (simp add: ostore_sync_summary_if_eb_new_def[unfolded tuple_simps sanitizers])

lemma ostore_write_buf_inv_ostore_index:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and inv_mount_st: "inv_mount_st mount_st"
  and ubi_vol:"\<alpha>wubi ubi_vol' = (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))
       [unat (wbuf_eb\<^sub>f ostore_st) :=
          \<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) ! unat (wbuf_eb\<^sub>f ostore_st) @
          buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st + nb_bytes)]"
shows
 "inv_ostore_index mount_st (ostore_st\<lparr>OstoreState.ubi_vol\<^sub>f := ubi_vol'\<rparr>)"
     using inv_ostore inv_mount_st[unfolded inv_mount_st_def]
  apply (clarsimp simp: inv_ostore_def Let_def inv_ostore_index_def ostore_get_obj_def)
  apply (rename_tac oid addr)
  apply (erule_tac x=oid in ballE)
  apply (case_tac "ObjAddr.ebnum\<^sub>f addr \<noteq> wbuf_eb\<^sub>f ostore_st")
   using ubi_vol apply (clarsimp simp: is_valid_addr_def)+
 done

lemma map_list_trans_upd_eq:
 "(map f (drop m (xs[n:=y''])))[n-m:=y] =
  (map f (drop m xs))[n-m:=y]"
  apply (clarsimp simp: list_eq_iff_nth_eq )
  apply (rename_tac i, case_tac "i = n-m")
   apply (clarsimp simp del: list_trans.simps)+
 done

lemma ostore_write_buf_inv_ostore_fsm:
 " inv_ubi_vol mount_st ubi_vol' \<Longrightarrow>
   \<alpha>wubi ubi_vol' = (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))
   [unat (wbuf_eb\<^sub>f ostore_st) :=
    \<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) ! unat (wbuf_eb\<^sub>f ostore_st) @
    buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st + nb_bytes)] \<Longrightarrow>
   inv_ostore_fsm mount_st ostore_st \<Longrightarrow>
   inv_ostore_fsm mount_st (ostore_st\<lparr>OstoreState.ubi_vol\<^sub>f := ubi_vol'\<rparr>)"
  apply (subgoal_tac "list_eb_log_wbuf (ostore_st\<lparr>OstoreState.ubi_vol\<^sub>f := ubi_vol'\<rparr>) = list_eb_log_wbuf ostore_st")
   apply (clarsimp simp add: inv_ostore_fsm_def list_eb_log_wbuf_def list_eb_log_def simp del:list_trans.simps)+
   apply (rule map_list_trans_upd_eq)
 done 

lemma word_not_0_gr_n:
  "(\<not> 0 < (n::'a::len0 word)) = (n = 0)"
  by (unat_arith, simp add: unat_0_iff)

lemma inv_ostore_sync_offs_agnostic:
 "inv_ostore_summary mount_st (ostore_st\<lparr>sync_offs\<^sub>f:=v\<rparr>) = inv_ostore_summary mount_st ostore_st"
 "inv_ostore_index mount_st (ostore_st\<lparr>sync_offs\<^sub>f := v\<rparr>)= inv_ostore_index mount_st ostore_st"
 "inv_ostore_index_gim_disjoint (ostore_st\<lparr>sync_offs\<^sub>f := v\<rparr>) = inv_ostore_index_gim_disjoint ostore_st"
 "inv_ostore_fsm mount_st (ostore_st\<lparr>sync_offs\<^sub>f := v\<rparr>) = inv_ostore_fsm mount_st ostore_st"
 "inv_flash (list_eb_log_wbuf (ostore_st\<lparr>sync_offs\<^sub>f := v\<rparr>)) = inv_flash (list_eb_log_wbuf ostore_st)"
      apply (clarsimp simp: inv_ostore_summary_def room_for_summary_def
              inv_sum_consistent_def os_sum_sz_def)
     apply (simp add: inv_ostore_index_def Let_def is_valid_addr_def ostore_get_obj_def)
    apply (simp add: inv_ostore_index_gim_disjoint_def)
   apply (simp add: inv_ostore_fsm_def list_eb_log_wbuf_def list_eb_log_def del: list_trans.simps)
  apply (simp add: inv_flash_def)
 done

lemma inv_ostore_medium_buf_prepared:
shows
 "\<alpha>_ostore_medium
        (ostore_st
         \<lparr>wbuf\<^sub>f := wbuf\<^sub>f ostore_st
            \<lparr>data\<^sub>f :=
               WordArrayT.make
                (buf_prepared ostore_st (used\<^sub>f ostore_st)
                  (padding_to (mount_st, ostore_st, ostoreWriteNone))
                  (prepared_pad_obj ostore_st (padding_to (mount_st, ostore_st, ostoreWriteNone)) crc))\<rparr>,
         used\<^sub>f := padding_to (mount_st, ostore_st, ostoreWriteNone) \<rparr>) =
       \<alpha>_ostore_medium ostore_st"
by (clarsimp simp add: \<alpha>_ostore_medium_def abstract_mount_\<alpha>_ostore_def list_eb_log_def)

lemma snd_list_trans_buf_prepared_eq:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and     used_gt_zero: "0 < used\<^sub>f ostore_st"
  and     sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"

  notes  invs_pad_ofs = inv_ostore inv_mount_st pad_to used_gt_zero sync_lt_used
  shows
  "prod.snd (list_trans_no_pad
   (buf_slice
     (wbuf\<^sub>f ostore_st
      \<lparr>data\<^sub>f :=
         WordArrayT.make
          (buf_prepared ostore_st (used\<^sub>f ostore_st)
            (padding_to (mount_st, ostore_st, ostoreWriteNone))
            (prepared_pad_obj ostore_st
              (padding_to (mount_st, ostore_st, ostoreWriteNone)) crc))\<rparr>)
     (sync_offs\<^sub>f ostore_st)
     (padding_to (mount_st, ostore_st, ostoreWriteNone)))) =
   prod.snd(list_trans_no_pad (buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st)
       (used\<^sub>f ostore_st)))"
 proof -
   show ?thesis
   proof cases
     assume pt: "padding_to (mount_st, ostore_st, ostoreWriteNone) - used\<^sub>f ostore_st < bilbyFsObjHeaderSize"
     have bound: "unat (bound\<^sub>f (wbuf\<^sub>f ostore_st)) \<le> length (\<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st)))"
        using  inv_ostore_bound_le_lenD[OF inv_ostore] by simp
     have used_of: "used\<^sub>f ostore_st \<le> used\<^sub>f ostore_st + (pad_to - used\<^sub>f ostore_st)"
        apply (simp add: pad_to)
        using used_le_padding_to[OF inv_ostore inv_mount_st] by simp
        
     show ?thesis
     using pt
     using snd_list_trans_memset[OF invs_pad_ofs, where frm="sync_offs\<^sub>f ostore_st"]
     by (simp add: buf_prepared_def pad_to buf_memset_eq[where buf="wbuf\<^sub>f ostore_st", OF bound used_of, simplified pad_to])
   next
     assume "\<not> padding_to (mount_st, ostore_st, ostoreWriteNone) - used\<^sub>f ostore_st < bilbyFsObjHeaderSize"
     thus ?thesis
     apply (simp add: buf_prepared_def pad_to)
       apply (rule snd_list_trans_no_pad_padding_obj_sync_pad_to[OF invs_pad_ofs, simplified pad_to])
       apply (simp add: prepared_pad_obj_def)
       apply (rule valid_commit_pad_obj[OF inv_ostore inv_mount_st pad_to, simplified is_valid_ObjTrans, THEN conjunct1])
       apply (rule_tac x=crc in exI)
       apply (simp add: prepared_pad_obj_def prepared_pad_obj_no_crc_def ostore_update_padding_obj' pad_to bilbyFsObjHeaderSize_def bilbyFsTransCommit_def)+
     apply (rule_tac x=crc in exI)
     apply (simp add: prepared_pad_obj_no_crc_def  ostore_update_padding_obj' pad_to bilbyFsObjHeaderSize_def bilbyFsTransCommit_def)
     using inv_ostore_valid_pad_objD[OF inv_ostore]
      apply (clarsimp simp add: prepared_pad_obj_no_crc_def valid_pad_obj_def prepared_pad_obj_def is_valid_Obj_def)
      apply simp
    done
   qed
qed

lemma valid_list_trans_buf_prepared_eq:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and     used_gt_zero: "0 < used\<^sub>f ostore_st"
  and     sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"

  notes invs_pad = inv_ostore inv_mount_st pad_to 

  shows
 "valid_list_trans
     (buf_slice
       (wbuf\<^sub>f ostore_st
        \<lparr>data\<^sub>f :=
           WordArrayT.make
            (buf_prepared ostore_st (used\<^sub>f ostore_st) pad_to
              (prepared_pad_obj ostore_st pad_to crc))\<rparr>)
       (sync_offs\<^sub>f ostore_st) pad_to)"
proof -
      have bound: "unat (bound\<^sub>f (wbuf\<^sub>f ostore_st)) \<le> length (\<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st)))"
        using  inv_ostore_bound_le_lenD[OF inv_ostore] by simp
     have used_of: "used\<^sub>f ostore_st \<le> used\<^sub>f ostore_st + (pad_to - used\<^sub>f ostore_st)"
        apply (simp add: pad_to)
        using used_le_padding_to[OF inv_ostore inv_mount_st] by simp
        
show ?thesis

  apply (simp add: buf_prepared_def prepared_pad_obj_def)
  apply (case_tac "pad_to - used\<^sub>f ostore_st < bilbyFsObjHeaderSize")
   apply simp
   using buf_slice_buf_memset_is_append_padding[OF invs_pad, where frm="sync_offs\<^sub>f ostore_st", simplified buf_memset_eq[OF bound used_of]]
   using inv_bufsD[OF inv_ostore]  sync_lt_used
   apply (simp add: valid_list_trans_append_padding valid_list_trans_no_pad_imp_valid_list_trans)
   apply simp
   apply (rule  valid_list_trans_buf_slice_sync_offs_pad_to[OF invs_pad used_gt_zero sync_lt_used])
     apply (rule valid_commit_pad_obj[OF inv_ostore inv_mount_st pad_to, simplified is_valid_ObjTrans, THEN conjunct1])
      apply (rule_tac x=crc in exI)
      apply (simp add: prepared_pad_obj_def prepared_pad_obj_no_crc_def ostore_update_padding_obj' pad_to bilbyFsObjHeaderSize_def bilbyFsTransCommit_def)+
    apply (rule_tac x=crc in exI)
     apply (simp add: prepared_pad_obj_def prepared_pad_obj_no_crc_def ostore_update_padding_obj' pad_to bilbyFsObjHeaderSize_def bilbyFsTransCommit_def)+
     using inv_ostore_valid_pad_objD[OF inv_ostore]
      apply (clarsimp simp add: prepared_pad_obj_no_crc_def valid_pad_obj_def prepared_pad_obj_def is_valid_Obj_def)
    apply simp
 done
qed

lemma list_trans_no_pad_slice_drop_append:
notes list_trans.simps[simp del]
and   pTrans.simps[simp del]
assumes valid_slice: "valid_list_trans (slice frm to xs)"
and valid_drop: "valid_list_trans (drop to xs)"
and "frm \<le> to"
and "to \<le> length xs"
shows
 "prod.snd (list_trans_no_pad (slice frm to xs)) @ prod.snd (list_trans_no_pad (drop to xs)) =
  prod.snd (list_trans_no_pad (drop frm xs))"
  using list_trans_no_pad_append[where xs="slice frm to xs" and ys="drop to xs"]
        assms
  by (clarsimp simp: slice_drop)

lemma map_ostore_update_append:
 "map ostore_update xs @ map ostore_update ys = map ostore_update (xs @ ys)"
 by simp

lemma fold_id_append:
 "fold id xs (fold id ys Map.empty) = fold id (ys @ xs) Map.empty"
 by simp

(* Taken from AFP containers *)
lemma insort_key_append1:
  "\<forall>y \<in> set ys. f x < f y \<Longrightarrow> insort_key f x (xs @ ys) = insort_key f x xs @ ys"
proof(induct xs)
  case Nil
  thus ?case by(cases ys) auto
qed simp

lemma insort_key_append2:
  "\<forall>y \<in> set xs. f x > f y \<Longrightarrow> insort_key f x (xs @ ys) = xs @ insort_key f x ys"
by(induct xs) auto

lemma sort_key_append[symmetric]:
  "\<forall>x\<in>set xs. \<forall>y\<in>set ys. f x < f y \<Longrightarrow> sort_key f (xs @ ys) = sort_key f xs @ sort_key f ys"
by(induct xs)(simp_all add: insort_key_append1)

(* end of AFP containers *)

lemma inj_on_filter_key_eq:
  "inj_on s (insert k (set xs)) \<Longrightarrow> [x\<leftarrow>xs . s k = s x] = filter ((=) k) xs"
  apply (induct xs)
   apply simp
  apply (drule meta_mp, erule subset_inj_on)
   apply auto[1]
  apply (drule_tac x=k and y=a in inj_on_eq_iff, auto)
  done

lemma filter_eq_replicate_count_multiset:
  "filter ((=) k) xs = replicate (count (mset xs) k) k"
  by (induct xs, auto)

lemma sort_key_multiset_eq:
  assumes multiset: "mset xs = mset ys"
        and inj_on: "inj_on f (set xs)"
  shows "sort_key f xs = sort_key f ys"
proof -
  from multiset have set:
    "set xs = set ys"
    by (rule mset_eq_setD)
  note filter = inj_on_filter_key_eq[OF subset_inj_on, OF inj_on]
  show ?thesis
  apply (rule properties_for_sort_key)
    apply (simp add: multiset)
   apply (simp add: filter set)
   apply (simp add: filter_eq_replicate_count_multiset multiset)
  apply simp
  done
qed

lemma sort_key_concat_map:
  assumes i: "i < length xs" "i \<ge> n"
      and f: "f (xs!i@ys) = f (xs!i) @ f ys"
      and s: "inj_on s (set (concat (map f (drop n xs@[ys]))))"
  shows "sort_key s (concat (map f (drop n (xs[i:=xs!i@ys])))) =
    sort_key s (concat (map f ((drop n xs)@[ys])))"
proof -
  from i obtain xs1 xi xs2 where xs_split: "xs = xs1 @ [xi] @ xs2"
        and xi: "xs ! i = xi" and length_xs1[simp]: "length xs1 = i"
    apply (erule_tac x="take i xs" in meta_allE)
    apply (erule_tac x="xs ! i" in meta_allE)
    apply (erule_tac x="tl (drop i xs)" in meta_allE)
    apply (cases "drop i xs", simp_all)
    apply (frule_tac f=hd in arg_cong, subst(asm) hd_drop_conv_nth, simp+)
    apply (cut_tac n=i and xs=xs in append_take_drop_id, simp)
    done

  from i have multiset: "mset (concat (map f (drop n xs))) + mset (f ys) =
        mset (concat (map f (drop n (xs[i := xs ! i @ ys]))))"

    apply (simp add: xs_split drop_list_update)
    apply (simp add: list_update_append nth_append f[simplified xi])
    done

  note set = arg_cong[where f=set_mset, OF multiset[symmetric], simplified]

  show ?thesis
    apply (rule sort_key_multiset_eq)
     apply (simp add: multiset)
    apply (rule subset_inj_on[OF s])
    apply (simp add: set)
    done
qed

lemma sort_key_concat_ignores_order:
 assumes inv_ostore: "inv_ostore mount_st ostore_st"
 assumes trans_order:
 "\<forall>x\<in>set (concat $ list_eb_log (\<alpha>wubi $ OstoreState.ubi_vol\<^sub>f ostore_st)).
       \<forall>y\<in>set (prod.snd (list_trans_no_pad xs)).
          trans_order x < trans_order y"
 assumes inj: "inj_on trans_order
     (set (concat
            (map (prod.snd \<circ> list_trans_no_pad)
              (drop (unat bilbyFsFirstLogEbNum) (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st)) @
               [xs]))))"
 assumes used_gt_0: "0 < used\<^sub>f ostore_st"
 assumes valid_xs: "valid_list_trans xs"
shows
"sort_key trans_order
 (concat (map (prod.snd \<circ> list_trans_no_pad) (drop (unat bilbyFsFirstLogEbNum)
  ((\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st)) [unat (wbuf_eb\<^sub>f ostore_st) :=
    \<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) ! unat (wbuf_eb\<^sub>f ostore_st) @ xs])))) =
sort_key trans_order
 (concat (map (prod.snd \<circ> list_trans_no_pad) (drop (unat bilbyFsFirstLogEbNum)
 (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st)) @ [xs])))"
  apply (rule sort_key_concat_map)
     using inv_ostore apply (clarsimp simp: inv_ostore_def inv_bufs_def inv_ubi_vol_def, unat_arith)
    using inv_ostore apply (clarsimp simp: inv_ostore_def, unat_arith)
   apply (simp)
   apply (rule list_trans_no_pad_append[symmetric])
    using inv_bufsD[OF inv_ostore] used_gt_0
      apply (clarsimp)
     apply (drule sym[where t="buf_take (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) "])
    apply (simp add: buf_simps valid_list_trans_no_pad_def)
   using valid_xs apply simp
  using inj apply simp
 done

lemma inv_ostore_list_trans_wbuf_sorted[simplified Let_def]:
 "inv_ostore mount_st ostore_st \<Longrightarrow> 
  (let sync_to_used = buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st) in
  sort_key trans_order (prod.snd (list_trans_no_pad sync_to_used)) =
     prod.snd (list_trans_no_pad sync_to_used))"
 by (drule inv_bufsD, clarsimp simp: Let_def)

lemma ostore_sync_\<alpha>_ostore_uptodate:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and     used_gt_zero: "0 < used\<^sub>f ostore_st"
  and     sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
  and     wubi: "list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st')) = 
list_eb_log ((\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))
 [unat (wbuf_eb\<^sub>f ostore_st) :=
    \<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) ! unat (wbuf_eb\<^sub>f ostore_st) @
    buf_slice
     (wbuf\<^sub>f ostore_st
      \<lparr>data\<^sub>f :=
         WordArrayT.make
          (buf_prepared ostore_st (used\<^sub>f ostore_st)
            (padding_to (mount_st, ostore_st, ostoreWriteNone))
            (prepared_pad_obj ostore_st (padding_to (mount_st, ostore_st, ostoreWriteNone)) crc))\<rparr>)
     (sync_offs\<^sub>f ostore_st) (padding_to (mount_st, ostore_st, ostoreWriteNone))])"
     (is "... = list_eb_log (?ubi[?wbuf_eb:=?old_ubi@?buf_prepared])")
 and ostore_m: "ostore_st'\<lparr>OstoreState.ubi_vol\<^sub>f := v\<rparr> = ostore_st
       \<lparr>wbuf\<^sub>f := wbuf\<^sub>f ostore_st
          \<lparr>data\<^sub>f :=
             WordArrayT.make
              (buf_prepared ostore_st (used\<^sub>f ostore_st)
                (padding_to (mount_st, ostore_st, ostoreWriteNone))
                (prepared_pad_obj ostore_st (padding_to (mount_st, ostore_st, ostoreWriteNone)) crc))\<rparr>,
          used\<^sub>f := padding_to (mount_st, ostore_st, ostoreWriteNone),
          fsm_st\<^sub>f := prepared_fsm_padding_obj ostore_st (used\<^sub>f ostore_st'), OstoreState.oaddr\<^sub>f := oaddr,
          OstoreState.next_sqnum\<^sub>f := nxtsqnum, opad\<^sub>f := opad\<^sub>f ostore_st\<lparr>Obj.len\<^sub>f := len, Obj.sqnum\<^sub>f := sqnum, crc\<^sub>f := crc\<rparr>\<rparr>" 
          (is "... = ?ostore_st")

  notes invs_pad_offs = inv_ostore inv_mount_st pad_to used_gt_zero sync_lt_used

shows
 "\<alpha>_ostore_medium (ostore_st'\<lparr>sync_offs\<^sub>f := used\<^sub>f ostore_st'\<rparr>) = \<alpha>_ostore_uptodate ostore_st"
 
proof -

have sort_key_trans_key_eq: "sort_key trans_order (concat  (map (prod.snd \<circ> list_trans_no_pad)
   (drop (unat bilbyFsFirstLogEbNum) (?ubi
       [?wbuf_eb := ?ubi ! ?wbuf_eb @ ?buf_prepared])))) =
 sort_key trans_order (concat  (map (prod.snd \<circ> list_trans_no_pad)
   (drop (unat bilbyFsFirstLogEbNum) ?ubi @ [?buf_prepared])))"
   apply (subst sort_key_concat_ignores_order[OF inv_ostore _ _ used_gt_zero])
       using snd_list_trans_buf_prepared_eq[OF invs_pad_offs]
       apply (simp only: )
       using inv_logD[OF inv_ostore]
       apply clarsimp
      apply (simp only: map_append)
       using snd_list_trans_buf_prepared_eq[OF invs_pad_offs]
             inv_logD[OF inv_ostore]
       apply (fastforce simp: list_eb_log_def)
      using sync_lt_used inv_bufsD[OF inv_ostore] apply clarsimp
      using valid_list_trans_buf_prepared_eq[OF invs_pad_offs]
      apply (simp add: pad_to)+
   done

  have sort_trans_key_list_eb_log_eq_append_list_trans: 
  "sort_key trans_order (concat (list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st')))) =
    sort_key trans_order (concat (list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))) @
      prod.snd (list_trans_no_pad (buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st))))"
   apply (simp only: wubi)
   apply (simp add:  ostore_m list_eb_log_def Let_def)
   apply (simp only: sort_key_trans_key_eq)
   apply simp
   apply (simp only: snd_list_trans_buf_prepared_eq[OF invs_pad_offs])
  done

 from inv_logD[OF inv_ostore] have trans_order':
 "\<forall>x\<in>set (concat $ list_eb_log $ \<alpha>wubi $ OstoreState.ubi_vol\<^sub>f ostore_st).
       \<forall>y\<in>set (prod.snd (list_trans_no_pad (buf_slice (wbuf\<^sub>f ostore_st)
                (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st)))).
          trans_order x < trans_order y"
    by (simp add: snd_list_trans_buf_prepared_eq[OF inv_ostore inv_mount_st])

show ?thesis
   apply (simp add: \<alpha>_ostore_uptodate_def \<alpha>_ostore_medium_def abstract_mount_\<alpha>_ostore_def
       wubi \<alpha>_updates_def del: list_trans.simps)
   apply (simp only: fold_id_append map_ostore_update_append)
   apply (rule arg_cong[where f="\<lambda>x. fold id x Map.empty"])
   apply (rule arg_cong[where f="map ostore_update"])
   apply (subst inv_ostore_list_trans_wbuf_sorted[OF inv_ostore, symmetric])
   using sort_key_append[OF trans_order'[unfolded fun_app_def] ]
   apply (simp add: sort_trans_key_list_eb_log_eq_append_list_trans[simplified wubi])
  done
qed

lemma inv_ostore_updated_ubi_preserved:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     nb_bytes_eq_pad_to_minus_sync: "nb_bytes = padding_to (mount_st, ostore_st, ostoreWriteNone) - sync_offs\<^sub>f ostore_st"
  and     nb_bytes: "0 < nb_bytes"
  and     used_gt_zero: "0 < used\<^sub>f ostore_st"
  and     sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
  and     inv_ubi_vol: "inv_ubi_vol mount_st ubi_vol'"
  and     wubi:
 "\<alpha>wubi ubi_vol' = (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))
   [unat (wbuf_eb\<^sub>f ostore_st) :=
      \<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) ! unat (wbuf_eb\<^sub>f ostore_st) @
      buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st + nb_bytes)]"
  and nb_bytes_eq: "sync_offs\<^sub>f ostore_st + nb_bytes = used\<^sub>f ostore_st"

  shows
   "inv_ostore mount_st (ostore_st\<lparr>OstoreState.ubi_vol\<^sub>f := ubi_vol', sync_offs\<^sub>f := used\<^sub>f ostore_st\<rparr>)"
  (is "inv_ostore mount_st ?ostore_st")
 proof -
 have ostore_upt_Nil: "\<alpha>_updates ?ostore_st = []"
   using wubi by (simp add: \<alpha>_updates_def \<alpha>_ostore_uptodate_def buf_slice_n_n)
 have wubi_mod_ostore_get_obj_eq:
   "\<And>addr. addr \<in> ran (\<alpha>_index (index_st\<^sub>f ostore_st)) \<Longrightarrow> ostore_get_obj ?ostore_st addr = ostore_get_obj ostore_st addr"
   using wubi by (simp add: ostore_get_obj_def)
 moreover have ostore_rt_eq: "\<alpha>_ostore_runtime ?ostore_st = \<alpha>_ostore_runtime ostore_st"
   apply (rule ext)
   apply (clarsimp simp: option.case_eq_if \<alpha>_ostore_runtime_def \<alpha>_ostore_medium_def)
   using wubi_mod_ostore_get_obj_eq[simplified ran_def] apply fastforce
   done
(* copy-paste from proof above should unify them somehow*)
 from inv_logD[OF inv_ostore] have trans_order':
 "\<forall>x\<in>set (concat ( list_eb_log ( \<alpha>wubi ( OstoreState.ubi_vol\<^sub>f ostore_st)))).
       \<forall>y\<in>set (prod.snd (list_trans_no_pad (buf_slice (wbuf\<^sub>f ostore_st)
                (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st)))).
          trans_order x < trans_order y"
    by (simp add: snd_list_trans_buf_prepared_eq[OF inv_ostore inv_mount_st])

have sort_key_trans_key_eq:
  "sort_key trans_order
     (concat (map (prod.snd \<circ> list_trans_no_pad)
               (drop (unat bilbyFsFirstLogEbNum)
                 ((\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))
                  [unat (wbuf_eb\<^sub>f ostore_st) :=
                     \<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) ! unat (wbuf_eb\<^sub>f ostore_st) @
                     buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st)])))) =
    sort_key trans_order
     (concat (map (prod.snd \<circ> list_trans_no_pad) (drop (unat bilbyFsFirstLogEbNum) (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st)))) @
      prod.snd (list_trans_no_pad (buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st))))"
   apply (subst sort_key_concat_ignores_order[OF inv_ostore _ _ used_gt_zero])
       apply (simp add: trans_order')
       using inv_logD[OF inv_ostore]
       apply (clarsimp simp: list_eb_log_def)
      using sync_lt_used inv_bufsD[OF inv_ostore] apply (clarsimp simp: valid_list_trans_no_pad_imp_valid_list_trans)
      using valid_list_trans_buf_prepared_eq[OF inv_ostore inv_mount_st, where pad_to="padding_to (mount_st, ostore_st, ostoreWriteNone)"]
      apply (simp)+
   done

  have sort_trans_key_list_eb_log_eq_append_list_trans: 
  "sort_key trans_order (concat (list_eb_log (\<alpha>wubi ubi_vol'))) =
    sort_key trans_order (concat (list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))) @
      prod.snd (list_trans_no_pad (buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st))))"
   apply (simp only: wubi nb_bytes_eq)
   apply (simp add:  list_eb_log_def Let_def)
   apply (simp only: sort_key_trans_key_eq)
  done

  moreover have ostore_uptodate_eq_new_ostore_medium:
   "\<alpha>_ostore_medium ?ostore_st = \<alpha>_ostore_uptodate ostore_st"
   apply (simp add: \<alpha>_ostore_medium_def abstract_mount_\<alpha>_ostore_def wubi)
   apply (simp add: \<alpha>_ostore_uptodate_def nb_bytes_eq)
   apply (simp add: \<alpha>_ostore_uptodate_def \<alpha>_ostore_medium_def abstract_mount_\<alpha>_ostore_def
       wubi \<alpha>_updates_def del: list_trans.simps)
   apply (simp only: fold_id_append map_ostore_update_append)
   apply (rule arg_cong[where f="\<lambda>x. fold id x Map.empty"])
   apply (rule arg_cong[where f="map ostore_update"])
   apply (subst inv_ostore_list_trans_wbuf_sorted[OF inv_ostore, symmetric])
   apply (rule sym)
   apply (rule trans[OF sort_key_append[OF trans_order' ]])
   using sort_trans_key_list_eb_log_eq_append_list_trans[simplified wubi,symmetric]
   apply (simp add: nb_bytes_eq)
  done

  moreover have ostore_uptodate_eq:
   "\<alpha>_ostore_uptodate ?ostore_st = \<alpha>_ostore_uptodate ostore_st"
   using ostore_uptodate_eq_new_ostore_medium ostore_upt_Nil
   by (simp add: \<alpha>_ostore_uptodate_def)

 moreover have "inv_fsm_st mount_st (fsm_st\<^sub>f ?ostore_st)"
  using inv_fsm_stD[OF inv_ostore] by(simp add: inv_fsm_st_def)

 moreover have list_eb_log_wbuf_eq:
   "list_eb_log_wbuf ?ostore_st = list_eb_log_wbuf ostore_st"
   apply (simp add: list_eb_log_wbuf_def wubi list_eb_log_def)
   apply (clarsimp simp add: list_eq_iff_nth_eq)
   apply (case_tac "i  = unat (wbuf_eb\<^sub>f ostore_st) - unat bilbyFsFirstLogEbNum")
    apply simp
   apply simp
  done

 moreover have "inv_ostore_fsm mount_st  ?ostore_st"
   using list_eb_log_wbuf_eq inv_ostore[simplified inv_ostore_def] 
   by (clarsimp simp add: inv_ostore_fsm_def wubi)

 moreover have "inv_ostore_index mount_st ?ostore_st"
   using inv_ostore_indexD[OF inv_ostore]  wubi_mod_ostore_get_obj_eq[simplified ran_def]
   apply (clarsimp simp add:  Let_def inv_ostore_index_def)
   apply (rename_tac oid oaddr, erule_tac x=oid in ballE)
   apply (simp add: is_valid_addr_def)
   apply fastforce+
  done

  moreover have "inv_bufs mount_st ?ostore_st"
    using inv_bufsD[OF inv_ostore] inv_ubi_vol apply (clarsimp simp: inv_bufs_def wubi Let_def nb_bytes_eq)
    apply (simp add: buf_slice_n_n)
    apply (simp add: used_gt_zero )
    apply (simp add: sync_lt_used buf_take_buf_slice_adjacent[OF order_less_imp_le[OF sync_lt_used]])
    using inv_ostore_wbuf_eb_rangeD[OF inv_ostore ] inv_ubi_vol
    apply (clarsimp simp add:inv_ubi_vol_def wubi)
    apply (rule conjI)
     apply (simp add: unat_arith_simps)
    using buf_take_buf_slice_adjacent[OF order_less_imp_le[OF sync_lt_used],symmetric]
          valid_list_trans_no_pad_append
    by fastforce

  moreover have " inv_log (list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ?ostore_st)))
    (prod.snd $ list_trans_no_pad (buf_slice (wbuf\<^sub>f ?ostore_st) (sync_offs\<^sub>f ?ostore_st) (used\<^sub>f ?ostore_st)))"
    using inv_logD[OF inv_ostore, THEN conjunct2]
    apply (simp add: wubi buf_slice_n_n inv_log_def nb_bytes_eq list_eb_log_def del: set_concat)
    using inv_ostore_wbuf_eb_rangeD[OF inv_ostore ] inv_ubi_vol
    apply (clarsimp simp add:word_less_nat_alt word_le_nat_alt inv_ubi_vol_def wubi simp del: set_concat)
    apply (simp add: drop_list_update)
    apply (erule subset_inj_on)
    apply (rule order_trans, rule UN_mono, rule set_update_subset_insert, rule subset_refl)
    apply simp
    apply (subst list_trans_no_pad_append[where xs="\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) ! unat (wbuf_eb\<^sub>f ostore_st)"
        and ys=" buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st)",symmetric])
    prefer 3
    apply (simp, simp add: subset_iff)
    apply (intro allI impI, rule disjI1, rule rev_bexI,
        rule_tac n="unat (wbuf_eb\<^sub>f ostore_st) - unat bilbyFsFirstLogEbNum" in nth_mem, simp)
    apply simp
     using inv_bufsD[OF inv_ostore] used_gt_zero apply (simp add: inv_ubi_vol_def valid_list_trans_no_pad_imp_valid_list_trans)
     using inv_bufsD[OF inv_ostore] sync_lt_used apply (simp add: inv_ubi_vol_def valid_list_trans_no_pad_imp_valid_list_trans)
   done

  moreover have "io_size\<^sub>f (super\<^sub>f mount_st) udvd used\<^sub>f ostore_st"
   using nb_bytes_eq[symmetric] nb_bytes_eq_pad_to_minus_sync
   apply simp
   apply (thin_tac _)+
   (* Why do I need to do this thin_tac nonsense to get this goal? *)
   apply (simp add: padding_to_def[unfolded tuple_simps sanitizers])
   apply (rule al_dvd_align32)
   using inv_mount_st[simplified inv_mount_st_def Let_def] apply clarsimp
   using inv_ostore_used_no_overflowD[OF inv_ostore] apply simp
  done
 ultimately show ?thesis
 using inv_ostore apply (simp add: inv_ostore_def ostore_uptodate_eq_new_ostore_medium ostore_rt_eq wubi)
  apply (clarsimp simp: inv_ostore_simps Let_def )
  done
qed

lemma \<alpha>_updates_buf_prepare_eq:
assumes inv_ostore: "inv_ostore mount_st ostore_st"
and     inv_mount_st: "inv_mount_st mount_st"
and     sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
shows
 "
  OstoreState.next_sqnum\<^sub>f ostore_st \<le> next_sqnum \<Longrightarrow>
  inv_ostore mount_st
   (ostore_st
    \<lparr>wbuf\<^sub>f := wbuf\<^sub>f ostore_st
       \<lparr>data\<^sub>f :=
          WordArrayT.make
           (buf_prepared ostore_st (used\<^sub>f ostore_st)
             (padding_to (mount_st, ostore_st, ostoreWriteNone))
             (prepared_pad_obj ostore_st (padding_to (mount_st, ostore_st, ostoreWriteNone)) crc))\<rparr>,
       used\<^sub>f := padding_to (mount_st, ostore_st, ostoreWriteNone),
      fsm_st\<^sub>f := prepared_fsm_padding_obj ostore_st (padding_to (mount_st, ostore_st, ostoreWriteNone)), OstoreState.oaddr\<^sub>f := oaddr,
      OstoreState.next_sqnum\<^sub>f := nxtsqnum, opad\<^sub>f := opad\<^sub>f ostore_st\<lparr>Obj.len\<^sub>f := len, Obj.sqnum\<^sub>f := sqnum, crc\<^sub>f := crc\<rparr>\<rparr>) \<Longrightarrow>
  \<alpha>_updates
       (ostore_st
        \<lparr>wbuf\<^sub>f := wbuf\<^sub>f ostore_st
           \<lparr>data\<^sub>f :=
              WordArrayT.make
               (buf_prepared ostore_st (used\<^sub>f ostore_st)
                 (padding_to (mount_st, ostore_st, ostoreWriteNone))
                 (prepared_pad_obj ostore_st (padding_to (mount_st, ostore_st, ostoreWriteNone)) crc))\<rparr>,
           used\<^sub>f := padding_to (mount_st, ostore_st, ostoreWriteNone),
          fsm_st\<^sub>f := prepared_fsm_padding_obj ostore_st (padding_to (mount_st, ostore_st, ostoreWriteNone)), OstoreState.oaddr\<^sub>f := oaddr,
          OstoreState.next_sqnum\<^sub>f := nxtsqnum, opad\<^sub>f := opad\<^sub>f ostore_st\<lparr>Obj.len\<^sub>f := len, Obj.sqnum\<^sub>f := sqnum, crc\<^sub>f := crc\<rparr>
        \<rparr>) =  \<alpha>_updates ostore_st"
   proof -
     obtain pad_to::U32 where pad_to:"pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)" by simp
     have used_gt_zero: "0 < used\<^sub>f ostore_st"
      using sync_lt_used by unat_arith

     have bound: "unat (bound\<^sub>f (wbuf\<^sub>f ostore_st)) \<le> length (\<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st)))"
        using  inv_ostore_bound_le_lenD[OF inv_ostore] by simp
     have used_of: "used\<^sub>f ostore_st \<le> used\<^sub>f ostore_st + (pad_to - used\<^sub>f ostore_st)"
        apply (simp add: pad_to)
        using used_le_padding_to[OF inv_ostore inv_mount_st] by simp

    show ?thesis
   apply (simp add: buf_prepared_def)
   apply (case_tac "padding_to (mount_st, ostore_st, ostoreWriteNone) - used\<^sub>f ostore_st
                 < bilbyFsObjHeaderSize")

    apply (simp add: \<alpha>_updates_def)
    apply (rule arg_cong[where f="map ostore_update"])
    using buf_slice_buf_memset_is_append_padding[OF inv_ostore inv_mount_st pad_to, where frm="sync_offs\<^sub>f ostore_st", simplified pad_to]
    using  buf_memset_eq[OF bound used_of, simplified pad_to]
    apply (simp )
    apply (rule snd_list_trans_no_pad_padding_unchanged)
    using inv_bufsD[OF inv_ostore] sync_lt_used
     apply (simp add: valid_list_trans_no_pad_imp_valid_list_trans)
   apply (simp add: \<alpha>_updates_def)
   apply (rule arg_cong[where f="map ostore_update"])
   apply (rule snd_list_trans_no_pad_padding_obj_sync_pad_to[OF inv_ostore inv_mount_st pad_to used_gt_zero sync_lt_used, simplified pad_to])
   apply (rule valid_commit_pad_obj[OF inv_ostore inv_mount_st pad_to, simplified is_valid_ObjTrans, THEN conjunct1])
      apply (rule_tac x=crc in exI)
      apply (simp add: prepared_pad_obj_def prepared_pad_obj_no_crc_def ostore_update_padding_obj' pad_to bilbyFsObjHeaderSize_def bilbyFsTransCommit_def)+
     apply (rule_tac x=crc in exI)
     apply (simp add: prepared_pad_obj_def prepared_pad_obj_no_crc_def ostore_update_padding_obj' pad_to bilbyFsObjHeaderSize_def bilbyFsTransCommit_def)+
          using inv_ostore_valid_pad_objD[OF inv_ostore]
      apply (clarsimp simp add: prepared_pad_obj_no_crc_def valid_pad_obj_def prepared_pad_obj_def is_valid_Obj_def)
     apply simp
  done
qed

lemma ostore_write_buf_ret:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and inv_mount_st: "inv_mount_st mount_st"
  and inv_step: "inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st)"
  and used_gt_zero: "0 < used\<^sub>f ostore_st"
  and sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
  and offs_ok: "unat (sync_offs\<^sub>f ostore_st) + unat nb_bytes \<le> unat (eb_size\<^sub>f (super\<^sub>f mount_st))"
  and nb_bytes_ok: "io_size\<^sub>f (super\<^sub>f mount_st) udvd nb_bytes"
  and sync_offs: "sync_offs = sync_offs\<^sub>f ostore_st"
  and nb_bytes_eq: "sync_offs\<^sub>f ostore_st + nb_bytes = used\<^sub>f ostore_st"
  and nb_bytes_eq_pad_to_minus_sync: "nb_bytes = padding_to (mount_st, ostore_st, ostoreWriteNone) - sync_offs\<^sub>f ostore_st"
  and err:
   "\<And>ex'. P ((ex',ostore_st), Error eIO)"
  and suc:
  "\<And>ex' ostore_st'. \<lbrakk>
     inv_ostore mount_st (ostore_st' \<lparr> sync_offs\<^sub>f := used\<^sub>f ostore_st\<rparr>);
     \<exists>v. ostore_st'\<lparr>OstoreState.ubi_vol\<^sub>f := v\<rparr> = ostore_st;
     \<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st') = (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))[(unat (wbuf_eb\<^sub>f ostore_st)):=((\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st)!(unat (wbuf_eb\<^sub>f ostore_st)))@buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st + nb_bytes))] \<rbrakk> \<Longrightarrow>
      P ((ex', ostore_st'), Success ())
 "
shows
"P (ostore_write_buf(ex, mount_st, ostore_st, sync_offs, nb_bytes, ostoreWriteNone))"
unfolding ostore_write_buf_def[unfolded tuple_simps sanitizers, simplified take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def]
  apply (simp add: sync_offs)
  apply safe
   apply (rule wubi_leb_write_ret[where mount_st=mount_st])
         apply (rule length_ubi_buf_eq_sync_offsD[OF inv_ostore inv_mount_st])
        apply (rule inv_ostore_wbuf_lengthD[OF inv_ostore])
       apply (rule offs_ok)
      apply (rule nb_bytes_ok)
     using inv_bufsD[OF inv_ostore] apply clarsimp
    apply (simp add: err)
   apply simp
   apply (rule suc)
      apply (erule (2) inv_ostore_updated_ubi_preserved[OF inv_ostore inv_mount_st nb_bytes_eq_pad_to_minus_sync _  used_gt_zero sync_lt_used])
       apply (simp add: nb_bytes_eq)
    apply (rule_tac x="OstoreState.ubi_vol\<^sub>f ostore_st" in exI, fastforce)
   apply simp
  apply (rule suc)
     using sync_lt_used nb_bytes_eq inv_ostore apply (clarsimp simp: word_not_0_gr_n)+
 done

lemma extra_padding_is_aligned:
 assumes inv_ostore: "inv_ostore mount_st ostore_st"
 and     inv_mount_st: "inv_mount_st mount_st"
 and     sync_neq_used: "sync_offs\<^sub>f ostore_st \<noteq> used\<^sub>f ostore_st"
 shows
 "io_size\<^sub>f (super\<^sub>f mount_st) udvd  padding_to (mount_st, ostore_st, ostoreWriteNone) - sync_offs\<^sub>f ostore_st"
proof -
  have io_size_dvd_sync_offs: "io_size\<^sub>f (super\<^sub>f mount_st) udvd sync_offs\<^sub>f ostore_st"
    using inv_ostore by (clarsimp simp: inv_ostore_def)
  show ?thesis
  using inv_mount_st[simplified inv_mount_st_def Let_def]
  apply clarsimp
  apply (drule al_dvd_align32[OF _ inv_ostore_used_no_overflowD[OF inv_ostore]])
  using sync_offs_le_padding_to[OF inv_ostore inv_mount_st ]
        io_size_dvd_sync_offs
  apply (simp add: padding_to_def[unfolded tuple_simps sanitizers] ostoreWriteNone_def )
  apply (simp add: udvd_iff_dvd word_le_nat_alt unat_sub_if')
 done
qed

lemmas OstoreState_ext_eq_expand = trans[OF _ OstoreState.ext_inject,
    OF arg_cong2[where f="(=)"], OF refl OstoreState.surjective]
 
lemma ostore_sync_ret:
 assumes inv_ostore: "inv_ostore mount_st ostore_st"
 and inv_mount_st: "inv_mount_st mount_st"
 and inv_step: "inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st)"
 and suc: "\<And>ostore_st' ex'. \<lbrakk> inv_ostore mount_st ostore_st';
        inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st');
        \<alpha>_ostore_medium ostore_st' = \<alpha>_ostore_uptodate ostore_st;
        \<alpha>_updates ostore_st' = []
        \<rbrakk> \<Longrightarrow>
      P ((ex', ostore_st'), Success ())"
 and err: "\<And>e ostore_st' ex' n. \<lbrakk> inv_ostore mount_st ostore_st';
       inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st');
       e \<in> {eIO, eNoMem, eNoSpc,eOverflow};
       n < length (\<alpha>_updates ostore_st); 
       \<alpha>_ostore_medium ostore_st' = apply_n_updates n (\<alpha>_ostore_medium ostore_st) (\<alpha>_updates ostore_st);
       \<alpha>_updates ostore_st' = (drop n $ \<alpha>_updates ostore_st)
       \<rbrakk> \<Longrightarrow>
      P ((ex', ostore_st'), Error e)"

 notes pad_simps = padding_to_def[unfolded tuple_simps sanitizers] ostoreWriteNone_def

 shows "P (ostore_sync (ex, mount_st, ostore_st, ostoreWriteNone))"
using [[goals_limit=2]]
  unfolding ostore_sync_def[unfolded tuple_simps sanitizers]
  apply (case_tac "sync_offs\<^sub>f ostore_st = used\<^sub>f ostore_st")
   apply (simp add: ostoreWriteNone_def Let_def ostoreWriteNewEb_def)
   apply (rule suc[OF inv_ostore inv_step])
    apply (simp add: \<alpha>_ostore_uptodate_def used_eq_sync_offs_means_no_update)
   apply ( simp add: \<alpha>_updates_def buf_simps )
  apply (simp add: Let_def)
  apply (rule prepare_wbuf_ret[OF inv_ostore inv_mount_st inv_step])
      apply (rule refl)     
     using inv_ostore[simplified inv_ostore_def] apply clarsimp apply unat_arith
    using inv_ostore[simplified inv_ostore_def] apply clarsimp apply unat_arith
  apply (simp split: prod.split)
   apply (rule err[OF inv_ostore inv_step, where e=eOverflow and n=0, simplified])
    apply (erule used_neq_sync_offs_means_updates_not_Nil[OF inv_ostore])
  apply (simp)
  apply (rule ostore_sync_summary_if_eb_new_ret[OF _ inv_mount_st], simp_all)
  apply clarsimp
(*  apply (subgoal_tac "used\<^sub>f ostore_st' =  padding_to (mount_st, ostore_st, ostoreWriteNone)")
   apply (subgoal_tac "sync_offs\<^sub>f ostore_st' =  sync_offs\<^sub>f ostore_st")*)
    apply (rule ostore_write_buf_ret[OF _ inv_mount_st])
               apply simp
              apply (fastforce)
              apply clarsimp
              using used_le_padding_to[OF inv_ostore inv_mount_st ]
                    inv_ostore_sync_offsD[OF inv_ostore]  apply unat_arith
             using used_le_padding_to[OF inv_ostore inv_mount_st]
                   inv_ostore_sync_offsD[OF inv_ostore]
             apply (simp add: )
            apply (clarsimp simp add: OstoreState.splits OstoreState_ext_eq_expand offs_pl_padding_to_le_eb_size[OF inv_ostore inv_mount_st])
           apply (clarsimp simp: OstoreState.splits OstoreState_ext_eq_expand  extra_padding_is_aligned[OF inv_ostore inv_mount_st])
          apply (clarsimp simp: OstoreState.splits OstoreState_ext_eq_expand)
         apply (clarsimp simp: OstoreState.splits OstoreState_ext_eq_expand)
         apply (clarsimp simp: OstoreState.splits OstoreState_ext_eq_expand)
       apply (simp add: pad_simps)
       apply (subst align32_idempotence)
        using inv_mount_st[simplified inv_mount_st_def] apply (clarsimp simp: Let_def)
       using inv_ostore_used_no_overflowD[OF inv_ostore] apply simp
      apply simp
     apply (clarsimp)
    apply (rule err[where e=eIO and n=0, simplified])
         apply simp
        apply simp
      using inv_ostore_sync_offsD[OF inv_ostore]
            \<alpha>_updates_buf_prepare_eq[OF inv_ostore inv_mount_st]
            used_neq_sync_offs_means_updates_not_Nil[OF inv_ostore]
      apply (fastforce) 
    apply (fastforce simp add: \<alpha>_ostore_medium_def)
   using inv_ostore_sync_offsD[OF inv_ostore]
         \<alpha>_updates_buf_prepare_eq[OF inv_ostore inv_mount_st]
         used_neq_sync_offs_means_updates_not_Nil[OF inv_ostore]
   apply (fastforce)
  apply simp
  apply (rename_tac ex' ostore_st'')
  apply (subgoal_tac "padding_to (mount_st, ostore_st, ostoreWriteNone) = used\<^sub>f ostore_st''")
   apply (rule suc)
      apply clarsimp
     apply clarsimp
        apply (cut_tac v=v and crc=crc and ostore_st'=ostore_st''
                 and len=len and oaddr=oaddr and nxtsqnum=nxtsqnum
                 and sqnum=sqnum in
                ostore_sync_\<alpha>_ostore_uptodate[OF inv_ostore inv_mount_st])
           apply (rule refl)
          using used_le_padding_to[OF inv_ostore inv_mount_st ]
                inv_ostore_sync_offsD[OF inv_ostore]  apply unat_arith
         using [[goals_limit=1]]
         using inv_ostore_sync_offsD[OF inv_ostore] apply simp
         apply simp
         apply simp
    apply (rename_tac v)
    apply (drule_tac t=" used\<^sub>f ostore_st''" in sym)
    using inv_step apply (simp add: \<alpha>_ostore_uptodate_def \<alpha>_updates_def buf_slice_n_n)
    apply clarsimp
    apply (rename_tac v)
    apply (cut_tac v=v and crc=crc and ostore_st'=ostore_st''
                  and len=len and oaddr=oaddr and nxtsqnum=nxtsqnum
                  and sqnum=sqnum in
                ostore_sync_\<alpha>_ostore_uptodate[OF inv_ostore inv_mount_st])
         apply (rule refl)
        using inv_ostore_sync_offsD[OF inv_ostore] apply  unat_arith
       using inv_ostore_sync_offsD[OF inv_ostore] apply  unat_arith
      using inv_bufsD[OF inv_ostore] apply simp
      apply simp
     apply (simp add: buf_slice_n_n \<alpha>_updates_def)
    apply (simp add: \<alpha>_updates_def buf_slice_n_n)
  apply (clarsimp, drule arg_cong[where f=used\<^sub>f], simp)
 done

lemma ostore_write_ret:
   "\<And>P. \<lbrakk> inv_ostore mount_st ostore_st;
     inv_\<alpha>_step_updates ostore_st;

     \<And>ex' ostore_st' objs' n. \<lbrakk> inv_ostore mount_st ostore_st';
      inv_\<alpha>_step_updates ostore_st' ;
      \<alpha>_ostore_medium ostore_st' = apply_n_updates n (\<alpha>_ostore_medium ostore_st) (\<alpha>_updates ostore_st @ [ostore_update (trimNone $ \<alpha>a objs)]);
      \<alpha>_updates ostore_st' = drop n (\<alpha>_updates ostore_st @ [ostore_update (trimNone $ \<alpha>a objs)]);
      is_set (osw, ostoreWriteForceSync) \<longrightarrow> n = length (\<alpha>_updates ostore_st) + 1
      \<rbrakk> \<Longrightarrow>
        P ((ex', ostore_st', objs'), Success ());

     \<And>e ex' ostore_st' objs' n. \<lbrakk> inv_ostore mount_st ostore_st';
        inv_\<alpha>_step_updates ostore_st' ;
        e \<in> {eIO, eNoMem, eNoSpc} ;
       \<alpha>_ostore_medium ostore_st' = apply_n_updates n (\<alpha>_ostore_medium ostore_st) (\<alpha>_updates ostore_st);
       \<alpha>_updates ostore_st' = drop n (\<alpha>_updates ostore_st)
      \<rbrakk> \<Longrightarrow>
        P ((ex', ostore_st', objs'), Error e)
    \<rbrakk> \<Longrightarrow>
     P (ostore_write (ex, mount_st, ostore_st, objs, osw))"
oops

end

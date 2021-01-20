(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory BufferT
imports
  "../impl/BilbyFs_Shallow_Desugar_Tuples"
  "../impl/BilbyFs_ShallowConsts_Desugar_Tuples"
  "../adt/WordArrayT"
begin


definition
  buf_slice :: "Buffer\<^sub>T \<Rightarrow> U32 \<Rightarrow> U32 \<Rightarrow> U8 list"
where
 "buf_slice buf frm to \<equiv> slice (unat frm) (unat to) (\<alpha>wa $ data\<^sub>f buf)"

definition
  buf_sub_slice :: "Buffer\<^sub>T \<Rightarrow> U32 \<Rightarrow> U32 \<Rightarrow> U8 list \<Rightarrow> U8 list"
where
 "buf_sub_slice buf frm to xs \<equiv>
 take (length (\<alpha>wa $ data\<^sub>f buf)) (take (unat frm) (\<alpha>wa $ data\<^sub>f buf) @ 
 (take (unat to - unat frm) (xs@replicate (unat to - unat frm) 0)) @
  List.drop (max (unat to) (unat frm)) (\<alpha>wa $ data\<^sub>f buf))"
  

lemma buf_sub_slice_length:
  "length (buf_sub_slice buf frm to xs) = length (\<alpha>wa (data\<^sub>f buf))"
  apply (simp add: buf_sub_slice_def)
  apply(subst min_def)+
using [[linarith_split_limit=20]]
apply clarsimp (* take a while *)
apply safe
apply unat_arith+
done

definition
  buf_drop :: "Buffer\<^sub>T \<Rightarrow> U32 \<Rightarrow> U8 list"
where
 "buf_drop buf offs \<equiv> List.drop (unat offs) (\<alpha>wa $ data\<^sub>f buf)"

definition
  buf_take :: "Buffer\<^sub>T \<Rightarrow> U32 \<Rightarrow> U8 list"
where
 "buf_take buf offs \<equiv> take (unat offs) (\<alpha>wa $ data\<^sub>f buf)"

definition
  buf_update_bounded :: "Buffer\<^sub>T \<Rightarrow> U8 list \<Rightarrow> U8 list"
where
 "buf_update_bounded buf buf_updated \<equiv>
    take (min (unat $ bound\<^sub>f buf) (length $ \<alpha>wa $ data\<^sub>f buf)) buf_updated @
    List.drop (min (unat $ bound\<^sub>f buf) (length buf_updated)) (\<alpha>wa $ data\<^sub>f buf) "

definition
  buf_memset' :: "Buffer\<^sub>T \<Rightarrow> U32 \<Rightarrow> U32 \<Rightarrow> U8 \<Rightarrow> U8 list"
where
 "buf_memset' buf offs len v \<equiv>
   buf_update_bounded buf $ buf_take buf offs @ replicate (min (unat len) (unat (bound\<^sub>f buf) - unat offs)) v @ buf_drop buf (offs+len)"


lemma buf_update_bounded_length:
 "length (buf_update_bounded buf upd) = length (\<alpha>wa $ data\<^sub>f buf)"
  by (simp add: buf_bound_def buf_update_bounded_def buf_length_def)

lemmas buf_simps = buf_take_def buf_drop_def buf_slice_def 
    buf_bound_def buf_update_bounded_def buf_length_def
    buf_memset'_def buf_update_bounded_length
    slice_def

lemma drop_take_drop:
  "n \<le> m \<Longrightarrow> List.drop n (take m xs) @ List.drop m xs = List.drop n xs"
  by (metis add.commute atd_lem drop_drop drop_take le_add_diff_inverse)

lemma buf_memset_bound_assm_eq:
  "unat (bound\<^sub>f buf) \<le>  length (\<alpha>wa (data\<^sub>f buf)) \<Longrightarrow>
  offs \<le> offs + len \<Longrightarrow>
  unat offs \<le> unat (bound\<^sub>f buf) \<Longrightarrow>
  offs + len \<le> bound\<^sub>f buf \<Longrightarrow>
  wordarray_set (data\<^sub>f buf, offs, len, v) = WordArrayT.make (buf_memset' buf offs len v)"
 unfolding buf_memset_def[unfolded tuple_simps sanitizers]
   apply (simp add: Let_def wordarray_set_ret buf_simps min_absorb1)
   apply (rule arg_cong[where f=WordArrayT.make])
   apply (subgoal_tac "(unat (bound\<^sub>f buf) - unat offs) \<ge> (unat len)")
    prefer 2
    apply unat_arith
   apply (simp add: min_absorb1 )
   apply (subgoal_tac "(unat (bound\<^sub>f buf)) \<le>
            (unat offs + (unat len + (length (\<alpha>wa (data\<^sub>f buf)) - unat (offs + len))))")
   prefer 2
   apply (unat_arith)
  apply (simp add: min_absorb1 take_drop)
  apply (subgoal_tac " (unat offs + unat len) =  unat (offs + len)")
   apply (simp add: drop_take_drop)
  apply unat_arith
 done

lemma take_prefix_length:
 "take n xs = take n ys \<Longrightarrow>
   n \<le> length xs \<Longrightarrow> n \<le> length ys"
by (metis length_take min.absorb_iff2)

lemma buf_bounded_update_bounded_prefix:
 "unat (bound\<^sub>f buf) \<le> length (\<alpha>wa (data\<^sub>f buf)) \<Longrightarrow>
 take (unat (bound\<^sub>f buf)) xs = take (unat (bound\<^sub>f buf)) ys \<Longrightarrow>
  buf_update_bounded buf xs = buf_update_bounded buf ys"
 apply (simp add: buf_simps)
 apply (case_tac "(unat (bound\<^sub>f buf)) \<le> (length xs)")
  apply (frule (1) take_prefix_length)
  apply (simp add: min_absorb1)
 apply simp
done

lemma buf_memset_bound:
 "unat (bound\<^sub>f buf) \<le> length (\<alpha>wa (data\<^sub>f buf)) \<Longrightarrow>
    offs \<le> offs + len \<Longrightarrow>
    offs < bound\<^sub>f buf \<Longrightarrow>
    \<not> offs + len < bound\<^sub>f buf \<Longrightarrow>
    buf_memset' buf offs (bound\<^sub>f buf - offs) v = buf_memset' buf offs len v"
  apply (simp add: buf_memset'_def)
  apply (subgoal_tac "unat (bound\<^sub>f buf - offs) = unat (bound\<^sub>f buf) - unat offs")
   apply (simp add: min_absorb2)
   apply (subgoal_tac "(unat len) \<ge> (unat (bound\<^sub>f buf) - unat offs)")
    apply simp
    apply (rule buf_bounded_update_bounded_prefix)
     apply ((simp add: buf_simps)+)[2]
   apply unat_arith
  apply unat_arith
  done

lemma take_n_m_double_append:
 "n \<le> m \<Longrightarrow> n \<le> length xs \<Longrightarrow>
    take n (take m xs @ ys ) = take n xs"
 by simp

lemma buf_memset_offs_bound:
 "unat (bound\<^sub>f buf) \<le> length (\<alpha>wa (data\<^sub>f buf)) \<Longrightarrow>
   offs \<le> offs + len \<Longrightarrow>
   \<not> offs < bound\<^sub>f buf \<Longrightarrow>
   buf_memset' buf (bound\<^sub>f buf) len' v =
   buf_memset' buf offs len v"
  apply (simp add: buf_memset'_def)
  apply (rule buf_bounded_update_bounded_prefix)
   apply simp
  apply (simp only: buf_take_def )
  apply (subst take_n_m_double_append)
     apply simp
    apply unat_arith
   apply unat_arith
  apply simp
 done


lemma buf_memset_eq:
  "unat (bound\<^sub>f buf) \<le>  length (\<alpha>wa (data\<^sub>f buf)) \<Longrightarrow>
  offs \<le> offs + len \<Longrightarrow>
  buf_memset (buf, offs, len, v) = buf\<lparr>data\<^sub>f:=WordArrayT.make (buf_memset' buf offs len v)\<rparr>"
 unfolding buf_memset_def[unfolded tuple_simps sanitizers]
  apply (simp only: Let_def prod.case_eq_if prod.sel take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def)
  apply (subst buf_memset_bound_assm_eq)
      apply simp
     apply ((case_tac " offs < bound\<^sub>f buf", ((simp, unat_arith)+)[2])+)[3]
  apply (rule arg_cong[where f="\<lambda>v. data\<^sub>f_update v buf"])
  apply (rule ext)
  apply (rule arg_cong[where f=WordArrayT.make])
  apply (case_tac "offs < bound\<^sub>f buf")
   apply (simp add: buf_memset_bound)
  apply (simp add: buf_memset_offs_bound)
 done

\<comment>\<open> ALTERNATIVE proof that does not rely on @{thm wordarray_length_ret} \<close>
lemma buf_memset'_length:
  "length (buf_memset' buf offs len v) = length (\<alpha>wa $ data\<^sub>f buf)"
  by (simp add: buf_memset'_def buf_update_bounded_length)
(*
\<comment>\<open> ORIGINAL proof that relies on @{thm wordarray_length_ret} \<close>
lemma buf_memset_length_eq:
  "unat (bound\<^sub>f buf) \<le> length (\<alpha>wa (data\<^sub>f buf)) \<Longrightarrow>
 offs \<le> offs + len \<Longrightarrow>
buf_length (buf_memset (buf, offs, len, v)) = buf_length buf"
 by (simp add: buf_length_def wordarray_length_ofnat[OF wordarray_length_ret] 
      buf_memset_eq wordarray_make buf_update_bounded_length buf_memset'_def)
*)

lemma buf_memset_length_eq:
  "unat (bound\<^sub>f buf) \<le> length (\<alpha>wa (data\<^sub>f buf)) \<Longrightarrow>
 offs \<le> offs + len \<Longrightarrow>
buf_length (buf_memset (buf, offs, len, v)) = buf_length buf"
  apply (simp add: buf_length_def buf_memset_eq)
  apply (rule length_eq_imp_wordarray_length_eq)
  apply (simp add: wordarray_make buf_memset'_length)
  done

lemma buf_take_buf_slice_adjacent:
 "st \<le>  end \<Longrightarrow> buf_take b st @ buf_slice b st end = buf_take b end"
by (simp add: buf_simps word_le_nat_alt) 
  (metis (no_types, lifting) append_take_drop_id min_def take_take)

lemma length_buf_memset:
  "unat (bound\<^sub>f wbuf) \<le>  length (\<alpha>wa (data\<^sub>f wbuf)) \<Longrightarrow>
 n < n + m \<Longrightarrow>
length (\<alpha>wa (data\<^sub>f (buf_memset (wbuf, n, m, v)))) = length (\<alpha>wa (data\<^sub>f wbuf))"
 by (simp add: buf_memset_eq buf_memset'_def wordarray_make buf_update_bounded_length)

lemma buf_slice_n_n:
  "buf_slice buf n n = []"
  by (simp add: buf_simps)

lemma buf_slice_0_eq_buf_take:
 "buf_slice buf 0 n = buf_take buf n"
 by (simp add: buf_simps)


lemma buf_slice_out_of_buf_memset:
 "frm \<le> to \<Longrightarrow> to \<le> st \<Longrightarrow> st \<le> st + len \<Longrightarrow> st \<le> bound\<^sub>f b \<Longrightarrow> unat (bound\<^sub>f b) = length (\<alpha>wa (data\<^sub>f b)) \<Longrightarrow>
  buf_slice (buf_memset (b, st, len, v)) frm to = buf_slice b frm to"
  apply (subst buf_memset_eq)
   apply simp+
  apply (simp add:  buf_simps wordarray_make min_absorb1 min_absorb2)
  apply (simp only: unat_arith_simps)
  apply (simp add: min_absorb1 min_absorb2)
  done

lemma buf_slice_out_of_buf_memset':
 "frm \<le> to \<Longrightarrow> to \<le> st \<Longrightarrow> st \<le> st + len \<Longrightarrow> st \<le> bound\<^sub>f b \<Longrightarrow> unat (bound\<^sub>f b) \<le> length (\<alpha>wa (data\<^sub>f b)) \<Longrightarrow>
  buf_slice (buf_memset (b, st, len, v)) frm to = buf_slice b frm to"
  apply (subst buf_memset_eq)
   apply simp+
  apply (simp add:  buf_simps wordarray_make min_absorb1 min_absorb2)
  apply (simp only: unat_arith_simps)
  apply (simp add: min_absorb1 min_absorb2)
 done

lemma buf_update_boundedI:
 "unat (buf_bound wbuf) \<le> length (\<alpha>wa (data\<^sub>f wbuf)) \<Longrightarrow>
  length xs = length (\<alpha>wa (data\<^sub>f wbuf)) \<Longrightarrow>
  List.drop (unat (bound\<^sub>f wbuf)) (\<alpha>wa (data\<^sub>f wbuf)) = List.drop (unat (bound\<^sub>f wbuf)) xs \<Longrightarrow>
  P xs \<Longrightarrow>
  P (buf_update_bounded wbuf xs)"
by (simp add: buf_bound_def buf_update_bounded_def min_absorb1)

lemma take_n_buf_sub_slice_n:
 "unat n \<le> length (\<alpha>wa (data\<^sub>f b)) \<Longrightarrow> take (unat n) (buf_sub_slice b n t xs) = take (unat n) (\<alpha>wa (data\<^sub>f b))"
 by (simp add: buf_sub_slice_def min_absorb1)

 lemma take_n_buf_sub_slice_m:
 "unat m \<le> length (\<alpha>wa (data\<^sub>f b)) \<Longrightarrow> n \<le> m \<Longrightarrow>  take (unat n) (buf_sub_slice b m t xs) = take (unat n) (\<alpha>wa (data\<^sub>f b))"
 by (simp add: buf_sub_slice_def min_absorb1 word_le_nat_alt) 
 

lemma slice_buf_sub_slice:
 "frm \<le> mid \<Longrightarrow> mid \<le> to \<Longrightarrow> unat to \<le> length (\<alpha>wa (data\<^sub>f b)) \<Longrightarrow>
  unat (to - mid) = length xs \<Longrightarrow>
 slice (unat frm) (unat to) (buf_sub_slice b mid to xs) = buf_slice b frm mid @ take (unat to - unat mid) xs"
  apply (simp add: buf_simps buf_sub_slice_def min_absorb1 min_absorb2)
  apply (subgoal_tac "unat mid \<le> length (\<alpha>wa (data\<^sub>f b))")
   apply (subgoal_tac "unat frm \<le> length (\<alpha>wa (data\<^sub>f b))")
    apply (subgoal_tac "unat frm \<le> unat mid")
  apply (simp add: buf_simps buf_sub_slice_def min_absorb1 min_absorb2 word_le_nat_alt)
  apply unat_arith+
  done

end

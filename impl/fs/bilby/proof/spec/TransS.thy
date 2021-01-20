(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory TransS
imports
  "../impl/BilbyFs_Shallow_Desugar_Tuples"
  "../impl/BilbyFs_ShallowConsts_Desugar_Tuples"
  "../spec/OstoreInvS"
begin

lemma pTrans_remainder:
 "prod.fst (pTrans buf) = List.drop (trans_len buf) buf"
  apply (induct buf rule:trans_len.induct)
   apply simp
  apply (rename_tac v va)
  apply (case_tac "trans\<^sub>f (pObj (v # va) 0) = bilbyFsTransIn")
   apply (clarsimp simp: Let_def is_valid_ObjTrans)
   apply (rule conjI)
    apply (fastforce simp: trans_len_Cons bilbyFsObjHeaderSize_def )
   apply (clarsimp simp: trans_len_Cons drop_n_ge_0 prod.case_eq_if)
   apply (rule_tac f="\<lambda>a. List.drop a (v#va)" in arg_cong, fastforce)
  apply (fastforce simp: Let_def trans_len_Cons bilbyFsObjHeaderSize_def is_valid_ObjTrans)
 done

lemma list_trans_not_Nil_Nil:
 "xs \<noteq> [] \<Longrightarrow>
  list_trans xs \<noteq> ([],[])"
 by (simp split: list.splits prod.splits)

lemma prefix_n_takeD:
 "prefix xs ys \<Longrightarrow>
  n \<le> length xs \<Longrightarrow>
  take n ys = take n xs"
by (auto simp: prefix_def)

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

lemma take_length_eq:
  "\<lbrakk>take n xs = take n ys; length xs \<ge> n\<rbrakk> \<Longrightarrow> length ys \<ge> n"
  by (fastforce dest!: arg_cong[where f=length]) 

lemma take_drop_eq_bounded:
  "\<lbrakk>take n xs = take n ys; j + k < n\<rbrakk>
    \<Longrightarrow> take j (List.drop k xs) = take j (List.drop k ys)"
  apply (case_tac "length xs \<ge> n")
   apply (subgoal_tac "length ys \<ge> n")
    prefer 2
    apply (erule (1) take_length_eq)
   apply (rule nth_equalityI)
    apply simp
   apply clarsimp
   apply (simp add: take_n_eq_simp[where xs=ys])  
  apply (simp add: not_less_eq_eq)
  done
    
lemma pObjI:
 "P(pObj ys 0) \<Longrightarrow>
  unat bilbyFsObjHeaderSize \<le> unat (Obj.len\<^sub>f (pObj xs 0)) \<Longrightarrow>
  take (unat (Obj.len\<^sub>f (pObj xs 0))) xs = take (unat (Obj.len\<^sub>f (pObj xs 0))) ys \<Longrightarrow>
   P(pObj xs 0)"
  apply (erule subst[where P=P,rotated])
  apply (simp add: pObj_def pObjHeader_simp)
  apply (subgoal_tac "\<forall>n<bilbyFsObjHeaderSize - 4. ple32 ys n = ple32 xs n")
  apply (subgoal_tac "\<forall>n<bilbyFsObjHeaderSize - 8. ple64 ys n = ple64 xs n")
  apply (simp add: pObj_def pObjHeader_simp
   take_n_and_len'_eq_simp[where xs=ys and ys=xs and len'="unat bilbyFsObjHeaderSize"])
  
   apply (clarsimp simp: ple64_def bilbyFsObjHeaderSize_def)
   apply (subst take_drop_eq_bounded[where xs=xs and ys=ys and n="unat (ple32 xs 0x10)"])
       apply ((simp | unat_arith)+)[3]
  apply clarsimp
  apply (subst ple32_def)+
  apply (clarsimp simp: bilbyFsObjHeaderSize_def)
  apply (subst take_drop_eq_bounded[where xs=xs and ys=ys and n="unat (ple32 xs 0x10)"])
       apply ((simp | unat_arith)+)
  done

lemma pObjD:
 "take (unat (Obj.len\<^sub>f (pObj xs 0))) ys = take (unat (Obj.len\<^sub>f (pObj xs 0))) xs \<Longrightarrow>
  unat bilbyFsObjHeaderSize \<le> unat (Obj.len\<^sub>f (pObj xs 0)) \<Longrightarrow>
  pObj ys 0 = pObj xs 0"
by (auto intro: pObjI)

lemma length_bilbyFsObjHeaderSize_le_trans:
 "unat len \<le> length xs \<Longrightarrow>
     length xs \<le> length ys \<Longrightarrow>
     unat bilbyFsObjHeaderSize \<le> length ys \<Longrightarrow>
    bilbyFsObjHeaderSize \<le> len \<Longrightarrow>
    unat bilbyFsObjHeaderSize \<le> length xs"
by unat_arith

lemma is_valid_ObjHeader_prefix_eq:
 "prefix xs ys \<Longrightarrow>
  unat (Obj.len\<^sub>f (pObj xs 0)) \<le> length xs \<Longrightarrow>
  unat bilbyFsObjHeaderSize \<le> unat (Obj.len\<^sub>f (pObj xs 0)) \<Longrightarrow>
  is_valid_ObjHeader (pObj ys 0) ys = is_valid_ObjHeader (pObj xs 0) xs"
  apply (frule (1) prefix_n_takeD[where n="unat (Obj.len\<^sub>f (pObj xs 0))"])
  apply (drule (1) pObjD)
  apply (frule prefix_n_takeD[where n="length xs" and xs=xs and ys=ys], fastforce)
  apply (subgoal_tac "take (unat $ Obj.len\<^sub>f $ pObj xs 0) xs = take (unat $ Obj.len\<^sub>f $ pObj xs 0) ys")
   prefer 2
   apply (drule (1) prefix_n_takeD, fastforce)
  apply (frule prefix_length_le)
  apply (auto simp: is_valid_ObjHeader_def length_bilbyFsObjHeaderSize_le_trans)
  done

lemma is_valid_ObjHeader_prefix:
 "is_valid_ObjHeader (pObj xs 0) xs \<Longrightarrow>
  prefix xs ys \<Longrightarrow>
  is_valid_ObjHeader (pObj ys 0) ys"
  apply (frule is_valid_ObjHeader_buf_len)
  apply (frule is_valid_ObjHeader_len)
  apply (drule is_valid_ObjHeader_prefix_eq) 
    apply (clarsimp , unat_arith?)+
  done

lemma is_valid_ObjHeader_prefix_rev:
 "is_valid_ObjHeader (pObj ys 0) ys \<Longrightarrow>
  prefix xs ys \<Longrightarrow>
  unat (Obj.len\<^sub>f (pObj xs 0)) \<le> length xs \<Longrightarrow>
  unat bilbyFsObjHeaderSize \<le> unat (Obj.len\<^sub>f (pObj xs 0)) \<Longrightarrow>
  is_valid_ObjHeader (pObj xs 0) xs"
by (drule is_valid_ObjHeader_prefix_eq, auto)

lemma is_valid_ObjHeader_data_len:
 "is_valid_ObjHeader (pObj xs n) (take nb ys) \<Longrightarrow>
    is_valid_ObjHeader (pObj xs n) ys"
by (clarsimp simp: is_valid_ObjHeader_def)

lemma is_valid_ObjHeader_trans_len:
  "is_valid_ObjHeader (pObj xs 0) xs \<Longrightarrow>
  unat (Obj.len\<^sub>f (pObj xs 0)) \<le> trans_len xs"
by (case_tac "xs")
   (clarsimp split:if_splits simp: trans_len_Cons)+

lemma valid_trans_valid_ObjHeaderD:
  "valid_trans ys \<Longrightarrow> is_valid_ObjHeader (pObj ys 0) ys"
  apply (erule valid_trans.elims)
  apply (clarsimp split:if_splits simp: is_valid_ObjTrans)
 done

lemma valid_trans_pObj_trans_len:
  "valid_trans xs \<Longrightarrow>
  unat (Obj.len\<^sub>f (pObj xs 0)) \<le> trans_len xs"
  apply (case_tac "xs")
   apply (simp)
  apply (erule valid_trans.elims)
  apply (clarsimp split:if_splits)
 done

lemma valid_trans_pObj_take_trans_len:
  "valid_trans (take (trans_len ys) ys) \<Longrightarrow>
  unat (Obj.len\<^sub>f (pObj (take (trans_len ys) ys) 0)) \<le> trans_len ys"
  apply (case_tac "(take (trans_len ys) ys)")
   apply (clarsimp)
  apply (erule valid_trans.elims)
  apply (clarsimp simp:is_valid_ObjTrans split:if_splits )
   apply (drule sym, simp only:)
   apply (drule is_valid_ObjHeader_buf_len)
   apply simp
  apply (drule sym, simp only:)
  apply (drule is_valid_ObjHeader_buf_len)
  apply simp
 done

lemma valid_trans_take_trans_len_valid_ObjHeaderD:
 assumes "valid_trans (take (trans_len ys) ys)"
 shows "is_valid_ObjHeader (pObj ys 0) ys"
proof -
  have tl_take_bound: "unat (Obj.len\<^sub>f (pObj (take (trans_len ys) ys) 0)) \<le> trans_len ys"
   by (rule valid_trans_pObj_take_trans_len[OF assms])
  have "unat bilbyFsObjHeaderSize \<le> length (take (trans_len ys) ys)"
   using is_valid_ObjHeader_len_facts[OF valid_trans_valid_ObjHeaderD[OF assms]]
   by (clarsimp simp: is_valid_ObjHeader_def)
  moreover have "length (take (trans_len ys) ys) \<le> length ys"
    by simp
  ultimately have len_eq: "Obj.len\<^sub>f (pObj ys 0) = (Obj.len\<^sub>f (pObj (take (trans_len ys) ys) 0))"
   by (clarsimp simp: pObj_def pObjHeader_def Let_def Obj.make_def bilbyFsObjHeaderSize_def ple32_take)
  from tl_take_bound and len_eq
  have tl_bound: "unat (Obj.len\<^sub>f (pObj ys 0)) \<le> trans_len ys"
   by simp

  have valid: "is_valid_ObjHeader (pObj (take (trans_len ys) ys) 0) (take (trans_len ys) ys)"
   by (rule valid_trans_valid_ObjHeaderD[OF assms])

  have len_lower_bound: "unat bilbyFsObjHeaderSize \<le> unat (Obj.len\<^sub>f (pObj ys 0))"
    using len_eq[symmetric] is_valid_ObjHeader_len[OF valid] by simp unat_arith

  show ?thesis
    using tl_bound valid len_eq
    by - (rule pObjI[where ys="(take (trans_len ys) ys)", OF _ len_lower_bound], simp_all add: is_valid_ObjHeader_def min_absorb1)
qed


lemma valid_log_buf_fun_imp_valid_ObjHeader:
  "valid_list_trans ys \<Longrightarrow> is_valid_ObjHeader (pObj ys 0) ys"
  apply (erule valid_list_trans.elims)
  apply (clarsimp simp: is_valid_ObjTrans)
  apply (drule sym[where s=ys], simp)
  apply (erule valid_trans.elims)
  apply (rename_tac v va)
  apply (subgoal_tac "is_valid_ObjHeader (pObj (v#va) 0) (v#va)")
   apply (erule is_valid_ObjHeader_prefix)
   apply (drule_tac t="v # va" in sym, fastforce)
  apply (fastforce simp: is_valid_ObjTrans split: if_splits dest: is_valid_ObjHeader_buf_len)+
 done

lemma n_idx_in_range:
  "n < length xs \<Longrightarrow> (xs @ ys) ! n = xs ! n"
  by (metis nth_append)

lemma is_down_32_8[simp]:
  "is_down (c::(U32 \<Rightarrow> U8))"
  by (simp add: is_down_def word_size target_size source_size)

lemma u32_to_u8_ignored[simp]:
  "u32_to_u8 (ucast x) = x"
  by (simp add: u32_to_u8_is_ucast ucast_down_ucast_id)

lemma word_rcat_8_32_ucast_last:
  "list \<noteq> [] \<Longrightarrow> ucast (word_rcat list :: word32) = (last list :: word8)"
  apply (cases list rule: rev_cases, simp_all)
  apply (rule word_eqI)
  apply (simp add: word_size test_bit_rcat[OF _ refl] nth_ucast)
  done
  
lemma is_valid_ObjHeader_first_byte:
 assumes "is_valid_ObjHeader (pObj data 0) data"
 shows
 "hd data = u32_to_u8 bilbyFsMagic"
proof -
  have len_data: "length data > 4"
    using is_valid_ObjHeader_len_facts[OF assms]
    by (clarsimp simp: is_valid_ObjHeader_def bilbyFsObjHeaderSize_def)
  have "magic\<^sub>f (pObj data 0) = bilbyFsMagic"
    using assms  unfolding is_valid_ObjHeader_def by simp
  hence "ple32 data 0 = bilbyFsMagic"
    by (simp add: pObj_def pObjHeader_def Let_def Obj.make_def)
  hence "u32_to_u8 (ple32 data 0) = u32_to_u8 bilbyFsMagic"
    by (simp)
  thus ?thesis
    using len_data 
    by (case_tac data) 
        (clarsimp simp: ple32_def u32_to_u8_is_ucast word_rcat_8_32_ucast_last)+
qed

lemma is_valid_ObjHeader_not_pad:
  "is_valid_ObjHeader (pObj data 0) data \<Longrightarrow> hd data \<noteq> bilbyFsPadByte"
by (drule is_valid_ObjHeader_first_byte)
   (simp add: bilbyFsMagic_def bilbyFsPadByte_def u32_to_u8_is_ucast)

lemma valid_list_trans_non_empty:
  "valid_list_trans ys \<Longrightarrow> ys \<noteq> []"
by (erule valid_list_trans.elims, simp_all)

lemma nopad_not_Nil:
 "nopad xs \<noteq> [] \<Longrightarrow> xs \<noteq> []"
by (case_tac xs) (simp_all add: nopad_def)

lemma valid_trans_imp_valid_trans_trans_len:
"valid_trans xs \<Longrightarrow> trans_len xs \<le> length xs"
  apply (induct xs rule: trans_len.induct)
   apply (simp)
  apply (erule valid_trans.elims)
  apply (clarsimp split: if_splits simp add: is_valid_ObjTrans)
   apply (rename_tac v vs)
   apply (subgoal_tac "Suc (length vs) \<ge> unat (Obj.len\<^sub>f (pObj (v#vs) 0))")
    apply (fastforce simp: is_valid_ObjHeader_def)+
 done

lemma validObjIn_imp_validObjHeader:
 "is_valid_ObjIn obj buf \<Longrightarrow> is_valid_ObjHeader obj buf"
by (simp add: is_valid_ObjTrans)

lemma trans_len_induct:
 "P [] \<Longrightarrow>
 (\<And>v vs. (is_valid_ObjIn (pObj (v#vs) 0) (v#vs) \<Longrightarrow>
          P (List.drop (unat $ Obj.len\<^sub>f $ pObj (v#vs) 0) (v#vs))) \<Longrightarrow>
         P (v#vs)) \<Longrightarrow> P a0"
by (erule trans_len.induct)
   (fastforce intro: validObjIn_imp_validObjHeader) 

lemma not_is_valid_ObjHeader_trans_len:
  "\<not>is_valid_ObjHeader (pObj xs 0) xs \<Longrightarrow>  trans_len xs  = max (unat bilbyFsObjHeaderSize) (unat (Obj.len\<^sub>f (pObj xs 0)))"
by (case_tac xs, simp_all add: trans_len_Cons)

lemma trans_len_idempotence:
notes notI [rule del]
shows
  "trans_len (take (trans_len xs) xs) = trans_len xs"
proof (induction xs rule: trans_len_induct)
  show "trans_len (take (trans_len []) []) = trans_len []"
    by simp
  next
  fix v vs
  assume IH: "is_valid_ObjIn (pObj (v#vs) 0) (v#vs) \<Longrightarrow>
   trans_len (take (trans_len (List.drop (unat $ Obj.len\<^sub>f $ pObj (v # vs) 0) (v # vs)))
     (List.drop (unat $ Obj.len\<^sub>f $ pObj (v#vs) 0) (v # vs))) =
     trans_len (List.drop (unat $ Obj.len\<^sub>f $ pObj (v # vs) 0) (v # vs))"
   have hdr_sz_le_tl: "unat bilbyFsObjHeaderSize \<le> trans_len (v#vs)" 
     using hdr_sz_le_trans_len[where xs="v#vs"] .
   hence hdr_eq: "pObjHeader (take (trans_len (v#vs)) (v#vs)) 0 = pObjHeader (v#vs) 0"
     by (simp add: pObjHeader_simp ple32_take ple64_take)
   have len_eq: "unat (Obj.len\<^sub>f (pObj (take (trans_len (v # vs)) (v # vs)) 0)) =  unat (Obj.len\<^sub>f (pObj (v # vs) 0))"
     using hdr_sz_le_trans_len[where xs="v#vs"] ple32_take[where ys="v#vs"]
     by (simp add: pObjHeader_simp pObj_def)
  have trans_otype_eq: "\<And>f. f \<in> {Obj.trans\<^sub>f, Obj.otype\<^sub>f} \<Longrightarrow> (f (pObj (take (trans_len (v # vs)) (v # vs)) 0)) =  f (pObj (v # vs) 0)"
     using hdr_sz_le_trans_len[where xs="v#vs"] 
     by (fastforce simp: pObjHeader_simp pObj_def)
  have magic_eq: "\<And>f. f \<in> {Obj.magic\<^sub>f, Obj.offs\<^sub>f} \<Longrightarrow> (f (pObj (take (trans_len (v # vs)) (v # vs)) 0)) =  f (pObj (v # vs) 0)"
     using hdr_sz_le_trans_len[where xs="v#vs"] ple32_take[where ys="v#vs"]
     by (fastforce simp: pObjHeader_simp pObj_def)
  show "trans_len (take (trans_len (v#vs)) (v#vs)) = trans_len (v#vs)"
  proof (cases)
   assume valid_in: "is_valid_ObjIn (pObj (v#vs) 0) (v#vs)"
   hence valid_hdr: "is_valid_ObjHeader (pObj (v#vs) 0) (v#vs)"
     by (simp add: is_valid_ObjTrans)
   have valid_in': "is_valid_ObjIn (pObj (take (trans_len (v#vs)) (v#vs)) 0) (take (trans_len (v#vs)) (v#vs))"
     using hdr_eq hdr_sz_le_trans_len[where xs="v#vs"] hdr_sz_le_tl valid_in
     by (simp add: is_valid_ObjTrans is_valid_ObjHeader_def pObj_def Obj.make_def Let_def
          ple32_take[where ys="v#vs"] ple64_take[where ys="v#vs"] pObjHeader_def
          bilbyFsObjHeaderSize_def min_absorb1) (* this takes ages *)
   let ?olen = "unat (Obj.len\<^sub>f (pObj (v # vs) 0))"
   let ?dropolen = "List.drop ?olen (v # vs)"

    have tl: "trans_len (v#vs) = ?olen + trans_len ?dropolen"
      using valid_in trans_len_Cons by (simp add: is_valid_ObjTrans)

    have tl': "trans_len (take (trans_len (v # vs)) (v # vs)) = (unat $ Obj.len\<^sub>f $ pObj (take (trans_len (v # vs)) (v # vs)) 0) +
            trans_len (List.drop (unat $ Obj.len\<^sub>f $ pObj (take (trans_len (v # vs)) (v # vs)) 0) (take (trans_len (v # vs)) (v # vs)))"
      using valid_in' trans_len_Cons by (simp add: is_valid_ObjTrans)

    have olen_assoc: "?olen + trans_len ?dropolen = trans_len ?dropolen + ?olen"
     by simp

    have tl_plus_eq: "trans_len (List.drop ?olen (take (?olen + trans_len ?dropolen) (v # vs))) =
     trans_len (take (trans_len ?dropolen) ?dropolen)"
      by (rule arg_cong[where f="trans_len"]) (simp add: take_drop olen_assoc)

    have "?olen + trans_len ?dropolen = (unat $ Obj.len\<^sub>f $ pObj (take (trans_len (v # vs)) (v # vs)) 0) +
     trans_len (List.drop (unat $ Obj.len\<^sub>f $ pObj (take (trans_len (v # vs)) (v # vs)) 0)
     (take (trans_len (v # vs)) (v # vs)))"
      using len_eq IH[OF valid_in,simplified] tl_plus_eq
      by (simp add: len_eq  valid_in valid_hdr trans_len_Cons)
    thus ?thesis
      by (simp add: tl[symmetric] tl')
   next
   assume not_in: "\<not>is_valid_ObjIn (pObj (v#vs) 0) (v#vs)"
    thus ?thesis
     proof (cases)
      assume valid: "is_valid_ObjHeader (pObj (v#vs) 0) (v#vs)"

    have valid': "is_valid_ObjHeader (pObj (take (trans_len (v#vs)) (v#vs)) 0) (take (trans_len (v#vs)) (v#vs))"
      using hdr_eq  len_eq hdr_sz_le_trans_len[where xs="v#vs"] valid apply (simp only: is_valid_ObjTrans is_valid_ObjHeader_def pObj_def Obj.make_def Let_def
         pObjHeader_def )
      using is_valid_ObjHeader_trans_len[OF valid, simplified pObjHeader_simp pObj_def]
      by (simp add: ple32_take[where ys="v#vs"] ple64_take[where ys="v#vs"] bilbyFsObjHeaderSize_def
        min_absorb1)
    hence not_in':   "\<not>is_valid_ObjIn (pObj (take (trans_len (v#vs)) (v#vs)) 0) (take (trans_len (v#vs)) (v#vs))"
     using valid' valid not_in apply (simp add: is_valid_ObjTrans)
     apply (drule is_valid_ObjHeader_buf_len)+
     apply (simp only: pObjHeader_simp pObj_def)
     apply clarsimp
     done
    thus ?thesis
       using valid valid' not_in not_in' apply (simp add: trans_len_Cons)
       apply (case_tac "take (unat (Obj.len\<^sub>f (pObj (v # vs) 0))) (v # vs)", fastforce)
       using len_eq apply (clarsimp simp: trans_len_Cons bilbyFsObjHeaderSize_def)
     done
  next
    assume not_valid: "\<not>is_valid_ObjHeader (pObj (v#vs) 0) (v#vs)"
    hence not_valid': "\<not>is_valid_ObjHeader (pObj (take (trans_len (v#vs)) (v#vs)) 0) (take (trans_len (v#vs)) (v#vs))"
     using len_eq
     by (fastforce simp: is_valid_ObjHeader_def magic_eq trans_otype_eq)+

    have "unat (Obj.len\<^sub>f
                (pObj (take (max (unat bilbyFsObjHeaderSize) (unat (Obj.len\<^sub>f (pObj (v # vs) 0))))
                        (v # vs))
                  0)) = (unat (Obj.len\<^sub>f (pObj (v # vs) 0)))"
     using ple32_take[where ys="(v # vs)" and ntake="(max (unat bilbyFsObjHeaderSize) (unat (Obj.len\<^sub>f (pObj (v # vs) 0))))"]
       by (simp add: pObj_def pObjHeader_simp)
    thus ?thesis
     apply (simp add: trans_len_Cons)
     using not_valid and not_valid' apply simp
     apply (case_tac "(take (max (unat bilbyFsObjHeaderSize) (unat (Obj.len\<^sub>f (pObj (v # vs) 0)))) (v # vs))")
      apply (simp add: bilbyFsObjHeaderSize_def)
     apply (simp add: trans_len_Cons)
     done
    qed
  qed
qed

lemma trans_len_take_drop_eq:
assumes is_in:"is_valid_ObjIn (pObj (v # vs) 0) (v # vs)"
and valid_trans: "valid_trans (v#vs)"
shows
 "take (trans_len (List.drop (unat (Obj.len\<^sub>f (pObj (v # vs) 0))) (v # vs)))
  (List.drop (unat (Obj.len\<^sub>f (pObj (v # vs) 0))) (v # vs)) =
  List.drop (unat (Obj.len\<^sub>f (pObj (v # vs) 0))) (take (trans_len (v # vs)) (v # vs))"
proof -
  have "valid_trans (List.drop (unat $ Obj.len\<^sub>f $ pObj (v # vs) 0) (v # vs))"
    using valid_trans is_in by - (erule valid_trans.elims, fastforce)
  let ?lenobj = "unat (Obj.len\<^sub>f (pObj (v # vs) 0))"
  have "trans_len (List.drop ?lenobj (v#vs)) + ?lenobj = trans_len (v#vs)"
    using is_in by (subst trans_len.simps) (clarsimp simp: is_valid_ObjTrans)
  thus ?thesis
    by (simp add: take_drop)
qed


lemma trans_len_take_drop_eq':
assumes yys_eq: "y#ys = take (trans_len (v#vs)) (v#vs)"
and is_in': "is_valid_ObjIn (pObj (v#vs) 0) (v#vs)"
and len_eq: "(unat (Obj.len\<^sub>f (pObj (y#ys) 0))) = (unat (Obj.len\<^sub>f (pObj (v#vs) 0)))"
shows
 "take (trans_len (List.drop (unat (Obj.len\<^sub>f (pObj (v#vs) 0))) (v#vs)))
  (List.drop (unat (Obj.len\<^sub>f (pObj (v#vs) 0))) (v#vs)) =
  List.drop (unat (Obj.len\<^sub>f (pObj (v#vs) 0))) (y#ys)"
  apply (simp add: yys_eq)
  apply (subst trans_len_Cons)
  using is_in' apply (clarsimp simp: is_valid_ObjTrans)
  apply (simp add: take_drop len_eq[simplified yys_eq])
  apply (case_tac "(List.drop (unat (Obj.len\<^sub>f (pObj (v # vs) 0))) (v # vs))")
   apply simp
  apply (rename_tac x xs)
  apply (drule_tac t="x#xs" in sym)
  apply (subgoal_tac "(trans_len (List.drop (unat (Obj.len\<^sub>f (pObj (v # vs) 0))) (v # vs)) +
               unat (Obj.len\<^sub>f (pObj (v # vs) 0))) = ( unat (Obj.len\<^sub>f (pObj (v # vs) 0)) +
  trans_len (List.drop (unat (Obj.len\<^sub>f (pObj (v # vs) 0))) (v # vs)))")
   apply (simp only:)+
done

lemma take_trans_len_is_valid_ObjHeader_preserved:
assumes hdr: "is_valid_ObjHeader (pObj (v#vs) 0) (v#vs)"
and trans: "Obj.trans\<^sub>f (pObj (v#vs) 0) = tr"
and valid: "valid_trans (v # vs)"
and yys_eq:"take (trans_len (v#vs)) (v#vs) = y#ys"
shows
 "is_valid_ObjHeader (pObj (y#ys) 0) (y#ys) \<and>
  Obj.trans\<^sub>f (pObj (y#ys) 0) = tr \<and>
  unat (Obj.len\<^sub>f (pObj (y#ys) 0)) = unat (Obj.len\<^sub>f (pObj (v#vs) 0))"
proof -
  have prefix: "prefix (y#ys) (v#vs)"
    using yys_eq by (metis take_is_prefix)
  have len_eq: "unat (Obj.len\<^sub>f (pObj (y#ys) 0)) = unat (Obj.len\<^sub>f (pObj (v#vs) 0))"
    using hdr_sz_le_trans_len[where xs="v#vs"] 
    by (simp only: yys_eq[symmetric] bilbyFsObjHeaderSize_def
          pObj_def pObjHeader_def Obj.make_def Let_def ple32_take)
    (simp add: ple32_take)
  moreover hence len_obj: "unat (Obj.len\<^sub>f (pObj (y#ys) 0)) \<le> length (y#ys)"
    using yys_eq[symmetric] is_valid_ObjHeader_buf_len[OF hdr] is_valid_ObjHeader_trans_len[OF hdr]
    by clarsimp
  have lower_bound: "unat bilbyFsObjHeaderSize \<le> unat (Obj.len\<^sub>f (pObj (y#ys) 0))"
    using is_valid_ObjHeader_len[OF hdr] len_eq by unat_arith
  have hdr_yys: "is_valid_ObjHeader (pObj (y # ys) 0) (y # ys)"
    using is_valid_ObjHeader_prefix_rev[OF hdr prefix len_obj lower_bound] .
  moreover have "unat bilbyFsObjHeaderSize \<le> length (y#ys)"
    using is_valid_ObjHeader_buf_len[OF hdr_yys] by clarsimp
  hence "Obj.trans\<^sub>f (pObj (y#ys) 0) = Obj.trans\<^sub>f (pObj (v#vs) 0)"
    by (simp only: yys_eq[symmetric] bilbyFsObjHeaderSize_def
                   pObj_def pObjHeader_def Obj.make_def Let_def ple32_def)
       simp
  ultimately show "?thesis"
    using trans by simp
qed

lemma valid_trans_imp_valid_trans_take_trans_len:
assumes valid: "valid_trans xs"
shows
 "valid_trans (take (trans_len xs) xs)"
using valid_trans_imp_valid_trans_trans_len[OF valid]  valid
proof (induction xs rule: trans_len_induct)
  assume "valid_trans []"
  hence False by simp
  thus "valid_trans (take (trans_len []) [])" by simp
next
  fix v vs
  assume valid: "valid_trans (v # vs)"
  and tllen: "trans_len (v # vs) \<le> length (v # vs)"
  and IH:"\<lbrakk>  is_valid_ObjIn (pObj (v#vs) 0) (v#vs);
           trans_len (List.drop (unat $ Obj.len\<^sub>f $ pObj (v # vs) 0) (v # vs))
             \<le> length (List.drop (unat $ Obj.len\<^sub>f $ pObj (v # vs) 0) (v # vs));
           valid_trans (List.drop (unat $ Obj.len\<^sub>f $ pObj (v # vs) 0) (v # vs)) \<rbrakk> \<Longrightarrow>
        valid_trans (take (trans_len (List.drop (unat $ Obj.len\<^sub>f $ pObj (v#vs) 0) (v#vs))) (List.drop (unat $ Obj.len\<^sub>f $ pObj (v#vs) 0) (v#vs)))"
  thus "valid_trans (take (trans_len (v # vs)) (v # vs))"
  proof (cases "is_valid_ObjIn (pObj (v#vs) 0) (v#vs)")
    case True
      obtain y ys where yys_eq:"take (trans_len (v#vs)) (v#vs) = y#ys"
        using trans_len_non_zero[where xs="v#vs"]
        by (drule_tac x=v and y="take (trans_len (v#vs) - 1) vs" in meta_spec2)
           (case_tac "trans_len (v # vs)", fastforce+)
      have trans_len_le: "trans_len (List.drop (unat $ Obj.len\<^sub>f $ pObj (v # vs) 0) (v # vs))
             \<le> length (List.drop (unat $ Obj.len\<^sub>f $ pObj (v # vs) 0) (v # vs))"
        using valid True
        by - (fastforce split: if_splits dest: valid_trans_imp_valid_trans_trans_len)
      have valid_nxt: "valid_trans (List.drop (unat $ Obj.len\<^sub>f $ pObj (v # vs) 0) (v # vs))"
         using valid True by - fastforce
      have valid_trans_len: "valid_trans (take (trans_len (List.drop (unat $ Obj.len\<^sub>f $ pObj (v#vs) 0) (v#vs))) (List.drop (unat $ Obj.len\<^sub>f $ pObj (v#vs) 0) (v#vs)))"
       using IH[OF True trans_len_le valid_nxt] .

      have "is_valid_ObjHeader (pObj (v#vs) 0) (v#vs)"
      and "Obj.trans\<^sub>f (pObj (v#vs) 0) = bilbyFsTransIn"
        using True by (simp add: is_valid_ObjTrans)+

      hence "is_valid_ObjIn  (pObj (y#ys) 0) (y#ys)"
      and "unat (Obj.len\<^sub>f (pObj (y#ys) 0)) = unat (Obj.len\<^sub>f (pObj (v#vs) 0))"
        using take_trans_len_is_valid_ObjHeader_preserved[OF _ _ valid yys_eq]
        by (simp add: is_valid_ObjTrans)+

      thus ?thesis
        using  valid_trans_len  trans_len_take_drop_eq[OF True valid]
        by (auto simp: yys_eq[symmetric])
  next
    case False
     hence validCommit: "is_valid_ObjCommit (pObj (v#vs) 0) (v#vs)"
       using valid by - (erule valid_trans.elims, simp)
     thus ?thesis
     proof (cases "take (trans_len (v # vs)) (v # vs)")
       case Nil
       hence False using trans_len_non_zero[where xs="v#vs"] by simp
       thus ?thesis by simp
     next
       case (Cons y ys)

       have "is_valid_ObjHeader (pObj (v#vs) 0) (v#vs)"
       and  "Obj.trans\<^sub>f (pObj (v#vs) 0) = bilbyFsTransCommit"
         using validCommit by (simp add: is_valid_ObjTrans)+

       hence "is_valid_ObjCommit  (pObj (y#ys) 0) (y#ys)"
         using take_trans_len_is_valid_ObjHeader_preserved[OF _ _ valid Cons]
         by (simp add: is_valid_ObjTrans)

       thus ?thesis
         using Cons by simp
     qed
  qed
qed

lemma drop_append':
 "List.drop n (x#xs @ ys) = List.drop n (x#xs) @ List.drop (n - length (x#xs)) ys"
by (metis append_Cons drop_append)

lemma obj_len_append:
 assumes "unat bilbyFsObjHeaderSize \<le> Suc (length vs)"
 shows " (Obj.len\<^sub>f (pObj (v # vs @ zs) 0)) = Obj.len\<^sub>f (pObj (v # vs) 0)"
using assms by  (auto simp: pObj_def pObjHeader_simp n_idx_in_range ple32_def)

lemma valid_trans_take_trans_len_imp_valid_trans:
assumes valid: "valid_trans (take (trans_len xs) xs)"
shows "valid_trans xs"
using valid
proof (induction "xs" rule: valid_trans.induct)
  assume "valid_trans (take (trans_len []) [])"
  hence "False" by simp
  thus "valid_trans []" by simp
  next
  fix v vs
  assume valid: "valid_trans (take (trans_len (v # vs)) (v # vs))"
  and IH: "is_valid_ObjIn (pObj (v # vs) 0) (v # vs) \<Longrightarrow>
           valid_trans (take (trans_len (List.drop (unat $ Obj.len\<^sub>f $ pObj (v # vs) 0) (v # vs)))
                (List.drop (unat $ Obj.len\<^sub>f $ pObj (v # vs) 0) (v # vs))) \<Longrightarrow>
           valid_trans (List.drop (unat $ Obj.len\<^sub>f $ pObj (v # vs) 0) (v # vs))"
  obtain y ys where yys_eq: "y#ys = take (trans_len (v#vs)) (v#vs)"
   using trans_len_non_zero[where xs="v#vs"] by (cases "take (trans_len (v # vs)) (v # vs)" ,simp+)
  have len_le_trans_len: "unat (Obj.len\<^sub>f (pObj (y#ys) 0)) \<le> trans_len (y#ys)"
   using valid_trans_pObj_trans_len[OF valid] yys_eq by simp
  have valid_obj_xs: "is_valid_ObjHeader (pObj (y#ys) 0) (y#ys)"
    using valid yys_eq by - (erule valid_trans.elims, clarsimp simp: is_valid_ObjTrans split:if_splits)
  have trans_len_eq: "trans_len (y#ys) = trans_len (v#vs)"
   using trans_len_idempotence yys_eq by simp
  have len_yys: "unat bilbyFsObjHeaderSize \<le> length (y#ys)"
   using hdr_sz_le_trans_len[where xs="y#ys"] yys_eq[symmetric]
         valid_trans_imp_valid_trans_trans_len[OF valid] by simp
  have len_eq: "Obj.len\<^sub>f (pObj (y#ys) 0) = Obj.len\<^sub>f (pObj (v#vs) 0)"
   using len_yys
   by (simp add: pObj_def pObjHeader_def Obj.make_def yys_eq
          ple32_take bilbyFsObjHeaderSize_def Let_def)
  have min_obj_len_trans_len:"min (unat (Obj.len\<^sub>f (pObj (v#vs) 0))) (trans_len (v#vs)) = unat (Obj.len\<^sub>f (pObj (v#vs) 0))"
    using len_le_trans_len[simplified trans_len_eq len_eq] by simp
  have len_lower_bound: "unat bilbyFsObjHeaderSize \<le> unat (Obj.len\<^sub>f (pObj (v#vs) 0))"
   using is_valid_ObjHeader_len[OF valid_obj_xs] by (simp add: len_eq yys_eq[symmetric]) unat_arith

  show "valid_trans (v # vs)"
  proof cases
    assume is_in: "is_valid_ObjIn (pObj (y#ys) 0) (y#ys)"    
    hence is_in': "is_valid_ObjIn (pObj (v#vs) 0) (v#vs)"
       apply (clarsimp simp: is_valid_ObjTrans yys_eq )
       apply (drule is_valid_ObjHeader_data_len[where ys="v#vs"])
       apply (frule is_valid_ObjHeader_len)
       using len_eq min_obj_len_trans_len 
       by (auto elim: pObjI[OF _ len_lower_bound] simp:  bilbyFsObjHeaderSize_def)
    have "valid_trans (List.drop (unat $ Obj.len\<^sub>f $ pObj (y#ys) 0) (y#ys))"
      using valid yys_eq[symmetric] by - (erule valid_trans.elims,simp add: is_in)
    hence valid_take_trans_len_nxt:
     "valid_trans (take (trans_len (List.drop (unat $ Obj.len\<^sub>f $ pObj (v # vs) 0) (v # vs)))
                (List.drop (unat $ Obj.len\<^sub>f $ pObj (v # vs) 0) (v # vs)))"
      apply (simp add: yys_eq len_eq[simplified yys_eq])
      apply (erule  subst[rotated,where P=valid_trans])
      using trans_len_take_drop_eq'[OF yys_eq is_in'] len_eq
      by (simp add: yys_eq)

    have "valid_trans (List.drop (unat $ Obj.len\<^sub>f $ pObj (v#vs) 0) (v#vs))"
      using IH[OF is_in' valid_take_trans_len_nxt] .
    thus ?thesis
      using is_in' by (simp add: valid_trans_Cons)
  next
    assume is_not_in: "\<not>is_valid_ObjIn (pObj (y#ys) 0) (y#ys)"
    hence is_commit: "is_valid_ObjCommit (pObj (y#ys) 0) (y#ys)"
      using valid by - (erule valid_trans.elims, simp add: yys_eq)
    hence is_commit':"is_valid_ObjCommit (pObj (v#vs) 0) (v#vs)"
      apply (clarsimp simp: is_valid_ObjTrans yys_eq)
      apply (drule is_valid_ObjHeader_data_len[where ys="v#vs"])
      apply (frule is_valid_ObjHeader_len)
      using len_eq min_obj_len_trans_len 
      apply (auto elim: pObjI[OF _ len_lower_bound] simp:  bilbyFsObjHeaderSize_def)
      done
    thus ?thesis
     using is_commit' by (simp add: valid_trans_Cons is_valid_Obj_diff)
  qed
qed

lemma valid_trans_eq_valid_trans_take_trans_len:
 "valid_trans xs = valid_trans (take (trans_len xs) xs)"
  apply (rule iffI)
   apply (erule valid_trans_imp_valid_trans_take_trans_len)
  apply (erule valid_trans_take_trans_len_imp_valid_trans)
 done

lemma valid_trans_prefixD:
 "valid_trans xs \<Longrightarrow>
  prefix xs ys \<Longrightarrow>
  trans_len ys = trans_len xs"
  apply (clarsimp simp: prefix_def)
  apply (rename_tac zs)
  apply (thin_tac "ys = xs @ zs")
  apply (induct xs rule: trans_len_induct)
   apply simp
  apply (erule valid_trans.elims)
  apply (rename_tac v vs)
  apply (case_tac "is_valid_ObjIn (pObj (v#vs) 0) (v#vs)")
   apply simp
   apply (case_tac "(v # vs @ zs)")
    apply (simp add: trans_len_Cons)
   apply (subst trans_len_Cons)
   apply (clarsimp simp: is_valid_ObjTrans)
   apply (rename_tac v)
   apply (frule_tac ys="(v # vs @ zs)" in is_valid_ObjHeader_prefix)
    apply (simp)
   apply simp
   apply (frule_tac data="(v # vs @ zs)" in is_valid_ObjHeader_len_unat)
   apply (drule_tac  xs="(v # vs @ zs)" and ys="v#vs" in pObjD[rotated])
    apply (drule_tac data="(v # vs )" in is_valid_ObjHeader_buf_len)
    apply clarsimp
    apply (rule nth_take_lemma)
      apply (drule_tac is_valid_ObjHeader_buf_len)
      apply (simp add:  pObj_def pObjHeader_simp ple32_append_Cons)
     apply (simp add:  pObj_def pObjHeader_simp ple32_append_Cons)
    apply (subgoal_tac "unat (Obj.len\<^sub>f (pObj (v # vs @ zs) 0)) = unat (Obj.len\<^sub>f (pObj (v#vs) 0)) ")
     apply (simp)
     apply (rename_tac i)
     apply (case_tac i, simp_all add: nth_append)
    apply (simp add:  pObj_def pObjHeader_simp ple32_append_Cons)
   apply (drule_tac x=zs in meta_spec)
   apply (erule_tac P="\<lambda>xs. trans_len xs =
       trans_len (List.drop (unat (Obj.len\<^sub>f (pObj (v # vs @ zs) 0))) (v # vs))" in subst[rotated])
   apply (subgoal_tac " (unat (Obj.len\<^sub>f (pObj (v # vs @ zs) 0))) \<le> length (v#vs)")
    apply (simp add: )
    apply (subgoal_tac "unat bilbyFsObjHeaderSize \<le> unat (Obj.len\<^sub>f (pObj (v # vs @ zs) 0)) ")
     apply (simp add: bilbyFsObjHeaderSize_def drop_n_ge_0)
    apply (drule is_valid_ObjHeader_len, unat_arith)
   apply (drule is_valid_ObjHeader_buf_len, simp)
  apply (clarsimp simp: trans_len_Cons is_valid_ObjTrans split: if_splits)
  apply (frule is_valid_ObjHeader_len)
  apply (drule is_valid_ObjHeader_buf_len, simp)+
  apply (clarsimp simp:  pObj_def pObjHeader_simp ple32_append_Cons nth_append max_absorb2)
  apply unat_arith
  done

lemma valid_trans_prefix_imp:
 "valid_trans xs \<Longrightarrow>
  prefix xs ys \<Longrightarrow>
  valid_trans ys"
  apply (frule valid_trans_imp_valid_trans_take_trans_len)
  apply (frule valid_trans_imp_valid_trans_trans_len)
  apply (subgoal_tac "take (trans_len xs) xs = take (trans_len xs) ys")
   apply simp
   apply (frule valid_trans_imp_valid_trans_take_trans_len)
   apply (drule (1) valid_trans_prefixD[THEN sym])
   apply simp
   apply (drule (1) valid_trans_take_trans_len_imp_valid_trans)
  apply (fastforce simp: prefix_def)
 done

lemma drop_prefixI:
 "prefix xs ys \<Longrightarrow>
  prefix (List.drop n xs) (List.drop n ys)"
by (auto simp: prefix_def)

lemma drop_Nil_prefixD:
 "prefix xs ys \<Longrightarrow>
 List.drop n xs \<noteq> [] \<Longrightarrow> (List.drop n ys) \<noteq> []"
by (auto simp: prefix_def)

lemma drop_length_append:
 "List.drop (length xs) (xs@ys) = ys"
by auto

lemma drop_trans_len_Nil_eq_length:
  "List.drop (trans_len xs) xs = [] \<Longrightarrow>
   valid_trans xs \<Longrightarrow>
   trans_len xs = length xs"
   apply (induct xs rule: trans_len.induct)
    apply fastforce
  apply (simp)
  apply (subst (asm) valid_trans.simps)
  apply (clarsimp split:if_splits simp:is_valid_ObjTrans)
   apply (fastforce dest: is_valid_ObjHeader_buf_len)+
 done

definition valid_obj :: "U8 list \<Rightarrow> bool"
where
 "valid_obj xs \<equiv> is_valid_ObjHeader (pObj xs 0) xs"

lemma not_valid_obj_list_trans:
 "\<not>valid_obj xs \<Longrightarrow>
  prod.fst (list_trans xs) = xs"
by (case_tac xs)
   (simp add: Let_def valid_obj_def split: list.splits)+

lemma valid_obj_imp_no_pad_byte:
 "valid_obj xs \<Longrightarrow> xs!0 \<noteq> bilbyFsPadByte"
 using is_valid_ObjHeader_not_pad[where data=xs]
  apply (simp add: valid_obj_def)
  apply (drule is_valid_ObjHeader_buf_len)
  apply (case_tac xs,  simp_all add: bilbyFsObjHeaderSize_def)
 done

lemma valid_trans_imp_valid_obj:
 "valid_trans xs \<Longrightarrow> valid_obj xs"
 by (erule valid_trans.elims)
    (simp add: is_valid_ObjTrans valid_obj_def split:if_splits)

lemma nopad_Nil:
 "\<And>n. nopad xs = [] \<Longrightarrow> nopad (xs@(replicate n bilbyFsPadByte)) = []"
  by (simp add:nopad_def)

lemma list_Cons_append_simp:
 "b # buf = xs \<Longrightarrow>
 (b # buf @ ys) = xs @ ys"
 by simp

definition
  padding :: "nat \<Rightarrow> U8 list"
where
 "padding n = replicate n bilbyFsPadByte"

lemma Cons_append: "x # xs @ ys = (x#xs) @ ys"
by simp

lemma slice_Cons_append: "slice f t (x #xs @ ys) = slice f t (x#xs) @ slice (f - min (length (x#xs)) t) (t - length (x#xs)) ys"
 by (simp only: Cons_append slice_append )

lemma is_valid_ObjHeader_pObj_eq:
 "is_valid_ObjHeader (pObj (b # buf @ xs) 0) (b # buf @xs) \<Longrightarrow>
  is_valid_ObjHeader (pObj (b # buf) 0) (b # buf) \<Longrightarrow>
  pObj (b # buf @ xs) 0 = pObj (b # buf) 0 "
  apply (frule is_valid_ObjHeader_len_facts[where data="b # buf"])
  apply (frule is_valid_ObjHeader_len_facts[where data="b # buf@xs"])
  apply (clarsimp simp: is_valid_ObjHeader_def bilbyFsObjHeaderSize_def pObj_def Let_def pObjHeader_def Obj.make_def)
  apply (simp add: ple32_eq_slice4 ple64_eq_slice8 slice_Cons_append slice_n_n )
  apply (simp only: Cons_append take_append nth_append)
  apply simp
 done


lemma pTrans_remainderD:
 "P (prod.fst (pTrans buf)) \<Longrightarrow> P (List.drop (trans_len buf) buf)"
 by (simp add: pTrans_remainder)

lemma is_valid_ObjHeader_trans_len_le_buf_len:
  "is_valid_ObjHeader (pObj xs 0) xs \<Longrightarrow>
  unat (Obj.len\<^sub>f (pObj xs 0)) \<le> length xs"
by (clarsimp simp: is_valid_ObjHeader_def)

lemma snd_pTrans_append:
 "valid_trans xs \<Longrightarrow> prod.snd (pTrans (xs @ ys)) = prod.snd (pTrans xs)"
  apply (induct rule:pTrans.induct)
   apply simp
  apply (erule valid_trans.elims)
  apply (clarsimp split:if_splits simp: is_valid_ObjTrans simp: Let_def)
  apply (frule is_valid_ObjHeader_pObj_eq[rotated, where xs="ys"])
    apply (clarsimp simp: prefix_def is_valid_ObjHeader_prefix)
    apply (rename_tac v vs)
   apply (frule_tac  ys="(v # vs @ ys)" in is_valid_ObjHeader_prefix)
    apply simp
   apply (simp add: prod.case_eq_if)
  apply (subgoal_tac "(List.drop (unat (Obj.len\<^sub>f (pObj (v # vs) 0))) (v # vs) @ ys) = (List.drop (unat (Obj.len\<^sub>f (pObj (v # vs) 0))) (v # vs @ ys))")
   apply simp
   apply (drule is_valid_ObjHeader_trans_len_le_buf_len)
   apply (simp add: drop_append' prod.case_eq_if)
  apply (frule is_valid_ObjHeader_pObj_eq[rotated, where xs="ys"])
    apply (clarsimp simp: prefix_def is_valid_ObjHeader_prefix)
  apply (frule_tac ys="(vb # vaa @ ys)" in is_valid_ObjHeader_prefix, simp)
   apply (drule is_valid_ObjHeader_trans_len_le_buf_len)
   apply (simp)
done

text {* @{term pTrans_valid_non_empty} says that pTrans cannot fail if valid_trans holds *}
lemma pTrans_valid_non_empty:
 "valid_trans xs \<Longrightarrow> prod.snd (pTrans (xs@ys)) \<noteq> []"
  apply (case_tac "xs@ys")
   apply simp
  apply (rename_tac v va )
  apply (simp add: Let_def, drule sym, simp)
  apply (erule valid_trans.elims)
  apply (rename_tac vb vaa)
  apply (drule_tac t="vb # vaa" in sym)
  apply (simp only:)
  apply (subgoal_tac "is_valid_ObjHeader (pObj (xs @ ys) 0) (xs @ ys)")
   apply (clarsimp simp: is_valid_ObjTrans split:if_splits)
    apply (fastforce simp: prod.case_eq_if)+
  apply (clarsimp simp: is_valid_ObjTrans split:if_splits)
   apply (erule is_valid_ObjHeader_prefix, simp_all)+
 done

lemma valid_trans_pTrans_non_empty_trans:
notes notI [rule del]
shows
 "valid_trans xs \<Longrightarrow>
   prod.snd (pTrans xs) \<noteq> []"
 using pTrans_valid_non_empty[where ys=Nil]
 by fastforce

text {* Nicer induction lemma (variable renamed) *}
lemma list_trans_induct:
 "(\<And>data. (\<And>data' tx. (data', tx) = pTrans data \<Longrightarrow> data' \<noteq>[] \<Longrightarrow> tx \<noteq> [] \<Longrightarrow> P (nopad data')) \<Longrightarrow> P data) \<Longrightarrow> P a0"
  apply (rule list_trans.induct)
  apply (drule_tac x=data in meta_spec)
  apply (drule meta_mp)
   apply (drule_tac x=data' and y=tx in meta_spec2)
   apply (drule_tac x="hd data'" and y="tl data'" in meta_spec2)
   apply (drule_tac x="hd tx" and y="tl tx" in meta_spec2)
   apply fastforce
  apply assumption
 done

lemma snd_list_trans_Nil:
 "prod.snd (list_trans []) = []"
by simp

lemma no_pad_Nil:
  "nopad [] = []"
unfolding nopad_def
by simp

lemma nopad_padding_drop_eq_Nil:
 "(nopad (List.drop n (xs @ padding m)) = []) = (nopad (List.drop n xs) = [])"
 by (auto simp add: drop_append' nopad_def padding_def)

lemma nopad_padding_drop_eq_NilD:
 "(nopad (List.drop n xs) = []) \<Longrightarrow> ( nopad (List.drop n (xs @ padding m)) = [])"
using nopad_padding_drop_eq_Nil
by auto

lemma nopad_padding_drop_eq_Nil':
 "( nopad (List.drop n (x # xs @ padding m)) = []) = (nopad (List.drop n (x # xs)) = [])"
using nopad_padding_drop_eq_Nil[where xs="(x # xs)" and n=n and m=m]
by (subst Cons_append) auto

lemma nopad_padding_append:
 "nopad xs \<noteq> [] \<Longrightarrow>
  nopad (xs @ padding m) = nopad xs @ padding m"
 by (clarsimp simp add: nopad_def padding_def)

lemma valid_list_trans_append_padding:
 "valid_list_trans xs \<Longrightarrow>
  valid_list_trans (xs @ padding n)"
  apply (induct xs rule: valid_list_trans.induct)
   apply simp
  apply (erule valid_list_trans.elims)
  apply simp
  apply (rename_tac b' buf' b buf)
  apply (clarsimp)
  apply (frule_tac ys="(b # buf @ padding n)" in valid_trans_prefixD, simp)
  apply (clarsimp simp add: nopad_padding_drop_eq_Nil' split:if_splits)
   apply (frule_tac ys="(b # buf @ padding n)" in valid_trans_prefix_imp, simp)
   apply assumption
  apply (frule_tac ys="(b # buf @ padding n)" in valid_trans_prefix_imp, simp)
  apply simp
  apply (subgoal_tac "(nopad (List.drop (trans_len (b # buf)) (b # buf)) @ padding n) = (nopad (List.drop (trans_len (b # buf)) (b # buf @ padding n)))")
   apply simp
  apply (frule valid_trans_imp_valid_trans_trans_len)
  apply (simp add: drop_append')
  apply (case_tac "nopad (List.drop (trans_len (b # buf)) (b # buf))")
   apply (simp add: nopad_padding_drop_eq_Nil' nopad_padding_append)+
 done

lemma snd_list_trans_padding_unchanged:
notes list_trans.simps[simp del]
and length_drop[simp del]
and pTrans.simps[simp del]
shows
 "valid_list_trans xs \<Longrightarrow> 
  prod.snd (list_trans (xs @ padding n)) = prod.snd (list_trans xs)"
  apply (case_tac n, simp add: padding_def)
  apply (induct xs rule: list_trans_induct)
  apply (frule valid_list_trans_append_padding[where n=n])
  apply (erule valid_list_trans.elims)
  apply (erule valid_list_trans.elims)
  apply clarsimp
  apply (rename_tac pad_len buf b)
  apply (clarsimp split: if_splits)
     apply (subgoal_tac "nopad (List.drop (trans_len (b # buf @ padding (Suc pad_len))) (b # buf @ padding (Suc pad_len))) = nopad (List.drop (trans_len (b # buf)) (b # buf))")
      prefer 2
      apply (drule valid_trans_valid_ObjHeaderD,drule is_valid_ObjHeader_trans_len_le_buf_len)
      apply (simp add: drop_append')
     apply (subst list_trans.simps)
     apply (rule sym, subst list_trans.simps, rule sym)
     apply (frule_tac xs="(b # buf)" and ys="padding (Suc pad_len)" in  snd_pTrans_append)
     apply (simp only: prod.case_eq_if list.case_eq_if pTrans_remainder)
     apply (case_tac "List.drop (trans_len (b # buf)) (b # buf)")
      apply (simp add: snd_list_trans_Nil)+
    apply (subst list_trans.simps)
    apply (rule sym, subst list_trans.simps, rule sym)
    apply (frule_tac xs="(b # buf)" and ys="padding (Suc pad_len)" in  snd_pTrans_append)
    apply (simp only: prod.case_eq_if list.case_eq_if pTrans_remainder)
    apply (subgoal_tac "List.drop (trans_len (b # buf @ padding (Suc pad_len))) (b # buf @ padding (Suc pad_len)) \<noteq> []")
     prefer 2
     apply (frule_tac ys="b # buf @ padding (Suc pad_len)" in valid_trans_prefixD, simp)
     apply (drule valid_trans_imp_valid_trans_trans_len)
     apply (simp add: drop_append' padding_def)
    apply simp
    apply (frule valid_trans_imp_valid_trans_trans_len)
    apply (simp add:  valid_trans_pTrans_non_empty_trans snd_list_trans_Nil)
    apply (frule_tac ys="(b # buf @ padding (Suc pad_len))" in valid_trans_prefixD, simp)
    apply (simp add: )
    apply (frule_tac m="(Suc pad_len)" in nopad_padding_drop_eq_NilD)
    apply simp
   apply (frule_tac ys="(b # buf @ padding (Suc pad_len))" in valid_trans_prefixD, simp)
   apply (simp add: nopad_padding_drop_eq_Nil')
  (* last subgoal uses the induction hypothesis *)
  apply (subst list_trans.simps)
  apply (rule sym, subst list_trans.simps, rule sym)
  apply (frule_tac xs="b # buf @ padding (Suc pad_len)" in valid_trans_pTrans_non_empty_trans)
  apply (frule_tac xs="b # buf" in valid_trans_pTrans_non_empty_trans)
  apply (frule_tac ys="padding (Suc pad_len)" in  snd_pTrans_append)
  apply (frule nopad_not_Nil)
  apply (frule_tac ys="(b # buf @ padding (Suc pad_len))" in valid_trans_prefixD, simp)
  apply (simp add: prod.case_eq_if list.case_eq_if del: drop_eq_Nil)
  apply (simp add: pTrans_remainder nopad_padding_drop_eq_Nil' drop_append')
  apply (drule_tac x="prod.fst $ pTrans (b#buf)" and y="prod.snd $ pTrans (b#buf)" in meta_spec2)
  apply (drule_tac x=pad_len in meta_spec)
  apply (simp add: pTrans_remainder)
  apply (erule meta_impE)
  apply (simp add: prod_eq[symmetric] pTrans_remainder)
  apply (erule trans[rotated])
  apply (rule arg_cong[where f="\<lambda>xs. prod.snd (list_trans xs)"])
  apply (simp add: nopad_padding_append)
  done

lemma snd_list_trans_no_pad_padding_unchanged:
 "valid_list_trans xs \<Longrightarrow> 
  prod.snd (list_trans_no_pad (xs @ padding n)) = prod.snd (list_trans_no_pad xs)"
  by (fastforce dest: snd_list_trans_padding_unchanged[where n=n] simp: list_trans_no_pad_def prod.case_eq_if simp del: list_trans.simps)

lemma valid_list_trans_no_pad_append_padding:
 "valid_list_trans_no_pad xs \<Longrightarrow>
  valid_list_trans_no_pad (xs @ padding n)"
 by (clarsimp simp add: valid_list_trans_no_pad_def
   valid_list_trans_append_padding[where n=n]
   snd_list_trans_no_pad_padding_unchanged) 

 
lemma snd_list_trans_not_Nil:
 "valid_list_trans xs \<Longrightarrow>
    prod.snd (list_trans xs) \<noteq> []"
  apply (erule valid_list_trans.elims)
  apply (clarsimp simp del: pTrans.simps)
  apply (frule valid_trans_pTrans_non_empty_trans)
  apply (clarsimp simp: prod.case_eq_if simp del: pTrans.simps split:list.splits)
 done

 
lemma snd_list_trans_nopad_not_Nil:
 "valid_list_trans_no_pad xs \<Longrightarrow>
    prod.snd (list_trans_no_pad xs) \<noteq> []"
  by (simp add: valid_list_trans_no_pad_def)

lemma valid_trans_nth_0_neq_pad_byte:
 "valid_trans xs \<Longrightarrow> xs!0 \<noteq> bilbyFsPadByte"
 by (fastforce elim: valid_trans.elims dest: is_valid_ObjHeader_not_pad
               simp: is_valid_ObjTrans split:if_splits)

lemma valid_list_trans_nth_0_neq_pad_byte:
 "valid_list_trans ys \<Longrightarrow> ys!0 \<noteq> bilbyFsPadByte"
 by (fastforce elim: valid_list_trans.elims dest: valid_trans_nth_0_neq_pad_byte)
 
lemma nopad_drop_trans_len_Nil_append:
 "valid_list_trans ys \<Longrightarrow>
  nopad (List.drop (trans_len xs) xs) = [] \<Longrightarrow>
  valid_trans xs \<Longrightarrow>
  nopad (List.drop (trans_len (xs @ ys)) (xs @ ys)) = ys"
  apply (frule valid_trans_prefixD[where ys="(xs @ ys)"], simp)
  apply (frule valid_trans_imp_valid_trans_trans_len)
  apply (simp add: nopad_def)
  apply (frule valid_list_trans_nth_0_neq_pad_byte)
  apply (case_tac ys, fastforce+)
 done

lemma nopad_drop_trans_len_Nil_append':
 "valid_list_trans ys \<Longrightarrow>
  nopad (List.drop (trans_len xs) xs) = [] \<Longrightarrow>
  valid_trans xs \<Longrightarrow>
  nopad (List.drop (trans_len xs) (xs @ ys)) = ys"
  apply (frule valid_trans_prefixD[where ys="(xs @ ys)"], simp)
  apply (frule valid_trans_imp_valid_trans_trans_len)
  apply (simp add: nopad_def)
  apply (frule valid_list_trans_nth_0_neq_pad_byte)
  apply (case_tac ys, fastforce+)
 done


lemma nopad_drop_trans_len_not_Nil_append:
  "nopad (List.drop (trans_len xs) xs) \<noteq> [] \<Longrightarrow>
    valid_trans xs \<Longrightarrow>
    nopad (List.drop (trans_len (xs @ ys)) (xs @ ys)) \<noteq> []"
  apply (frule valid_trans_prefixD[where ys="xs@ys"], simp)
  apply (frule valid_trans_imp_valid_trans_trans_len)
  apply (fastforce simp add: nopad_def)
done    

lemma nopad_ys_eq_ys_nopad_append:
 "nopad ys = ys \<Longrightarrow>
  nopad (xs @ ys) = nopad xs @ ys"
by (metis (no_types, hide_lams) nopad_def append_self_conv dropWhile_append3
  dropWhile_eq_Cons_conv valid_list_trans.cases)

lemma valid_list_trans_nopad_eq_id:
  "valid_list_trans xs \<Longrightarrow> nopad xs = xs"
  by (cases xs) (frule valid_list_trans_nth_0_neq_pad_byte, simp add: nopad_def)+

lemma valid_list_trans_append:
  assumes val_xs: "valid_list_trans xs"
  and     val_ys: "valid_list_trans ys"
  shows
   "valid_list_trans (xs@ys)"
proof -
  obtain y' ys' where ys_cons: "ys = y'#ys'" using val_ys by (case_tac ys, simp)
  show ?thesis
  using assms
  apply (induct xs rule: valid_list_trans.induct)
   apply simp
  apply (rename_tac x' xs')
  apply (clarsimp simp add:   split: if_splits)
  apply (case_tac "nopad (List.drop (trans_len (x' # xs' @ ys)) (x' # xs' @ ys)) = []")
   apply simp
    apply (erule valid_trans_prefix_imp, simp)
   apply simp
   apply (frule_tac ys="x'#xs'@ys" in  valid_trans_prefix_imp)
    apply simp
   apply (simp only:  Cons_append)
   apply (frule (2) nopad_drop_trans_len_Nil_append)
   apply simp
  apply (simp only: Cons_append)
  apply (frule (1) nopad_drop_trans_len_not_Nil_append[where ys="ys"])
  apply clarsimp
  apply (frule_tac ys="x'#xs' @ ys"  in valid_trans_prefix_imp, simp)
  apply (simp)
  apply (frule_tac ys="(x' # xs' @ ys)" in valid_trans_prefixD, simp)
  apply simp
  apply (simp add: drop_append')
  apply (frule_tac xs="x'#xs'" in valid_trans_imp_valid_trans_trans_len)
  apply simp
  apply (frule valid_list_trans_nopad_eq_id)
  apply (simp add: nopad_ys_eq_ys_nopad_append)
 done
qed

lemma trans_len_append:
 "valid_trans xs \<Longrightarrow>
   trans_len (xs @ ys) = trans_len xs"
  apply (induct xs rule:trans_len.induct)
  apply simp
  apply (erule valid_trans.elims)
  apply (simp add: is_valid_ObjTrans)
  apply (clarsimp split: if_splits)
   apply (subst trans_len.simps)
   apply (rename_tac v vs)
   apply (frule_tac ys="(v#vs @ ys)" in is_valid_ObjHeader_prefix, simp)
   apply (simp add: is_valid_ObjTrans)
   apply (frule (1) is_valid_ObjHeader_pObj_eq[where xs=ys] )
   apply (simp add: )
   apply (erule trans[rotated])
   apply (rule arg_cong[where f=trans_len])
   apply (frule is_valid_ObjHeader_trans_len_le_buf_len)
   apply (simp add: drop_append')
  apply (clarsimp simp add: is_valid_ObjTrans)
  apply (subst trans_len.simps)
  apply (simp add: is_valid_ObjTrans)
  apply (rename_tac v vs)
  apply (frule_tac ys="(v#vs @ ys)" in is_valid_ObjHeader_prefix, simp)
  apply (simp add: is_valid_ObjTrans)
  apply (frule (1) is_valid_ObjHeader_pObj_eq[where xs=ys] )
  apply simp
 done

lemma fst_pTrans_append_valid_trans_not_Nil:
shows
 "valid_trans xs \<Longrightarrow> ys \<noteq> [] \<Longrightarrow>
  prod.fst (pTrans (xs @ ys)) \<noteq> []"
  apply (subgoal_tac "valid_trans (take (trans_len xs) xs)")
   prefer 2
   apply (simp add: valid_trans_eq_valid_trans_take_trans_len[symmetric])
   apply (simp add: pTrans_remainder)
   apply (subgoal_tac "trans_len (xs @ ys) = trans_len xs \<and> trans_len xs \<le> length xs")
   apply simp
   apply (frule valid_trans_imp_valid_trans_trans_len, simp)
   apply (simp add: trans_len_append)
done

lemma no_pad_byte_nopad_append:
  "ys ! 0 \<noteq> bilbyFsPadByte \<Longrightarrow> 
  nopad xs @ ys = nopad (xs @ ys)"
 apply (simp add: nopad_def)
 apply (case_tac ys)
  apply simp
 apply simp
 apply (simp add: dropWhile_append3)
done

lemma list_trans_append:
  notes list_trans.simps[simp del]
  and   pTrans.simps[simp del]

  assumes valid_xs: "valid_list_trans xs"
  and     valid_ys: "valid_list_trans ys"

  shows
   "prod.snd (list_trans xs) @ prod.snd (list_trans ys) =
    prod.snd (list_trans (xs@ys))"
proof -
  obtain y' ys' where ys_cons: "ys = y'#ys'" using valid_ys by (case_tac ys, simp)

  have ys_not_Nil: "ys \<noteq> []" using valid_ys by auto

  show ?thesis
  using assms
  proof (induction xs rule: list_trans_induct)
    fix data
    assume IH:
     "(\<And>data' tx.
      (data', tx) = pTrans data \<Longrightarrow>
      data' \<noteq> [] \<Longrightarrow>
      tx \<noteq> [] \<Longrightarrow>
      valid_list_trans (nopad data') \<Longrightarrow>
      valid_list_trans ys \<Longrightarrow>
      prod.snd (list_trans (nopad data')) @ prod.snd (list_trans ys) =
      prod.snd (list_trans (nopad data' @ ys)))"
    and valid_data: "valid_list_trans data"
    obtain d ds where data_cons: "data = d#ds" using valid_data by (case_tac data, simp)

    have val_trans_ys: "valid_trans ys"
      using valid_ys by (simp add: ys_cons)

    have val_trans_data: "valid_trans data"
      using valid_data by (simp add: data_cons)

    show "prod.snd (list_trans data) @ prod.snd (list_trans ys) = prod.snd (list_trans (data @ ys))"
    proof (cases "nopad (List.drop (trans_len data) data)")
      case Nil
       show ?thesis
       using Nil
      apply -
      apply (subst data_cons, subst list_trans.simps, simp only:data_cons[symmetric])
      apply (simp add: prod.case_eq_if)
      apply (simp add: pTrans_remainder)
      apply (simp add: list.case_eq_if)
      using valid_trans_pTrans_non_empty_trans[OF val_trans_data]
      apply simp
      using valid_trans_imp_valid_trans_trans_len[OF val_trans_data] 
      apply (simp add: prod.case_eq_if snd_list_trans_Nil)
      apply (subst list_trans.simps[where data="data@ys"])
      apply (simp add: prod.case_eq_if list.case_eq_if)
      using fst_pTrans_append_valid_trans_not_Nil[OF val_trans_data  ys_not_Nil]
      apply (simp add: pTrans_valid_non_empty[OF val_trans_data] snd_pTrans_append[OF val_trans_data])
      apply (simp add: pTrans_remainder trans_len_append[OF val_trans_data] )
      using valid_trans_nth_0_neq_pad_byte[OF val_trans_ys]
      apply (simp add: nopad_def)
      apply (rule arg_cong[where f=prod.snd])
      apply (rule arg_cong[where f=list_trans])
      apply (case_tac ys, simp_all)
      done
    next
    case (Cons v vs)
    show ?thesis
    using Cons
      apply (subst list_trans.simps)
      apply (simp add: prod.case_eq_if list.case_eq_if)
      apply (simp add: pTrans_remainder)
      apply (simp add:  valid_trans_pTrans_non_empty_trans[OF val_trans_data]) 
      using  valid_trans_pTrans_non_empty_trans[OF val_trans_data]
      apply (case_tac "length data \<le> trans_len data")
       apply (simp add: nopad_def)
      apply (simp add: )
      using IH[where data'="prod.fst (pTrans data)" and tx="prod.snd (pTrans data)"]
      apply simp
      apply (erule meta_impE)
       apply (simp add: pTrans_remainder nopad_def)
      apply (simp add: valid_ys)
      apply (erule meta_impE)
       apply (simp only: pTrans_remainder)
       apply (drule sym[where t="v#vs"], simp)
       apply (cut_tac valid_data[simplified data_cons valid_list_trans.simps, THEN conjunct2])
       apply (clarsimp simp add: data_cons[symmetric] split:if_splits)
      apply (drule sym[where t="v#vs"])
      apply simp
      apply (simp only: pTrans_remainder)
      apply (thin_tac _)+
      apply (rule sym, subst list_trans.simps, rule sym)
      apply (simp only: prod.case_eq_if)
      apply (simp only: list.case_eq_if)
      apply (simp add: fst_pTrans_append_valid_trans_not_Nil[OF val_trans_data ys_not_Nil])
      apply (simp add: pTrans_valid_non_empty[OF val_trans_data])
      apply (simp add: snd_pTrans_append[OF val_trans_data])
      apply (simp only: pTrans_remainder)
      apply (simp add: valid_trans_prefixD[OF val_trans_data, where ys="data@ys"])
      apply (simp add: valid_trans_imp_valid_trans_trans_len[OF val_trans_data])
      apply (rule arg_cong[where f=prod.snd])
      apply (rule arg_cong[where f=list_trans])
      using valid_trans_nth_0_neq_pad_byte[OF val_trans_ys]
      using valid_trans_imp_valid_trans_trans_len[OF val_trans_data] 
      apply (simp add: no_pad_byte_nopad_append )
     done
    qed
  qed
qed

lemma valid_list_trans_no_pad_append:
 "valid_list_trans_no_pad xs \<Longrightarrow>
  valid_list_trans_no_pad ys \<Longrightarrow>
  valid_list_trans_no_pad (xs@ys)"
 using valid_list_trans_append[where xs=xs and ys=ys]
  snd_list_trans_not_Nil[where xs=xs] snd_list_trans_not_Nil[where xs=ys]
  list_trans_append[where xs=xs and ys=ys, symmetric]
 by (clarsimp simp add: prod.case_eq_if  valid_list_trans_no_pad_def
     list_trans_no_pad_def  simp del:list_trans.simps)

lemma valid_list_trans_no_pad_imp_valid_list_trans:
 "valid_list_trans_no_pad xs \<Longrightarrow> valid_list_trans xs"
 by (simp add: valid_list_trans_no_pad_def)

lemma slice_drop:
 "to \<le> length xs \<Longrightarrow> frm \<le> to \<Longrightarrow> slice frm to xs @ List.drop to xs = List.drop frm xs"
  using drop_append[where xs="take to xs" and ys="List.drop to xs" and n=frm]
  by (simp add: slice_def min_absorb1 min_absorb2 unat_arith_simps)

lemma list_trans_no_pad_append:
notes list_trans.simps[simp del]
and   pTrans.simps[simp del]
assumes valid_slice: "valid_list_trans xs"
and valid_drop: "valid_list_trans ys"
shows
 "prod.snd (list_trans_no_pad xs) @ prod.snd (list_trans_no_pad ys) =
  prod.snd (list_trans_no_pad (xs@ys))"
  using list_trans_append assms
  by (clarsimp simp: valid_list_trans_no_pad_def list_trans_no_pad_def
      prod.case_eq_if filter_append[symmetric]  slice_drop min_absorb2)


(* Do I need this lemma?
  It seems that it's not needed it until I start reasoning about pollute_buf. *)
(*
lemma fst_list_trans:
assumes prefixeq:  "prefixeq xs ys"
and valid_list: "valid_list_trans xs"
and no_valid_obj: "\<not>valid_obj (drop (length xs) ys)"
  (*nopad (drop (length xs) ys) \<noteq> [] \<Longrightarrow>*)
shows
 "fst (list_trans ys) = drop (length xs) ys"
proof -
  from valid_list have "valid_trans xs"
    by - (erule valid_list_trans.elims, simp)
  hence valid_ys: "valid_trans ys"
    using prefixeq by (rule valid_trans_prefixeq_imp)
  have  "snd (pTrans ys) \<noteq> []"
    using  valid_trans_pTrans_non_empty_trans[OF valid_ys] .
  thus ?thesis
  using assms
  proof (induction "ys" arbitrary:xs  rule: list_trans_induct)
    fix xs ys
    assume snd_pTrans: "snd (pTrans ys) \<noteq> []"
    and prefixeq: "prefixeq xs ys"
    and valid_list: "valid_list_trans xs"
    and not_valid_obj: "\<not> valid_obj (drop (length xs) ys)"
    and IH:
    "\<And>data' tx xs.
           (data', tx) = pTrans ys \<Longrightarrow>
           data' \<noteq> [] \<Longrightarrow>
           tx \<noteq> [] \<Longrightarrow>
           snd (pTrans (nopad data')) \<noteq> [] \<Longrightarrow>
           prefixeq xs (nopad data') \<Longrightarrow>
           valid_list_trans xs \<Longrightarrow>
           \<not> valid_obj (drop (length xs) (nopad data')) \<Longrightarrow>
         fst (list_trans (nopad data')) = drop (length xs) (nopad data')"
    show "fst (list_trans ys) = drop (length xs) ys"
    proof -
      obtain zs where zsimp: "ys = xs @ zs"
        using prefixeq by (fastforce simp : prefixeq_def)
      have valid_trans_xs: "valid_trans xs"
        using valid_list by - (erule valid_list_trans.elims, simp)
      hence xs_not_nil: "xs \<noteq> []"
        using valid_trans_xs by (case_tac xs, simp_all)
      have valid_trans_ys: "valid_trans (xs@zs)"
        using valid_trans_prefixeq_imp[OF valid_trans_xs prefixeq, simplified zsimp] .
      hence ys_not_nil: "(xs@zs) \<noteq> []"
        using valid_trans_xs by (case_tac "xs@zs", simp_all)
      have trans_len_eq: "trans_len (xs@zs) = trans_len xs"
        using valid_trans_prefixeqD[OF valid_trans_xs prefixeq, simplified zsimp] .
      have trans_len_le_length_xs: "trans_len xs \<le> length xs"
        using valid_trans_imp_valid_trans_trans_len[OF valid_trans_xs] .
      have xs_remainder: "fst (pTrans xs) = drop (trans_len xs) xs"
       using pTrans_remainder[where buf="xs"] .
      have ys_remainder: "fst (pTrans (xs @ zs)) = drop (trans_len (xs @ zs)) (xs @ zs)"
        using pTrans_remainder[where buf="xs@zs"] .
     thus ?thesis
     proof cases
       assume length_xs: "trans_len xs = length xs"
       hence fst_pTrans_ys:"fst (pTrans (xs@zs)) = zs"
         using ys_remainder trans_len_eq by simp
       thus ?thesis
         using snd_pTrans apply (case_tac ys, simp, simp del:pTrans.simps)
         apply (drule sym[where s=ys], simp add: zsimp prod.case_eq_if)
         apply (case_tac zs, simp split:list.splits)
         apply (simp)
         apply (case_tac " snd (pTrans (xs @ zs))", fastforce)
         using not_valid_obj_list_trans[OF not_valid_obj[simplified zsimp drop_length_append]]
         apply (simp del:pTrans.simps list_trans.simps add: prod.case_eq_if)
       oops
     next
       fix tx
       let ?vs = "drop (trans_len xs) xs"
       assume length_xs:  "trans_len xs \<noteq> length xs"
       hence vs_not_nil: "?vs \<noteq> []"
         using trans_len_eq trans_len_le_length_xs by simp
       obtain data' where data'_pTrans: "data' = fst (pTrans ys)"
         by simp
       hence data_eq: "data' = drop (trans_len ys) ys"
         using zsimp ys_remainder by simp
       hence data'_not_nil: "data' \<noteq> []"
         using ys_remainder zsimp trans_len_eq trans_len_le_length_xs length_xs by simp
       obtain tx where tx_facts: "tx = snd (pTrans ys) \<and> tx \<noteq> []"
         using snd_pTrans by fastforce

       hence a1: "(data', tx) = pTrans ys"
         using data'_pTrans tx_facts by fastforce
       have a5: "prefixeq ?vs (nopad data')"
        by (simp add: data_eq trans_len_eq zsimp)
       have a6: "valid_list_trans ?vs"
         using valid_list trans_len_le_length_xs length_xs
         by - (erule valid_list_trans.elims, fastforce)
       have a4: "snd (pTrans (nopad data')) \<noteq> []"
         proof -
           have "valid_trans ?vs"
             using valid_list a6 length_xs trans_len_le_length_xs
             by - (fastforce elim: valid_list_trans.elims)
           hence "valid_trans data'"
             using a5 by - (drule valid_trans_prefixeq_imp)
           thus ?thesis
             by - (drule valid_trans_pTrans_non_empty_trans)
         qed
       have a7: "\<not> valid_obj (drop (length ?vs) data')"
         using trans_len_le_length_xs trans_len_eq not_valid_obj
         by (simp add: zsimp data_eq)
       have "fst (list_trans data') = drop (length ?vs) data'"
         using IH[OF a1 data'_not_nil conjunct2[OF tx_facts] a4 ]
         using IH[OF a1 data'_not_nil conjunct2[OF tx_facts] a4 a5 a6 a7] oops
       thus ?thesis
        apply (simp only:zsimp data_eq)
        apply (subst list_trans.simps)
        using ys_remainder snd_pTrans[simplified zsimp] length_xs trans_len_eq
        apply (simp add: prod.case_eq_if  del: list_trans.simps)
        apply (subgoal_tac "drop (trans_len xs) xs @ drop (trans_len xs - length xs) zs \<noteq> []")
         using trans_len_le_length_xs
         apply (clarsimp simp: prod.case_eq_if simp del: list_trans.simps split: list.splits)+
        done
      qed
    qed
  qed
qed
*)
end
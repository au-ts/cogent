(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory SerialS
imports
  PleSle
begin  
type_synonym U8 = "8 word"
type_synonym U16 = "16 word"
type_synonym U32 = "32 word"
type_synonym U64 = "64 word"

lemma sle32_length:
  "length (sle32 x) = 4"
  by (simp add: sle32_def length_word_rsplit_exp_size' word_size)

lemma ple32_word_rcat_eq1:
  "ple32 (sle32 x @ xs) 0 = x"
  apply (simp only: ple32_def unat_0)
  apply (subst drop_0)
  apply (cut_tac x=x in sle32_length)
  apply (simp add: sle32_def word_rcat_rsplit)
  done
  
lemma ple32_word_rcat_eq2:
 "length ys = (unat n) \<Longrightarrow> ple32 (ys @ sle32 x @ xs) n = x"
  by (simp add: ple32_def ple32_word_rcat_eq1[simplified ple32_def, simplified])

lemmas ple32_word_rcat_eq = ple32_word_rcat_eq1 ple32_word_rcat_eq2

lemma sle64_length:
  "length (sle64 x) = 8"
  by (simp add: sle64_def length_word_rsplit_exp_size' word_size)
  
lemma ple64_word_rcat_eq1:
  "ple64 (sle64 x @ xs) 0 = x"
  apply (simp only: ple64_def unat_0)
  apply (subst drop_0)
  apply (cut_tac x=x in sle64_length)
  apply (simp add: sle64_def word_rcat_rsplit)
 done
  
lemma ple64_word_rcat_eq2:
 "length ys = (unat n) \<Longrightarrow> ple64 (ys @ sle64 x @ xs) n = x"
  by (simp add: ple64_def ple64_word_rcat_eq1[simplified ple64_def, simplified])

lemmas ple64_word_rcat_eq = ple64_word_rcat_eq1 ple64_word_rcat_eq2

definition pObjDel :: "U8 list \<Rightarrow> U32 \<Rightarrow> U64 ObjDel"
where
  "pObjDel data' offs' \<equiv> ObjDel.make (ple64 data' offs')  \<comment> \<open>id\<close>
   \<comment> \<open>End 4 bytes\<close>"
       
definition sObjDel :: "ObjDel\<^sub>T \<Rightarrow> U8 list"
where
  "sObjDel odel \<equiv> (sle64 $ ObjDel.id\<^sub>f odel)"  (* id *) (* End 8 bytes *)

lemma objDel_inverse:
 "pObjDel (sObjDel odel) 0 = odel"
  apply(simp add: pObjDel_def sObjDel_def)
  apply(simp add: ObjDel.defs)
  using ple64_word_rcat_eq[where xs=Nil]
  by simp

definition pObjData :: "U8 list \<Rightarrow> U32 \<Rightarrow> U32 \<Rightarrow> ObjData\<^sub>T"
where
  "pObjData data offs olen \<equiv>
   ObjData.make (ple64 data offs) \<comment> \<open> id \<close>
     (WordArrayT.make $ slice (unat (offs + 8)) (unat (offs + 8) + unat (olen - bilbyFsObjHeaderSize - bilbyFsObjDataHeaderSize)) data)"

definition sObjData :: "ObjData\<^sub>T \<Rightarrow> U32 \<Rightarrow> U8 list"
where
  "sObjData odata len \<equiv> (sle64 $ ObjData.id\<^sub>f odata) @ take (unat len) (\<alpha>wa (ObjData.odata\<^sub>f odata))"

lemma length_sle32: 
 "length ((sle32 (x::U32))::U8 list) = 4"
by (simp add: Word.length_word_rsplit_exp_size' Word.word_size sle32_def )

lemma length_sle64: 
 "length ((sle64 (x::U64))::U8 list) = 8"
by (simp add: Word.length_word_rsplit_exp_size' Word.word_size sle64_def )

lemma objData_inverse:
  "unat (len - bilbyFsObjHeaderSize - bilbyFsObjDataHeaderSize) = length (\<alpha>wa (odata\<^sub>f odata)) \<Longrightarrow>
  len - bilbyFsObjHeaderSize - bilbyFsObjDataHeaderSize < len \<Longrightarrow>
  pObjData (sObjData odata len) 0 len = odata"
  apply(simp add: pObjData_def)
  apply(simp add: sObjData_def)
  apply(simp add: ObjData.defs)
  apply(simp add: ple64_word_rcat_eq length_sle64 slice_def)
  apply (subgoal_tac "unat len \<ge> length (\<alpha>wa (odata\<^sub>f odata)) ")
   apply (simp add:  wordarray_make')
  apply unat_arith
 done

definition
 pu8 :: "U8 list \<Rightarrow> U32 \<Rightarrow> U8"
where
 "pu8 xs offs =  word_rcat (slice (unat offs) (unat offs+1) xs)"
 
definition pObjDentry :: "U8 list \<Rightarrow> U32 \<Rightarrow> ObjDentry\<^sub>T"
where
 "pObjDentry data offs \<equiv>
   let nlen = ple16 data (offs+6)
   in ObjDentry.make
    (ple32 data (offs+0)) \<comment> \<open> ino \<close>
    (pu8 data (offs+4))   \<comment> \<open> dtype \<close>
    \<comment> \<open> 1 byte padding \<close>
    nlen  \<comment> \<open> nlen \<close>
    (WordArrayT.make $ slice (unat (offs+ 8)) (unat (offs + 8) + unat nlen) data) \<comment> \<open> name \<close>"

definition pArrObjDentry :: "U8 list \<Rightarrow> U32 \<Rightarrow> U32 \<Rightarrow> (ObjDentry\<^sub>T Array \<times> 32 word \<times> 32 word list)"
where
 "pArrObjDentry data offs nb_dentry =
    (case (fold      
    (\<lambda>_ (xs,doffs,offslist).
      let dentry = pObjDentry data doffs ;
          newoffs = doffs +  8 + wordarray_length (ObjDentry.name\<^sub>f dentry)
      in (xs@[Option.Some dentry], newoffs, offslist@ [newoffs])) [0..<unat nb_dentry] ([], offs, []))
   of (xs, doffs, offslist) \<Rightarrow> (ArrayT.make (xs@ [Option.None ()]), doffs, offslist))"

definition pObjDentarr :: "U8 list \<Rightarrow> U32 \<Rightarrow> U32 \<Rightarrow> ObjDentarr\<^sub>T"
where
"pObjDentarr data offs olen \<equiv>
 let nb_dentry = ple32 data (offs+8)
 in ObjDentarr.make
     (ple64 data offs) \<comment> \<open> id \<close>
     (nb_dentry) \<comment> \<open> nb_dentry \<close>
     (prod.fst (pArrObjDentry (take (unat (offs+olen-bilbyFsObjHeaderSize)) data) (offs+bilbyFsObjDentarrHeaderSize) nb_dentry))
     "

definition pObjDentarrSize :: "U8 list \<Rightarrow> U32 \<Rightarrow> U32 \<Rightarrow> U32"
where
"pObjDentarrSize data offs olen \<equiv>
 let nb_dentry = ple32 data (offs+8)
 in (prod.fst (prod.snd (pArrObjDentry (take (unat (offs+olen-bilbyFsObjHeaderSize)) data) (offs+bilbyFsObjDentarrHeaderSize) nb_dentry)))
 "

definition pObjSuper :: "U8 list \<Rightarrow> U32 \<Rightarrow> ObjSuper\<^sub>T"
where
  "pObjSuper data offs \<equiv>
   ObjSuper.make
     (ple32 data offs) \<comment> \<open> nb_eb \<close>
     (ple32 data (offs+4)) \<comment> \<open> eb_size \<close>
     (ple32 data (offs+8)) \<comment> \<open> io_size \<close>
     (ple32 data (offs+12)) \<comment> \<open> nb_reserved_gc \<close>
     (ple32 data (offs+16)) \<comment> \<open> nb_reserved_del \<close>
     (ple32 data (offs+20)) \<comment> \<open> cur_eb \<close>
     (ple32 data (offs+24)) \<comment> \<open> cur_offs \<close>
     (ple32 data (offs+28)) \<comment> \<open> last_inum \<close>
     (ple64 data (offs+32)) \<comment> \<open> next_sqnum \<close>
     "

(* TODO: we do not have pObjSumEntry . Probably we need it.*)
definition sObjSumEntry :: "ObjSumEntry\<^sub>T \<Rightarrow> U8 list"
where
 "sObjSumEntry ose \<equiv> 
   (sle64 $ ObjSumEntry.id\<^sub>f ose)
 @ (sle64 $ ObjSumEntry.sqnum\<^sub>f ose)
 @ (sle32 $ ObjSumEntry.len\<^sub>f ose)
 @ (sle32 $ ObjSumEntry.del_flags_and_offs\<^sub>f ose)
 @ (sle16 $ ObjSumEntry.count\<^sub>f ose)"

consts sObjSuper :: "ObjSuper\<^sub>T \<Rightarrow> U8 list" 

type_synonym Buffer\<^sub>T = "(U8 WordArray, U32) Buffer"

definition bounded :: "Buffer\<^sub>T \<Rightarrow> U8 list"
where
 "bounded buf = take (unat (bound\<^sub>f buf)) (WordArrayT.\<alpha>wa (data\<^sub>f buf))"

definition wellformed_buf :: "Buffer\<^sub>T \<Rightarrow> bool"
where
 "wellformed_buf buf \<equiv> unat (bound\<^sub>f buf) \<le> List.length (\<alpha>wa (Buffer.data\<^sub>f buf))"

lemma elem_take_n:
 "i<n \<Longrightarrow> (take n xs ! i) = xs ! i"
 by simp

lemma deserialise_le32_bounded_ret:
assumes bounded:
  "bbuf = bounded buf"
assumes valid_offs:
  "unat offs + 3 < length (bounded buf)"
shows
  "deserialise_le32 (buf, offs) = ple32 bbuf offs"
apply (simp add: bounded)
using valid_offs
  apply (subgoal_tac "(\<forall>i\<in>{0..3}. unat (offs+i) < length (bounded buf))")
   prefer 2
   apply unat_arith
  apply (simp add: bounded_def)
  apply (clarsimp simp: wordarray_get_ret[where arr="data\<^sub>f buf"] ple32_def 
                        deserialise_le32_def)
  apply (subgoal_tac "\<forall>j\<in>{1..3}. (unat (offs + j) > 0)")
   prefer 2
   apply clarsimp
   apply (drule_tac x=j in bspec, simp)
   apply unat_arith
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
 
lemma deserialise_le64_bounded_ret:
assumes bounded:
  "bbuf = bounded buf"
assumes valid_offs:
  "unat offs + 7 < length (bounded buf)"
shows
  "deserialise_le64 (buf, offs) = ple64 bbuf offs"
apply (simp add: bounded)
using valid_offs
  apply (subgoal_tac "(\<forall>i\<in>{0..7}. unat (offs+i) < length (bounded buf))")
   prefer 2
   apply unat_arith
  apply (simp add: bounded_def)
  apply (clarsimp simp: wordarray_get_ret[where arr="data\<^sub>f buf"] ple64_def 
                       deserialise_le64_def)
  apply (subgoal_tac "\<forall>j\<in>{1..7}. (unat (offs + j) > 0)")
   prefer 2
   apply clarsimp
   apply (drule_tac x=j in bspec, simp)
   apply unat_arith
  (* feel free to improve this apply script..*)
  apply (subst take_drop_decomp, (simp+))+
  apply (subst unatSuc[symmetric], (simp add: unat_gt_0[symmetric] add.commute[where b=offs]))+
  apply simp
  apply (rule trans, rule word_rcat_rsplit[symmetric])
  apply (rule arg_cong[where f=word_rcat])
  apply (subst word_rsplit_upt[where n=8], simp add: word_size)
   apply simp
  apply (simp add: upt_rec shiftr_over_or_dist shiftl_shiftr1 shiftl_shiftr2 word_size)
  apply (safe intro!: word_eqI, simp_all add: word_size word_ops_nth_size nth_ucast
        nth_shiftr nth_shiftl add.commute[where b=offs] test_bit_out_of_bounds)
  done


definition buf_unchanged :: "Buffer\<^sub>T \<Rightarrow> Buffer\<^sub>T \<Rightarrow> U32 \<Rightarrow> U32 \<Rightarrow> bool"
where
 "buf_unchanged newbuf oldbuf offs' l \<equiv> take (unat offs') (\<alpha>wa (data\<^sub>f newbuf)) = take (unat offs') (\<alpha>wa (data\<^sub>f oldbuf)) \<and>
  drop (unat offs' + unat l) (\<alpha>wa (data\<^sub>f newbuf)) = drop (unat offs' + unat l) (\<alpha>wa (data\<^sub>f oldbuf)) \<and>
  bound\<^sub>f newbuf = bound\<^sub>f oldbuf"

lemma bounded_le_length:
  "(length $ bounded  x) \<le> length (\<alpha>wa $ data\<^sub>f x)"
  by (simp add: bounded_def)

lemmas serialise_le64_simps = ArrA.make_def ElemA.make_def ElemAO.make_def ArrayUseValueP.defs
                              setu8_def[unfolded sanitizers] wordarray_make bounded_def
                             serialise_u8_def[unfolded tuple_simps sanitizers]
(*
lemma serialise_le64_ret:
assumes valid_offs:
  "unat offs + 7 < length (bounded buf)"
assumes ret:
  "P (buf\<lparr>data\<^sub>f := WordArrayT.make (\<alpha>wa (data\<^sub>f buf)[
      unat offs := u64_to_u8 v,
      unat (offs+1) := u64_to_u8 (v >> 8),
      unat (offs+2) := u64_to_u8 (v >> 16),
      unat (offs+3) := u64_to_u8 (v >> 24),
      unat (offs+4) := u64_to_u8 (v >> 32),
      unat (offs+5) := u64_to_u8 (v >> 40),
      unat (offs+6) := u64_to_u8 (v >> 48),
      unat (offs+7) := u64_to_u8 (v >> 56)])\<rparr>)"
notes  wa_modify_ret = wordarray_modify_ret[rotated - 1, simplified Let_def ArrayUseValueP.defs ArrA.defs]
shows
  "P (serialise_le64 (buf, offs, v))"
  unfolding serialise_le64_def[unfolded tuple_simps sanitizers]
  apply (simp add: serialise_le64_simps Let_def)
  apply (rule wa_modify_ret[where index="offs"], simp add: serialise_le64_simps)
    apply (rule wa_modify_ret[where index="offs+1"], simp add: serialise_le64_simps)
      apply (rule wa_modify_ret[where index="offs+2"], simp add: serialise_le64_simps)
        apply (rule wa_modify_ret[where index="offs+3"], simp add: serialise_le64_simps)
          apply (rule  wa_modify_ret[where index="offs+4"], simp add: serialise_le64_simps)
            apply (rule wa_modify_ret[where index="offs+5"], simp add: serialise_le64_simps)
              apply (rule wa_modify_ret[where index="offs+6"], simp add: serialise_le64_simps)
                apply (rule wa_modify_ret[where index="offs+7"], simp add: serialise_le64_simps)
                  using ret apply simp
                 using valid_offs 
                 apply ((simp add: serialise_le64_simps) , unat_arith?)+
 done
*)
lemma take_irrelevance:
  "P (xs!(unat (x + y))) \<Longrightarrow> unat (x + y) < unat z \<Longrightarrow>
   P ((take (unat z) xs)!(unat (x + y)))" 
   by auto

lemma unat_space:
assumes "unat (x + y) < z"
and "unat (x + y) > unat x"
and "y' \<le> y"
shows "unat (x + y') < z"
proof -
  have "\<And>x\<^sub>1. unat (x + y) \<le> x\<^sub>1 \<or> \<not> z \<le> x\<^sub>1"
  using assms(1)  by fastforce
  thus ?thesis using assms
  by (metis antisym_conv leI less_not_sym word_le_nat_alt word_plus_mono_right)
qed

lemma ple32_ret:
  assumes 1:"unat offs < unat (offs + 3)"
  assumes 2:"unat (offs + 3) < (length $ bounded buf)"
  assumes 3:"P(ple32 (bounded buf) offs)"
  shows "P (deserialise_le32 (buf, offs))"
  proof -
    from 1 2 have 4:"unat offs + 3 < (length $ bounded buf)" by (unat_arith, auto?)
    show ?thesis
    apply(subst deserialise_le32_bounded_ret)
       apply simp
      using 1 2 apply unat_arith
      apply auto[1]
     using 1 2 apply unat_arith
    using 3 apply auto
    done
  qed

lemma ple64_ret:
  assumes 1:"unat offs < unat (offs + 7)"
  assumes 2:"unat (offs + 7) < (length $ bounded buf)"
  assumes 3:"P (ple64 (bounded buf) offs)"
  shows "P (deserialise_le64 (buf, offs))"
  proof -
    from 1 2 have 4:"unat offs + 7 < (length $ bounded buf)" by (unat_arith, auto?)
    show ?thesis
    apply(subst deserialise_le64_bounded_ret)
       apply simp
      using 1 2 apply unat_arith
      apply auto[1]
     using 1 2 apply unat_arith
    using 3 apply auto
    done
  qed

lemma offs_le:
 assumes "offs < offs+n"
 assumes "unat (offs + n) \<le> ntake"
 shows   "unat offs < ntake"
 using assms by unat_arith

lemma word_add_eq_unat:
 assumes "(offs::('a::len word)) < offs + n"
 assumes "i < n"
 shows   "unat (offs + i) = unat offs  + unat i"
using assms by unat_arith

lemma ple16_eq_slice2:
 assumes "offs < offs + 2" 
 assumes "unat offs + 2 \<le> length xs"
 shows   "ple16 xs offs = ple16 (slice (unat offs) (unat offs + 2) xs) 0"
 using assms by (simp add:  slice_def ple16_def drop_take word_add_eq_unat)

lemma ple32_eq_slice4:
 assumes "offs < offs + 4" 
 assumes "unat offs + 4 \<le> length xs"
 shows   "ple32 xs offs = ple32 (slice (unat offs) (unat offs + 4) xs) 0"
 using assms by (simp add:  slice_def ple32_def drop_take word_add_eq_unat)

lemma ple64_eq_slice8:
 assumes "offs < offs + 8" 
 assumes "unat offs + 8 \<le> length xs"
 shows   "ple64 xs offs = ple64 (slice (unat offs) (unat offs + 8) xs) 0"
 using assms by (simp add:  slice_def ple64_def drop_take word_add_eq_unat)

definition pObjInode :: "U8 list \<Rightarrow> U32 \<Rightarrow> ObjInode\<^sub>T"
where
 "pObjInode data offs \<equiv>
     ObjInode.make
       (((ple64 data offs) AND (NOT (bilbyFsOidMaskAll OR ucast word32Max))) OR bilbyFsOidMaskInode) \<comment> \<open> id \<close>
       (ple64 data (offs+8)) \<comment> \<open> size \<close>
       (ple64 data (offs+16)) \<comment> \<open> atime \<close>
       (ple64 data (offs+24)) \<comment> \<open> ctime \<close>
       (ple64 data (offs+32)) \<comment> \<open> mtime \<close>
       (ple32 data (offs+40)) \<comment> \<open> nlink \<close>
       (ple32 data (offs+44)) \<comment> \<open> uid \<close>
       (ple32 data (offs+48)) \<comment> \<open> gid \<close>
       (ple32 data (offs+52)) \<comment> \<open> mode \<close>
       (ple32 data (offs+56)) \<comment> \<open> flags \<close>
       \<comment> \<open> End 60 bytes \<close>"

definition sObjInode :: "ObjInode\<^sub>T \<Rightarrow> U8 list"
where
 "sObjInode odata \<equiv> 
   (sle64 $ ObjInode.id\<^sub>f odata) 
 @ (sle64 $ ObjInode.size\<^sub>f odata) 
 @ (sle64 $ ObjInode.atime_sec\<^sub>f odata)
 @ (sle64 $ ObjInode.ctime_sec\<^sub>f odata)
 @ (sle64 $ ObjInode.mtime_sec\<^sub>f odata)
 @ (sle32 $ ObjInode.nlink\<^sub>f odata)
 @ (sle32 $ ObjInode.uid\<^sub>f odata)
 @ (sle32 $ ObjInode.gid\<^sub>f odata)
 @ (sle32 $ ObjInode.mode\<^sub>f odata)
 @ (sle32 $ ObjInode.flags\<^sub>f odata)  \<comment> \<open> End 60 bytes \<close>"

definition pObjHeader :: "U8 list \<Rightarrow> U32 \<Rightarrow> Obj\<^sub>T"
where
 "pObjHeader data offs \<equiv>
     Obj.make
       (ple32 data offs)      \<comment> \<open> magic \<close>
       (ple32 data (offs+4))  \<comment> \<open> crc \<close>
       (ple64 data (offs+8))  \<comment> \<open> sqnum \<close>
       (offs)                    \<comment> \<open> offs not stored on medium \<close> \<comment> \<open> changed back to offs, otherwise this doesnt correspond to the code\<close>
       (ple32 data (offs+16)) \<comment> \<open> len \<close>
       \<comment> \<open> 2 padding bytes \<close>
       (data!unat (offs+22))  \<comment> \<open> trans \<close>
       (data!unat (offs+23))  \<comment> \<open> otype \<close>
       undefined               \<comment> \<open> ounion \<close>
       \<comment> \<open> End 24 bytes \<close>"

definition sObjHeader :: "Obj\<^sub>T \<Rightarrow> U8 list"
where
  "sObjHeader obj \<equiv>
   (sle32 $ Obj.magic\<^sub>f obj)
 @ (sle32 $ Obj.crc\<^sub>f obj)
 @ (sle64 $ Obj.sqnum\<^sub>f obj)
 @ (sle32 $ Obj.len\<^sub>f obj)
 @ [bilbyFsPadByte]
 @ [bilbyFsPadByte]
 @ [Obj.trans\<^sub>f obj]
 @ [Obj.otype\<^sub>f obj] \<comment> \<open> End 24 bytes \<close>"

lemma ObjHeader_inverse:
  "pObjHeader (sObjHeader obj@xs) 0 = (obj\<lparr> Obj.ounion\<^sub>f := undefined, Obj.offs\<^sub>f := 0\<rparr>) "
   apply(clarsimp simp: pObjHeader_def sObjHeader_def)
   apply(clarsimp simp: Obj.defs)
   apply(clarsimp simp: ple32_word_rcat_eq length_sle32 length_sle64)
   apply(clarsimp simp: bilbyFsObjHeaderSize_def bilbyFsPadByte_def)
   proof -
     let ?magic = "sle32 (magic\<^sub>f obj)"
     let ?crc = "sle32 (crc\<^sub>f obj)"
     let ?sqnum = "sle64 (Obj.sqnum\<^sub>f obj)"
     let ?len = "sle32 (Obj.len\<^sub>f obj)"
     let ?tail = "0x42 # 0x42 # trans\<^sub>f obj # otype\<^sub>f obj # xs"

     have append_assoc_intro : "\<And>P ys1 ys2 xs. 
       P ((ys1 @ ys2) @ xs) \<Longrightarrow> P (ys1 @ (ys2 @ xs))" by auto

     have sqnum: "ple64 (?magic @ ?crc @ ?sqnum @ ?len @ ?tail) 8 = (Obj.sqnum\<^sub>f obj)"
     apply(rule append_assoc_intro)
     apply(rule ple64_word_rcat_eq)
     apply(subst List.length_append)
     using length_sle32 by auto

     have len: "ple32 (?magic @ ?crc @ ?sqnum @ ?len @ ?tail) 16 = Obj.len\<^sub>f obj"
     apply(rule append_assoc_intro[of _ "?magic"])
     apply(rule append_assoc_intro[of _ "?magic @ ?crc"])
     apply(rule append_assoc_intro[of _ "?magic @ ?crc @ ?sqnum"])
     apply(rule ple32_word_rcat_eq)
     using length_sle32 length_sle64 by auto

     have trans:"(?magic @ ?crc @ ?sqnum @ ?len @ ?tail) ! 22 = Obj.trans\<^sub>f obj"
     proof -
       have "length (?magic @ ?crc @ ?sqnum @ ?len @ (66::8 word) # [66::8 word]) = 22"
       using length_sle32 length_sle64 by simp
       from this show ?thesis
       by (metis (erased, hide_lams) append_Cons append_Nil append_assoc nth_append_length)
     qed

     have otype:"(?magic @ ?crc @ ?sqnum @ ?len @ ?tail) ! 23 = Obj.otype\<^sub>f obj"
     proof -
       have "length (?magic @ ?crc @ ?sqnum @ ?len @ (66::8 word) # (66::8 word) # [trans\<^sub>f obj]) = 23"
       using length_sle32 length_sle64 by simp
       from this show ?thesis
       by (metis (erased, hide_lams) append_Cons append_Nil append_assoc nth_append_length)
     qed

     from sqnum len trans otype
     show 
       "\<lparr>magic\<^sub>f = magic\<^sub>f obj, crc\<^sub>f = crc\<^sub>f obj,
         sqnum\<^sub>f = ple64 (?magic @ ?crc @ ?sqnum @ ?len @ ?tail) 8,
         offs\<^sub>f = 0,
         len\<^sub>f = ple32 (?magic @ ?crc @ ?sqnum @ ?len @ ?tail) 16,
         trans\<^sub>f = (?magic @ ?crc @ ?sqnum @ ?len @ ?tail) ! 22,
         otype\<^sub>f = (?magic @ ?crc @ ?sqnum @ ?len @ ?tail) ! 23,
         ounion\<^sub>f = undefined\<rparr> = obj\<lparr>ounion\<^sub>f := undefined, Obj.offs\<^sub>f := 0\<rparr>"
      by auto
   qed

lemmas pObjHeader_simp =
  pObjHeader_def Let_def Obj.make_def bilbyFsObjHeaderSize_def

definition is_valid_ObjHeader :: "Obj\<^sub>T \<Rightarrow> U8 list \<Rightarrow> bool"
where
 "is_valid_ObjHeader obj data \<equiv>
    magic\<^sub>f obj = bilbyFsMagic \<and>
    (unat $ Obj.len\<^sub>f obj) \<le> length data \<and>
    trans\<^sub>f obj \<in> {bilbyFsTransIn, bilbyFsTransCommit} \<and>
    is_len_and_type_ok (otype\<^sub>f obj, Obj.len\<^sub>f obj)"

lemma is_len_and_type_ok_hdr_szD:
  "is_len_and_type_ok (otype, olen) \<Longrightarrow> bilbyFsObjHeaderSize \<le> olen"
 by (auto simp add: 
         is_len_and_type_ok_def[unfolded sanitizers tuple_simps] 
        bilbyFsObjHeaderSize_def
        prod.case_eq_if split: if_splits)
  unat_arith+

lemma is_valid_ObjHeader_len_facts:
 "is_valid_ObjHeader obj data \<Longrightarrow> unat bilbyFsObjHeaderSize \<le> length data \<and>
   bilbyFsObjHeaderSize \<le> Obj.len\<^sub>f obj"
  apply (clarsimp simp: is_valid_ObjHeader_def)
  apply (drule is_len_and_type_ok_hdr_szD)
  apply unat_arith
 done


lemmas otype_simps =
  bilbyFsObjTypeInode_def
  bilbyFsObjTypeData_def
  bilbyFsObjTypeDentarr_def
  bilbyFsObjTypeDel_def
  bilbyFsObjTypePad_def
  bilbyFsObjTypeSuper_def
  bilbyFsObjTypeSum_def

lemma is_len_and_type_ok_otype_valD:
  "is_len_and_type_ok (otype, olen) \<Longrightarrow> otype \<in> {bilbyFsObjTypeInode,bilbyFsObjTypeData,bilbyFsObjTypeDentarr,bilbyFsObjTypeDel,bilbyFsObjTypePad,bilbyFsObjTypeSuper,bilbyFsObjTypeSum} "
 by (auto simp add: 
         is_len_and_type_ok_def[unfolded sanitizers tuple_simps] 
         otype_simps  split: if_splits)

definition is_valid_Obj :: "Obj\<^sub>T \<Rightarrow> bool"
where
 "is_valid_Obj obj \<equiv> 
    if otype\<^sub>f obj = bilbyFsObjTypePad then \<exists>v. ounion\<^sub>f obj = TObjPad v else
    if otype\<^sub>f obj = bilbyFsObjTypeInode then \<exists>v. ounion\<^sub>f obj = TObjInode v else
    if otype\<^sub>f obj = bilbyFsObjTypeData then \<exists>v. ounion\<^sub>f obj = TObjData v else
    if otype\<^sub>f obj = bilbyFsObjTypeDentarr then \<exists>v. ounion\<^sub>f obj = TObjDentarr v else
    if otype\<^sub>f obj = bilbyFsObjTypeDel then \<exists>v. ounion\<^sub>f obj = TObjDel v else
    True"


lemma is_valid_ObjHeader_len:
  "is_valid_ObjHeader obj data \<Longrightarrow> bilbyFsObjHeaderSize \<le> Obj.len\<^sub>f obj"
  apply (clarsimp simp add: is_valid_ObjHeader_def)
  apply (erule is_len_and_type_ok_hdr_szD)
 done

lemma is_valid_ObjHeader_len_unat:
  "is_valid_ObjHeader obj data \<Longrightarrow> unat bilbyFsObjHeaderSize \<le> unat (Obj.len\<^sub>f obj)"
 by (drule is_valid_ObjHeader_len) unat_arith

lemma is_valid_ObjHeader_buf_len:
  "is_valid_ObjHeader obj data \<Longrightarrow>
   (unat $ Obj.len\<^sub>f obj) \<le> length data \<and>
  unat bilbyFsObjHeaderSize \<le> length data"
  apply (clarsimp simp add: is_valid_ObjHeader_def)
  apply (drule is_len_and_type_ok_hdr_szD)
  apply unat_arith
 done

definition sObjPad :: "U32 \<Rightarrow> U8 list"
where
  "sObjPad olen \<equiv> replicate (unat (olen - bilbyFsObjHeaderSize)) bilbyFsPadByte"

consts pObjSummary :: "U8 list \<Rightarrow> U32 \<Rightarrow> ObjSummary\<^sub>T"
consts pObjPad :: "U8 list \<Rightarrow> U32 \<Rightarrow> unit"

definition pObjUnion :: "U8 list \<Rightarrow> U8 \<Rightarrow> U32 \<Rightarrow> U32 \<Rightarrow> ObjUnion\<^sub>T"
where
 "pObjUnion data otype olen offs  \<equiv>
   if otype = bilbyFsObjTypePad then
    TObjPad ()
   else if otype = bilbyFsObjTypeData then
    TObjData (pObjData data offs olen)
   else if otype = bilbyFsObjTypeInode then
    TObjInode (pObjInode data offs)
   else if otype = bilbyFsObjTypeDentarr then
    TObjDentarr (pObjDentarr data offs olen)
   else if otype = bilbyFsObjTypeDel then
    TObjDel (pObjDel data offs)
   else if otype = bilbyFsObjTypeSuper then
    TObjSuper (pObjSuper data offs)
   else \<comment> \<open>if otype = bilbyFsObjTypeSum then
    TObjSummary (pObjSummary data offs) \<close> \<comment> \<open> see comments in: serial.cogent for deserialise_ObjUnion:\<close>
    TObjPad ()"

definition pObj :: "U8 list \<Rightarrow> U32 \<Rightarrow> Obj\<^sub>T"
where
 "pObj data offs \<equiv>
   let obj = pObjHeader data offs
   in obj \<lparr>ounion\<^sub>f:= pObjUnion (take (unat offs + unat (Obj.len\<^sub>f obj)) data) (otype\<^sub>f  obj) (Obj.len\<^sub>f obj) (offs+bilbyFsObjHeaderSize)\<rparr>"

text {* This could be implemented in Cogent instead *}
definition serialise_size_summary_Obj :: "ObjSummary\<^sub>T \<Rightarrow> U32"
where
 "serialise_size_summary_Obj summary \<equiv>
   bilbyFsObjHeaderSize + serialise_size_ObjSummary (nb_sum_entry\<^sub>f summary)"

definition os_sum_sz :: "OstoreState\<^sub>T \<Rightarrow> U32"
where
 "os_sum_sz ostore_st \<equiv> serialise_size_summary_Obj (summary\<^sub>f ostore_st)"

definition bilbyFsMinObjSize :: U32
where
 "bilbyFsMinObjSize \<equiv> bilbyFsObjHeaderSize + 8"

lemma deserialise_u8_ret:
assumes wf: "wellformed_buf buf"
assumes valid_offs:
  "offs < bound\<^sub>f buf"
shows
  "deserialise_u8 (buf, offs) =  (\<alpha>wa $ data\<^sub>f buf) ! (unat offs)"
using valid_offs wordarray_get_ret[where arr="data\<^sub>f buf" and index=offs]
  wf[simplified wellformed_buf_def]
  apply  (simp add: deserialise_u8_def)
  apply (erule meta_impE)
   apply unat_arith
  apply simp
 done

lemmas objheaders_simps = bilbyFsMagic_def
    bilbyFsObjTypeInode_def bilbyFsObjTypeData_def
                  bilbyFsObjTypeDentarr_def bilbyFsObjTypeDel_def bilbyFsObjTypePad_def
                  bilbyFsObjTypeSuper_def bilbyFsObjTypeSum_def
    bilbyFsTransIn_def bilbyFsTransCommit_def is_valid_ObjHeader_def pObjHeader_def
    Obj.make_def  

lemma deserialise_ObjHeader_ret:
  assumes wf: "wellformed_buf buf"
  assumes bound: "offs + bilbyFsObjHeaderSize \<le> bound\<^sub>f buf"
  assumes no_of: "offs < offs + bilbyFsObjHeaderSize"
  assumes err: "\<And>obj. P (obj, Error eInval)"
  assumes suc:
  "\<And>obj offs'. \<lbrakk>  is_valid_ObjHeader (pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs) (bounded buf) ;
    \<exists>v. obj\<lparr>ounion\<^sub>f:=v\<rparr> = pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs;
    offs' = offs + bilbyFsObjHeaderSize;
    offs + Obj.len\<^sub>f obj \<le> bound\<^sub>f buf;
    offs < offs + Obj.len\<^sub>f obj\<rbrakk> \<Longrightarrow> 
   P (obj, Success (offs'))"
 notes bilbyFsObjHeaderSize_def[simp]
  shows "P (deserialise_ObjHeader (buf, offs, obj))"
proof -
  have des_u8: 
    "deserialise_u8 (buf, offs + 23) =  (\<alpha>wa $ data\<^sub>f buf) ! unat (offs + 23)"  
    "deserialise_u8 (buf, offs + 22) =  (\<alpha>wa $ data\<^sub>f buf) ! unat (offs + 22)"
    using bound no_of
    by - ((subst deserialise_u8_ret[OF wf]), (unat_arith, simp+))+

  have des_le64:
    "deserialise_le64 (buf, offs + 8) = (ple64 (\<alpha>wa $ data\<^sub>f buf) (offs + 8))"
  apply (rule ple64_ret)
    using no_of
    apply (simp add: )
    apply (simp add: unat_arith_simps, unat_arith)
   using bound wf no_of
   apply (simp add: bounded_def wellformed_buf_def unat_arith_simps)
   apply unat_arith
  apply (simp add: bounded_def)
  apply (subst  ple64_take)
    using bound no_of
    apply (simp add: bounded_def unat_arith_simps)
    apply unat_arith
   using wf bound no_of
   apply (simp add: wellformed_buf_def unat_arith_simps)
  apply unat_arith
  apply simp
 done

 have des_le32:
    "deserialise_le32 (buf, offs) = (ple32 (\<alpha>wa $ data\<^sub>f buf) offs)"  
    "deserialise_le32 (buf, offs+4) = (ple32 (\<alpha>wa $ data\<^sub>f buf) (offs + 4))"  
    "deserialise_le32 (buf, offs+16) = (ple32 (\<alpha>wa $ data\<^sub>f buf) (offs + 16))"
ML_prf{*
fun solve_deserialise_le32 ctxt = 
  let 
  val add_simp = Simplifier.add_simp;
  fun add_simps ctxt [] = ctxt
   |  add_simps ctxt (thm::thms) = add_simps (add_simp thm ctxt) thms;
  val simp = Simplifier.asm_full_simp_tac;
  val unat = (unat_arith_tac ctxt 1);

  val ple32 = Method.rule_tac ctxt @{thms ple32_ret} [] 1;
  val wf_bounded_unat = @{thms wellformed_buf_def bounded_def unat_arith_simps};
  val simp_wf_bounded_unat = simp (add_simps ctxt wf_bounded_unat) 1;
  val simp_bounded = simp (add_simp @{thm bounded_def} ctxt) 1;
  val ple32_take = Method.rule_tac ctxt @{thms ple32_take} [] 1;
  val simp_unat_plus = REPEAT_DETERM_N 2 ( simp_wf_bounded_unat THEN unat);
  in
    DETERM (ple32 THEN  simp_unat_plus )
    THEN (simp_bounded THEN ple32_take THEN simp_unat_plus)
  end
*}
    using wf bound no_of
    by - (tactic {* solve_deserialise_le32  @{context} *})+
    
  show ?thesis
  unfolding deserialise_ObjHeader_def[unfolded tuple_simps sanitizers]
  apply (clarsimp simp:Let_def err[simplified eInval_def])
  apply (frule is_len_and_type_ok_hdr_szD)
  apply (rule suc)
       apply (clarsimp simp: objheaders_simps buf_simps des_le32 des_u8 )
       apply (subgoal_tac "\<exists>v. ple32 (\<alpha>wa (data\<^sub>f buf)) (offs + 0x10) = v")
        prefer 2
        apply clarsimp
       apply (erule exE, simp add: bounded_def)
       using bound no_of wf apply (simp add: wellformed_buf_def)
      apply (rule conjI)
       apply unat_arith
      apply (unat_arith)
     apply (rule_tac x=undefined in exI) 
     apply (simp add: pObjHeader_def Obj.defs buf_simps des_le32 des_u8 des_le64)
    apply (simp)
   apply (simp, unat_arith)+
 done
qed

definition
  sObjUnion :: "ObjUnion\<^sub>T \<Rightarrow> U8 \<Rightarrow> U32 \<Rightarrow> U8 list"
where
 "sObjUnion (ou::ObjUnion\<^sub>T) (otype::U8) (olen::U32) \<equiv> 
  case ou of
    TObjDentarr odent \<Rightarrow> undefined \<comment> \<open> TODO: no dentarr support for now \<close>
  | TObjInode oinod \<Rightarrow> sObjInode oinod
  | TObjData odata \<Rightarrow> sObjData odata olen
  | TObjDel odel \<Rightarrow> sObjDel odel
  | TObjSuper osup \<Rightarrow> sObjSuper osup
  | TObjSummary g \<Rightarrow> undefined \<comment> \<open> TODO: sObjSummary is undefined\<close>
  | TObjPad opad \<Rightarrow>  sObjPad olen"

lemmas bilbyFsObjTypes = 
  bilbyFsObjTypePad_def
  bilbyFsObjTypeInode_def
  bilbyFsObjTypeData_def
  bilbyFsObjTypeDentarr_def
  bilbyFsObjTypeDel_def
  bilbyFsObjTypeSuper_def
  bilbyFsObjTypeSum_def

lemma ObjUnion_inverse:
 "\<And>v. ounion = TObjPad v \<Longrightarrow> otype = bilbyFsObjTypePad \<Longrightarrow>
 pObjUnion (sObjUnion ounion otype olen @ xs) otype olen 0 = ounion"
 by (simp add: sObjUnion_def pObjUnion_def )

lemma length_sObjUnion:
 "\<And>v. ounion = TObjPad v \<Longrightarrow> otype = bilbyFsObjTypePad \<Longrightarrow>
  olen \<ge> bilbyFsObjHeaderSize  \<Longrightarrow>
    length (sObjUnion ounion otype olen) = unat olen - unat bilbyFsObjHeaderSize"
  apply (simp add: sObjUnion_def sObjPad_def )
  apply unat_arith
 done


definition sObj :: "Obj\<^sub>T \<Rightarrow> U8 list"
where
 "sObj obj \<equiv> sObjHeader obj @ sObjUnion (ounion\<^sub>f obj) (otype\<^sub>f obj) (Obj.len\<^sub>f obj)"

lemma length_sObjHeader:
 "length (sObjHeader obj) = unat bilbyFsObjHeaderSize"
 by (simp add: sObjHeader_def length_sle32 length_sle64 bilbyFsObjHeaderSize_def)
 
lemma length_sObj:
  "Obj.len\<^sub>f obj \<ge> bilbyFsObjHeaderSize \<Longrightarrow>
   otype\<^sub>f obj = bilbyFsObjTypePad \<Longrightarrow> 
   is_valid_Obj obj \<Longrightarrow>
   length (sObj obj) = unat (Obj.len\<^sub>f obj)"
  apply (clarsimp simp add: is_valid_Obj_def split:if_splits)
  apply (drule (2)  length_sObjUnion)
  apply (simp add: sObj_def length_sObjHeader word_le_nat_alt)
 done

lemma Obj_inverse:
 "otype\<^sub>f obj = bilbyFsObjTypePad \<Longrightarrow>
   is_valid_Obj obj \<Longrightarrow>
   Obj.offs\<^sub>f obj = 0 \<Longrightarrow>
   pObj (sObj obj @ xs) 0 = obj"
 unfolding pObj_def sObj_def Let_def
  apply (simp add: ObjHeader_inverse)
  apply (clarsimp simp: is_valid_Obj_def)
  apply (frule (1) ObjUnion_inverse)
  apply (simp add: pObjUnion_def sObjHeader_def word_le_nat_alt length_sObjHeader)
 done

lemma buf_sub_slice_len_simplified:
  "length v1 = unat j \<Longrightarrow> unat (offs :: 32 word) < length (\<alpha>wa (data\<^sub>f buf)) \<Longrightarrow>
    unat (offs + j) \<le> length (\<alpha>wa (data\<^sub>f buf)) \<Longrightarrow>
    unat offs < unat (offs + j) \<Longrightarrow>
     length (take (unat offs) (\<alpha>wa (data\<^sub>f buf)) @
              v1 @
              drop (unat (offs + j)) (\<alpha>wa (data\<^sub>f buf))) = length (\<alpha>wa (data\<^sub>f buf))"
    by simp unat_arith
 
lemma buf_sub_slice_absorb:
  assumes len1: "length v1 = unat j"
  and     len2: "length v2 = unat (k-j)"
  and   j_less: "j \<le> k"
  and     j_nz: "j > 0"
  and    no_of: "unat offs < unat (offs + k)"
  and   len_ge: "unat (offs + k) \<le> length (\<alpha>wa (data\<^sub>f buf))"
  shows "(buf_sub_slice (buf \<lparr>data\<^sub>f := WordArrayT.make
      (buf_sub_slice buf offs (offs + j) v1)\<rparr>)
                               (offs + j) (offs + k)
                               v2) =
             buf_sub_slice buf offs (offs + k) (v1 @ v2)"
  proof -
    have j_sub: "unat (offs + j) - unat offs = unat j"
      using no_of j_less by unat_arith
    have j_max: "unat (offs + j) \<ge> unat offs"
      using no_of j_less by unat_arith
    have k_j_sub: "unat (offs + k) - unat (offs + j) = unat (k - j)"
      using no_of j_less by unat_arith
    have k_sub: "(unat (offs + k) - unat offs) = unat k"
      using no_of by unat_arith
    have k_max: "(unat (offs + k)) \<ge> (unat offs)"
      using no_of by unat_arith
    have k_j_max: "(unat (offs + k)) \<ge> (unat (offs + j))"
      using no_of j_less by unat_arith
    have xx: "\<And>x v. data\<^sub>f (x\<lparr>data\<^sub>f := v\<rparr>) = v"
      by simp
    have len_ge': " unat offs < length (\<alpha>wa (data\<^sub>f buf))"
      using len_ge no_of by unat_arith
    have len_ge'': " unat (offs + j) \<le> length (\<alpha>wa (data\<^sub>f buf))"
      using len_ge no_of j_less by unat_arith
    have no_of': "unat offs < unat (offs + j)"
      using no_of j_less j_nz by unat_arith
    have len_app: "length (v1 @ v2) = unat k"
      using len1 len2 j_less by unat_arith
    have take_prefix: "(take (unat (offs + j))
           (take (unat offs) (\<alpha>wa (data\<^sub>f buf)) @
            v1 @ drop (unat (offs + j)) (\<alpha>wa (data\<^sub>f buf)))) 
         = take (unat offs) (\<alpha>wa (data\<^sub>f buf)) @
            v1" 
        using len1 no_of' len_ge' j_sub by simp
    have drop_prefix: "drop (unat (offs + k))
           (take (unat offs) (\<alpha>wa (data\<^sub>f buf)) @
            v1 @ drop (unat (offs + j)) (\<alpha>wa (data\<^sub>f buf))) 
             = drop (unat (offs + k))(\<alpha>wa (data\<^sub>f buf))"
        apply (subgoal_tac "(unat k - unat j + unat (offs + j)) = unat (offs + k)")
         prefer 2
         using no_of j_less apply unat_arith
        using len1 len_ge' k_sub j_less no_of apply simp
        by unat_arith
    thus ?thesis
      unfolding buf_sub_slice_def 
      using j_sub j_max k_j_sub k_sub k_max k_j_max apply (simp only: max_absorb1)
      using len1
      apply (subst take_append[where n="unat j"])+
      apply (simp only: diff_self_eq_0 take_0 append_Nil2)
      using len2 apply (subst take_append[where n="unat (k-j)"])+
      apply (simp only: diff_self_eq_0 take_0 append_Nil2)
      using len_app apply (subst take_append[where n="unat k"])
      apply (simp only: diff_self_eq_0 take_0 append_Nil2)
      using len1 k_j_sub apply (simp only:)
      apply (simp only:  xx wordarray_make fun_app_def)
      using len1 len2 len_app apply (simp only: take_all[where n="unat j"]
                                        take_all[where n="unat k"]
                                        take_all[where n="unat (k-j)"])
      using len1 len_ge len_ge' len_ge'' no_of' len_app no_of
      by (simp add: buf_sub_slice_len_simplified take_prefix drop_prefix)
   qed

lemma serialise_u8_ret':
    notes  wa_modify_ret = wordarray_modify_ret[rotated - 1, simplified Let_def]
    assumes no_of: "offs < offs + 1"
       and len_ge: "unat offs + 1 \<le> length (\<alpha>wa (data\<^sub>f buf))"
    shows "serialise_u8 (buf, offs, v) = 
      buf \<lparr>data\<^sub>f := WordArrayT.make (buf_sub_slice buf offs (offs + 1) [v])\<rparr>"
   proof -
    have offs_sub: "(unat (offs + 1) - unat offs) = 1" using no_of by unat_arith
    have no_of_unat: " unat offs < unat (offs + 1)" using no_of by (simp add: word_less_nat_alt)
    show ?thesis
    unfolding serialise_u8_def[unfolded sanitizers] Let_def
  using no_of len_ge
  apply simp
  apply (rule wa_modify_ret[where index="offs" and varr="(data\<^sub>f buf)"])
   prefer 2
   apply (unat_arith)
  apply (simp_all  add:ArrA.defs ElemAO.defs  ElemA.defs
                  setu8_def[unfolded tuple_simps sanitizers] wordarray_make buf_simps
                  min_absorb1 min_absorb2)
  apply (rule arg_cong[where f="\<lambda>v. Buffer.data\<^sub>f_update v buf"])
  apply (rule ext)
  apply (rule arg_cong[where f="WordArrayT.make"])
  apply (simp only: list_eq_iff_nth_eq)
  apply (clarsimp simp: buf_sub_slice_length)
  apply (simp add: buf_sub_slice_def min_absorb1 min_absorb2)
  apply (case_tac "i=unat offs")
   apply (simp only: append_assoc[symmetric] nth_append)
   apply (simp add: min_absorb1 min_absorb2)
   apply unat_arith
  apply (case_tac "i < unat offs")
   apply (simp add: min_absorb1 offs_sub max_absorb1 no_of no_of_unat nth_append)
  apply (simp add: min_absorb1 offs_sub max_absorb1)
  apply (subgoal_tac "(max (unat (offs + 1)) (unat offs)) = unat (offs + 1)")
   prefer 2
   using no_of_unat apply auto[1]
  apply (clarsimp simp add: nth_append nth_Cons split: nat.splits)
  apply (subst nth_drop)
   apply unat_arith
  apply (subgoal_tac "unat (offs + 1) = unat offs + 1")
   prefer 2
   using no_of_unat offs_sub apply simp
  apply simp
  apply (subgoal_tac "i = Suc (unat offs + x2)")
   apply simp
  apply unat_arith
 done
 qed

lemma serialise_ObjHeader_ret:
  assumes no_overflow: "offs \<le> offs + bilbyFsObjHeaderSize"
  and     is_valid_obj: "is_valid_ObjHeader obj (drop (unat offs) (\<alpha>wa (data\<^sub>f buf)))"
  and     suc: "\<And>buf' offs'. 
   offs' = offs + bilbyFsObjHeaderSize \<Longrightarrow>
   buf' = buf\<lparr>data\<^sub>f := WordArrayT.make (buf_sub_slice buf offs (offs +bilbyFsObjHeaderSize) (sObjHeader obj))\<rparr> \<Longrightarrow>
    P (buf', offs')"
  shows
   "P (serialise_ObjHeader (buf, offs, obj))" 
   proof -
    have offs_le_length: "unat offs \<le> length (\<alpha>wa (data\<^sub>f buf))"
      using is_valid_ObjHeader_len_facts[OF is_valid_obj]
      by (clarsimp simp: is_valid_ObjHeader_def bilbyFsObjHeaderSize_def) unat_arith
   have offs_sub_le: "(unat (offs + bilbyFsObjHeaderSize) - unat offs) \<le> (length (\<alpha>wa (data\<^sub>f buf)) - unat offs)"
      using is_valid_obj is_valid_ObjHeader_len_facts[OF is_valid_obj]
      by (clarsimp simp: is_valid_ObjHeader_def bilbyFsObjHeaderSize_def) unat_arith
   have offs_len_sub_eq: "unat (offs + bilbyFsObjHeaderSize) - unat offs = unat (bilbyFsObjHeaderSize)"
      using no_overflow by unat_arith
   have offs_obj_len_le_length: "unat (offs + bilbyFsObjHeaderSize) \<le> length (\<alpha>wa (data\<^sub>f buf))"
     using is_valid_obj offs_sub_le is_valid_ObjHeader_len_facts[OF is_valid_obj]
     by (clarsimp simp: is_valid_ObjHeader_def bilbyFsObjHeaderSize_def) unat_arith
   have offs_obj_len_le_length': "(unat (offs + bilbyFsObjHeaderSize) -
                (unat offs + unat bilbyFsObjHeaderSize)) \<le> (length (\<alpha>wa (data\<^sub>f buf)) -
                   (unat offs + unat bilbyFsObjHeaderSize))"
      using offs_obj_len_le_length by unat_arith   
   have offs_plus_eq: " (unat (offs + bilbyFsObjHeaderSize) = (unat offs + unat bilbyFsObjHeaderSize))"
      using no_overflow by unat_arith
   show ?thesis
  unfolding serialise_ObjHeader_def[unfolded sanitizers tuple_simps]
  apply (simp add: Let_def)
  apply (rule suc)
   apply (simp add: bilbyFsObjHeaderSize_def)
  apply (simp add: buf_sub_slice_def wordarray_make)
  apply (simp add:  min_absorb1 offs_le_length offs_sub_le)
  apply (simp add: offs_len_sub_eq length_sObjHeader
                    offs_obj_len_le_length' offs_plus_eq)
  using no_overflow apply (simp add: word_le_nat_alt max_absorb1 bilbyFsObjHeaderSize_def)
  using no_overflow offs_obj_len_le_length apply (simp add: bilbyFsObjHeaderSize_def)
  apply (subst serialise_le32_ret[where v="magic\<^sub>f obj"])
    apply ((unat_arith, auto)+)[2]
  apply (subst serialise_le32_ret[where v="crc\<^sub>f obj"])
     apply ((unat_arith, auto)+)[1]
    apply (simp add: buf_sub_slice_length wordarray_make)
    apply (unat_arith, auto)[1]
   apply (simp)
   apply (subst add.commute[where a=8])
   apply (subst buf_sub_slice_absorb[where offs=offs and j=4 and k=8, simplified])
       apply (simp add: length_sle32)+
     apply unat_arith 
     apply auto[1]
    apply unat_arith 
    apply auto[1]
   apply (subst serialise_le64_ret)
     apply (unat_arith, auto)[1]

    apply (simp add: buf_sub_slice_length wordarray_make)
    apply (unat_arith, auto)[1]
   apply simp
   apply (subst add.commute[where a="0x10"])
   apply (subst buf_sub_slice_absorb)
         apply (simp add: length_sle32 length_sle64)+
     apply ((unat_arith, auto)+)[2]
   apply (subst serialise_le32_ret)
     apply ((unat_arith, auto)+)[1]
    apply (simp add: buf_sub_slice_length wordarray_make)
    apply (unat_arith, auto)[1]
   apply (simp)
   apply (subst add.commute[where a="0x14"])
   apply (subst buf_sub_slice_absorb)
           apply (simp add: length_sle32 length_sle64)+
      apply ((unat_arith, auto)+)[2]
   apply (subst serialise_u8_ret'[where offs="offs + 0x14"])
     apply (unat_arith, auto)[1]
    apply (simp add: buf_sub_slice_length wordarray_make)
    apply (unat_arith, auto)[1]
   apply (simp)
   apply (subst add.commute[where a="0x15"])
   apply (subst buf_sub_slice_absorb)
         apply (simp add: length_sle32 length_sle64)+
     apply ((unat_arith, auto)+)[2]
    apply (subst serialise_u8_ret'[where offs="offs + 0x15"])
     apply (unat_arith, auto)[1]
    apply (simp add: buf_sub_slice_length wordarray_make)
    apply (unat_arith, auto)[1]
   apply (simp)
   apply (subst add.commute[where a="0x16"])
   apply (subst buf_sub_slice_absorb)
         apply (simp add: length_sle32 length_sle64)+
     apply ((unat_arith, auto)+)[2] 
   apply (subst serialise_u8_ret'[where offs="offs + 0x16"])
     apply (unat_arith, auto)[1]
    apply (simp add: buf_sub_slice_length wordarray_make)
    apply (unat_arith, auto)[1]
   apply (simp)
   apply (subst add.commute[where a="0x17"])
   apply (subst buf_sub_slice_absorb)
         apply (simp add: length_sle32 length_sle64)+
     apply ((unat_arith, auto)+)[2] 
   apply (subst serialise_u8_ret'[where offs="offs + 0x17"])
     apply (unat_arith, auto)[1]
    apply (simp add: buf_sub_slice_length wordarray_make)
    apply (unat_arith, auto)[1]
   apply (simp)
   apply (subst add.commute[where a="0x18"])
   apply (subst buf_sub_slice_absorb)
         apply (simp add: length_sle32 length_sle64)+
     apply ((unat_arith, auto)+)[2]
  
  apply (simp add: sObjHeader_def bilbyFsPadByte_def)
  apply (unfold buf_sub_slice_def)
  apply (simp add: offs_len_sub_eq[unfolded bilbyFsObjHeaderSize_def, simplified])
  apply (simp add: length_sle32 length_sle64)
  apply (subgoal_tac "(length (\<alpha>wa (data\<^sub>f buf)) - unat offs) \<ge> 24")
   prefer 2
   using offs_len_sub_eq bilbyFsObjHeaderSize_def apply (unat_arith, auto)[1]
  apply simp
  apply (subgoal_tac "(unat (offs + 0x18)) > (unat offs)")
   prefer 2
   using no_overflow apply (unat_arith, auto)[1]
  apply (simp add: max_absorb1)
  apply (rule arg_cong[where f="\<lambda>v. Buffer.data\<^sub>f_update v buf"])
  apply (rule ext)
  apply (rule arg_cong[where f="WordArrayT.make"])
   apply simp
  by (subst take_all, 
          ( simp add: length_sle32 length_sle64 | (unat_arith, auto)[1] )+
     )+
qed
  
lemmas ObjUnion_splits = ObjUnion.splits

lemma take_drop_decomp:"x \<ge> a \<Longrightarrow> take (x - a) (drop a xs) @ drop x xs = drop a xs"
  by (metis drop_take drop_take_drop)

lemma serialise_ObjPad_ret:
  assumes no_overflow: "offs \<le> offs + (olen - bilbyFsObjHeaderSize)"
  and     no_underflow: "olen - bilbyFsObjHeaderSize \<ge> 0"
  and     bound: "offs+ (olen - bilbyFsObjHeaderSize) \<le> bound\<^sub>f buf \<and> unat (bound\<^sub>f buf) \<le> length (\<alpha>wa (data\<^sub>f buf))" 
  and     suc: "\<And>buf' offs'. 
   offs' = offs + olen - bilbyFsObjHeaderSize \<Longrightarrow>
   buf' = buf\<lparr>data\<^sub>f := WordArrayT.make (buf_sub_slice buf offs (offs + (olen - bilbyFsObjHeaderSize)) (sObjPad olen))\<rparr> \<Longrightarrow>
    P (buf', offs')"
  shows
   "P (serialise_ObjPad (buf, offs, olen))"
   proof -
   
    have offs_le_bound: "offs \<le> bound\<^sub>f buf"
      using bound no_overflow by unat_arith
    have sub1: "(unat (olen - 0x18)) \<le> (unat (bound\<^sub>f buf) - unat offs)"
      using bound no_overflow no_underflow apply (clarsimp simp: bilbyFsObjHeaderSize_def)
      by unat_arith
    have sub2: "(unat (offs + (olen - 0x18)) - unat offs) = unat (olen - 0x18)"
      using bound no_overflow no_underflow apply (clarsimp simp: bilbyFsObjHeaderSize_def)
      by unat_arith (* takes ages *)
    have sub3: "unat (olen - 0x18) \<le> (length (\<alpha>wa (data\<^sub>f buf)) - unat offs)"
      using bound no_overflow no_underflow apply (clarsimp simp: bilbyFsObjHeaderSize_def)
      by unat_arith
    have sub4: "(unat (offs + (olen - 0x18)) - (unat offs + unat (olen - 0x18))) = 0"
      using bound no_overflow no_underflow apply (clarsimp simp: bilbyFsObjHeaderSize_def)
      by unat_arith
    have sub5: "(unat offs +
            (unat (olen - 0x18) + length (\<alpha>wa (data\<^sub>f buf))) -
            unat (offs + (olen - 0x18))) = length (\<alpha>wa (data\<^sub>f buf))"
      using bound no_overflow no_underflow apply (clarsimp simp: bilbyFsObjHeaderSize_def)
      by unat_arith
    have no_of_unat: "unat offs \<le> (unat (offs + (olen - 0x18)))"
      using no_overflow no_underflow by (simp add: bilbyFsObjHeaderSize_def word_le_nat_alt)
    have assoc: "(unat (offs + (olen - 0x18))) = unat offs + unat (olen - 0x18)"
      using no_overflow no_underflow by (simp add: bilbyFsObjHeaderSize_def) unat_arith
   show ?thesis
    unfolding serialise_ObjPad_def[unfolded sanitizers tuple_simps]
  apply (simp add: Let_def split: ObjUnion_splits)
  apply (rule suc)
   apply (simp add: bilbyFsObjHeaderSize_def)
  apply (subst buf_memset_eq)
    using bound apply simp
   using no_overflow  apply  (simp add: bilbyFsObjHeaderSize_def)
  apply (rule arg_cong[where f="\<lambda>v. Buffer.data\<^sub>f_update v buf"])
  apply (rule ext)
  apply (rule arg_cong[where f="WordArrayT.make"])
  using bound offs_le_bound apply (clarsimp simp: buf_sub_slice_def bilbyFsObjHeaderSize_def)
  apply (simp add: sObjPad_def bilbyFsPadByte_def buf_simps
                    min_absorb1 min_absorb2 word_le_nat_alt sub1 sub2 sub3 sub4 sub5
                    bilbyFsObjHeaderSize_def no_of_unat max_absorb1 assoc)
   
  apply (subst take_drop_decomp)
   using no_overflow no_underflow apply (clarsimp simp: bilbyFsObjHeaderSize_def)
  apply simp
 done
 qed
   
lemma serialise_ObjUnion_ret:
  assumes no_overflow: "offs \<le> offs + (olen - bilbyFsObjHeaderSize)"
  and     otype: "otype = bilbyFsObjTypePad"
  and     ounion: "\<And>v. ounion = TObjPad v"
  and     olen: " 0 \<le> olen - bilbyFsObjHeaderSize"
  and     bound: "offs + (olen - bilbyFsObjHeaderSize) \<le> bound\<^sub>f buf \<and> unat (bound\<^sub>f buf) \<le> length (\<alpha>wa (data\<^sub>f buf))" 
  and     suc: "\<And>buf' offs'. 
   offs' = offs + olen - bilbyFsObjHeaderSize \<Longrightarrow>
   buf' = buf\<lparr>data\<^sub>f := WordArrayT.make (buf_sub_slice buf offs (offs + (olen - bilbyFsObjHeaderSize)) (sObjUnion ounion otype olen))\<rparr> \<Longrightarrow>
    P (buf', offs')"
  shows
   "P (serialise_ObjUnion (buf, offs, ounion, olen))"
  unfolding serialise_ObjUnion_def[unfolded sanitizers tuple_simps]
  using ounion apply (simp add: Let_def split: ObjUnion_splits)
  apply (rule serialise_ObjPad_ret)
    using no_overflow apply simp
    using olen apply simp
    using bound apply simp
   apply (rule suc, simp)
  apply (simp add: sObjUnion_def)
 done

lemma data\<^sub>f_of_data\<^sub>f_update:
  "data\<^sub>f (x\<lparr>data\<^sub>f := v\<rparr>) = v"
 by simp

lemma serialise_Obj_ret:
  assumes no_overflow: "offs \<le> offs + Obj.len\<^sub>f obj"
  and     is_valid_obj: "is_valid_ObjHeader obj (drop (unat offs) (\<alpha>wa (data\<^sub>f buf)))"
  and     otype: "otype\<^sub>f obj = bilbyFsObjTypePad"
  and     ounion: "\<And>v. ounion\<^sub>f obj = TObjPad v"
  and     bound: " offs + Obj.len\<^sub>f obj \<le> bound\<^sub>f buf \<and>
           unat (bound\<^sub>f buf) \<le> length (\<alpha>wa (data\<^sub>f buf))"
  and     suc: "\<And>buf'. 
   buf' = buf\<lparr>data\<^sub>f := WordArrayT.make (buf_sub_slice buf offs (offs + Obj.len\<^sub>f obj) (sObj obj))\<rparr> \<Longrightarrow>
    P (buf', offs + Obj.len\<^sub>f obj)"
  shows
   "P (serialise_Obj (buf, offs, obj))"
   unfolding serialise_Obj_def[unfolded tuple_simps sanitizers]
  apply (simp add: Let_def)
  apply (rule serialise_ObjHeader_ret)
    using no_overflow is_valid_obj apply (clarsimp simp: is_valid_ObjHeader_def bilbyFsObjHeaderSize_def)
    apply (frule is_len_and_type_ok_hdr_szD, simp add: bilbyFsObjHeaderSize_def)
    apply unat_arith
   using is_valid_obj apply assumption
  apply simp
  apply (rule serialise_ObjUnion_ret)
       using is_valid_obj no_overflow apply (clarsimp simp: is_valid_ObjHeader_def bilbyFsObjHeaderSize_def )
       apply (frule  is_len_and_type_ok_hdr_szD)
       apply (simp add: bilbyFsObjHeaderSize_def)
       apply unat_arith
      apply (rule otype)
     using ounion apply simp
    using is_valid_obj no_overflow apply (clarsimp simp: is_valid_ObjHeader_def bilbyFsObjHeaderSize_def)
   using bound apply (simp add: wordarray_make buf_sub_slice_length)
  apply simp
 apply (rule suc)
    apply (rule arg_cong[where f="\<lambda>v. Buffer.data\<^sub>f_update v buf"])
   apply (rule ext)
   apply (rule arg_cong[where f="WordArrayT.make"])
   apply (thin_tac x for x)+
   apply (subst buf_sub_slice_absorb)
         apply (simp  add: length_sObjHeader)
        apply (subst length_sObjUnion[OF ounion otype])
        using is_valid_obj apply (clarsimp simp: is_valid_ObjHeader_def is_len_and_type_ok_hdr_szD)
       using is_valid_obj no_overflow apply (clarsimp simp: is_valid_ObjHeader_def  unat_plus_simple)
       apply (drule is_len_and_type_ok_hdr_szD)
       apply (unat_arith)
       apply (simp add: is_len_and_type_ok_hdr_szD)
      apply(simp add: bilbyFsObjHeaderSize_def)
     using no_overflow is_valid_obj apply (clarsimp simp: is_valid_ObjHeader_def  bilbyFsObjHeaderSize_def)
     apply (simp add:  is_len_and_type_ok_def otype otype_simps)
     apply (unat_arith)
    using bound is_valid_obj apply (clarsimp simp: is_valid_ObjHeader_def)
    apply unat_arith
   apply (simp add: sObj_def)
 done

lemma binNot_NOT: "binNot (x::64 word) = NOT x"
  unfolding  binNot_def[unfolded Let_def]
  by (rule subst[where s="-1"], fastforce, fastforce)

lemma deserialise_ObjDel_ret:
  assumes bound: "unat offs + 8 \<le> length (\<alpha>wa $ data\<^sub>f buf)"
  assumes err: "P (Error (eInval, ex))"
  assumes offs: "offs < offs + 8"
  assumes suc:
   "\<And>obj offs'. \<lbrakk> 
    obj = pObjDel (\<alpha>wa $ data\<^sub>f buf) offs;
    ObjDel.id\<^sub>f obj AND NOT bilbyFsOidMaskAll \<in> 
      { bilbyFsOidMaskData, bilbyFsOidMaskInode,bilbyFsOidMaskDentarr};
    offs' = offs + 8\<rbrakk> \<Longrightarrow> 
   P (Success (ex, obj, offs'))"
  shows "P (deserialise_ObjDel (ex, buf, offs))"
proof - 
  have des_le64: "deserialise_le64 (buf, offs) = ple64 (\<alpha>wa $ data\<^sub>f buf) offs"
   using bound offs
   by (fastforce intro!: deserialise_le64_ret simp: unat_arith_simps)
  show ?thesis
  unfolding deserialise_ObjDel_def[unfolded tuple_simps sanitizers] 
  apply (clarsimp simp: Let_def err[simplified eInval_def])
  by (fastforce
     intro: suc
     simp: Let_def binNot_NOT bilbyFsOidMaskData_def des_le64 bilbyFsOidMaskAll_def
      bilbyFsOidMaskInode_def bilbyFsOidMaskDentarr_def pObjDel_def ObjDel.make_def)
qed

lemma deserialise_ObjInode_ret:
  assumes bound: "unat offs + 60 \<le> length (\<alpha>wa $ data\<^sub>f buf)"
  assumes offs: "offs < offs + 60"
  assumes err: "\<And>ex e. e \<in> {eInval, eNoMem} \<Longrightarrow> P (Error (e, ex))"
  assumes suc:
   "\<And>ex oi offs'. \<lbrakk> 
    oi = pObjInode (\<alpha>wa (data\<^sub>f buf)) offs;
    offs' = offs + 60\<rbrakk> \<Longrightarrow> 
   P (Success (ex, oi, offs'))"
  shows "P (deserialise_ObjInode (ex, buf, offs))"
proof -
  have des_le64:
    "deserialise_le64 (buf, offs) = (ple64 (\<alpha>wa $ data\<^sub>f buf) offs)"
    "deserialise_le64 (buf, offs + 8) = (ple64 (\<alpha>wa $ data\<^sub>f buf) (offs + 8))"
    "deserialise_le64 (buf, offs + 16) = (ple64 (\<alpha>wa $ data\<^sub>f buf) (offs + 16))"
    "deserialise_le64 (buf, offs + 24) = (ple64 (\<alpha>wa $ data\<^sub>f buf) (offs + 24))"
    "deserialise_le64 (buf, offs + 32) = (ple64 (\<alpha>wa $ data\<^sub>f buf) (offs + 32))"
     using bound offs
     by - (simp,rule deserialise_le64_ret[simplified];
                  (simp add: unat_arith_simps, unat_arith?))+
  have des_le32:
   "deserialise_le32 (buf, offs + 40) = (ple32 (\<alpha>wa $ data\<^sub>f buf) (offs + 40))"
   "deserialise_le32 (buf, offs + 44) = (ple32 (\<alpha>wa $ data\<^sub>f buf) (offs + 44))"
   "deserialise_le32 (buf, offs + 48) = (ple32 (\<alpha>wa $ data\<^sub>f buf) (offs + 48))"
   "deserialise_le32 (buf, offs + 52) = (ple32 (\<alpha>wa $ data\<^sub>f buf) (offs + 52))"
   "deserialise_le32 (buf, offs + 56) = (ple32 (\<alpha>wa $ data\<^sub>f buf) (offs + 56))"
     using bound offs
     by - (simp,rule deserialise_le32_ret[simplified];
                  (simp add: unat_arith_simps, unat_arith?))+

  show ?thesis
  unfolding deserialise_ObjInode_def[unfolded tuple_simps sanitizers] 
  by (fastforce 
     intro: suc err
     split: R.split
     simp: eInval_def eNoMem_def binNot_NOT Let_def bilbyFsOidMaskAll_def des_le32
      bilbyFsOidMaskInode_def word32Max_def pObjInode_def ObjInode.make_def des_le64)
qed

lemma deserialise_ObjSuper_ret:
  assumes bound: "unat offs + 40 \<le> length (\<alpha>wa $ data\<^sub>f buf)"
  assumes offs: "offs \<le> offs + 40" (* added by Yutaka on 11th.*)
  assumes err: "\<And>ex. P (Error (eNoMem, ex))"
  assumes suc:
   "\<And>ex osup offs'. \<lbrakk> 
    osup = pObjSuper (\<alpha>wa (data\<^sub>f buf)) offs;
    offs' = offs + 40\<rbrakk> \<Longrightarrow> 
   P (Success (ex, osup, offs'))"
  shows "P (deserialise_ObjSuper (ex, buf, offs))"
proof -
  have des_le64:
    "deserialise_le64 (buf, offs + 32) = (ple64 (\<alpha>wa $ data\<^sub>f buf) (offs + 32))"
     using bound offs
     by - (simp,rule deserialise_le64_ret[simplified];
                  (simp add: unat_arith_simps, unat_arith?))
  have des_le32:
   "deserialise_le32 (buf, offs) = (ple32 (\<alpha>wa $ data\<^sub>f buf) offs)"
   "deserialise_le32 (buf, offs + 4) = (ple32 (\<alpha>wa $ data\<^sub>f buf) (offs + 4))"
   "deserialise_le32 (buf, offs + 8) = (ple32 (\<alpha>wa $ data\<^sub>f buf) (offs + 8))"
   "deserialise_le32 (buf, offs + 12) = (ple32 (\<alpha>wa $ data\<^sub>f buf) (offs + 12))"
   "deserialise_le32 (buf, offs + 16) = (ple32 (\<alpha>wa $ data\<^sub>f buf) (offs + 16))"
   "deserialise_le32 (buf, offs + 20) = (ple32 (\<alpha>wa $ data\<^sub>f buf) (offs + 20))"
   "deserialise_le32 (buf, offs + 24) = (ple32 (\<alpha>wa $ data\<^sub>f buf) (offs + 24))"
   "deserialise_le32 (buf, offs + 28) = (ple32 (\<alpha>wa $ data\<^sub>f buf) (offs + 28))"
     using bound offs
     by - (simp,rule deserialise_le32_ret[simplified];
                  (simp add: unat_arith_simps, unat_arith?))+

  show ?thesis
  unfolding deserialise_ObjSuper_def[unfolded tuple_simps sanitizers] 
  by (fastforce 
     intro: suc err[unfolded eNoMem_def] 
     split: R.split 
     simp: pObjSuper_def ObjSuper.make_def des_le32 des_le64)
qed

lemma slice_Cons_helper:
  "i < length xs \<Longrightarrow>
    xs \<noteq> [] \<Longrightarrow>
    drop i xs = 
    (xs !  i) # drop ( (i + 1)) xs" 
    apply (cases xs, simp_all)
    by (metis (no_types, hide_lams) drop_Suc_Cons Cons_nth_drop_Suc length_Cons)

lemma slice_singleton:
 "f < length xs \<Longrightarrow> slice f (Suc f) xs = [xs ! f]"
 unfolding slice_def by (simp add:drop_take list_eq_iff_nth_eq)

lemma take_n_minus_1_append:
  "0<n \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> n \<le> length xs \<Longrightarrow>
 take (n - Suc 0) xs @ [xs ! (n - Suc 0)] = take n xs"
  apply (simp only: list_eq_iff_nth_eq)
  apply clarsimp
  apply (case_tac "(length xs) < (n - Suc 0)")
   apply (clarsimp simp add: min_absorb2)+
  by (metis One_nat_def Suc_pred' elem_take_n le0 le_less_trans diff_le_self
  less_not_refl linorder_neqE_nat diff_Suc_less take_Suc_conv_app_nth)

lemma take_n_minus_1_append_eq:
  "v = xs ! (unat (n - 1)) \<Longrightarrow> unat n  \<le> length xs \<Longrightarrow> n> 0 \<Longrightarrow>
  take (unat ((n::U32) - 1)) xs @ [v] = take (unat n) xs"
  apply (simp add: list_eq_iff_nth_eq min_absorb2 unat_arith_simps)
  apply clarsimp
  apply (subst take_n_minus_1_append)
     apply simp+
  apply (case_tac xs, simp_all)
 done

lemma slice_n_minus_1_append_last:
 "unat acc + unat n \<le> length xs \<Longrightarrow>
  (n::U32) > 0 \<Longrightarrow>
  acc \<le> acc + n \<Longrightarrow>
  slice (unat acc) (unat acc + unat (n - 1)) xs @
  [xs ! unat (acc + (n - 1))] =
  slice (unat acc) (unat acc + unat n) xs"
  apply (simp add:  slice_def list_eq_iff_nth_eq)
  apply (subgoal_tac "(length xs) \<ge> (unat acc + unat (n - 1))")
   prefer 2
   apply unat_arith
  apply (rule conjI)
   apply (simp add: min_absorb1 min_absorb2)
  apply (clarsimp simp: drop_take min_absorb1 min_absorb2 )
  apply (subst take_n_minus_1_append_eq)
     apply simp
     apply (rule arg_cong[where f="nth xs"]) 
     apply unat_arith (* takes long *)
    apply simp+
 done

lemma map_deserialise_waU8_map_eq_slice_apply:
  assumes nonempty: "xs \<noteq> []"
  assumes "length xs = unat (n:: 32 word)"
  assumes n_gr_0: "n > 0"
  assumes no_overflow: "acc \<le> acc + n"
  assumes bound: "unat acc + length xs \<le> length (\<alpha>wa d)"
  shows "
    (mapAccumObs 0 (length xs) deserialise_waU8_map xs acc d) =
 (FunBucket.slice (unat acc) (unat acc + (length xs)) (\<alpha>wa d), acc + n)"
  using assms
  apply (clarsimp simp: mapAccumObs_def ElemAO.make_def
        deserialise_waU8_map_def[unfolded tuple_simps sanitizers] slice_def[where frm=0])
  apply (induct "xs" arbitrary: n rule: rev_nonempty_induct)
   apply (drule sym, simp add: slice_singleton wordarray_get_ret unat_arith_simps)
  apply (drule_tac x="n - 1" in meta_spec)
  apply (erule meta_impE)
   apply unat_arith
  apply (erule meta_impE)
   apply (subgoal_tac "unat n \<ge> 2")
   apply unat_arith
   apply (case_tac xs, simp, simp)
  apply (erule meta_impE)
   apply unat_arith
  apply (erule meta_impE)
   apply unat_arith
  apply (simp add: prod.case_eq_if)
  apply (rule wordarray_get_ret')
   apply unat_arith (* takes a while *)
  apply (simp only: slice_n_minus_1_append_last)
 done

lemma map_deserialise_waU8_map_eq_slice:
  assumes n_gr_0: "n > 0"
  assumes no_overflow: "acc \<le> acc + n"
  assumes bound: "unat acc + unat n \<le> length (\<alpha>wa d)"
  assumes "length xs = unat (n:: 32 word)"
  shows "
    prod.fst (mapAccumObs 0 (unat n) deserialise_waU8_map xs acc d) =
     (FunBucket.slice (unat acc) (unat acc + unat n ) (\<alpha>wa d))"
  using map_deserialise_waU8_map_eq_slice_apply[THEN arg_cong[where f=prod.fst]]
        assms

 by (subgoal_tac "xs \<noteq> []") (fastforce simp: unat_arith_simps)+

lemma deserialise_wordarray_U8_ret:
  assumes err: "\<And>ex. P (Error (eNoMem, ex))"
  assumes suc:                       
   "\<And>ex wa. 
   offs \<le> offs + len \<longrightarrow> unat offs + unat len \<le> length (\<alpha>wa $ data\<^sub>f buf) \<longrightarrow> 
   wa = WordArrayT.make (slice (unat offs) (unat offs + unat len) (\<alpha>wa (data\<^sub>f buf))) \<Longrightarrow> 
   P (Success (ex, wa))"
  shows "P (deserialise_wordarray_U8 (ex, buf, offs, len))"
  unfolding deserialise_wordarray_U8_def[unfolded tuple_simps sanitizers] 
  apply (simp add: Let_def)
  apply (rule wordarray_create_ret)
   apply simp
   apply (simp add: err[unfolded eNoMem_def])
  apply (rename_tac ex' wa)
  apply  simp
  apply (rule wordarray_copy_ret)
  apply (simp add:Let_def prod.case_eq_if)
  apply (rule suc)
  apply clarsimp
 done

lemma deserialise_ObjData_ret:
  assumes offs_no_of: "offs \<le> offs + (olen - bilbyFsObjHeaderSize)"
  assumes buf_len: "unat (offs + (olen - bilbyFsObjHeaderSize)) \<le> length (\<alpha>wa (data\<^sub>f buf))"
  assumes olen: "is_len_and_type_ok (bilbyFsObjTypeData, olen)"
  assumes err: "\<And>ex e. e \<in> {eInval, eNoMem} \<Longrightarrow> P (Error (e, ex))"
  assumes suc:
   "\<And>ex od offs' . \<lbrakk>
   ObjData.id\<^sub>f od AND NOT bilbyFsOidMaskAll OR bilbyFsOidMaskData = ObjData.id\<^sub>f od;
     od = pObjData (\<alpha>wa (data\<^sub>f buf)) offs olen;
    offs' = offs + olen - bilbyFsObjHeaderSize\<rbrakk> \<Longrightarrow> 
   P (Success (ex, od, offs'))"
  shows "P (deserialise_ObjData (ex, buf, offs, olen))"
  proof -

   have hdr_le_olen: "bilbyFsObjDataHeaderSize \<le> (olen - bilbyFsObjHeaderSize)"
    using olen
    by (simp add: is_len_and_type_ok_def[unfolded sanitizers tuple_simps] otype_simps
      bilbyFsObjHeaderSize_def bilbyFsObjDataHeaderSize_def) unat_arith

  have offs_pl_hdr_le_offs_pl_olen:
  "offs + bilbyFsObjDataHeaderSize \<le> offs + (olen - bilbyFsObjHeaderSize)"
   using hdr_le_olen offs_no_of
   by (simp add: bilbyFsObjDataHeaderSize_def bilbyFsObjHeaderSize_def word_plus_mono_right)


  have offs_pl_hdr_no_of:
   "offs < offs + bilbyFsObjDataHeaderSize"
    using offs_no_of  hdr_le_olen
    by (simp add: bilbyFsObjDataHeaderSize_def bilbyFsObjHeaderSize_def)
       unat_arith

  have offs_pl_hdr_le_buf_len:
   "unat offs + unat bilbyFsObjDataHeaderSize \<le> length (\<alpha>wa (data\<^sub>f buf))"
   using  buf_len hdr_le_olen offs_pl_hdr_no_of offs_pl_hdr_le_offs_pl_olen
   by (simp add: bilbyFsObjHeaderSize_def bilbyFsObjDataHeaderSize_def)
      unat_arith

  have unat_offs_pl_olen_etc_eq: "unat (offs + (olen - bilbyFsObjHeaderSize)) = unat (offs + 8) + unat (0xFFFFFFE0 + olen)"
   using olen hdr_le_olen offs_pl_hdr_no_of offs_pl_hdr_le_offs_pl_olen
   apply (simp add: bilbyFsObjHeaderSize_def bilbyFsObjDataHeaderSize_def)
   apply (simp add: is_len_and_type_ok_def[unfolded sanitizers tuple_simps] otype_simps bilbyFsObjHeaderSize_def)
   apply (subgoal_tac "unat (offs + (olen - 0x18)) = unat (offs + 8) + unat (olen - 0x18 - 8)")
    apply unat_arith
   apply (simp add: unat_arith_simps)
   apply unat_arith
  done

  show ?thesis
  unfolding deserialise_ObjData_def[unfolded tuple_simps sanitizers] 
  apply (clarsimp simp: Let_def err[unfolded eNoMem_def eInval_def] binNot_NOT)
  apply (rule deserialise_wordarray_U8_ret)
    apply (simp add: err)
   apply (erule impE)
    using offs_pl_hdr_no_of apply (simp add: bilbyFsObjHeaderSize_def bilbyFsObjDataHeaderSize_def add.commute add.assoc)
    apply (subgoal_tac "olen + 0xFFFFFFE8 = olen - 0x18") (* Oh! Beloved words <3 *)
     prefer 2
     apply simp
   apply (simp only:)
   apply simp
   using offs_pl_hdr_le_offs_pl_olen apply (simp add: bilbyFsObjHeaderSize_def bilbyFsObjDataHeaderSize_def )
  apply simp
  apply (rule suc)
    apply simp
    apply (simp add: bilbyFsOidMaskAll_def bilbyFsOidMaskData_def
      pObjData_def ObjData.make_def bilbyFsObjHeaderSize_def)
   apply (simp add: Let_def  pObjData_def ObjData.make_def bilbyFsObjHeaderSize_def bilbyFsObjDataHeaderSize_def)
  apply (subst deserialise_le64_ret)
    using offs_pl_hdr_le_buf_len[simplified bilbyFsObjHeaderSize_def bilbyFsObjDataHeaderSize_def]
    apply (simp add:)
   using offs_pl_hdr_no_of
    apply (simp add: bilbyFsObjDataHeaderSize_def)
   apply (erule impE)
    using buf_len unat_offs_pl_olen_etc_eq
    apply simp
   apply simp
  apply (simp add: bilbyFsObjHeaderSize_def)
 done
qed

lemma deserialise_ObjPad_ret:
  assumes err: "P (Error (eInval, ex))"
  assumes suc: "\<And> out offs' .
    \<lbrakk> olen - bilbyFsObjHeaderSize \<le> olen ; 
      out=(); 
      offs' = offs + (olen - bilbyFsObjHeaderSize) \<rbrakk> \<Longrightarrow> 
    P (Success (ex, out, offs'))"
  shows "P (deserialise_ObjPad (ex, buf, offs, olen))"
  unfolding deserialise_ObjPad_def[unfolded tuple_simps sanitizers]
  by (auto simp: Let_def err[unfolded eInval_def] suc[unfolded bilbyFsObjHeaderSize_def] split: R.split)

lemma no_offs_overflow:
  assumes wellformed_buf: "wellformed_buf buf"
  assumes no_overflow: "length (\<alpha>wa $ data\<^sub>f buf) \<le> unat bilbyFsMaxEbSize"
  assumes offs_bound: "offs \<le> (bound\<^sub>f buf)"
  assumes "n < bilbyFsMaxEbSize"
  assumes "m < bilbyFsMaxEbSize"
  shows "offs + n \<le> offs + n + m"
  using assms
  by (auto simp add: bilbyFsMaxEbSize_def wellformed_buf_def unat_arith_simps)

lemma no_offs_overflow_le:
  assumes wellformed_buf: "wellformed_buf buf"
  assumes no_overflow: "length (\<alpha>wa $ data\<^sub>f buf) \<le> unat bilbyFsMaxEbSize"
  assumes offs_bound: "offs \<le> (bound\<^sub>f buf)"
  assumes "n < bilbyFsMaxEbSize"
  assumes "m < bilbyFsMaxEbSize"
  assumes "m > 0"
  shows "offs + n < offs + n + m"
  using assms
  by (auto simp add: bilbyFsMaxEbSize_def wellformed_buf_def unat_arith_simps)

lemma conc_offs_no_of:
  assumes wellformed_buf: "wellformed_buf buf"
  assumes no_overflow: "length (\<alpha>wa $ data\<^sub>f buf) \<le> unat bilbyFsMaxEbSize"
  assumes offs_bound: "offs \<le> (bound\<^sub>f buf)"
  assumes "m < bilbyFsMaxEbSize"
  assumes "m > 0"
  shows "offs < offs + m"
  using assms
  by (auto simp add: bilbyFsMaxEbSize_def wellformed_buf_def unat_arith_simps)

lemma slice_take:
  "m \<le> l \<Longrightarrow> 
  slice n m (take l xs) = slice n m xs"
  by (simp add: slice_def)

lemma deserialise_pu8_ret:
assumes valid_offs:
  "unat offs + 1 < length (\<alpha>wa $ data\<^sub>f buf)"
assumes no_of:
  "offs < offs + 1"
shows
  "deserialise_u8 (buf, offs) = (pu8 (\<alpha>wa $ data\<^sub>f buf) offs)"
proof -
  from no_of have no_of': "offs \<le> offs + 1" by simp
  hence offs_pl_1: "unat (offs + 1) = unat offs + 1" by (simp add: unat_plus_simple)
  show ?thesis
using valid_offs
  apply (clarsimp simp:  wordarray_get_ret[where arr="data\<^sub>f buf"]
                        deserialise_u8_def pu8_def)
  apply (rule trans, rule word_rcat_rsplit[symmetric])
  apply (rule arg_cong[where f=word_rcat])
  apply (subst word_rsplit_upt[where n=1], simp add: word_size)
   apply (simp)
  apply (simp add: slice_def)
  apply (simp add: ucast_def)
  apply (subst Cons_nth_drop_Suc[symmetric])
   apply simp
  apply simp
 done
qed

lemma pu8_take:
 assumes offs:"offs < offs+1"
 assumes ntake:"unat (offs + 1) \<le> ntake"
 shows   "pu8 (take ntake ys) offs = pu8 ys offs"
  apply (simp add: pu8_def)
  apply (rule arg_cong[where f="word_rcat"])
  apply (rule slice_take)
 using ntake offs by unat_arith

lemma deserialise_ObjDentry_ret:
  assumes wellformed_buf: "wellformed_buf buf"
  assumes no_buf_overflow: "length (\<alpha>wa $ data\<^sub>f buf) \<le> unat bilbyFsMaxEbSize"
  assumes bound: "end_offs \<le> bound\<^sub>f buf"
  assumes off_less_end_offs: "offs \<le> end_offs"
  assumes err:
    "\<And>ex e. e \<in> {eInval, eNoMem} \<Longrightarrow> P (Error (e, ex))"
  assumes suc:
    "\<And>ex dentry offs'. \<lbrakk>
      unat offs + 8 + unat (wordarray_length (name\<^sub>f dentry)) \<le> unat (bound\<^sub>f buf);
      wordarray_length (name\<^sub>f dentry) \<le> bilbyFsMaxNameLen + 1;
      offs + 8 + wordarray_length (name\<^sub>f dentry) \<le> end_offs ;
      dentry = pObjDentry (take (unat end_offs) (\<alpha>wa (data\<^sub>f buf))) offs ;
      offs' = offs + 8 + wordarray_length (name\<^sub>f dentry);
      offs' \<le> (bound\<^sub>f buf)
        \<rbrakk> \<Longrightarrow>
      P (Success (ex, dentry, offs'))"
  shows "P (deserialise_ObjDentry (ex, buf, offs, end_offs))"
proof -
  {
    fix ex' dentry offs'
    assume des_suc: "unat offs + 8 \<le> unat (bound\<^sub>f buf)"

    then have offs_ok:"\<forall>n\<in>{0..7}. unat (offs + n)  < length (\<alpha>wa $ data\<^sub>f buf)"
    proof -
      from wellformed_buf[unfolded wellformed_buf_def] des_suc
      have "unat offs + 8 \<le> length (\<alpha>wa $ data\<^sub>f buf)"
        by unat_arith

      thus ?thesis
        by unat_arith
    qed

    from des_suc have deserialises:
      "deserialise_le32 (buf, offs)     = (ple32 (\<alpha>wa $ data\<^sub>f buf) offs)"
      "deserialise_u8   (buf, offs + 4) = (pu8 (\<alpha>wa $ data\<^sub>f buf) (offs + 4))"
      "deserialise_le16 (buf, offs + 6) = (ple16 (\<alpha>wa $ data\<^sub>f buf) (offs + 6))"
        apply clarsimp
        apply(rule deserialise_le32_ret[simplified])
      using assms[simplified bilbyFsMaxEbSize_def wellformed_buf_def]
         apply unat_arith 
      using assms[simplified bilbyFsMaxEbSize_def ]
        apply unat_arith
       apply (subst deserialise_pu8_ret)
      using offs_ok des_suc wellformed_buf
         apply (simp add: wellformed_buf_def, unat_arith)
      using des_suc
        apply unat_arith
       apply simp+
      apply(rule deserialise_le16_ret[simplified])
      using offs_ok des_suc wellformed_buf apply (simp add: wellformed_buf_def, unat_arith)
      using des_suc
      apply unat_arith
      done
  }
  note deserialises = this

  have offs_le_bound: "offs  \<le> bound\<^sub>f buf"
    using off_less_end_offs bound by simp

  have const_offs_no_of: "\<And>n. n < bilbyFsMaxEbSize \<Longrightarrow> 0 < n \<Longrightarrow> offs < offs + n"
    apply (rule conc_offs_no_of[OF wellformed_buf no_buf_overflow, unfolded bilbyFsMaxEbSize_def, simplified])
    using offs_le_bound by (simp add:bilbyFsMaxEbSize_def)+
  note no_of_8 = no_offs_overflow[OF wellformed_buf no_buf_overflow offs_le_bound, where m=8 and n=0, unfolded bilbyFsMaxEbSize_def, simplified, simplified unat_plus_simple]
  show ?thesis
    unfolding deserialise_ObjDentry_def[simplified tuple_simps sanitizers]
    apply (clarsimp simp: Let_def err[unfolded eNoMem_def eInval_def])
    apply (subst (asm) not_less)+
    apply (rule deserialise_wordarray_U8_ret)
     apply (clarsimp simp add: err)
    apply(clarsimp simp add: err eNoMem_def Let_def prod.case_eq_if split: R.splits)
    apply (erule impE)
     apply (rule no_offs_overflow[OF wellformed_buf no_buf_overflow])
    using off_less_end_offs bound apply fastforce
      apply (simp add: bilbyFsMaxEbSize_def)+
     apply unat_arith
    apply (subgoal_tac "unat offs + unat (8::32word) + unat (ucast (deserialise_le16 (buf, offs + 6))) \<le> unat end_offs")
     prefer 2
     apply (subst add.assoc)
     apply (subst unat_plus_simple[THEN iffD1, symmetric])
      apply (simp add: unat_arith_simps)
     apply (subst unat_plus_simple[THEN iffD1, symmetric])
      apply (rule no_offs_overflow[OF wellformed_buf no_buf_overflow, where n=0, simplified])
    using off_less_end_offs bound apply fastforce
       apply (simp add: bilbyFsMaxEbSize_def)+
      apply (simp add: unat_arith_simps)
     apply (simp add: word_le_nat_alt[symmetric] add.assoc)
    apply (erule impE)
    using bound wellformed_buf[unfolded wellformed_buf_def] 
     apply (simp add: unat_arith_simps)
     apply unat_arith
    apply (subgoal_tac "unat offs + 8 \<le> unat (bound\<^sub>f buf)")
     prefer 2 
     apply (subst unat_plus_simple[THEN iffD1, symmetric, 
          where y="8::32word", simplified])
      apply (rule no_offs_overflow[OF wellformed_buf no_buf_overflow, 
          where n=0, simplified])
    using off_less_end_offs bound apply fastforce
       apply (simp add: bilbyFsMaxEbSize_def)+ 
     apply (subst word_le_nat_alt[symmetric])
     apply (cut_tac no_offs_overflow[OF wellformed_buf no_buf_overflow, 
          where offs=offs and n=8 and m="ucast (deserialise_le16 (buf, offs + 6))"])
    using off_less_end_offs bound apply (simp_all add: bilbyFsMaxEbSize_def)
     apply unat_arith
    apply (simp add: deserialises) 
    apply (subgoal_tac "wordarray_length (WordArrayT.make
         (FunBucket.slice (unat (offs + 8)) 
          (unat (offs + 8) + unat (ucast (ple16 (\<alpha>wa (data\<^sub>f buf)) (offs + 6)) :: 32 word))
          (\<alpha>wa (data\<^sub>f buf)))) \<le> ucast (ple16 (\<alpha>wa (data\<^sub>f buf)) (offs + 6))")
     prefer 2
     apply (subst wordarray_length_ofnat)
      apply (simp add: wordarray_length_ret)
     apply (subst wordarray_make)
     apply (simp add: slice_length)
     apply (subst min_absorb1)  
      prefer 3
    using wellformed_buf[unfolded wellformed_buf_def]  no_buf_overflow[unfolded bilbyFsMaxEbSize_def]
      apply (simp add: unat_arith_simps)
      apply (subgoal_tac 
        "unat (ucast (ple16 (\<alpha>wa (data\<^sub>f buf)) (offs + 6)) :: 32 word) = 
              unat (ple16 (\<alpha>wa (data\<^sub>f buf)) (offs + 6))")
       prefer 2 
       apply (fastforce intro: uint_up_ucast simp: eq_nat_nat_iff unat_def is_up) 
      apply (rule suc)  
           apply (simp_all add: Let_def pObjDentry_def ObjDentry.make_def bilbyFsMaxNameLen_def)
    using bound apply unat_arith
    using wellformed_buf[unfolded wellformed_buf_def]  no_buf_overflow[unfolded bilbyFsMaxEbSize_def]
        apply (simp add: unat_arith_simps)
       apply (simp add: ple16_take ple32_take const_offs_no_of bilbyFsMaxEbSize_def plus_no_overflow_unat_lift[OF const_offs_no_of[unfolded bilbyFsMaxEbSize_def, simplified]])
       apply (subst ple16_take)
         apply (rule no_offs_overflow_le[OF wellformed_buf no_buf_overflow offs_le_bound])
           apply (simp add: bilbyFsMaxEbSize_def)+
    using no_of_8
        apply (simp add: add.commute)
       apply (subst ple16_take)
         apply (rule no_offs_overflow_le[OF wellformed_buf no_buf_overflow offs_le_bound])
           apply (simp add: bilbyFsMaxEbSize_def)+
    using no_of_8
        apply (simp add: add.commute)
       apply (subst pu8_take)
    using no_offs_overflow[OF wellformed_buf no_buf_overflow offs_le_bound, where m=5 and n=0, unfolded bilbyFsMaxEbSize_def, simplified]
      no_offs_overflow[OF wellformed_buf no_buf_overflow offs_le_bound, where m=4 and n=0, unfolded bilbyFsMaxEbSize_def, simplified]
         apply (simp add: add.commute unat_plus_simple)
         apply unat_arith
    using no_of_8
      no_offs_overflow[OF wellformed_buf no_buf_overflow offs_le_bound, where m=5 and n=0, unfolded bilbyFsMaxEbSize_def, simplified]
        apply (fastforce simp add: unat_plus_simple add.commute)
       apply (subst ObjDentry.surjective, simp)
       apply (rule arg_cong[where f=WordArrayT.make])
       apply (rule slice_take[symmetric], simp)
      apply (rule word_unat.Rep_eqD)
      apply (simp add: wordarray_length_ret wordarray_make length_slice)
    using no_of_8 wellformed_buf
     apply (simp add: wellformed_buf_def)
     apply unat_arith
    using wellformed_buf[unfolded wellformed_buf_def]  no_buf_overflow[unfolded bilbyFsMaxEbSize_def]
    apply (simp add: unat_arith_simps)
    done
qed

lemma loop_deserialise_ObjDentry_ret:
  assumes wellformed_buf: "wellformed_buf buf"
  assumes no_buf_overflow: "length (\<alpha>wa $ data\<^sub>f buf) \<le> unat bilbyFsMaxEbSize"
  assumes bound: "end_offs \<le> bound\<^sub>f buf"
  assumes off_less_end_offs: "offs  \<le> end_offs"
  assumes st_offs: "st_offs \<le> offs"
  shows "case loop_deserialise_ObjDentry (OptElemAO.make dentry (ex, offs) (buf, end_offs)) of
            Break (none, e, ex) \<Rightarrow> none= Option.None () \<and> e = eInval 
          | Iterate (optdentry, ex, offs') \<Rightarrow>
             \<exists>dentry. optdentry = Option.Some dentry \<and>
                unat offs + 8 + unat (wordarray_length (name\<^sub>f dentry)) \<le> unat (bound\<^sub>f buf)  \<and>
                wordarray_length (name\<^sub>f dentry) \<le> bilbyFsMaxNameLen + 1  \<and>
                offs + 8 + wordarray_length (name\<^sub>f dentry) \<le> end_offs  \<and>
                dentry = pObjDentry (take (unat end_offs) (\<alpha>wa (data\<^sub>f buf))) offs  \<and>
                offs' = offs + 8 + wordarray_length (name\<^sub>f dentry) \<and>
                offs' \<le> (bound\<^sub>f buf)"
  unfolding loop_deserialise_ObjDentry_def[unfolded tuple_simps sanitizers]
  apply (clarsimp simp: Let_def OptElemAO.make_def)
  apply (rule deserialise_ObjDentry_ret[OF assms(1-4)])
  by (clarsimp simp: eInval_def)+

lemma slice_Cons:
  "frm < length xs \<Longrightarrow> frm < to
    \<Longrightarrow> slice frm to xs = xs ! frm # slice (Suc frm) to xs"
  apply (simp add: slice_def)
  apply (subst slice_Cons_helper[where i=frm], simp_all)
  apply clarsimp
  done

lemma slice_list_update:
  "n < length xs
    \<Longrightarrow> slice i j (xs[n := x]) = (if n < i then slice i j xs
        else if n \<ge> j then slice i j xs
        else (slice i j xs)[n - i := x])"
  by (simp add: slice_def drop_list_update take_list_update)

lemma mapAccumObsOpt_step:
  assumes frm: "frm < to" "frm < length xs"
  shows "mapAccumObsOpt frm to fn xs vacc obs =
        (case fn (OptElemAO.make (xs ! frm) vacc obs)
         of Iterate (oelem, acc) \<Rightarrow> 
             mapAccumObsOpt (Suc frm) to fn (xs [frm := oelem]) acc obs
         | Break (oelem, d) \<Rightarrow> Break (xs [frm := oelem], d))"
proof -
  let ?folder = "(\<lambda>elem. case_LoopResult (\<lambda>(ys, d). Break (ys @ [elem], d))
                               (\<lambda>(ys, acc).
                                   case fn (OptElemAO.make elem acc obs) of
                                  Break (oelem, d) \<Rightarrow> Break (ys @ [oelem], d)
                                | Iterate (oelem, acc) \<Rightarrow> Iterate (ys @ [oelem], acc)))"

  { fix xs ys d
  have fold_break: "fold ?folder xs (Break (ys, d))
        = Break (ys @ xs, d)"
    by (induct xs arbitrary: ys d, simp_all)
  }
  note fold_break = this

  have fold_iterate_Cons: "\<And>xs. \<forall>y ys acc. fold ?folder xs (Iterate (y # ys, acc))
        = (case (fold ?folder xs (Iterate (ys, acc)))
            of Iterate (zs, acc) \<Rightarrow> Iterate (y # zs, acc)
          | Break (zs, d) \<Rightarrow> Break (y # zs, d))"
    apply (induct_tac xs, simp_all)
    apply clarsimp
    apply (case_tac "fn (OptElemAO.make a acc obs)")
     apply (clarsimp simp add: fold_break)
    apply clarsimp
    done

  from frm have drop_helper: "\<And>x xs. drop (to - frm) (x # xs) = drop (to - Suc frm) xs"
    apply (cases "to - frm", simp_all)
    apply (cases to, simp_all)
    apply (cases frm, simp_all)
    apply (metis Suc_diff_Suc Suc_inject)
    done

  show ?thesis using frm
    apply (simp add: mapAccumObsOpt_def)
    apply (simp add: slice_Cons)
    apply (cases "fn (OptElemAO.make (xs ! frm) vacc obs)")
     apply (clarsimp simp: fold_break)
     apply (simp add: slice_def upd_conv_take_nth_drop max_absorb2)
     apply (subst append_take_drop_id
                  [where xs="drop (Suc frm) xs" and n="to -frm - 1", 
                    simplified take_drop, symmetric])
     apply simp
    apply (clarsimp simp: mapAccumObsOpt_def slice_list_update take_list_update)
    apply (simp add: fold_iterate_Cons)
    apply (simp split: LoopResult.split)
    apply (clarsimp simp: slice_def upd_conv_take_nth_drop min_absorb2 max_absorb2
                          drop_helper)
    done
 qed

lemma mapAccumObsOpt_n_n:
  "mapAccumObsOpt n n fn xs vacc obs = Iterate (xs, vacc)"
  by (clarsimp simp: mapAccumObsOpt_def slice_n_n)

lemma mapAccumObsOpt_frm_eq_len:
  "frm = length xs \<Longrightarrow> mapAccumObsOpt frm to fn xs vacc obs = Iterate (xs @ [], vacc)"
  by (clarsimp simp: mapAccumObsOpt_def slice_def)

lemma snd_fold_simp:
 "prod.snd (fold (\<lambda>_ (a, b). (f a b, f' b)) xs (a,b)) =
  fold (\<lambda>_ b. f' b) xs b"
  by (induct xs arbitrary: a b, simp_all) 

lemma fst_fold_append_simp:
  "prod.fst (fold (\<lambda>_ (xs, n). (xs @ [f n], f' n)) ls (f n' # xs, f' n)) = 
   f n' # prod.fst (fold (\<lambda>_ (xs, n). (xs @ [f n], f' n)) ls (xs, f' n)) "
   by (induct ls arbitrary: n xs, simp_all)

lemma snd_snd_fold_simp:
  "(prod.snd (fold (\<lambda>_ (xs, doffs, offslist). (f xs doffs, f' doffs, f'' doffs offslist))  ls (xs, n, offslist))) =
    fold (\<lambda>_ (doffs, offslist).  (f' doffs, f'' doffs offslist)) ls (n, offslist)" 
  by (induct ls arbitrary: xs n offslist, simp_all) 

lemma snd_fold_append_gen_simp:
 "prod.snd (fold (\<lambda>_ (x, xs). (f' x, xs @ [f x])) ls (x, xs @ ys)) =
   xs @ prod.snd (fold (\<lambda>_ (x, xs). (f' x, xs @ [f x])) ls (x, ys))"
  by (induct ls arbitrary: x ys, simp_all)

lemma snd_fold_append_simp:
 "prod.snd (fold (\<lambda>_ (x, xs). (f' x, xs @ [f x])) ls (x, xs)) =
   xs @ prod.snd (fold (\<lambda>_ (x, xs). (f' x, xs @ [f x])) ls (x, []))"
 using snd_fold_append_gen_simp[where ys=Nil, simplified] .

lemma fst_fold_triple_simp:
 "prod.fst (fold (\<lambda>_ (a, b, c). (f a b, f' b, f'' b c)) ns (a, b, c)) =
  prod.fst (fold (\<lambda>_ (a, b). (f a b, f' b)) ns (a, b))"
  by (induct  ns arbitrary: a b c, simp_all)

lemma fst_snd_fold_triple_simp:
 "prod.fst (prod.snd (fold (\<lambda>_ (a, b, c). (f a b, f' b, f'' b c)) ns (a, b, c))) =
  prod.snd (fold (\<lambda>_ (a, b). (f a b, f' b)) ns (a, b))"
  by (induct  ns arbitrary: a b c, simp_all)

definition dentarr_offs_list_drop :: "U8 list \<Rightarrow> U32 \<Rightarrow> nat list \<Rightarrow> U32 \<Rightarrow> (32 word list)"
where
 "dentarr_offs_list_drop data ost entriesno offs =
    prod.snd (fold (\<lambda>_ (doffs, offslist).
      let dentry = pObjDentry (drop (unat offs) data) (doffs - offs);
          newoffs = doffs + 8 + wordarray_length (ObjDentry.name\<^sub>f dentry)
       in (newoffs, offslist @ [newoffs]))
      entriesno (ost, []))
"
definition
  dentarr_offs_list_drop_end_offs_pred
where
 "dentarr_offs_list_drop_end_offs_pred data ost entriesno offs end_offs \<equiv>
 \<forall>v\<in>set (dentarr_offs_list_drop data ost entriesno offs).
   v \<le> end_offs"

definition
 "dentarr_offs_list data ost entriesno \<equiv> 
  (prod.snd (fold (\<lambda>_ (doffs, offslist).
     let dentry = pObjDentry data doffs;
         newoffs = doffs + 8 + wordarray_length (ObjDentry.name\<^sub>f dentry)
     in (newoffs, offslist @ [newoffs]))
   entriesno (ost, [])))"

definition
  dentarr_offs_list_end_offs_pred
where
 "dentarr_offs_list_end_offs_pred data ost entriesno end_offs \<equiv>
 \<forall>v\<in>set (dentarr_offs_list data ost entriesno).
   v \<le> end_offs"

definition
  dentarr_otype_end_offs_pred
where
 "dentarr_otype_end_offs_pred otype data offs end_offs \<equiv>
 (otype = bilbyFsObjTypeDentarr \<longrightarrow>
 (let nbentry = ple32 data (offs + 8)
 in dentarr_offs_list_end_offs_pred data (offs+bilbyFsObjDentarrHeaderSize) [0..<unat nbentry] end_offs))"

lemmas dentarr_end_offs_simps = dentarr_offs_list_def dentarr_offs_list_end_offs_pred_def
  dentarr_otype_end_offs_pred_def

definition
  dentarr_otype_drop_end_offs_pred
where
 "dentarr_otype_drop_end_offs_pred otype data offs end_offs \<equiv>
 (otype = bilbyFsObjTypeDentarr \<longrightarrow>
  (let nbentry = ple32 data (offs+8)
  in dentarr_offs_list_drop_end_offs_pred data (offs+bilbyFsObjDentarrHeaderSize)
  [0..<unat nbentry] offs end_offs))
"
definition
  dentarr_otype_drop_end_offs_st_pred
where
 "dentarr_otype_drop_end_offs_st_pred otype data offs st_offs end_offs \<equiv>
 (otype = bilbyFsObjTypeDentarr \<longrightarrow>
  (let nbentry = ple32 data (offs+8)
  in dentarr_offs_list_drop_end_offs_pred data (offs+bilbyFsObjDentarrHeaderSize)
  [0..<unat nbentry] st_offs end_offs))
"

lemmas dentarr_drop_end_offs_simps = dentarr_offs_list_drop_def dentarr_offs_list_drop_end_offs_pred_def
  dentarr_otype_drop_end_offs_pred_def dentarr_otype_drop_end_offs_st_pred_def

lemma ple32_eq_slice:
 assumes "offs < offs + 4" 
 assumes "unat offs + 4 \<le> length xs"
 assumes "offs + 4 < end_offs"
 shows   "ple32 xs offs = ple32 (slice (unat offs) (unat end_offs) xs) 0"
 using assms 
  apply (simp add:  slice_def ple32_def drop_take word_add_eq_unat)
  apply (drule less_to_le, simp add: unat_plus_simple word_less_nat_alt)
 done

lemma split_upt_on_l_n:
  "n < m \<Longrightarrow> l \<le> n \<Longrightarrow> [l ..< m] = [l ..< n] @ [n] @ [Suc n ..< m]"
  apply (subst upt_add_eq_append')
  apply simp+
  apply (simp add: upt_conv_Cons)
  done

lemma unat_plus_simple_imp:
 "x \<le> (x::'a::len word) + y \<Longrightarrow> (unat (x + y) = unat x + unat y)"
 by (simp add: unat_plus_simple)

lemma pObjDentry_drop_eq:
 assumes offs_le_ost: "offs \<le> ost"
 and     ost_no_of8: " ost < ost + 8"
 and     ost_le_offs_olen: " ost \<le> end_offs"
 and     offs_olen_ys: "unat end_offs \<le> length ys"
 and     ys_le_max: " length ys \<le> unat bilbyFsMaxEbSize"
 and     end_offs: "end_offs_nat = unat end_offs"
 shows " pObjDentry (take end_offs_nat ys) ost = pObjDentry (drop (unat offs) (take end_offs_nat ys)) (ost - offs)"
proof -
 have ost_4_nat: "unat (ost + 4) = unat ost + 4"
   using ost_no_of8 by (simp add: unat_arith_simps) unat_arith

 have ost_le_max: "ost \<le> bilbyFsMaxEbSize" using ys_le_max offs_olen_ys ost_le_offs_olen
  by unat_arith

 hence offs_le_max: "offs \<le> bilbyFsMaxEbSize"
  using offs_le_ost by unat_arith


 have ost_minus_offs_bound: "ost - offs \<le> bilbyFsMaxEbSize"
  using  offs_le_ost ost_le_max
  by unat_arith

 have ost_no_ofs: "ost < ost + 4" "ost < ost + 6" using ost_no_of8
   by (clarsimp simp add: unat_arith_simps , unat_arith)+

 hence ost_offs_x: "unat (ost - offs + 4) = unat ost - unat offs + 4"
                   "unat (ost - offs + 6) = unat ost - unat offs + 6"
                   "unat (ost - offs + 8) = unat ost - unat offs + 8"
   using offs_le_ost offs_le_ost[simplified word_le_nat_alt] ost_4_nat 
   ost_minus_offs_bound
   apply (simp_all add: bilbyFsMaxEbSize_def)
   apply ((drule plus_no_overflow_unat_lift)+, 
      (subst unat_plus_simple_imp,
       simp only: word_le_nat_alt, unat_arith,subst unat_sub, simp+))

   apply ((drule plus_no_overflow_unat_lift)+, 
      (subst unat_plus_simple_imp,
       simp only: word_le_nat_alt, unat_arith,subst unat_sub, simp+))

   apply ((drule plus_no_overflow_unat_lift)+)
   apply (subst unat_plus_simple_imp)
   apply (simp only: word_le_nat_alt word_less_nat_alt)
   using offs_le_max[simplified bilbyFsMaxEbSize_def word_le_nat_alt]
   ost_no_of8

   apply (simp only:unat_arith_simps)
   apply unat_arith
  apply (subst unat_sub, simp+)
 done

 have offs_cancel: "(unat ost - unat offs + 4 + unat offs) = unat ost + 4" 
                   "(unat ost - unat offs + 6 + unat offs) = unat ost + 6"
                   "(unat ost - unat offs + 8 + unat offs) = unat ost + 8"
  using offs_le_ost[simplified word_less_nat_alt] by unat_arith+

 have ple16_eq: "ple16 (take end_offs_nat ys) (ost + 6) = ple16 (drop (unat offs) (take end_offs_nat ys)) (ost - offs + 6)"
   apply (simp add: ple16_def)
   apply (rule arg_cong[where f=word_rcat])
   apply (rule arg_cong[where f=rev])
   apply (rule arg_cong[where f="take 2"])
   apply (fastforce simp add: ost_offs_x offs_cancel less_to_le[OF ost_no_ofs(2), simplified unat_plus_simple])
  done

 have offs_cancel': "\<forall>v. unat ost - unat offs + 8 + unat v + unat offs = unat ost + 8 + unat v"
  using offs_le_ost[simplified word_less_nat_alt]
  by unat_arith

 show ?thesis
  apply (simp add: pObjDentry_def Let_def ObjDentry.make_def)
  apply (rule conjI)
   apply (simp add: ple32_def)
   apply (rule arg_cong[where f=word_rcat])
   apply (rule arg_cong[where f=rev])
   apply (rule arg_cong[where f="take 4"])
   apply (subst unat_sub[OF offs_le_ost])
   using offs_le_ost
   apply (subst add_diff_assoc2, fastforce simp: word_le_nat_alt)
   apply fastforce
  apply (rule conjI)
   apply (simp add: pu8_def )
   apply (rule arg_cong[where f=word_rcat])
   apply (simp only: slice_def drop_take fun_app_def)
   using ost_offs_x ost_4_nat
   apply simp
   apply (simp add: take_drop offs_cancel)
   apply (subst add.commute, fastforce simp only: offs_cancel)
  apply (simp add: ple16_eq )
  apply (rule arg_cong[where f=WordArrayT.make])
  apply (subgoal_tac "\<exists>v. ple16 (drop (unat offs) (take (unat offs + unat (Obj.len\<^sub>f obj)) ys)) (ost - offs + 6) = v")
   apply (erule exE)
   apply (simp only: ost_offs_x less_to_le[OF ost_no_of8, simplified unat_plus_simple])
   apply (simp add: slice_def take_drop )
   apply (simp add: offs_cancel offs_cancel')+
  done
qed

lemma wa_length_ObjDentry_name_le:
 "unat (wordarray_length (ObjDentry.name\<^sub>f (pObjDentry xs ost))) \<le> length xs"
 by (simp add: pObjDentry_def Let_def ObjDentry.make_def wordarray_make wordarray_length_ret slice_def)

lemma wa_length_ObjDentry_name_le_len:
 "unat (wordarray_length (ObjDentry.name\<^sub>f (pObjDentry xs ost))) \<le> unat (ple16 xs (ost + 6))"
 by (simp add: pObjDentry_def Let_def ObjDentry.make_def wordarray_make wordarray_length_ret slice_def)

lemma dentarr_end_offs_list_induct_helper:
 assumes diff: "Suc diff = unat to - frm"
 and     ih: "dentarr_offs_list_end_offs_pred (take (unat end_offs) (\<alpha>wa (data\<^sub>f buf))) (offs + 8 +
     wordarray_length
      (ObjDentry.name\<^sub>f (pObjDentry (take (unat end_offs) (\<alpha>wa (data\<^sub>f buf))) offs)))
    [Suc frm..<unat to] end_offs"
 and cur: "   offs + 8 +
   wordarray_length (ObjDentry.name\<^sub>f (pObjDentry (take (unat end_offs) (\<alpha>wa (data\<^sub>f buf))) offs))
   \<le> end_offs"
 shows
 "dentarr_offs_list_end_offs_pred (take (unat end_offs) (\<alpha>wa (data\<^sub>f buf))) offs [frm..<unat to] end_offs"
proof -
  have frm_lt_to: "frm < unat to" using diff by unat_arith
  show ?thesis
  apply (clarsimp simp: dentarr_end_offs_simps )
  apply (subst (asm) upt_rec, simp add: frm_lt_to Let_def) 
  apply (subst (asm) snd_fold_append_simp)
  apply clarsimp
  apply (erule disjE)
   using cur apply simp
  using ih apply (simp add: dentarr_end_offs_simps Let_def)
 done
qed

lemma offs_pl_8_name_of:
  " wellformed_buf buf \<Longrightarrow>
    length (\<alpha>wa $ data\<^sub>f buf) \<le> unat bilbyFsMaxEbSize \<Longrightarrow>
    offs + 8 + wordarray_length (ObjDentry.name\<^sub>f (pObjDentry (take (unat end_offs) (\<alpha>wa (data\<^sub>f buf))) offs)) \<le> bound\<^sub>f buf \<Longrightarrow>
    offs \<le> bilbyFsMaxEbSize  \<Longrightarrow>
    offs < offs + 8"
 apply (simp add: bilbyFsMaxEbSize_def)
 using wa_length_ObjDentry_name_le[where xs="(take (unat end_offs) (\<alpha>wa (data\<^sub>f buf)))" and ost=offs]
 apply (clarsimp simp add: wellformed_buf_def)
 apply (simp add: unat_arith_simps)
done

lemma mapAccumObsOpt_loop_deserialise_ObjDentry_ret:
  assumes wellformed_buf: "wellformed_buf buf"
  assumes no_buf_overflow: "length (\<alpha>wa $ data\<^sub>f buf) \<le> unat bilbyFsMaxEbSize"
  assumes bound: "end_offs \<le> bound\<^sub>f buf"
  assumes off_less_end_offs: "offs  \<le> end_offs"
  assumes frm: "frm \<le> unat (to::word32)" "unat to \<le> length ys" 
  assumes st_offs: "st_offs \<le> offs"
  shows 
  "let list_spec = 
      case (fold (\<lambda>_ (xs, doffs, offslist).
             let dentry = pObjDentry (take (unat end_offs) (\<alpha>wa (data\<^sub>f buf))) doffs ;
                 newoffs = doffs +  8 + wordarray_length (ObjDentry.name\<^sub>f dentry)
             in (xs@[Option.Some dentry], 
                newoffs, offslist @ [newoffs])) 
           [frm..<unat to] ([], offs, [])) 
         of (xs, offs) \<Rightarrow> ((take frm ys) @ xs @ (drop (unat to) ys), offs);
      data = take (unat end_offs) (\<alpha>wa (data\<^sub>f buf)) in
  (case mapAccumObsOpt frm (unat to) loop_deserialise_ObjDentry 
     ys (ex, offs) (buf, end_offs) of
       Break (ys, d, ex) \<Rightarrow> 
        d \<in> {eInval, eNoMem}
     | Iterate (ys, ex, offs') \<Rightarrow> 
        
        (ys, ex, offs') = (prod.fst list_spec, ex, prod.fst (prod.snd list_spec)) \<and>
        offs' \<le> end_offs \<and>
        dentarr_offs_list_end_offs_pred data offs [frm..<unat to] end_offs \<and>
        dentarr_offs_list_drop_end_offs_pred data offs [frm..<unat to] st_offs end_offs)"
  using assms
  proof (induct "unat to - frm" arbitrary: frm ys ex offs)
  case 0
  thus ?case
   by (simp add: dentarr_end_offs_simps mapAccumObsOpt_n_n dentarr_drop_end_offs_simps)
next   
  case (Suc diff) 
  note IH = this(1) and rest = this(2-)

  have offs_le_max: "offs \<le> bilbyFsMaxEbSize"
   using rest by (simp add: unat_arith_simps wellformed_buf_def) 

  hence offs_pl_8: "offs < offs + 8"
   by (simp add: bilbyFsMaxEbSize_def unat_arith_simps)

  have offs_pl_8_pl_name:
  "offs + 8 \<le> offs + 8 + wordarray_length (ObjDentry.name\<^sub>f (pObjDentry (take (unat end_offs) (\<alpha>wa (data\<^sub>f buf))) offs))"
   using wa_length_ObjDentry_name_le[where xs="take (unat end_offs) (\<alpha>wa (data\<^sub>f buf))" and ost=offs] rest offs_le_max
     less_to_le[OF offs_pl_8]
   by (simp add: wellformed_buf_def bilbyFsMaxEbSize_def unat_arith_simps)

  have pObjDentry_eq: 
  "pObjDentry (drop (unat st_offs) (take (unat end_offs) (\<alpha>wa (data\<^sub>f buf)))) (offs - st_offs) = pObjDentry (take (unat end_offs) (\<alpha>wa (data\<^sub>f buf))) offs"
      using rest offs_pl_8 by (fastforce intro: pObjDentry_drop_eq[symmetric,where end_offs=end_offs and offs=st_offs]
                                simp add: wellformed_buf_def word_le_nat_alt)
  
  from rest show ?case
  apply (subst mapAccumObsOpt_step, simp, simp)
  apply (clarsimp simp: Let_def split: LoopResult.split)
  apply (rule conjI)
   using loop_deserialise_ObjDentry_ret[OF wellformed_buf no_buf_overflow bound , 
    where dentry="ys ! frm" and  ex = ex and offs=offs]
   apply fastforce
  apply clarsimp
  apply (rename_tac elem ex' offs')
  apply (cut_tac 
            frm="Suc frm" and 
            ys= "ys[frm := elem]" and    
            ex =ex' and offs = offs' in IH[OF _ wellformed_buf no_buf_overflow bound], simp_all)
    apply(cut_tac loop_deserialise_ObjDentry_ret[OF wellformed_buf no_buf_overflow bound ,
          where dentry="ys ! frm" and  ex = ex and offs=offs and st_offs=st_offs], simp_all)
   apply(cut_tac loop_deserialise_ObjDentry_ret[OF wellformed_buf no_buf_overflow bound ,
      where dentry="ys ! frm" and  ex = ex and offs=offs and st_offs=st_offs], simp_all)
   apply clarsimp
   using  offs_pl_8_pl_name less_to_le[OF offs_pl_8]
   apply (fastforce simp add:  unat_plus_simple word_le_nat_alt)
  apply (clarsimp simp: Let_def)
  apply (rule conjI)
   apply fastforce
  apply (clarsimp simp: Let_def)
  apply (rename_tac ex'')
  apply (thin_tac "mapAccumObsOpt _ _ _ _ _ _ = _")
  apply(cut_tac loop_deserialise_ObjDentry_ret[OF wellformed_buf no_buf_overflow bound, 
      where dentry="ys ! frm" and  ex = ex and offs=offs], simp_all)

  apply (clarsimp simp: Let_def fst_fold_triple_simp fst_snd_fold_triple_simp prod.case_eq_if)
  apply (rule conjI)
   apply (simp add: upt_conv_Cons[where i = frm])
   apply (subst take_Suc_conv_app_nth, simp)
   apply (simp add: take_list_update prod.case_eq_if snd_fold_simp)
   apply (subst fst_fold_append_simp[where xs="[]", simplified, symmetric]) 
   apply fastforce

  apply (rule conjI)
   apply (simp add: snd_fold_simp)
    apply (case_tac "[frm..<unat to]")
     apply (fastforce+)
   apply (rename_tac l ls)
   apply (subgoal_tac "[Suc frm..<unat to] = ls")
    prefer 2
    apply (subst (asm) upt_rec[where i=frm], case_tac "frm = unat to"; fastforce)
   apply simp

  apply (rule conjI)
   apply (erule (2) dentarr_end_offs_list_induct_helper)

  apply (simp add: dentarr_offs_list_drop_end_offs_pred_def)
  apply clarsimp
  apply (rename_tac offs')
  apply (simp add:  snd_fold_simp)
  apply (case_tac "offs' = offs + 8 + wordarray_length (ObjDentry.name\<^sub>f (pObjDentry (take (unat end_offs) (\<alpha>wa (data\<^sub>f buf))) offs))")
   apply simp

  apply (simp add: dentarr_offs_list_drop_def)
  apply (subst (asm) split_upt_on_l_n[where l=frm and n=frm, simplified], fastforce)
  apply (simp add: Let_def)
  apply (subst (asm) snd_fold_append_simp[where xs="[_]"])
  apply (erule_tac x="offs' " in ballE, fastforce)
  apply (fastforce simp add: pObjDentry_eq)
  done
qed 

lemma replicate_simp:
  "replicate (unat to + 1 - unat to) (Option.None ()) = [Option.None ()]"
  by (simp add: unat_arith_simps)

lemma mapAccumObsOpt_loop_deserialise_ObjDentry_array_ret:
  assumes wellformed_buf: "wellformed_buf buf"
  assumes no_buf_overflow: "length (\<alpha>wa $ data\<^sub>f buf) \<le> unat bilbyFsMaxEbSize"
  assumes bound: "end_offs \<le> bound\<^sub>f buf"
  assumes off_less_end_offs: "offs  \<le> end_offs"
  assumes st_offs: "st_offs \<le> offs"
  shows
  "let data = take (unat end_offs) (\<alpha>wa (data\<^sub>f buf));
       arr_spec = pArrObjDentry data offs to in 
   (case mapAccumObsOpt 0 (unat to) loop_deserialise_ObjDentry 
      (replicate (unat to + 1) (Option.None ())) (ex, offs) (buf, end_offs) of
        LoopResult.Break (ys, d, ex) \<Rightarrow> 
         d \<in> {eInval, eNoMem}
      | LoopResult.Iterate (ys, ex, offs') \<Rightarrow> 
         (ys, ex, offs') = (\<alpha>a (prod.fst arr_spec), ex, prod.fst (prod.snd arr_spec)) \<and> 
         offs' \<le> end_offs \<and>
        dentarr_offs_list_end_offs_pred data offs [0..<unat to] end_offs \<and>
        dentarr_offs_list_drop_end_offs_pred data offs [0..<unat to] st_offs end_offs)"
  unfolding pArrObjDentry_def Let_def
  apply (clarsimp simp: array_make split: LoopResult.splits prod.splits)
  using mapAccumObsOpt_loop_deserialise_ObjDentry_ret[OF assms(1-4), simplified Let_def, 
       where frm=0 and to=to and ex=ex  and st_offs=st_offs and
       ys="replicate (unat to + 1)(Option.None ())", simplified take_0 drop_replicate replicate_simp]
   st_offs
  apply (clarsimp split: LoopResult.splits) 
  done

lemma array_map_loop_deserialise_ObjDentry_ret:
  assumes wellformed_buf: "wellformed_buf buf"
  assumes no_buf_overflow: "length (\<alpha>wa $ data\<^sub>f buf) \<le> unat bilbyFsMaxEbSize"
  assumes bound: "end_offs \<le> bound\<^sub>f buf"
  assumes off_less_end_offs: "offs  \<le> end_offs"
  assumes st_offs: "st_offs \<le> offs"
  shows "case array_map (ArrayMapP.make (ArrayT.make (replicate (unat to + 1) (Option.None ())))
                   0 to loop_deserialise_ObjDentry (ex, offs) (buf, end_offs)) of
         LoopResult.Break (arr, err, ex) \<Rightarrow> err \<in> {eInval, eNoMem}
       | LoopResult.Iterate (arr, ex', offs') \<Rightarrow>
                  let data = take (unat end_offs) (\<alpha>wa (data\<^sub>f buf));
                      (parr, poffs, poffslist) = pArrObjDentry data offs to;
                      ostlist = pArrObjDentry data offs to
                  in
                   arr = parr \<and> offs' = poffs \<and>
                  offs' \<le> end_offs \<and>
        dentarr_offs_list_end_offs_pred data offs [0..<unat to] end_offs \<and>
        dentarr_offs_list_drop_end_offs_pred data offs [0..<unat to] st_offs end_offs"
  apply (clarsimp simp: ArrayMapP.make_def array_make array_map_ret)
  using assms mapAccumObsOpt_loop_deserialise_ObjDentry_array_ret
  [unfolded Let_def, where to=to and buf=buf and ex=ex and offs=offs and end_offs=end_offs and st_offs=st_offs]
  by (clarsimp simp: array_make' Let_def split: LoopResult.splits)

lemma deserialise_Array_ObjDentry_ret:
  assumes wellformed_buf: "wellformed_buf buf"
  assumes no_buf_overflow: "length (\<alpha>wa $ data\<^sub>f buf) \<le> unat bilbyFsMaxEbSize"
  assumes bound: "end_offs \<le> bound\<^sub>f buf"
  assumes off_less_end_offs: "offs  \<le> end_offs"
  assumes st_offs: "st_offs \<le> offs"
  assumes offs_pl_8_no_of: "offs \<le> offs + 8"
  assumes offs_pl_8_le_end_offs: "offs + 8 \<le> end_offs"
  assumes err: "\<And>ex e. e \<in> {eInval, eNoMem} \<Longrightarrow> P (Error (e, ex))"
  assumes suc:
   "\<And>ex arr offs' offslist data.
    \<lbrakk> (arr, offs',offslist) = (pArrObjDentry (take (unat end_offs) (\<alpha>wa (data\<^sub>f buf))) offs nb_dentry);
       offs' \<le>  end_offs;
       data = take (unat end_offs) (\<alpha>wa (data\<^sub>f buf));
        dentarr_offs_list_end_offs_pred data offs [0..<unat nb_dentry] end_offs;
        dentarr_offs_list_drop_end_offs_pred data offs [0..<unat nb_dentry] st_offs end_offs \<rbrakk> \<Longrightarrow>
      P (Success (ex, arr, offs'))"
  shows "P (deserialise_Array_ObjDentry (ex, buf, offs, nb_dentry, end_offs))"
  unfolding deserialise_Array_ObjDentry_def[unfolded tuple_simps sanitizers]
  apply (simp add: Let_def)
  apply (rule array_create_ret)
   apply (simp add: err[unfolded eNoMem_def])
  apply (rename_tac ex' arr a)
  apply (subgoal_tac "unat nb_dentry + 1 = unat (nb_dentry+1) ")
   apply (clarsimp simp: prod.case_eq_if id_def Let_def split: LoopResult.splits)
   apply (subgoal_tac "a = ArrayT.make (replicate (unat (nb_dentry + 1)) (Option.None ()))", simp)
    apply (cut_tac ex=ex' in array_map_loop_deserialise_ObjDentry_ret[OF assms(1-5), where to = nb_dentry])
    apply (clarsimp simp: Let_def err split: LoopResult.splits)
    apply (rename_tac offslist a ex'' offs')
    apply (rule suc)
     apply simp+
   apply (metis array_make')
  apply unat_arith
 done

lemma word_add_diff_assoc:
 "(a::'a:: len0 word) + b - c = a + (b - c)"
 by simp

method offs_olen_of_solver =
  (((drule less_to_le)?, simp add: word_add_diff_assoc unat_plus_simple),
   (simp only: unat_arith_simps)?, simp? ; unat_arith)

lemma deserialise_ObjDentarr_ret:
  assumes wf: "wellformed_buf buf"
  assumes buf_len: "length (\<alpha>wa $ data\<^sub>f buf) \<le> unat bilbyFsMaxEbSize"
  assumes err: "\<And>ex e. e \<in> {eInval, eNoMem} \<Longrightarrow> P (Error (e, ex))"
  assumes offs_bound: "offs + olen - bilbyFsObjHeaderSize \<le> (bound\<^sub>f buf)"
  assumes offs_olen: "offs < offs + olen - bilbyFsObjHeaderSize"
  assumes olen: "bilbyFsObjHeaderSize + bilbyFsObjDentarrHeaderSize + bilbyFsObjDentryHeaderSize \<le> olen"
  assumes st_offs: "st_offs \<le> offs"
  assumes suc:
  "\<And>ex dentarr offs'. \<lbrakk>
  dentarr = pObjDentarr (\<alpha>wa (data\<^sub>f buf)) offs olen;
  offs' = pObjDentarrSize (\<alpha>wa (data\<^sub>f buf)) offs olen;
  let end_offs = offs + olen - bilbyFsObjHeaderSize;
  data = take (unat end_offs) (\<alpha>wa (data\<^sub>f buf));
  nb_dentry = ple32 (\<alpha>wa (data\<^sub>f buf)) (offs+8) in
  dentarr_offs_list_end_offs_pred data (offs+bilbyFsObjDentarrHeaderSize) [0..<unat nb_dentry] end_offs \<and>
  dentarr_offs_list_drop_end_offs_pred data (offs+bilbyFsObjDentarrHeaderSize) [0..<unat nb_dentry] st_offs end_offs;
  offs' \<le> offs + olen - bilbyFsObjHeaderSize
  \<rbrakk> \<Longrightarrow>
  P (Success (ex, dentarr, offs'))"
 notes bilbyFsObjDentarrHeaderSize_def[simp] bilbyFsObjHeaderSize_def[simp]
       bilbyFsObjDentryHeaderSize_def[simp]
  shows "P (deserialise_ObjDentarr (ex, buf, offs, olen))"
  proof -

  have offs_no_of: "offs < offs + bilbyFsObjDentarrHeaderSize"
    using olen and offs_olen by simp unat_arith

   have bound_max: "bound\<^sub>f buf \<le> bilbyFsMaxEbSize"
     using wf and buf_len by (simp add: wellformed_buf_def) unat_arith

   have offs_bound':  "offs < bilbyFsMaxEbSize"
     using offs_bound offs_olen bound_max offs_no_of by simp

   have offs_hdr_no_of: "offs < offs + bilbyFsObjDentarrHeaderSize"
     using offs_bound' by (simp add: bilbyFsMaxEbSize_def unat_arith_simps)

  have offs_pl_hdr_le_len: "unat offs + unat bilbyFsObjDentarrHeaderSize \<le> length (\<alpha>wa $ data\<^sub>f buf)"
   using offs_bound wf offs_no_of offs_olen olen
   by (simp add: wellformed_buf_def) unat_arith
  have deserialises:
    "deserialise_le32 (buf, offs + 8) = (ple32 (\<alpha>wa $ data\<^sub>f buf) (offs + 8))"
    "deserialise_le64 (buf, offs) = (ple64 (\<alpha>wa $ data\<^sub>f buf) offs)"
       using offs_pl_hdr_le_len apply (clarsimp simp:)
       apply (rule deserialise_le32_ret[simplified])
         using offs_hdr_no_of apply unat_arith
       using offs_hdr_no_of apply (simp add: unat_arith_simps)
       apply unat_arith

     using offs_pl_hdr_le_len apply (clarsimp)
     apply (rule deserialise_le64_ret[simplified])
    using offs_hdr_no_of  apply unat_arith
   using offs_hdr_no_of apply (simp add: unat_arith_simps)
   apply unat_arith
  done
  show ?thesis
  unfolding deserialise_ObjDentarr_def[unfolded tuple_simps sanitizers]
   apply (clarsimp simp: Let_def err[unfolded eInval_def])
   apply (subgoal_tac "\<exists>v. olen - bilbyFsObjHeaderSize = v \<and> bilbyFsObjDentarrHeaderSize + bilbyFsObjDentryHeaderSize \<le> v")
    apply (erule exE)
    apply (erule conjE)
    apply (rule deserialise_Array_ObjDentry_ret[OF assms(1,2), where st_offs=st_offs,
             simplified])
         using offs_bound apply simp
        subgoal using offs_olen olen by - offs_olen_of_solver
       subgoal for v
        using st_offs  offs_olen by - offs_olen_of_solver
      subgoal for v
       using offs_olen by - offs_olen_of_solver
     subgoal for v
      using offs_olen by (simp add: word_add_diff_assoc add.commute)
                         (rule word_plus_mono_right; simp)
    subgoal for v _ e by (fastforce intro: err)
   subgoal for v ex arr offs' offslist
    apply (case_tac "R.Success (ex, arr, offs')", simp_all)
    apply (clarsimp simp: Let_def err[unfolded eNoMem_def] split: R.split)
    apply (rule suc)
        subgoal
        apply (simp add: pObjDentarr_def Let_def)
        apply (subst ObjDentarr.surjective, simp add: ObjDentarr.make_def deserialises prod_eq_iff)
        done
       subgoal by (clarsimp simp add: prod_eq_iff pObjDentarrSize_def deserialises)
      subgoal by (simp add: Let_def deserialises)
     subgoal by simp
   done
  subgoal using olen by (simp) unat_arith
  done
qed

lemmas pObjUnion_def' = 
  pObjUnion_def[unfolded otype_simps, simplified]

lemmas len_otype_ok = is_len_and_type_ok_def[unfolded sanitizers tuple_simps]

lemma olen_bound_trivial:
 "   0x28 \<le> (olen::U32) \<Longrightarrow>
    offs + olen - 0x18 \<le> bound\<^sub>f buf \<Longrightarrow>
    offs \<le> offs + olen - 0x18 \<Longrightarrow> offs + 0x10 \<le> bound\<^sub>f buf"
  by unat_arith

lemma offs_trivial:
 "(offs::U32) \<le> offs + olen - 0x18 \<Longrightarrow>
    0x28 \<le> olen \<Longrightarrow>
    offs < offs + 0x10"
 by unat_arith

lemma unat_obj_len_minus_hdrsz:
  assumes len_otype_rel: "bilbyFsObjHeaderSize \<le> olen"
  assumes offs_no_of: "offs \<le> offs + olen - bilbyFsObjHeaderSize"
shows
 "unat (offs + olen - bilbyFsObjHeaderSize) = unat offs + unat olen - unat bilbyFsObjHeaderSize"
 using assms
 by (simp add: bilbyFsObjHeaderSize_def word_add_diff_assoc  unat_plus_simple) (simp add: unat_arith_simps)
 

lemma deserialise_ObjUnion_ret:
  assumes wf: "wellformed_buf buf"
  assumes no_buf_overflow: "length (\<alpha>wa $ data\<^sub>f buf) \<le> unat bilbyFsMaxEbSize"
  assumes bound: "offs + olen - bilbyFsObjHeaderSize \<le> bound\<^sub>f buf"
  assumes len_otype_rel: "is_len_and_type_ok (otype, olen)"
  assumes offs_no_of: "offs \<le> offs + olen - bilbyFsObjHeaderSize"
  assumes offs_no_underflow: "offs - bilbyFsObjHeaderSize \<le> offs"
  assumes err:
  "\<And>ex e. e \<in> {eInval, eNoMem} \<Longrightarrow> P (Error (e, ex))"
  assumes suc:
  "\<And>ex ounion offs'. ounion = pObjUnion (\<comment> \<open>take (unat (offs + olen))\<close> (\<alpha>wa (data\<^sub>f buf))) otype olen offs  \<Longrightarrow>
   offs' \<le> (offs + olen - bilbyFsObjHeaderSize) \<Longrightarrow>
  let end_offs = offs + olen - bilbyFsObjHeaderSize;
  data = take (unat end_offs) (\<alpha>wa (data\<^sub>f buf));
  nb_dentry = ple32 (\<alpha>wa (data\<^sub>f buf)) (offs+8) in
  dentarr_otype_end_offs_pred otype data offs end_offs \<and>
  dentarr_otype_drop_end_offs_st_pred otype data offs (offs - bilbyFsObjHeaderSize) end_offs 
  \<Longrightarrow>
   P (Success (ex, ounion, offs'))"
  notes suc_simps = len_otype_ok Let_def  pObjUnion_def' suc add.commute bilbyFsObjHeaderSize_def
          otype_simps dentarr_end_offs_simps  dentarr_drop_end_offs_simps
        shows "P (deserialise_ObjUnion (ex, buf, offs, (otype, olen)))"
  unfolding deserialise_ObjUnion_def[unfolded tuple_simps, simplified sanitizers]
  using is_len_and_type_ok_hdr_szD[OF len_otype_rel] 
  apply (clarsimp simp: Let_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule deserialise_ObjSuper_ret, simp)
      using len_otype_rel offs_no_of bound wf
      apply (simp add: len_otype_ok Let_def prod.case_eq_if wellformed_buf_def bilbyFsObjHeaderSize_def)
      apply unat_arith
     using len_otype_rel offs_no_of bound wf
     apply (simp add: len_otype_ok Let_def prod.case_eq_if wellformed_buf_def bilbyFsObjHeaderSize_def)
     apply unat_arith
    apply (simp add: err)

   using len_otype_rel
   apply (simp add: suc_simps)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (rule deserialise_ObjDel_ret, simp)
      using len_otype_rel offs_no_of bound wf
      apply (simp add: len_otype_ok Let_def prod.case_eq_if wellformed_buf_def bilbyFsObjHeaderSize_def)
      apply unat_arith
     apply (simp add: err)
      using len_otype_rel offs_no_of bound wf
      apply (simp add: len_otype_ok Let_def prod.case_eq_if wellformed_buf_def bilbyFsObjHeaderSize_def)
      apply unat_arith
   using len_otype_rel
   apply (simp add: suc_simps)

  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (rule deserialise_ObjDentarr_ret[OF wf no_buf_overflow, where st_offs ="offs - bilbyFsObjHeaderSize"])
        apply (simp add: err)
       using bound  offs_no_of len_otype_rel 
       apply (simp add: len_otype_ok Let_def prod.case_eq_if wellformed_buf_def bilbyFsObjHeaderSize_def)
      using offs_no_of len_otype_rel 
      apply (simp add: len_otype_ok bilbyFsObjHeaderSize_def )
      apply (simp add: word_add_diff_assoc unat_plus_simple word_less_nat_alt )
      apply unat_arith
     using  len_otype_rel
     apply (simp add: len_otype_ok bilbyFsObjHeaderSize_def bilbyFsObjDentryHeaderSize_def bilbyFsObjDentarrHeaderSize_def)
     using offs_no_underflow apply simp
   apply (simp add: suc pObjUnion_def' )
   apply (rule suc)
      apply (clarsimp simp add: pObjUnion_def')+
   apply (simp add: dentarr_otype_drop_end_offs_st_pred_def dentarr_otype_end_offs_pred_def dentarr_otype_drop_end_offs_pred_def
        bilbyFsObjTypeDentarr_def Let_def)
   apply clarsimp
   apply (subgoal_tac "ple32 (take (unat (offs + olen - bilbyFsObjHeaderSize)) (\<alpha>wa (data\<^sub>f buf))) (offs + 8) = ple32 (\<alpha>wa (data\<^sub>f buf)) (offs + 8)")
    apply simp
   apply (subgoal_tac "\<exists>v. olen - bilbyFsObjHeaderSize = v")
    apply (erule exE)
    apply (subst ple32_take)
(* <automate?> *)
      using len_otype_rel 
      apply (simp add: len_otype_ok bilbyFsObjHeaderSize_def)
      using offs_no_of apply (simp add: word_add_diff_assoc  bilbyFsObjHeaderSize_def)
      apply (simp add: word_add_diff_assoc unat_plus_simple word_less_nat_alt word_le_nat_alt add.commute)
      apply (subst (asm) add.commute)
      using offs_no_of apply (simp add: bilbyFsObjHeaderSize_def) apply (simp add: word_add_diff_assoc word_le_nat_alt)
      apply (simp only: unat_arith_simps)
      apply unat_arith
    apply (simp add: bilbyFsObjHeaderSize_def word_add_diff_assoc)
     using offs_no_of 
     apply (simp add: bilbyFsObjHeaderSize_def word_add_diff_assoc word_less_nat_alt  add.commute)
     apply (subst (asm) add.commute, simp add: unat_plus_simple)
     using offs_no_of apply (simp add: bilbyFsObjHeaderSize_def)
     apply (simp add: word_add_diff_assoc)
     using len_otype_rel
      apply (simp add: len_otype_ok)
     apply (subgoal_tac "offs \<le> offs + 0xC")
      apply (simp add: unat_plus_simple add.commute, simp only: word_le_nat_alt)
      apply unat_arith
     apply (simp add: unat_plus_simple add.commute, simp only: word_le_nat_alt)
     apply unat_arith
(* </automate?> *)
    apply simp
   apply (fastforce)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (rule deserialise_ObjData_ret[OF ])
       using offs_no_of 
       apply (simp only: diff_conv_add_uminus)
       apply (simp only: add.assoc)
      using bound wf offs_no_of apply (simp add: bilbyFsObjHeaderSize_def
        wellformed_buf_def diff_conv_add_uminus add.assoc)
      apply unat_arith
     using len_otype_rel   apply (simp add: otype_simps)
    apply (simp add: err)
   apply simp
   apply (simp add: suc_simps)

  apply (clarsimp)
  apply (rule conjI)
   apply clarsimp
   apply (rule deserialise_ObjInode_ret)
      using len_otype_rel offs_no_of bound
         bound wf offs_no_of
       apply (simp add: bilbyFsObjHeaderSize_def wellformed_buf_def )
     using len_otype_rel  apply (simp add: otype_simps len_otype_ok)
       apply unat_arith
     using len_otype_rel  apply (simp add: otype_simps len_otype_ok)
       using  offs_no_of
       apply (simp add: bilbyFsObjHeaderSize_def)
       apply unat_arith
     apply (simp add: err)
     using len_otype_rel  apply (simp add: otype_simps len_otype_ok)
    apply (simp add: suc_simps)
  apply clarsimp
  apply (rule deserialise_ObjPad_ret)
   apply (simp add:err)  
  apply (simp add: suc_simps add_diff_eq)+
 done

lemma pObjDel_take:
 "is_valid_ObjHeader (pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs) (bounded buf) \<Longrightarrow>
       offs + Obj.len\<^sub>f obj \<le> bound\<^sub>f buf \<Longrightarrow>
       is_len_and_type_ok (otype\<^sub>f obj, Obj.len\<^sub>f obj) \<Longrightarrow>
       offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
       otype\<^sub>f obj = 3 \<Longrightarrow>
       \<exists>v. obj\<lparr>ounion\<^sub>f := v\<rparr> = pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs \<Longrightarrow>
   pObjDel (\<alpha>wa (data\<^sub>f buf)) (offs + bilbyFsObjHeaderSize) =
      pObjDel (take (unat (offs + Obj.len\<^sub>f obj)) (\<alpha>wa (data\<^sub>f buf))) (offs + bilbyFsObjHeaderSize)"
  apply (simp add: pObjDel_def)
  apply (frule is_valid_ObjHeader_buf_len, clarify)
  apply (subst ple64_take, (simp add: otype_simps len_otype_ok bilbyFsObjHeaderSize_def, unat_arith)+)
  apply simp
done

lemma pObjSuper_take:
 "is_valid_ObjHeader (pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs) (bounded buf) \<Longrightarrow>
       offs + Obj.len\<^sub>f obj \<le> bound\<^sub>f buf \<Longrightarrow>
       is_len_and_type_ok (otype\<^sub>f obj, Obj.len\<^sub>f obj) \<Longrightarrow>
       offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
       otype\<^sub>f obj = 4 \<Longrightarrow>
       \<exists>v. obj\<lparr>ounion\<^sub>f := v\<rparr> = pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs \<Longrightarrow>
    pObjSuper (\<alpha>wa (data\<^sub>f buf)) (offs + bilbyFsObjHeaderSize) =
     pObjSuper (take (unat (offs + Obj.len\<^sub>f obj)) (\<alpha>wa (data\<^sub>f buf))) (offs + bilbyFsObjHeaderSize)"
  apply (simp add: pObjSuper_def)
  apply (frule is_valid_ObjHeader_buf_len, clarify)
  apply (subst ple64_take, ((simp add: otype_simps len_otype_ok bilbyFsObjHeaderSize_def, unat_arith)+)[2])
  apply (subst ple32_take, ((simp add: otype_simps len_otype_ok bilbyFsObjHeaderSize_def, unat_arith)+)[2])+
  apply simp
 done

lemma pObjInode_take:
 "is_valid_ObjHeader (pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs) (bounded buf) \<Longrightarrow>
       offs + Obj.len\<^sub>f obj \<le> bound\<^sub>f buf \<Longrightarrow>
       is_len_and_type_ok (otype\<^sub>f obj, Obj.len\<^sub>f obj) \<Longrightarrow>
       offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
       otype\<^sub>f obj = 0 \<Longrightarrow>
       \<exists>v. obj\<lparr>ounion\<^sub>f := v\<rparr> = pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs \<Longrightarrow>
    pObjInode (\<alpha>wa (data\<^sub>f buf)) (offs + bilbyFsObjHeaderSize) =
     pObjInode (take (unat (offs + Obj.len\<^sub>f obj)) (\<alpha>wa (data\<^sub>f buf))) (offs + bilbyFsObjHeaderSize)"
  apply (simp add: pObjInode_def)
  apply (frule is_valid_ObjHeader_buf_len, clarify)
  apply (subst ple64_take, ((simp add: otype_simps len_otype_ok bilbyFsObjHeaderSize_def, unat_arith)+)[2])+
  apply (subst ple32_take, ((simp add: otype_simps len_otype_ok bilbyFsObjHeaderSize_def, unat_arith)+)[2])+
  apply simp
 done

lemma pObjDentarr_take:
 "is_valid_ObjHeader (pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs) (bounded buf) \<Longrightarrow>
       offs + Obj.len\<^sub>f obj \<le> bound\<^sub>f buf \<Longrightarrow>
       is_len_and_type_ok (otype\<^sub>f obj, Obj.len\<^sub>f obj) \<Longrightarrow>
       offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
       otype\<^sub>f obj = 2 \<Longrightarrow>
       \<exists>v. obj\<lparr>ounion\<^sub>f := v\<rparr> = pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs \<Longrightarrow>
    pObjDentarr (\<alpha>wa (data\<^sub>f buf)) (offs + bilbyFsObjHeaderSize) (Obj.len\<^sub>f obj) =
     pObjDentarr (take (unat (offs + Obj.len\<^sub>f obj)) (\<alpha>wa (data\<^sub>f buf))) (offs + bilbyFsObjHeaderSize) (Obj.len\<^sub>f obj)"
  apply (simp add: pObjDentarr_def)
  apply (frule is_valid_ObjHeader_buf_len, clarify)
  apply (subst ple64_take, ((simp add: otype_simps len_otype_ok bilbyFsObjHeaderSize_def, unat_arith)+)[2])+
  apply (subst ple32_take, ((simp add: otype_simps len_otype_ok bilbyFsObjHeaderSize_def, unat_arith)+)[2])+
  apply (simp add: Let_def) 
 done


lemma pObjData_take:
"is_valid_ObjHeader (pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs) (bounded buf) \<Longrightarrow>
       offs + Obj.len\<^sub>f obj \<le> bound\<^sub>f buf \<Longrightarrow>
       is_len_and_type_ok (otype\<^sub>f obj, Obj.len\<^sub>f obj) \<Longrightarrow>
       offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
       otype\<^sub>f obj = 1 \<Longrightarrow>
       \<exists>v. obj\<lparr>ounion\<^sub>f := v\<rparr> = pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs \<Longrightarrow>
pObjData (\<alpha>wa (data\<^sub>f buf)) (offs + bilbyFsObjHeaderSize) (Obj.len\<^sub>f obj) =
    pObjData (take (unat (offs + Obj.len\<^sub>f obj)) (\<alpha>wa (data\<^sub>f buf))) (offs + bilbyFsObjHeaderSize)
     (Obj.len\<^sub>f obj)"
   apply (simp add: pObjData_def)
  apply (subst ple64_take, ((simp add: otype_simps len_otype_ok bilbyFsObjHeaderSize_def, unat_arith)+)[2])+
    apply (simp add: otype_simps len_otype_ok)
    apply (subst slice_take)
      apply (frule is_valid_ObjHeader_len)
      apply (subgoal_tac " unat (Obj.len\<^sub>f obj - bilbyFsObjHeaderSize - bilbyFsObjDataHeaderSize) =  unat (Obj.len\<^sub>f obj) - unat bilbyFsObjHeaderSize - unat bilbyFsObjDataHeaderSize")
       apply (subgoal_tac "unat (offs + Obj.len\<^sub>f obj) = unat offs + unat ( Obj.len\<^sub>f obj)")
         apply simp
         apply (simp add: bilbyFsObjHeaderSize_def bilbyFsObjDataHeaderSize_def)
         apply unat_arith
        apply (simp add: word_less_nat_alt unat_plus_simple[symmetric], unat_arith)
      apply (subst unat_sub, simp add: bilbyFsObjHeaderSize_def bilbyFsObjDataHeaderSize_def, unat_arith)+
    apply simp+
 done

lemma pObjUnion_take:
 "is_valid_ObjHeader (pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs) (bounded buf) \<Longrightarrow>
       offs + Obj.len\<^sub>f obj \<le> bound\<^sub>f buf \<Longrightarrow>
       is_len_and_type_ok (otype\<^sub>f obj, Obj.len\<^sub>f obj) \<Longrightarrow>
       offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
       \<exists>v. obj\<lparr>ounion\<^sub>f := v\<rparr> = pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs \<Longrightarrow>
      pObjUnion (\<alpha>wa (data\<^sub>f buf)) (otype\<^sub>f obj) (Obj.len\<^sub>f obj) (offs + bilbyFsObjHeaderSize) = 
      pObjUnion (take (unat (offs + Obj.len\<^sub>f obj)) (\<alpha>wa (data\<^sub>f buf))) (otype\<^sub>f obj) (Obj.len\<^sub>f obj) (offs + bilbyFsObjHeaderSize)"
  apply (simp add: pObjUnion_def')
  apply (case_tac "otype\<^sub>f obj = 0")
   apply (simp add: pObjInode_take)
  apply (case_tac "otype\<^sub>f obj = 1")
   apply (simp add: pObjData_take)
  apply (case_tac "otype\<^sub>f obj = 2")
   apply (simp add: pObjDentarr_take)
  apply (case_tac "otype\<^sub>f obj = 3")
   apply (simp add: pObjDel_take)
  apply (case_tac "otype\<^sub>f obj = 4")
   apply (simp add: pObjSuper_take)
  apply simp
 done

lemmas Obj_ext_eq_expand = trans[OF _ Obj.ext_inject,
    OF arg_cong2[where f="(=)"], OF refl Obj.surjective]

lemma deserialise_Obj_ret:
  assumes wf: "wellformed_buf buf"
  assumes buf_len: "length (\<alpha>wa $ data\<^sub>f buf) \<le> unat bilbyFsMaxEbSize"
  assumes bound: "offs + bilbyFsObjHeaderSize \<le> bound\<^sub>f buf"
  assumes no_of: "offs < offs + bilbyFsObjHeaderSize"
  assumes err: "\<And>ex e. e \<in> {eInval, eNoMem} \<Longrightarrow> P (Error (e, ex))"
  assumes suc:
   "\<And>ex obj offs'. \<lbrakk> 
    is_valid_ObjHeader (pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs) (\<alpha>wa (data\<^sub>f buf)) ;

    let end_offs = offs + (Obj.len\<^sub>f obj);
    data = take (unat end_offs) (\<alpha>wa (data\<^sub>f buf));
    nb_dentry = ple32 (\<alpha>wa (data\<^sub>f buf)) (offs+8) in
    dentarr_otype_end_offs_pred (Obj.otype\<^sub>f obj) data (offs + bilbyFsObjHeaderSize) end_offs \<and>
    dentarr_otype_drop_end_offs_st_pred (Obj.otype\<^sub>f obj) data (offs + bilbyFsObjHeaderSize) offs end_offs;
    obj = pObj (\<alpha>wa (data\<^sub>f buf)) offs;
    offs' \<le> offs + Obj.len\<^sub>f obj \<rbrakk> \<Longrightarrow> 

   P (Success (ex, obj, offs'))"
  notes bilbyFsObjHeaderSize_def[simp]
  shows "P (deserialise_Obj (ex, buf, offs))"
  unfolding deserialise_Obj_def[unfolded tuple_simps sanitizers]
  apply (clarsimp simp: err eNoMem_def split: R.split)
  apply (rule deserialise_ObjHeader_ret[OF wf bound no_of])
   apply (simp add: err)
  apply simp
  apply (rule deserialise_ObjUnion_ret[OF wf buf_len])
      apply (simp)
     apply (clarsimp, drule sym[where t="pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs"])
     apply (clarsimp simp  add: is_valid_ObjHeader_def)
    apply simp
    apply (drule is_valid_ObjHeader_len)
    apply (clarsimp, drule sym[where t="pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs"])
    apply (drule arg_cong[where f=Obj.len\<^sub>f])
    using no_of bound
    apply simp
    apply  (simp only: word_le_nat_alt plus_no_overflow_unat_lift)
   apply (drule is_valid_ObjHeader_len)
    apply (clarsimp, drule sym[where t="pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs"])
    apply (drule arg_cong[where f=Obj.len\<^sub>f])
   apply (clarsimp simp add: )
   apply unat_arith
   apply (simp add: err)

  apply simp
  apply (rule suc)
       apply (clarsimp simp add: is_valid_ObjHeader_def bounded_def)
      apply simp
   apply (clarsimp simp add: pObj_def Let_def)
   apply (drule sym[where t="pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs"])
   apply (subst pObjUnion_take[simplified], (fastforce simp add: is_valid_ObjHeader_def)+)
   apply (rename_tac obj offs' v)
   apply (subgoal_tac "pObjUnion (take (unat (offs + Obj.len\<^sub>f obj)) (\<alpha>wa (data\<^sub>f buf))) (otype\<^sub>f obj)
              (Obj.len\<^sub>f obj) (offs + 0x18) = pObjUnion
           (take (unat offs + unat (Obj.len\<^sub>f (pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs))) (\<alpha>wa (data\<^sub>f buf)))
           (otype\<^sub>f (pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs))
           (Obj.len\<^sub>f (pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs)) (offs + 0x18)")
    apply simp
   apply (case_tac "pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs", case_tac obj, simp)
   apply (case_tac "pObjHeader (\<alpha>wa (data\<^sub>f buf)) offs", case_tac obj, simp)
   apply (simp add: plus_no_overflow_unat_lift)+
 done

lemma pObjHeader_take:
 "is_valid_ObjHeader (pObjHeader xs (ObjAddr.offs\<^sub>f oaddr)) xs \<Longrightarrow>
is_obj_addr_consistent (pObj (take (unat (ObjAddr.offs\<^sub>f oaddr) + unat (ObjAddr.len\<^sub>f oaddr)) xs)
          (ObjAddr.offs\<^sub>f oaddr)) oaddr \<Longrightarrow>
  ObjAddr.offs\<^sub>f oaddr < ObjAddr.offs\<^sub>f oaddr + bilbyFsObjHeaderSize \<Longrightarrow>
  bilbyFsObjHeaderSize \<le> ObjAddr.len\<^sub>f oaddr \<Longrightarrow>
   pObjHeader xs (ObjAddr.offs\<^sub>f oaddr) = pObjHeader (take (unat (ObjAddr.offs\<^sub>f oaddr) + unat (ObjAddr.len\<^sub>f oaddr)) xs) (ObjAddr.offs\<^sub>f oaddr)"

  apply (simp add: pObjHeader_def)
  apply (subst ple32_take, ((simp add: bilbyFsObjHeaderSize_def, unat_arith, fastforce? )[2])+)+
  apply (subst ple64_take, ((simp add: bilbyFsObjHeaderSize_def, unat_arith, fastforce? )[2])+)+
  apply (subst nth_take,   (simp add: bilbyFsObjHeaderSize_def, unat_arith))+
  apply (rule refl)
done

end


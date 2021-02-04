(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory WordArrayT
imports
  "../adt/BilbyT"
  "../lib/Loops"
  "../adt/WordArray_Shallow"
begin

definition \<alpha>wa :: "'a WordArray \<Rightarrow> 'a list"
  where
"\<alpha>wa wa = wa"

definition make :: "'a list \<Rightarrow> 'a WordArray"
  where
"make xs = xs"

definition
  mapAccumObs :: "nat \<Rightarrow> nat \<Rightarrow> (('a, 'acc, 'obsv) ElemAO \<Rightarrow> ('a \<times> 'acc))
   \<Rightarrow> 'a list \<Rightarrow> 'acc \<Rightarrow> 'obsv \<Rightarrow> 'a list \<times> 'acc"
where
  "mapAccumObs frm to fn xs vacc obs =
   (let (ys, acc) = fold (\<lambda>elem (ys,acc).
           let (elem,acc) = fn (ElemAO.make elem acc obs)
            in  (ys@[elem], acc)) (slice frm to xs) ([],vacc)
     in (take frm xs @ ys @ List.drop (max frm to) xs, acc))"

lemma length_mapAccum_helper:
  "length (fst $ fold (\<lambda>x (ys,a'). let  (elem, acc) = loopbody x a'
                                  in  (ys@[elem],acc)) (xs) (ys,a)
           )
         = length ys + length xs"
  by (induct xs arbitrary: a ys, auto simp: Let_def slice_def  split: prod.split)

lemma length_mapAccum_slice_helper:
  "length (let (xs', _) = fold (\<lambda>x (ys,a'). let  (elem, acc) = loopbody x a'
                                  in  (ys@[elem],acc)) (slice frm to xs) (ys,a)
           in xs') = length ys + length (slice frm to xs)"
proof -
  have f1: "(\<lambda>x (ys, a'). (ys @ [TypBucket.fst (loopbody x a')], TypBucket.snd (loopbody x a'))) =
            (\<lambda>x prod. (TypBucket.fst prod @ [TypBucket.fst (loopbody x (TypBucket.snd prod))], TypBucket.snd (loopbody x (TypBucket.snd prod))))"
    using split_beta by blast
  show ?thesis
    apply simp
    apply (simp only: Let_def prod.case_eq_if)
    using length_mapAccum_helper[unfolded fun_app_def prod.case_eq_if Let_def]
    apply (force simp add: f1)
    done
qed

lemma slice_length:
 "length (slice frm to xs) = min (to - frm) (length xs - frm)"
 by (simp add: slice_def)

lemma length_mapAccum_slice_helper':
  "length (take frm xs @ fst (let (xs', acc) = fold (\<lambda>x (ys,a'). let  (elem, acc) = loopbody x a'
                                  in  (ys@[elem],acc)) (slice frm to xs) (ys,a)
           in (xs',acc))  @ List.drop (max frm to) xs) = length ys + length xs"
  unfolding Let_def  prod.case_eq_if
  using length_mapAccum_slice_helper[unfolded prod.case_eq_if Let_def, where xs=xs and ys=ys and frm=frm and to=to and loopbody=loopbody and a=a]
  by (simp add: slice_length)

lemma length_mapAccum:
  "length (fst (mapAccumObs frm to fn xs a obs)) = length xs"
  unfolding mapAccumObs_def
  using length_mapAccum_slice_helper'[where frm=frm and to=to and xs=xs and a=a and ys="[]"]
  by (auto simp: Let_def prod.case_eq_if)


lemma length_mapAccumI:
  "P (length xs) \<Longrightarrow> P (length (fst (mapAccumObs frm to fn xs a obs)))"
  by (simp add : length_mapAccum)

lemma wordarray_make:
  "\<And>xs. \<alpha>wa (WordArrayT.make xs) = xs"
  by (simp add: \<alpha>wa_def WordArrayT.make_def)

lemma wordarray_make':
  "\<And>wa. WordArrayT.make (\<alpha>wa wa) = wa"
  by (simp add: \<alpha>wa_def WordArrayT.make_def)

lemma wordarray_get_ret:
  "\<lbrakk> unat index < length (\<alpha>wa arr) \<rbrakk> \<Longrightarrow>
    wordarray_get (arr, index) = \<alpha>wa arr ! unat index"
  by (simp add: wordarray_get' \<alpha>wa_def)

lemma mapAccum_fold_helper:
  "fold (\<lambda>a (ys, b). case f (ElemAO.make a b obs) of (a', b') \<Rightarrow> (ys @ [a'], b')) xs ([], acc)
    = mapAccum (\<lambda>a b. f (ElemAO.make a b obs)) xs acc"
  apply (induct arbitrary: acc rule: rev_induct)
   apply clarsimp
  apply (clarsimp simp: mapAccum_step split: prod.splits)
  done

lemma wordarray_map_no_break_ret:
  "\<And>P. (let (aarr, vacc) = mapAccumObs (unat frm) (unat to) body (\<alpha>wa arr) acc obs
          in P ((WordArrayT.make aarr), vacc)) 
   \<Longrightarrow> P (wordarray_map_no_break (ArrayMapP.make arr frm to body acc obs))"
  apply (unfold mapAccumObs_def wordarray_map_no_break')
  apply clarsimp
  apply (clarsimp split: prod.splits)
  apply (rename_tac vacc xs xs' vacc')
  apply (rule conjI; clarsimp simp: ArrayMapP.make_def \<alpha>wa_def WordArrayT.make_def)
  apply (clarsimp simp: mapAccum_fold_helper word_le_nat_alt max_def)
  apply (clarsimp simp: slice_def not_le word_less_nat_alt max_def)
  done

axiomatization
where
  wordarray_create_ret:
   "\<And>P.\<lbrakk>  \<And>ex'. (ex', Option.None ()) = malloc ex \<Longrightarrow> P (Error ex');
           \<And>ex' v. \<lbrakk> sz > 0 ; (ex', Option.Some v) = malloc ex; length (\<alpha>wa v) = unat sz \<rbrakk> \<Longrightarrow>
                 P (Success (ex', v))
        \<rbrakk> \<Longrightarrow>
      P (wordarray_create (ex, sz))"
  and wordarray_modify_ret:
   "\<And>P. \<lbrakk> unat index < List.length (\<alpha>wa varr);
       let r = modifier (ElemAO.make ((\<alpha>wa varr)!unat index) vacc obs) in
       P (ArrA.make (WordArrayT.make ((\<alpha>wa varr)[(unat index) := (ElemA.elem\<^sub>f r)])) (ElemA.acc\<^sub>f r)) \<rbrakk> \<Longrightarrow>
        P (wordarray_modify (ArrayUseValueP.make varr index modifier vacc obs))"
  and wordarray_cmp_ret:
  "\<And>P. P(\<alpha>wa a1 = \<alpha>wa a2) \<Longrightarrow> P (wordarray_cmp(a1, a2))"
  and wordarray_set_ret:
  "(offs::U32) \<le> offs + len \<Longrightarrow>
   wordarray_set (wa, offs, len, (v::U8)) =
   WordArrayT.make ((take (unat offs) (\<alpha>wa wa) @
                   replicate (unat len) v @ List.drop (unat (offs + len)) (\<alpha>wa wa)))"

  and wordarray_copy_ret:
  "\<And>P. \<lbrakk>  length (\<alpha>wa dst) = length (\<alpha>wa src) \<Longrightarrow>
                  offs = src_offs \<Longrightarrow>
                  offs \<le> offs + len \<Longrightarrow>
                  unat (offs + len) \<le> length (\<alpha>wa src) \<Longrightarrow>
         P (WordArrayT.make (take (unat offs) (\<alpha>wa dst) @ slice (unat offs) (unat offs + unat len) (\<alpha>wa src) @ List.drop (unat (offs+len)) (\<alpha>wa dst))) \<rbrakk>
     \<Longrightarrow>
      P (wordarray_copy(dst, src, offs, src_offs, len))"

lemma wordarray_\<alpha>wa_eq:
  "\<And>xs ys. (xs = ys) \<longleftrightarrow> \<alpha>wa xs = \<alpha>wa ys"
  apply (rule iffI)
   apply (erule arg_cong[where f=\<alpha>wa])
   apply (drule_tac x="\<alpha>wa xs" and y="\<alpha>wa ys" in arg_cong[where f=WordArrayT.make])
  apply (simp add: wordarray_make')
done

lemma ElemA_ext_inject_plus:
  "(\<lparr>ElemA.elem\<^sub>f = a, ElemA.acc\<^sub>f = b\<rparr> = v) = (ElemA.elem\<^sub>f v = a \<and> ElemA.acc\<^sub>f v = b)"
  by (case_tac v, auto)

lemma wordarray_modify_length':
  "\<And>index modifier vacc obs wa. unat index < length (\<alpha>wa wa) \<Longrightarrow>
   (length $ \<alpha>wa $ ArrA.arr\<^sub>f $ wordarray_modify (ArrayUseValueP.make wa index modifier vacc obs)) = (length $ \<alpha>wa $ wa)"
  by (fastforce intro: wordarray_modify_ret
                 simp: ArrA.make_def wordarray_make ElemA_ext_inject_plus
                       ElemA.make_def ElemAO.make_def)+

lemma wordarray_modify_length:
  "\<And>index modifier vacc obs wa. unat index < length (\<alpha>wa wa) \<Longrightarrow>
  P (length $ \<alpha>wa $ wa) \<Longrightarrow>
   P(length (\<alpha>wa (ArrA.arr\<^sub>f ( wordarray_modify (ArrayUseValueP.make wa index modifier vacc obs)))))"
   by (fastforce simp: wordarray_modify_length'[simplified])

lemma wordarray_get_ret':
  "\<lbrakk> unat index < length (\<alpha>wa arr); P (\<alpha>wa arr ! unat index) \<rbrakk> \<Longrightarrow>
    P (wordarray_get (arr, index))"
    using wordarray_get_ret by fastforce

lemma wordarray_length_ofnat:
  "unat (wordarray_length wa) = length (\<alpha>wa wa) \<Longrightarrow>
  wordarray_length wa = of_nat (length (\<alpha>wa wa))"
  by (drule sym, simp)

lemma wordarray_length_ofnat':
  "wordarray_length wa = of_nat (length (\<alpha>wa wa))"
  by (simp add: wordarray_length' \<alpha>wa_def)

lemma length_eq_imp_wordarray_length_eq:
  "length (\<alpha>wa xs) = length (\<alpha>wa ys) 
    \<Longrightarrow> wordarray_length xs = wordarray_length ys"
  by (simp add: wordarray_length' \<alpha>wa_def)

lemma wordarray_length_ret':
  "length (\<alpha>wa wa) \<le> unat (max_word :: 32 word) \<Longrightarrow> unat (wordarray_length wa) = length (\<alpha>wa wa)"
  apply (simp add: wordarray_length' \<alpha>wa_def)
  apply (rule unat_of_nat_eq)
  apply (clarsimp simp: max_word_def)
  done

lemma wordarray_length_leq_length:
  "unat (wordarray_length wa) \<le> length (\<alpha>wa wa)"
  apply (simp add: wordarray_length' \<alpha>wa_def)
  by (metis (mono_tags, hide_lams) le_cases le_unat_uoi)

lemmas wordarray_make_rev = wordarray_make'

end



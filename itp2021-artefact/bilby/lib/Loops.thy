(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Loops
imports "../adt/BilbyT"
begin

(*
lemma mapAccum_x_inv_wp:
  assumes x: "\<And>s. I s \<Longrightarrow> Q s"
  assumes y: "\<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>P\<rbrace> m x \<lbrace>\<lambda>rv. I\<rbrace>"
  assumes z: "\<And>s. I s \<Longrightarrow> P s"
  shows      "I a \<longrightarrow> (case mapAccum f xs a of (xs',a') \<Rightarrow> Q a')"
  apply (rule hoare_post_imp)
   apply (erule x)
  apply (rule mapM_x_wp)
   apply (rule hoare_pre_imp [OF _ y])
    apply (erule z)
   apply assumption
  apply simp
  done
 *)


definition 
  seq32_no_break :: "(U32 \<times> U32 \<times> U32 \<times> (('acc \<times> 'obs \<times> U32) \<Rightarrow> 'acc) \<times> 'acc \<times> 'obs) \<Rightarrow> 'acc"
where
 "seq32_no_break \<equiv> (\<lambda>(begin,end,inc,body,acc,obs).
   fold (\<lambda>n acc. body(acc, obs, n)) (if end >  0 then [begin,begin+inc .e. end - 1] else []) acc)"
     
fun arr_iteratei
  :: "nat \<Rightarrow> 'x list \<Rightarrow> ('\<sigma> \<Rightarrow>bool) \<Rightarrow> ('x \<Rightarrow> '\<sigma> \<Rightarrow> 'ob \<Rightarrow> '\<sigma>) \<Rightarrow> '\<sigma> \<Rightarrow> 'ob \<Rightarrow> '\<sigma>"
where
  "arr_iteratei i l c f \<sigma> obs = (
    if i=0 \<or> \<not> c \<sigma> then \<sigma>
    else arr_iteratei (i - 1) l c f (f (l ! (length l-i)) \<sigma> obs) obs
  )"
declare arr_iteratei.simps[simp del]  (* This is required to prevent infinite unfolding of arr_iteratei *)

lemma "arr_iteratei 2 [(1::nat)] (\<lambda>_. True) (\<lambda>x s _. s + x) 0 undefined = 2"
  apply(simp add: arr_iteratei.simps)
  done

lemma "arr_iteratei 1 [(1::nat),3] (\<lambda>_. True) (\<lambda>x s _. s + x) 0 undefined = 3"
  apply(simp add: arr_iteratei.simps)
  done

end

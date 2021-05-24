(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory TypBucket
  imports Main
      "BilbyFsConsts.BilbyFs_Shallow_Desugar_Tuples"
      "BilbyFsConsts.BilbyFs_ShallowConsts_Desugar_Tuples"
begin

text {* Override Cogent defined constructors so that 
  default Some and None are the option ones.
 *}
abbreviation Some :: "'a \<Rightarrow> 'a option" where "Some \<equiv> option.Some"
abbreviation None :: "'a option" where "None \<equiv> option.None"

abbreviation fst :: "'a \<times> 'b \<Rightarrow> 'a" where "fst \<equiv> Product_Type.fst"
abbreviation snd :: "'a \<times> 'b \<Rightarrow> 'b" where "snd \<equiv> Product_Type.snd"

(*
(* Should this be in a locale so it can be instantiated? *)
axiomatization
  select :: "('h \<times> 'a set) \<Rightarrow> ('h \<times> 'a)"
where
  select_in: "S \<noteq> {} \<Longrightarrow> snd (select (h,S)) \<in> S"
*)

fun select :: "'h \<times> 'a set \<Rightarrow> 'h \<times> 'a" where
  "select (h, S) = (h, (SOME x. x \<in> S))"

lemma select_in:
  "S \<noteq> {} \<Longrightarrow> (snd (select (h, S))) \<in> S"
  by (simp add: some_in_eq)

lemma select_in':
  "select (h,S) = (x,y) \<Longrightarrow> S \<noteq> {} \<Longrightarrow> y \<in> S"
  by (metis select_in snd_conv)

lemma select_in_val:
 "\<lbrakk> \<forall>v\<in>S. P v; S \<noteq> {} \<rbrakk>  \<Longrightarrow>  P(snd (select (h, S)))"
 using select_in by metis

lemma prod_split_asmE: 
  "\<lbrakk> (a,b) = x; P (fst x) (snd x) \<rbrakk> \<Longrightarrow> P a b"
  by (clarsimp split: prod.split)

lemma prod_eq: 
  "\<lbrakk> a = fst x ; b = snd x \<rbrakk> \<Longrightarrow> x = (a,b)"
  by simp


consts malloc :: "SysState \<Rightarrow> (SysState \<times> 'a Option\<^sub>T)"
       free :: "'a \<Rightarrow> SysState \<Rightarrow> SysState"

type_synonym U8 = "8 word"
type_synonym U16 = "16 word"
type_synonym U32 = "32 word"
type_synonym U64 = "64 word"

text {* Add associativity simp rules for bit word operations *}
lemmas word_assocs[simp] = word_bw_assocs

type_synonym ErrCode = U32
lemmas error_code_simps = eNoEnt_def eNoMem_def eInval_def eAgain_def eNFile_def
   eNotEmpty_def eIO_def eNameTooLong_def eNoSpc_def eOverflow_def  eRoFs_def
      eBadF_def
type_synonym Ino = U32
type_synonym Mode = U32
type_synonym SizeT = U64
type_synonym TimeT = U64
type_synonym Addr = U32

definition "DOT = 0x2E"
definition "NUL = 0x00"

lemmas sanitizers = 
  Let\<^sub>d\<^sub>s_def
  R.simps
  LoopResult.simps

lemmas [simp] = Px_px take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def

end
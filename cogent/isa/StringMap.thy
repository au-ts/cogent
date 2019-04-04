(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory StringMap
  imports CParser.StaticFun
begin 

datatype LexOrdChar = LexOrdChar char

instantiation LexOrdChar :: linorder begin

definition less_eq_LexOrdChar :: "LexOrdChar \<Rightarrow> LexOrdChar \<Rightarrow> bool" where
  "c \<le> c' \<equiv> case c of LexOrdChar c \<Rightarrow> case c' of LexOrdChar c' \<Rightarrow> (of_char c :: nat) \<le> of_char c'"

definition less_LexOrdChar :: "LexOrdChar \<Rightarrow> LexOrdChar \<Rightarrow> bool" where
  "(c < c') \<equiv> case c of LexOrdChar c \<Rightarrow> case c' of LexOrdChar c' \<Rightarrow> (of_char c :: nat) < of_char c'"

instance
  by (standard; force simp add: less_LexOrdChar_def less_eq_LexOrdChar_def less_le_not_le split: LexOrdChar.splits)
end

lemma LexOrdChar_inj: "inj LexOrdChar"
  by (meson LexOrdChar.inject injI)

lemmas LexOrdChar_map_eq_iff = inj_map_eq_map[OF LexOrdChar_inj]

datatype LexOrdString = LexOrdString "string"

instantiation LexOrdString :: linorder begin

definition
  less_LexOrdString_def[simp]:
  "(s < t) = (case s of LexOrdString s \<Rightarrow> case t of LexOrdString t \<Rightarrow>
    ord_class.lexordp (map LexOrdChar s) (map LexOrdChar t))"

definition
  less_eq_LexOrdString_def[simp]:
  "(s \<le> t) = (case s of LexOrdString s \<Rightarrow> case t of LexOrdString t \<Rightarrow>
    ord_class.lexordp_eq (map LexOrdChar s) (map LexOrdChar t))"

instance
  apply standard
      apply (clarsimp simp add: lexordp_conv_lexordp_eq split: LexOrdString.splits)
     apply (clarsimp simp add: lexordp_eq_refl split: LexOrdString.splits)
    apply (force dest: lexordp_eq_trans split: LexOrdString.splits)
   apply (auto dest!: lexordp_eq_antisym simp add: LexOrdChar_map_eq_iff lexordp_eq_refl split: LexOrdString.splits)[1]
  apply (clarsimp simp add: lexordp_eq_linear split: LexOrdString.splits)
  done

end

ML {*

structure StringMap = struct

fun define_string_map name assocs ctxt = let
    val th_names = map (prefix (Binding.name_of name ^ "_") o fst) assocs
    val mappings = map (apfst HOLogic.mk_string) assocs
  in StaticFun.define_tree_and_save_thms name th_names mappings
    @{term LexOrdString} @{thms of_char_def less_eq_LexOrdChar_def less_LexOrdChar_def} ctxt end

end

*}

text {* Testing *}

(*
local_setup {* StringMap.define_string_map @{binding foo}
  [("x", @{term "1 :: nat"}), ("y", @{term "2 :: nat"})]
  #> snd
*}
*)

end

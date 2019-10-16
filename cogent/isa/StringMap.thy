(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory StringMap

(* assumes CParser or AutoCorres to find StaticFun *)
imports CParser.StaticFun

begin

datatype LexOrdString = LexOrdString "string"

instantiation LexOrdString :: linorder begin

definition
  less_LexOrdString_def[simp]:
  "(s < t) = (case s of LexOrdString s' \<Rightarrow> case t of LexOrdString t' \<Rightarrow>
    (s', t') \<in> lexord {(c, c'). (of_char c :: nat) < of_char c'})"

definition
  le_LexOrdString_def[simp]:
  "(s \<le> t) = ((s :: LexOrdString) < t \<or> s = t)"

lemma nat_of_char_trans:
  "trans {(c, c'). (of_char c :: nat) < of_char c'}"
  by (auto intro!: transI)

instance
  apply intro_classes
      apply (clarsimp split: LexOrdString.split)
      apply safe[1]
       apply (drule(1) lexord_trans[OF _ _ nat_of_char_trans])
       apply (simp add: lexord_irreflexive)
      apply (simp add: lexord_irreflexive)
     apply (clarsimp)
    apply (clarsimp split: LexOrdString.split_asm)
    apply safe[1]
    apply (erule(1) lexord_trans)
    apply (rule nat_of_char_trans)
   apply (clarsimp split: LexOrdString.split_asm)
   apply safe[1]
   apply (drule(1) lexord_trans[OF _ _ nat_of_char_trans])
   apply (simp add: lexord_irreflexive)
  apply (clarsimp split: LexOrdString.split)
  apply (rename_tac lista listb)
  apply (cut_tac lexord_linear[where r="{(c, c'). (of_char c :: nat) < of_char c'}"])
   apply auto
  done

end

ML \<open>

structure StringMap = struct

fun define_string_map name assocs ctxt =
  let
    val th_names = map (prefix (Binding.name_of name ^ "_") o fst) assocs
    val mappings = map (apfst HOLogic.mk_string) assocs
  in StaticFun.define_tree_and_save_thms name th_names mappings
    @{term LexOrdString} @{thms of_char_def} ctxt
  end
end

\<close>

text \<open> Testing \<close>

(*
local_setup \<open> StringMap.define_string_map @{binding foo}
  [("x", @{term "1 :: nat"}), ("y", @{term "2 :: nat"})]
  #> snd
\<close>
*)

end

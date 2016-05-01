(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Middle_Shallow_C
imports
  "Middle_C"
  "../../cogent/isa/shallow/tests/Middle"
  "../COGENT_Corres_Shallow_C"
begin

locale middle_cogent_shallow = 
  "pass_middle-size-example" + correspondence +
  constrains upd_abs_typing :: "abstyp \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> sigil \<Rightarrow> ptrtyp set \<Rightarrow> ptrtyp set \<Rightarrow> bool"
       and abs_repr :: "abstyp \<Rightarrow> name \<times> repr list"
       and abs_upd_val :: "abstyp \<Rightarrow> 'b \<Rightarrow> char list \<Rightarrow> COGENT.type list \<Rightarrow> sigil \<Rightarrow> 32 word set \<Rightarrow> 32 word set \<Rightarrow> bool"

sublocale middle_cogent_shallow \<subseteq> middle_cogent _ upd_abs_typing abs_repr
  by (unfold_locales)

sublocale middle_cogent_shallow \<subseteq> correspondence_init
  by (unfold_locales)

sublocale middle_cogent_shallow \<subseteq> shallow val_abs_typing 
  by (unfold_locales)


context middle_cogent_shallow
begin
thm foo_corres[no_vars]  scorres_foo[where ts="[]",no_vars]
lemma foo_corres_shallow_C:
  "val_rel_shallow_C isv m' vv uv \<xi>' \<sigma> \<Xi> \<Longrightarrow>
   corres_shallow_C state_rel (Middle_S.foo isv) Middle_D.foo (foo' m') \<xi> \<xi>' [uv] [vv] \<Xi> [Some (fst (snd foo_type))] \<sigma> s"
  apply (tactic {* cut_tac (tree_hd (hd foo_typing_tree)) 1 *})
  apply (fastforce 
          intro!: corres_shallow_C_intro[where prog_s=Middle_S.foo]
                 foo_corres[where s=s and \<sigma>=\<sigma> and \<xi>=\<xi>]
                 scorres_foo[where ts="[]"]
          simp: foo_type_def val_rel_shallow_C_def)
  done
 
end

end

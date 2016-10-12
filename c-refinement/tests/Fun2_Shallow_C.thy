(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Fun2_Shallow_C
imports
  "FunFun2"
  "../../cogent/isa/shallow/tests/Fun2"
  "../Cogent_Corres_Shallow_C"
begin

locale fun2_cogent_shallow = 
  "fun2" + correspondence +
  constrains upd_abs_typing :: "abstyp \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> sigil \<Rightarrow> ptrtyp set \<Rightarrow> ptrtyp set \<Rightarrow> bool"
       and abs_repr :: "abstyp \<Rightarrow> name \<times> repr list"
       and abs_upd_val :: "abstyp \<Rightarrow> 'b \<Rightarrow> char list \<Rightarrow> Cogent.type list \<Rightarrow> sigil \<Rightarrow> 32 word set \<Rightarrow> 32 word set \<Rightarrow> bool" 


sublocale fun2_cogent_shallow \<subseteq> fun_u_sem _ upd_abs_typing abs_repr
  by (unfold_locales)

sublocale fun2_cogent_shallow \<subseteq> shallow val_abs_typing 
  by (unfold_locales)

sublocale fun2_cogent_shallow \<subseteq> correspondence_init 
  by (unfold_locales)

context fun2_cogent_shallow
begin

lemma foo_corres_shallow_C:
  "val_rel_shallow_C isv m' vv uv \<xi>' \<sigma> \<Xi> \<Longrightarrow>
   corres_shallow_C state_rel (Fun2_S.foo isv) Fun2_D.foo (foo' m') \<xi> \<xi>' [uv] [vv] \<Xi> [Some (fst (snd foo_type))] \<sigma> s"
  apply (tactic {* cut_tac (tree_hd (hd foo_typing_tree)) 1 *})
  apply (fastforce 
          intro!: corres_shallow_C_intro[where prog_s=Fun2_S.foo]
                 foo_corres[where s=s and \<sigma>=\<sigma> and \<xi>=\<xi> and srel=state_rel]
                 scorres_foo[where ts="[]"]
          simp: foo_type_def val_rel_shallow_C_def)
  done

lemma bar_corres_shallow_C:
  "val_rel_shallow_C isv m' vv uv \<xi>' \<sigma> \<Xi> \<Longrightarrow>
   corres_shallow_C state_rel (Fun2_S.bar isv) Fun2_D.bar (bar' m') \<xi> \<xi>' [uv] [vv] \<Xi> [Some (fst (snd bar_type))] \<sigma> s"
  apply (tactic {* cut_tac (tree_hd (hd bar_typing_tree)) 1 *})
  apply (fastforce 
          intro!: corres_shallow_C_intro[where prog_s=Fun2_S.bar]
                 bar_corres[where s=s and \<sigma>=\<sigma> and \<xi>=\<xi> and srel=state_rel]
                 scorres_bar[where ts="[]"]
          simp: bar_type_def val_rel_shallow_C_def)
  done

end

end

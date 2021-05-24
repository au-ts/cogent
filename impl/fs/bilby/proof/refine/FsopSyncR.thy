(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory FsopSyncR
imports
  "../lib/CogentCorres"
  "../refine/AfsFsopR"
  "../refine/OstoreR"
begin

definition
 rsync_res :: "(afs_state \<times> (unit,ErrCode) R\<^sub>T) \<Rightarrow> FsopFsP\<^sub>T \<times> (32 word, unit) R \<Rightarrow> bool"
where
 "rsync_res \<equiv> (\<lambda>(afs, ra) (fsr, rc). ra = rc \<and> afs_fsop_rel afs (FsopFsP.fs_st\<^sub>f fsr))"

lemmas rsync_simp = rsync_res_def afs_fsop_rel_def Let_def 
   afmsu_def afs_fsop_match_step_updates_def match_afs_data_fs_state_def

lemma fold_comp[rule_format]:
  "xs = ys @ zs \<longrightarrow> fold f xs accu = (fold f zs (fold f ys accu))"
  by (induct_tac xs, simp+)

lemma corres_sync_err:
"afs_fsop_rel afs fs_st \<Longrightarrow>
 cogent_corres rsync_res (return (afs, R.Error e)) (\<lparr>FsopFsP.ex\<^sub>f = ex, fs_st\<^sub>f = fs_st\<rparr>, R.Error e)"
  by (simp add: rsync_res_def cogent_corres_def  return_def)

lemma length_updates_eqD:
 "afs_fsop_rel afs fs_st \<Longrightarrow>
 length (\<alpha>_updates (FsState.ostore_st\<^sub>f fs_st)) = length (a_medium_updates afs)"
 by (clarsimp simp: rsync_simp)

lemma afs_fsop_match_updates:
 "afs_fsop_match (fold id xs' a) (fold id ys' c) \<Longrightarrow> xs' = xs \<Longrightarrow> ys' = ys \<Longrightarrow>
  afs_fsop_match (fold id xs a) (fold id ys c)"
by simp

lemma updates_take_eq:
 "na \<le> (length xs - n) \<Longrightarrow>
  n \<le> length xs \<Longrightarrow>
  length xs = length ys \<Longrightarrow>
  take (min (length ys) n + min (length (drop n ys)) na) xs =
    take n xs @ take na (drop n xs)"
  by (simp add: min_absorb2 take_add)

lemma refine_sync:
notes length_drop[simp del]
assumes rel:"afs_fsop_rel afs fs_st"
shows
  "\<And>ex. cogent_corres rsync_res
         (afs_sync afs) (fsop_sync_fs (FsopFsP.make ex fs_st))"
  unfolding afs_sync_def fsop_sync_fs_def[simplified tuple_simps sanitizers, folded eIO_def]
using [[goals_limit=5]]
  apply (rule cogent_corres_conc_let_exec, simp only: prod.case_eq_if)
  apply (rule cogent_corres_conc_let_exec, simp only: prod.case_eq_if)
  apply (rule cogent_corres_if)
    apply (simp add: FsopFsP.make_def)
    apply (fold eRoFs_def)
    apply (rule corres_sync_err[OF rel])
   apply (rule cogent_corres_conc_let_exec, simp only: prod.case_eq_if)
   apply (rule cogent_corres_conc_let_exec, simp only: prod.case_eq_if)
   apply (simp only:  FsopFsP.defs)
   apply (fold ostoreWriteNone_def)

  apply (rule ostore_sync_ret)
       using rel apply (simp add: rsync_simp)
      using rel apply (simp add: rsync_simp)
     using rel apply (simp add: rsync_simp)
     apply (clarsimp)
    apply (rule_tac v="length (a_medium_updates afs)" in cogent_corres_select, simp)
    apply (simp add: Let_def)
    apply (rule cogent_corres_return)
    using rel apply (clarsimp simp add: rsync_simp prod.case_eq_if)
    apply (erule_tac x="length (a_medium_updates afs)" in allE)
    apply (clarsimp simp: updated_afs_def id_def a_afs_updated_def \<alpha>_ostore_uptodate_def)
    apply (drule afs_inv_steps_updated_afsD)
    apply (simp add: afs_inv_steps_def updated_afs_def a_afs_updated_def id_def)
   apply clarsimp
   apply (rule_tac v="n" in cogent_corres_select)
    apply (simp)
    using length_updates_eqD[OF rel]
    apply simp
   using length_updates_eqD[OF rel]
   apply (simp add: Let_def)
   apply (rule_tac v="e" in cogent_corres_select, simp)
   apply (rule cogent_corres_return)
   using rel apply (clarsimp simp add: rsync_simp updated_afs_def)
    apply (rule conjI)
    apply (simp add: afs_inv_steps_def updated_afs_def a_afs_updated_def id_def)
     apply (fold id_def)
     apply clarsimp
     apply (subst fold_comp[symmetric], rule refl)+
     apply (erule_tac x="n+na" in allE)
     apply (fastforce simp add: take_add length_drop)
   apply (rule conjI)
    using length_updates_eqD[OF rel]
    apply (fastforce simp add: length_drop)
   apply clarsimp
    apply (rename_tac na)
    apply (erule_tac x="n + na" in allE)
    apply (erule impE)
     apply (drule sym[where s="length _" and t = "length _"])
     apply (simp only: length_drop)
     apply (subst fold_comp[symmetric], rule refl)+
     apply (erule afs_fsop_match_updates)
     apply (fastforce simp only: take_add)+
   using rel
   apply (simp add: rsync_simp FsopFsP.defs)
 done
end 

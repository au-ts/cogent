(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory FsopIgetR
imports
  "../lib/CogentCorres"
  "../refine/AfsFsopR"
  "../adt/InodeT"
  OstoreReadR
begin

lemmas vfs_inode_simps = vfs_inode_set_flags_ret vfs_inode_set_mode_ret vfs_inode_set_gid_ret vfs_inode_set_uid_ret
vfs_inode_set_ctime_ret vfs_inode_set_mtime_ret vfs_inode_set_nlink_ret vfs_inode_set_size_ret vfs_inode_set_ino_ret

text{* iget_res is the value-relation for the spec-SS correspondence for the function iget*}
definition
 iget_res :: "afs_state \<Rightarrow> ((VfsT.VfsInode) \<times> (unit,ErrCode) R\<^sub>T) \<Rightarrow> FsopIgetRR\<^sub>T \<times> (32 word, unit) R \<Rightarrow> bool"
where
 "iget_res afs_data \<equiv> (\<lambda>((avnode), ra) (fsr, rc). 
     ra = rc \<and> afs_fsop_rel afs_data (FsopIgetRR.fs_st\<^sub>f fsr)
       \<and> (let vnode = \<alpha>inode (FsopIgetRR.vnode\<^sub>f fsr) in
          avnode = vnode))"
     
lemmas iget_simps = FsopIgetP.defs  FsopIgetRR.defs
lemmas ObjUnion_simps =  ObjUnion.simps
 
lemma rel_afs_fsop_matchD:
 "afs_fsop_rel afs_data fs_st \<Longrightarrow> afs_fsop_match (updated_afs afs_data) (\<alpha>_ostore_uptodate $ ostore_st\<^sub>f fs_st)"
  apply (clarsimp simp :afs_fsop_rel_simps updated_afs_def a_afs_updated_def \<alpha>_ostore_uptodate_def)
  apply (erule_tac x="length (a_medium_updates afs_data)" in allE)
 apply (simp add: id_def)
 done

lemma time_conv_to_OSTimeSpec:
"time_conv (u64_to_TimeSpec x) = x"
by (simp add: time_conv_def u64_to_TimeSpec_def OSTimeSpec.make_def u64_to_u32_is_ucast Let_def)
   (word_bitwise)

lemma i_ino_updated_afs_inum_eq_inum:
assumes "afs_inv (updated_afs afs_data)"
 and  "inum\<in> dom(updated_afs afs_data)"
shows
"i_ino (the (updated_afs afs_data inum)) = inum"
  using assms by (fastforce intro: inv_afs_ino_from_valid_inode)

lemma afs_inode_eq_obj_inode_to_afs_inode:
assumes rel: " afs_fsop_match (updated_afs afs_data) (\<alpha>_ostore_uptodate ostore_st')"
assumes obj: "\<alpha>_ostore_uptodate ostore_st' (obj_id_inode_mk inum) = option.Some obj"
assumes inode: "\<exists>b. ounion\<^sub>f obj = ObjUnion.TObjInode b"
assumes inv: "afs_inv (updated_afs afs_data)"
shows
 "(the (updated_afs afs_data inum)) = obj_inode_to_afs_inode obj (the (updated_afs afs_data inum))"
using rel[simplified  afs_fsop_match_def afs_fsop_content_eq_def] obj
by (fastforce simp: Let_def  dom_def afs_fsop_dom_eq_def)

lemma ostore_obj_means_inum_valid:
assumes rel:"afs_fsop_rel afs_data fs_st"
shows
 "\<alpha>_ostore_uptodate ostore_st' (obj_id_inode_mk inum) = Some obj \<Longrightarrow>
       \<alpha>_ostore_medium ostore_st' = \<alpha>_ostore_medium (FsState.ostore_st\<^sub>f fs_st) \<Longrightarrow>
       \<alpha>_updates ostore_st' = \<alpha>_updates (FsState.ostore_st\<^sub>f fs_st) \<Longrightarrow>
  inum \<in> dom(updated_afs afs_data)"
using rel  apply (clarsimp simp add: afs_fsop_rel_simps)
  apply (erule allE[where x="length (\<alpha>_updates (FsState.ostore_st\<^sub>f fs_st))"])
  apply (clarsimp simp add: afs_fsop_rel_simps afs_fsop_match_def afs_fsop_dom_eq_def updated_afs_def a_afs_updated_def \<alpha>_ostore_uptodate_def)
 apply (fastforce simp: dom_def )
done

lemma inum_valid_means_obj_exist:
assumes rel:"afs_fsop_rel afs_data fs_st"
shows
 "inum \<in> dom(updated_afs afs_data) \<Longrightarrow>
       \<alpha>_ostore_medium ostore_st' = \<alpha>_ostore_medium (FsState.ostore_st\<^sub>f fs_st) \<Longrightarrow>
       \<alpha>_updates ostore_st' = \<alpha>_updates (FsState.ostore_st\<^sub>f fs_st) \<Longrightarrow>
  \<exists>obj. \<alpha>_ostore_uptodate ostore_st' (obj_id_inode_mk inum) = Some obj"
using rel  apply (clarsimp simp add: afs_fsop_rel_simps)
  apply (erule allE[where x="length (\<alpha>_updates (FsState.ostore_st\<^sub>f fs_st))"])
  apply (clarsimp simp add: dom_def afs_fsop_rel_simps afs_fsop_match_def afs_fsop_dom_eq_def updated_afs_def a_afs_updated_def \<alpha>_ostore_uptodate_def)
 apply (fastforce simp: dom_def )
done

lemma refine_iget:
assumes rel:"afs_fsop_rel afs_data fs_st"
shows
  "\<And>ex. cogent_corres (iget_res afs_data)
         (afs_iget afs_data inum (\<alpha>inode vnode)) (fsop_iget (FsopIgetP.make ex fs_st inum vnode))"
unfolding afs_iget_def fsop_iget_def[simplified tuple_simps sanitizers]
using [[goals_limit=1]]
  apply(rule cogent_corres_conc_let_exec)
  apply clarsimp
  apply(rule ostore_read_ret)
      apply (simp add: iget_simps  afs_fsop_rel_inv_ostoreD[OF rel])
     using rel apply (simp add: iget_simps afs_fsop_rel_simps)
    apply (simp add: iget_simps  afs_fsop_rel_inv_\<alpha>_ostoreD[OF rel])
   apply (simp only: prod.case_eq_if prod.sel R.simps iget_simps FsopIgetP.simps )
   apply (frule (2) ostore_obj_means_inum_valid[OF rel])
   apply (simp)
   apply(rule cogent_corres_conc_let_exec)
   apply(rule cogent_corres_conc_let_exec)
   apply(rule cogent_corres_R)
    using rel 
    apply (clarsimp simp: iget_simps read_afs_inode_def o_def prod.case_eq_if
           eInval_def monadic_simps nondet_error_def afs_fsop_rel_simps cogent_corres_def iget_res_def)
   apply (simp add:  Let_def iget_simps prod.case_eq_if)
   using rel 
   apply (clarsimp simp:  iget_simps read_afs_inode_def o_def prod.case_eq_if
          eInval_def monadic_simps nondet_error_def afs_fsop_rel_simps cogent_corres_def iget_res_def)
   apply(simp add: extract_inode_from_union_def[unfolded tuple_simps sanitizers, simplified ObjUnion_simps Let_def])
   apply(simp split: ObjUnion.splits)
   apply (cut_tac ostore_st'=ostore_st' and obj=obj in afs_inode_eq_obj_inode_to_afs_inode[where inum=inum and afs_data=afs_data])
       apply (erule_tac x="length (a_medium_updates afs_data)" in allE)
       apply (clarsimp simp: updated_afs_def a_afs_updated_def \<alpha>_ostore_uptodate_def)
      apply assumption
     apply fastforce
    apply (erule afs_inv_steps_updated_afsD)
   apply(clarsimp simp: afs_inode_to_vnode_def vfs_inode_simps  )
   apply(erule_tac t=" y" in ssubst)
   apply(clarsimp simp only:   afs_inode_to_vnode_def obj_inode_to_afs_inode_def 
         Let_def  time_conv_to_OSTimeSpec vfs_inode_simps)
   apply (simp add: obj_inode_to_afs_inode_def obj_oinode_def vfs_inode_simps)
   apply (rename_tac b y)
    apply simp
  apply (simp add: iget_simps read_afs_inode_def )
  using rel  
  apply (clarsimp simp :iget_res_def Let_def afs_fsop_rel_def match_afs_data_fs_state_def iget_simps read_afs_inode_def o_def prod.case_eq_if 
          monadic_simps nondet_error_def cogent_corres_def del: disjCI )
  apply (simp add: afmsu_def)
  apply (case_tac "inum \<in> dom (updated_afs afs_data)")
   apply simp
   apply (frule (2) inum_valid_means_obj_exist[OF rel])
   apply fastforce
  apply (clarsimp simp: error_code_simps)
  apply (frule (2) ostore_obj_means_inum_valid[OF rel])
  apply fastforce
 done

end
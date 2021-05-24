(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory AfsFsopR
imports
  "../adt/BilbyT"
  "../adt/VfsT"
  "../spec/AfsS"
  "../spec/AfsInvS"
  "../spec/OstoreInvS"
begin

text {*
 Relation between the abstract FS of the correctness
 spec and the FS implemented by the Fsop component relying on
 the object store. 

The object store is a projection from its internal state to a
mapping from OID to Object (ostore_map).
Each ostore update is a function update on the ostore_map and can non-deterministically
be synchronised to medium. Synchronisation is similar to correctness spec level,
applying all updates to ostore_map. Refinement proof (fsop_sync/ostore_sync) should be easy.
Each update should have a matching update at correctness spec level and applying all
and sequentially applying updates on both AFS and OstoreMap should yield an element
that satisfy the relation afs_fsop_sr.

*}

definition
 obj_inode_type_to_afs_type :: "ObjInode\<^sub>T \<Rightarrow> afs_inode \<Rightarrow> afs_inode_type"
where
  "obj_inode_type_to_afs_type i afsinode \<equiv> (if S_ISREG (ObjInode.mode\<^sub>f i) then IReg (i_data afsinode) else
                (if S_ISDIR (ObjInode.mode\<^sub>f i) then IDir (i_dir afsinode) else
                 (\<comment> \<open> if S_ISLNK (mode<^sub>f i) then \<close> ILnk (i_path afsinode) \<comment> \<open>else
                   undefined\<close>)))" 

definition
  obj_inode_to_afs_inode :: "Obj\<^sub>T \<Rightarrow> afs_inode \<Rightarrow> afs_inode"
where
  "obj_inode_to_afs_inode obj afsinode \<equiv>
    (let i = obj_oinode obj in
     \<lparr>i_type = obj_inode_type_to_afs_type i afsinode,
      i_ino = inum_from_obj_id $ ObjInode.id\<^sub>f i,
      i_nlink = ObjInode.nlink\<^sub>f i,
      i_size = ObjInode.size\<^sub>f i,
      i_mtime = ObjInode.mtime_sec\<^sub>f i,
      i_ctime = ObjInode.ctime_sec\<^sub>f i,
      i_uid = ObjInode.uid\<^sub>f i,
      i_gid = ObjInode.gid\<^sub>f i,
      i_mode = ObjInode.mode\<^sub>f i,
      i_flags = ObjInode.flags\<^sub>f i\<rparr>)"
      

text {*
 Relation between a AFS file and a file in the object store.
 A file in the correctness spec corresponds to two type of objects
 stored in the object store:
  - An inode object where file attributes are stored, including the
    size (i_data part is irrelevant)
  - Multiple data objects that contain the data stored in the file.
    Each data object contains a "block" of data of BILBYFS_BLOCK_SIZE
    bytes. The block index parameter of ObjIdData indicates the index
    of the block in the file. (Where index i is byte offset
    i \<times> BILBYFS_BLOCK_SIZE in the file.)
    We currently do not allow holes.
 *}

definition
  file_eq :: "afs_inode \<Rightarrow> ostore_map \<Rightarrow> bool"
where
 "file_eq file os \<equiv>
   (\<forall>blk_idx blk. (blk_idx < length (i_data file) \<and> blk = (i_data file) ! blk_idx) \<longrightarrow>
     blk = (\<alpha>wa $ odata\<^sub>f $ obj_odata $ the $ os $ obj_id_data_mk (i_ino file, of_nat blk_idx)))"                     

definition
  get_dent_type :: "afs_map \<Rightarrow> Ino \<Rightarrow> U8"
where
 "get_dent_type afs ino \<equiv>
    (case (i_type $ the $ afs ino) of
       IReg _ \<Rightarrow>  bilbyFsItypeReg | IDir _ \<Rightarrow> bilbyFsItypeDir | ILnk _ \<Rightarrow> bilbyFsItypeLnk )"

text {*
  Relation between a AFS directory and a directory in the object store.
  At the correctness spec level directories are a an inode that contains
  a bunch of attributes and a mapping from name to inode number.
  At the Fsop level, directories are:
    - An inode for attributes such as mode, owner...
    - Multiple directory entry arrays (dentarrs).
       Each directory entry contains a name, an inode number and a type.
       The idea is that in order to have a quick lookup for a name in a
       directory, we address directory entries using a hash of the
       name they contain. As different names can have the same hash,
       we group all hash collisions together within an array of directory
       entry (dentarr).
       Mapping entries on AFS directories and dentarr objects attached to
       Fsop directories have to match one another.
       Additionally, directory entries at Fsop level contain a type
       attribute which indicates the type of the inode referred by the
       inode number. This type attribute is a duplicated piece of
       information also contained in the inode itself, but having
       it is necessary for performance reason. When listing a directory
       reading an extra inode for each directory entry would be orders
       of magnitude slower.
   *}

definition
  dir_eq :: "afs_inode \<Rightarrow> afs_map \<Rightarrow>ostore_map \<Rightarrow> bool"
where
 "dir_eq dir afs os \<equiv>
    (\<forall>name. 
     (let obj = os $ obj_id_dentarr_mk (i_ino dir, name);
          entries = stripNone $ \<alpha>a $ ObjDentarr.entries\<^sub>f $ obj_odentarr $ the obj in
      (case i_dir dir $ \<alpha>wa name of
        option.Some in_ino \<Rightarrow>
         (case obj of
           option.Some _ \<Rightarrow>
            {e \<in> set entries. ObjDentry.ino\<^sub>f e = in_ino \<and> ObjDentry.name\<^sub>f e = name} =
              {\<lparr>ino\<^sub>f = in_ino, type\<^sub>f = get_dent_type afs in_ino, nlen\<^sub>f = u32_to_u16 $ wordarray_length name, name\<^sub>f = name \<rparr>} |
            option.None \<Rightarrow> False)
       | option.None \<Rightarrow>
           (case obj of
              option.Some _ \<Rightarrow>
                  {e \<in> set entries. ObjDentry.name\<^sub>f e = name} = {}
            | option.None \<Rightarrow> True))))"

text {* Relation between a AFS symlinks and a symlinks in the object store.
  This relation is quite similar to files except that symbolic links can
  only use a single data block to store the symbolic link path.
*}
definition
  symlink_eq :: "afs_inode \<Rightarrow> ostore_map \<Rightarrow> bool"
where
 "symlink_eq symlink os \<equiv>
   i_path symlink = (\<alpha>wa $ odata\<^sub>f $ obj_odata $ the $ os $ obj_id_data_mk (i_ino symlink, 0))"

text {*
  Domain equivalence ensures that there is an inode in the AFS
  iff there is an existing inode at Fsop level.
*}
definition
  afs_fsop_dom_eq :: "afs_map \<Rightarrow> ostore_map \<Rightarrow> bool"
where
 "afs_fsop_dom_eq afs os \<equiv> dom afs = dom (\<lambda>ino. os (obj_id_inode_mk ino))"

text {*
  Content equivalence
*}
definition
  afs_fsop_content_eq :: "afs_map \<Rightarrow> ostore_map \<Rightarrow> bool"
where
 "afs_fsop_content_eq afs os \<equiv> 
  (\<forall>ino \<in> dom afs.
      let inode = (the $ afs ino);
          oino = (the $ os $ obj_id_inode_mk ino) in
          obj_inode_to_afs_inode oino inode = inode \<and>
          (case i_type inode of
             IReg file_data \<Rightarrow> file_eq inode os |
             IDir dir \<Rightarrow> dir_eq inode afs os |
             ILnk path \<Rightarrow>  symlink_eq inode os))"

definition
  afs_fsop_match :: "afs_map \<Rightarrow> ostore_map \<Rightarrow> bool"
where
 "afs_fsop_match afs os \<equiv> afs_fsop_dom_eq afs os \<and> afs_fsop_content_eq afs os"
                                                         
text {*
 Definitions useful to describe parameters, pre/post conditions of
 refinement statements
*}
definition
 vnode_afs_inode_consistency :: "vnode \<Rightarrow> afs_inode \<Rightarrow> bool"
where
 "vnode_afs_inode_consistency v i \<equiv>
  v_ino v = i_ino i \<and>
  v_nlink v = i_nlink i \<and>
  v_mtime v = i_mtime i \<and>
  v_ctime v = i_ctime i \<and>
  v_uid v = i_uid i \<and>
  v_gid v = i_gid i \<and>
  v_mode v = i_mode i"

definition
 is_valid_vdir :: "vnode \<Rightarrow> (Ino \<rightharpoonup> afs_inode) \<Rightarrow> bool"
where
 "is_valid_vdir vdir afs \<equiv>
    v_ino vdir \<in> dom afs \<and>
    (v_mode vdir AND s_IFMT = s_IFDIR) \<and>
    afs_inode_is_dir (i_type $ the $ afs $ v_ino vdir) \<and>
    vnode_afs_inode_consistency vdir (the $ afs $ v_ino vdir)"

lemma vdir_dir_consistent:
 "is_valid_vdir vdir afs \<Longrightarrow> vnode_afs_inode_consistency vdir (the $ afs $ v_ino vdir)"
 by (clarsimp simp: is_valid_vdir_def dom_def)

lemma vdir_is_dir:
 "\<lbrakk> is_valid_vdir vdir afs \<rbrakk> \<Longrightarrow> afs_inode_is_dir (i_type $ the $ afs (v_ino vdir))"
  by (clarsimp simp: is_valid_vdir_def)

text {* Refinement proof of the operation sync. *}

definition
 match_afs_data_fs_state :: "afs_state \<Rightarrow> FsState\<^sub>T \<Rightarrow> bool"
where
 "match_afs_data_fs_state afs_data fs_st \<equiv>
  a_is_readonly afs_data = (is_ro\<^sub>f $ fsop_st\<^sub>f fs_st)"

definition
 afs_fsop_match_step_updates :: "afs_map \<Rightarrow> (afs_map \<Rightarrow> afs_map) list \<Rightarrow>
                                 ostore_map \<Rightarrow> (ostore_map \<Rightarrow> ostore_map) list \<Rightarrow> bool"
where
 "afs_fsop_match_step_updates afs afs_updates os os_updates \<equiv>
     length os_updates = length afs_updates \<and>
     (\<forall>n \<le> length os_updates.
        afs_fsop_match (a_afs_updated_n n afs afs_updates)
                       (apply_n_updates n os os_updates))"

definition
 "afmsu afs_data os_st \<equiv> 
   afs_fsop_match_step_updates
    (a_medium_afs afs_data) (a_medium_updates afs_data) 
    (\<alpha>_ostore_medium os_st) (\<alpha>_updates os_st)"

definition
  "afs_inv_steps afs \<equiv>
    (\<forall>n \<le> length (a_medium_updates afs).
     afs_inv (a_afs_updated_n n (a_medium_afs afs) (a_medium_updates afs)))"

lemma afs_inv_steps_updated_afsD:
 "afs_inv_steps afs \<Longrightarrow> afs_inv (updated_afs afs)"
  apply (simp add: updated_afs_def)
  apply (simp add: afs_inv_steps_def)
  apply (erule_tac x="length (a_medium_updates afs)" in allE)
  apply (fastforce simp add: a_afs_updated_def)
 done

text{* In the success case, we ensure that the updates match and that the on-medium
 states match too. Note that simply applying the updates on both sides and ensuring
 that the resulting states match is not enough, both syncs could have applied a different
 number of updates. *}
definition
 afs_fsop_rel :: "afs_state \<Rightarrow> FsState\<^sub>T \<Rightarrow> bool"
where
 "afs_fsop_rel afs_data fs_st \<equiv>
   inv_mount_st (FsState.mount_st\<^sub>f fs_st) \<and>
   afs_inv_steps afs_data \<and> 
   (let os_st = ostore_st\<^sub>f fs_st in
     afmsu afs_data os_st \<and>
     inv_ostore (mount_st\<^sub>f fs_st) os_st \<and> inv_\<alpha>_ostore (\<alpha>_ostore_uptodate os_st) \<and>
     match_afs_data_fs_state afs_data fs_st)"

lemma afs_fsop_rel_inv_ostoreD:
 "afs_fsop_rel afs_data fs_st \<Longrightarrow> inv_ostore (mount_st\<^sub>f fs_st) (ostore_st\<^sub>f fs_st)"
 by (clarsimp simp: afs_fsop_rel_def Let_def) 
(*
lemma afs_fsop_rel_inv_stepD:
"afs_fsop_rel afs_data fs_st \<Longrightarrow> inv_\<alpha>_step_updates (ostore_st\<^sub>f fs_st)"
by (clarsimp simp: afs_fsop_rel_def Let_def) 
*)
lemma afs_fsop_rel_inv_\<alpha>_ostoreD:
"afs_fsop_rel afs_data fs_st \<Longrightarrow>  inv_\<alpha>_ostore (\<alpha>_ostore_uptodate (ostore_st\<^sub>f fs_st))"
by (clarsimp simp: afs_fsop_rel_def Let_def) 

lemmas afs_fsop_rel_simps = 
  afs_fsop_rel_def 
  match_afs_data_fs_state_def
  afmsu_def
  Let_def
  afs_fsop_match_step_updates_def

end

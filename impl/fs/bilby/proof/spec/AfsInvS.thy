(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory AfsInvS
imports AfsS
begin  

definition
  "afs_files_ino afs \<equiv> {i\<in> dom afs. \<exists>d. i_type (the (afs i)) = IReg d }"
definition
  "afs_dirs_ino afs \<equiv> {i \<in> dom afs. \<exists>d. i_type (the (afs i)) = IDir d }"
definition
  "afs_links_ino afs \<equiv> {i \<in> dom afs. \<exists>p. i_type (the (afs i)) = ILnk p }"

definition "ROOT_INO \<equiv> bilbyFsRootIno"

type_synonym ino ="32 word"

text {*
We should derive the following no_cyclic invariant from the
one that says that no directory can have a hardlink.
*}
definition
  inv_afs_no_cyclic :: "(ino \<rightharpoonup> afs_inode) \<Rightarrow> bool"
where
  "inv_afs_no_cyclic afs \<equiv>
    (\<forall>ino \<in> dom afs. case i_type (the (afs ino)) of IDir d \<Rightarrow> (\<forall>name. d name \<noteq> option.Some ino \<and> d name \<noteq> option.Some ROOT_INO) | _ \<Rightarrow> True)"

definition
  inv_afs_files_nlink :: "(ino \<rightharpoonup> afs_inode) \<Rightarrow> bool"
where
  "inv_afs_files_nlink afs \<equiv>
  (\<forall>ino \<in> afs_files_ino afs \<union> afs_links_ino afs. 
     card {(dir_ino,name).
             dir_ino \<in> afs_dirs_ino afs \<and>
             (i_dir $ the $ afs dir_ino) name = option.Some ino} =
     unat (i_nlink $ the $ afs ino))"

definition
  inv_afs_dirs_nlink :: "(ino \<rightharpoonup> afs_inode) \<Rightarrow> bool"
where
  "inv_afs_dirs_nlink afs \<equiv>
  (\<forall>ino \<in> afs_dirs_ino afs. 
     2 + card {dir_ino \<in> ran (i_dir $ the $ afs ino).
               dir_ino \<in> afs_dirs_ino afs} =
      unat (i_nlink $ the $ afs ino))"

definition
  inv_afs_valid_ino :: "(ino \<rightharpoonup> afs_inode) \<Rightarrow> bool"
where
 "inv_afs_valid_ino afs \<equiv> (\<forall>ino \<in> dom afs. i_ino (the (afs ino)) = ino)"

definition
  inv_afs_size :: "(ino \<rightharpoonup> afs_inode) \<Rightarrow> bool"
where
 "inv_afs_size afs \<equiv> 
  \<forall>v\<in>ran afs.
  (case i_type v of
    IReg f \<Rightarrow> count (concat (i_data v)) = i_size v
   | ILnk l \<Rightarrow> count (i_path v) = i_size v)"

definition
  inv_root_ino :: "(ino \<rightharpoonup> afs_inode) \<Rightarrow> bool"
where
 "inv_root_ino afs \<equiv> (ROOT_INO \<in> afs_dirs_ino afs)"

definition "afs_inv afs \<equiv>
  inv_afs_no_cyclic afs \<and>
  inv_afs_files_nlink afs \<and>
  inv_afs_dirs_nlink afs \<and>
  inv_afs_valid_ino afs \<and>
  inv_afs_size afs \<and>
  inv_root_ino afs"

text {* Few lemmas to use these invariants *}
lemma inv_no_cyclic: "afs_inv afs \<Longrightarrow> inv_afs_no_cyclic afs" by (clarsimp simp: afs_inv_def)
lemma inv_valid_ino: "afs_inv afs \<Longrightarrow> inv_afs_valid_ino afs" by (clarsimp simp: afs_inv_def)
lemma inv_root_ino: "afs_inv afs \<Longrightarrow> inv_root_ino afs" by (clarsimp simp: afs_inv_def)
lemma inv_root_ino_no_cyclic:
 "afs_inv afs \<Longrightarrow> (\<forall>ino\<in>afs_dirs_ino afs. \<forall>name. i_dir (the (afs ino)) name \<noteq> option.Some ROOT_INO)"
   by (fastforce simp: afs_inv_def afs_dirs_ino_def inv_afs_no_cyclic_def inv_root_ino_def i_type_def  dom_def)+

lemma inv_afs_ino_from_valid_inode:
 "afs_inv afs \<Longrightarrow> afs any_ino = option.Some any_inode \<Longrightarrow> i_ino any_inode = any_ino"
  apply (drule inv_valid_ino[simplified inv_afs_valid_ino_def])
  apply (erule_tac x="any_ino" in ballE)
   apply clarsimp+
  done

end

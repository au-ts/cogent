(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory InodeT
imports
  "../adt/BilbyT"
begin

text {*
   We need to find a way to deal with abstract inodes,
   my idea is to add an axiomatize inode functions the
   same way we do it with ../adt/WordArray
*}
consts \<alpha>inode :: "VfsInode\<^sub>T \<Rightarrow> VfsT.VfsInode"
definition
time_conv :: "OSTimeSpec\<^sub>T \<Rightarrow> TimeT"
where "time_conv ts \<equiv> ((ucast (tv_sec\<^sub>f ts) :: U64) << 32) OR ucast (tv_nsec\<^sub>f ts)"


axiomatization
where
vfs_inode_set_flags_ret:
  "\<alpha>inode (vfs_inode_set_flags (r,v)) = (\<alpha>inode r)\<lparr> VfsT.VfsInode.v_flags := v \<rparr>"
and
vfs_inode_set_mode_ret:
  "\<alpha>inode (vfs_inode_set_mode (r,v)) = (\<alpha>inode r)\<lparr> VfsT.VfsInode.v_mode := v \<rparr>"
and
vfs_inode_set_gid_ret:
  "\<alpha>inode (vfs_inode_set_gid (r,v)) = (\<alpha>inode r)\<lparr> VfsT.VfsInode.v_gid := v \<rparr>"
and
vfs_inode_set_uid_ret:
  "\<alpha>inode (vfs_inode_set_uid (r,v)) = (\<alpha>inode r)\<lparr> VfsT.VfsInode.v_uid := v \<rparr>"
and
vfs_inode_set_ctime_ret:
  "\<alpha>inode (vfs_inode_set_ctime (r,t)) = (\<alpha>inode r)\<lparr> VfsT.VfsInode.v_ctime := time_conv t \<rparr>"
and
vfs_inode_set_mtime_ret:
  "\<alpha>inode (vfs_inode_set_mtime (r,t)) = (\<alpha>inode r)\<lparr> VfsT.VfsInode.v_mtime := time_conv t \<rparr>"
and
vfs_inode_set_nlink_ret:
  "\<alpha>inode (vfs_inode_set_nlink (r,v)) = (\<alpha>inode r)\<lparr> VfsT.VfsInode.v_nlink := v \<rparr>"
and
vfs_inode_set_size_ret:
"\<alpha>inode (vfs_inode_set_size (r,v')) = (\<alpha>inode r)\<lparr> VfsT.VfsInode.v_size := v' \<rparr>"
and
vfs_inode_set_ino_ret:
"\<alpha>inode (vfs_inode_set_ino (r,v)) = (\<alpha>inode r)\<lparr> VfsT.VfsInode.v_ino := v \<rparr>"

end

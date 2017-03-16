(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory VfsT
imports "../lib/TypBucket"
begin

text {* VFS types *}
typedecl vnode_ref
record VfsInode =
  v_ino :: "Ino"
  v_nlink :: "U32"
  v_size :: "SizeT"
  v_mtime :: "TimeT"
  v_ctime :: "TimeT"
  v_uid :: "U32"
  v_gid :: "U32"
  v_mode :: "Mode"
  v_flags :: "U32"

type_synonym vnode = VfsInode

fun S_ISLNK :: "Mode \<Rightarrow> bool"  where
 "S_ISLNK m = (m AND s_IFMT = s_IFLNK)"
fun  S_ISREG :: "Mode \<Rightarrow> bool" where
 "S_ISREG m = (m AND s_IFMT = s_IFREG)"
fun S_ISDIR :: "Mode \<Rightarrow> bool" where
 "S_ISDIR m = (m AND s_IFMT = s_IFDIR)"

type_synonym vblock = U32
typedecl vpage_ref
end
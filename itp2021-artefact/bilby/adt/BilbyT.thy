(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory BilbyT
imports
  "../lib/FunBucket"
  "../lib/TypBucket"
  VfsT
begin

text {* bilbyFsMaxEbSize fixes the maximum size of erase-block supported by BilbyFs to 16MiB *}
definition
  bilbyFsMaxEbSize :: U32
where
 "bilbyFsMaxEbSize \<equiv> 2^14 * 1024" 

definition
  inv_mount_st :: "MountState\<^sub>T \<Rightarrow> bool"
where
 "inv_mount_st mount_st \<equiv>
     let super = MountState.super\<^sub>f mount_st in
     \<not> no_summary\<^sub>f mount_st \<and>
     is_pow_of_2 (io_size\<^sub>f super) \<and>
     io_size\<^sub>f super \<ge> 512 \<and>
     io_size\<^sub>f super < eb_size\<^sub>f super \<and>
     io_size\<^sub>f super udvd eb_size\<^sub>f super \<and>
     eb_size\<^sub>f super \<le> bilbyFsMaxEbSize"


end
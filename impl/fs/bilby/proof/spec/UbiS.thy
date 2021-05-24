(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory UbiS
imports "../adt/BilbyT"
"../adt/BufferT"
  "BilbyFsConsts.BilbyFs_Shallow_Desugar_Tuples"
begin

type_synonym ubi_leb = "U8 list"

consts \<alpha>wubi :: "UbiVol \<Rightarrow> ubi_leb list"

definition
  "inv_ubi_vol mount_st vol \<equiv>
   unat (nb_eb\<^sub>f (super\<^sub>f mount_st)) = length ((\<alpha>wubi vol))"

axiomatization
where
  wubi_leb_write_ret:
 "\<And>P. \<lbrakk> length ( (\<alpha>wubi ubi_vol) ! (unat ebnum)) = unat sync_offs;
        buf_length wbuf = eb_size\<^sub>f (super\<^sub>f mount_st);
        unat sync_offs + unat nb_bytes  \<le> unat (eb_size\<^sub>f (super\<^sub>f mount_st));
        io_size\<^sub>f (super\<^sub>f mount_st) udvd nb_bytes;
        inv_ubi_vol mount_st ubi_vol;
        \<And>ex . P ((ex,ubi_vol), Error eIO);
        \<And>ex ubi_vol'.  \<lbrakk> inv_ubi_vol mount_st ubi_vol';
        (\<alpha>wubi ubi_vol') = (\<alpha>wubi ubi_vol)[(unat ebnum):=(\<alpha>wubi ubi_vol!(unat ebnum)@buf_slice wbuf sync_offs (sync_offs + nb_bytes))]
        \<rbrakk> \<Longrightarrow> P ((ex, ubi_vol'), Success ())
  \<rbrakk> \<Longrightarrow> P (wubi_leb_write (WubiLebWriteP.make ex ubi_vol ebnum wbuf sync_offs nb_bytes))"
and
  wubi_leb_change_ret:
 "\<And>P. \<lbrakk> length ( (\<alpha>wubi ubi_vol) ! (unat ebnum)) = unat sync_offs;
        buf_length wbuf = eb_size\<^sub>f (super\<^sub>f mount_st);
        unat sync_offs + unat nb_bytes  \<le> unat (eb_size\<^sub>f (super\<^sub>f mount_st));
         io_size\<^sub>f (super\<^sub>f mount_st) udvd nb_bytes;
        inv_ubi_vol mount_st ubi_vol;
        \<And>ex . P ((ex,ubi_vol), Error eIO);
        \<And>ex ubi_vol'.  \<lbrakk> inv_ubi_vol mount_st ubi_vol';
        (\<alpha>wubi ubi_vol') = (\<alpha>wubi ubi_vol)[(unat ebnum):= buf_take wbuf nb_bytes]
        \<rbrakk> \<Longrightarrow> P ((ex, ubi_vol'), Success ())
  \<rbrakk> \<Longrightarrow> P (wubi_leb_change ( (WubiLebChangeP.make ex ubi_vol ebnum wbuf nb_bytes)))"
and
 wubi_leb_read_ret:
 "\<And>P. \<lbrakk> buf_length rbuf = eb_size\<^sub>f (super\<^sub>f mount_st);
        unat buf_offs + unat nb_bytes  \<le> unat (eb_size\<^sub>f (super\<^sub>f mount_st));
        inv_ubi_vol mount_st ubi_vol;
        \<And>ex rbuf' . \<exists>v. rbuf'\<lparr>data\<^sub>f:=v\<rparr> = rbuf \<Longrightarrow> buf_length rbuf' = buf_length rbuf \<Longrightarrow> P ((ex,rbuf'), Error eBadF);
        \<And>ex rbuf'.  \<lbrakk> 
  rbuf' = rbuf\<lparr>data\<^sub>f:= WordArrayT.make (buf_take rbuf buf_offs @
            slice (unat buf_offs) (unat buf_offs + unat nb_bytes) (\<alpha>wubi ubi_vol !(unat ebnum) @ replicate (unat nb_bytes) 0xff) @
            buf_drop rbuf (buf_offs+ nb_bytes)) \<rparr>
        \<rbrakk> \<Longrightarrow> P ((ex,rbuf'), Success ())
  \<rbrakk> \<Longrightarrow> P (wubi_leb_read (WubiLebReadP.make ex ubi_vol ebnum rbuf buf_offs nb_bytes))"

end

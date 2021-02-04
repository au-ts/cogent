(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory OstoreReadR
imports
  "../spec/OstoreS"
  "../spec/OstoreInvS"
  "../impl/BilbyFs_Shallow_Desugar_Tuples"
  "../adt/BufferT"
  "../spec/SerialS"
begin

lemmas ostore_simps = 
  inv_ostore_summary_def
  inv_ostore_index_def 
  inv_ostore_index_gim_disjoint_def 
  inv_ostore_fsm_def 
  inv_flash_def 
  ostore_update_def
  
lemma inv_ostore_bound_eq: 
  "inv_ostore mount_st ostore_st \<Longrightarrow> 
  (ostore_st\<lparr>wbuf\<^sub>f := wbuf\<^sub>f ostore_st\<lparr>bound\<^sub>f := eb_size\<^sub>f (super\<^sub>f mount_st)\<rparr>\<rparr>) = ostore_st"
  by (simp add: inv_ostore_def buf_simps)

lemma inv_ostore_bound_upd:
  "inv_ostore mount_st ostore_st \<Longrightarrow>
   inv_ostore mount_st (ostore_st\<lparr>wbuf\<^sub>f := wbuf\<^sub>f ostore_st\<lparr>bound\<^sub>f := eb_size\<^sub>f (super\<^sub>f mount_st)\<rparr>\<rparr>)"
  by (simp add: inv_ostore_bound_eq)

lemma index_get_addr_ret:
  assumes err: " oid \<notin> dom (\<alpha>rbt $ addrs\<^sub>f $ index_st\<^sub>f ostore_st) \<Longrightarrow> P (R.Error eNoEnt)"
  and     suc: "\<And>oaddr. oid \<in> dom (\<alpha>rbt $ addrs\<^sub>f $ index_st\<^sub>f ostore_st) \<Longrightarrow>
            oaddr = the ((\<alpha>rbt $ addrs\<^sub>f $ index_st\<^sub>f ostore_st) oid) \<Longrightarrow>
      P (R.Success oaddr)"

  shows
  "P (index_get_addr (index_st\<^sub>f ostore_st, oid))"
 unfolding index_get_addr_def[unfolded tuple_simps sanitizers, folded eNoEnt_def]
  apply (simp add: Let_def)
  apply (clarsimp simp add: rbt_get_value_ret option.case_eq_if R.splits)
  apply (auto intro: err suc)
 done

lemma inv_ostore_wellformed_bufD:
 "inv_ostore mount_st ostore_st \<Longrightarrow> inv_mount_st mount_st \<Longrightarrow>  wellformed_buf (wbuf\<^sub>f ostore_st)"
  apply (frule inv_ostore_buf_boundD)
  apply (clarsimp simp add: inv_ostore_def wellformed_buf_def buf_simps)
 done

lemma inv_ostore_runtimeD:
 "inv_ostore mount_st ostore_st \<Longrightarrow>
   \<alpha>_ostore_runtime ostore_st = \<alpha>_ostore_uptodate ostore_st"
   by (simp add: inv_ostore_def)

lemma dom_uptodate_eq_dom_index:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
 shows
 "dom (\<alpha>_ostore_uptodate ostore_st) = dom (\<alpha>rbt $ addrs\<^sub>f $ index_st\<^sub>f ostore_st)"
  by (force intro!: Collect_eqI split: option.splits dest: inv_ostore_indexD
       simp add: \<alpha>_ostore_runtime_def \<alpha>_index_def dom_def inv_ostore_index_def Let_def
       inv_ostore_runtimeD[OF inv_ostore, symmetric])

lemma inv_mount_st_io_size_not_0D:
 "inv_mount_st mount_st \<Longrightarrow> io_size\<^sub>f (super\<^sub>f mount_st) \<noteq> 0"
 by (simp add: inv_mount_st_def Let_def) unat_arith

lemma offs_pl_olen_le_used:
 "inv_ostore mount_st ostore_st \<Longrightarrow>
 \<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid = TypBucket.Some y \<Longrightarrow>
         ObjAddr.ebnum\<^sub>f y = wbuf_eb\<^sub>f ostore_st \<Longrightarrow>
         ObjAddr.offs\<^sub>f y + bilbyFsObjHeaderSize \<le>  used\<^sub>f ostore_st"
  apply (drule inv_ostore_indexD)
  apply (simp add: \<alpha>_index_def inv_ostore_index_def)
  apply (erule_tac x=oid in ballE)
   apply (clarsimp simp add: \<alpha>_index_def Let_def is_valid_addr_def bilbyFsMinObjSize_def bilbyFsObjHeaderSize_def)
   apply unat_arith
  apply (simp add: dom_def)
 done

lemma inv_\<alpha>_ostore_wbuf_bound_eq_eb_size: 
"inv_ostore mount_st ostore_st \<Longrightarrow>
  inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st) \<Longrightarrow>
  inv_\<alpha>_ostore (\<alpha>_ostore_uptodate (ostore_st\<lparr>wbuf\<^sub>f := wbuf\<^sub>f ostore_st\<lparr>bound\<^sub>f := eb_size\<^sub>f (super\<^sub>f mount_st)\<rparr>\<rparr>))"
  apply (simp add: \<alpha>_ostore_uptodate_def)
  apply (simp add: \<alpha>_updates_def \<alpha>_ostore_medium_def buf_slice_def)
 done

lemma offs_lt_offs_pl_hdr:
 "inv_ostore mount_st ostore_st \<Longrightarrow>
 \<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid = TypBucket.Some y \<Longrightarrow>
         ObjAddr.ebnum\<^sub>f y = wbuf_eb\<^sub>f ostore_st \<Longrightarrow>
         ObjAddr.offs\<^sub>f y < ObjAddr.offs\<^sub>f y + bilbyFsObjHeaderSize"
  apply (drule inv_ostore_indexD)
  apply (simp add: \<alpha>_index_def inv_ostore_index_def)
  apply (erule_tac x=oid in ballE)
   apply (clarsimp simp add: \<alpha>_index_def Let_def is_valid_addr_def bilbyFsMinObjSize_def bilbyFsObjHeaderSize_def)
   apply unat_arith
  apply (simp add: dom_def)
 done

lemma is_obj_addr_consistent_lenD:
 "is_obj_addr_consistent obj oaddr \<Longrightarrow> Obj.len\<^sub>f obj = ObjAddr.len\<^sub>f oaddr"
 by (simp add: is_obj_addr_consistent_def)


lemma is_valid_addr_offs_no_ofD:
 "is_valid_addr mount_st ostore_st oaddr \<Longrightarrow> ObjAddr.offs\<^sub>f oaddr < ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr"
 by (simp add: is_valid_addr_def)

lemma is_valid_addr_offs_no_of_hdrszD:
 "is_valid_addr mount_st ostore_st oaddr \<Longrightarrow>
  is_obj_addr_consistent (pObj (take (unat (ObjAddr.offs\<^sub>f oaddr) + unat (ObjAddr.len\<^sub>f oaddr)) xs)
          (ObjAddr.offs\<^sub>f oaddr)) oaddr  \<Longrightarrow>
  xs = \<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st)) \<Longrightarrow>
  ObjAddr.offs\<^sub>f oaddr < ObjAddr.offs\<^sub>f oaddr + bilbyFsObjHeaderSize"
 by (clarsimp simp add: is_valid_addr_def bilbyFsMinObjSize_def bilbyFsObjHeaderSize_def)
    unat_arith
lemma pObj_take:
 "is_valid_ObjHeader (pObjHeader xs (ObjAddr.offs\<^sub>f oaddr)) xs \<Longrightarrow>
  is_valid_addr mount_st ostore_st oaddr \<Longrightarrow>
is_obj_addr_consistent (pObj (take (unat (ObjAddr.offs\<^sub>f oaddr) + unat (ObjAddr.len\<^sub>f oaddr)) xs)
          (ObjAddr.offs\<^sub>f oaddr)) oaddr  \<Longrightarrow>
  xs = \<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st)) \<Longrightarrow>
 pObj (take (unat (ObjAddr.offs\<^sub>f oaddr) + unat (ObjAddr.len\<^sub>f oaddr)) xs) (ObjAddr.offs\<^sub>f oaddr) =
  pObj xs (ObjAddr.offs\<^sub>f oaddr)"
  apply (subgoal_tac "bilbyFsObjHeaderSize \<le> ObjAddr.len\<^sub>f oaddr")
   prefer 2
   apply (clarsimp simp add: is_valid_addr_def bilbyFsObjHeaderSize_def bilbyFsMinObjSize_def)
   apply unat_arith
  apply (frule (1) is_valid_addr_offs_no_of_hdrszD, simp)
  apply (frule is_obj_addr_consistent_lenD)
  apply (simp (no_asm) add: pObj_def pObjHeader_take[where xs=xs] Let_def)
  apply (subst pObjHeader_take[where xs=xs], assumption+)+
  apply (simp add: pObj_def Let_def)
 done

lemma pObj_offs:
 "Obj.offs\<^sub>f (pObj xs offs) = offs"
 by (simp add: pObj_def pObjHeader_def Let_def Obj.make_def)

lemma get_obj_oid_offs_agnostic:
 "get_obj_oid (x\<lparr> Obj.offs\<^sub>f := offs \<rparr>) = get_obj_oid x"
 by (simp add: get_obj_oid_def)

lemma oaddr_is_valid_addr:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     oaddr: "\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid = TypBucket.Some oaddr"
  shows
  "is_valid_addr mount_st ostore_st oaddr"
  using inv_ostore_indexD[OF inv_ostore]
  by (auto simp add: inv_ostore_index_def Let_def oaddr \<alpha>_index_def
      elim: ballE[where x=oid])

lemma oaddr_add_len_pl_iosz_no_of:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     oaddr: "\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid = TypBucket.Some oaddr"
  shows
   "ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr < ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr + io_size\<^sub>f (super\<^sub>f mount_st)"
proof -

  have is_pow: "is_pow_of_2 (io_size\<^sub>f (super\<^sub>f mount_st))"
   using inv_mount_st by (simp add: Let_def inv_mount_st_def)

  have iosz_gt_0: "0 < io_size\<^sub>f (super\<^sub>f mount_st)"
  and iosz_lt_max_eb_sz: "io_size\<^sub>f (super\<^sub>f mount_st) \<le> bilbyFsMaxEbSize"
    using inv_mount_st[simplified inv_mount_st_def Let_def]
    by (clarsimp, unat_arith)+

  have maxeb_add: "bilbyFsMaxEbSize < bilbyFsMaxEbSize + io_size\<^sub>f (super\<^sub>f mount_st)"
   using  iosz_lt_max_eb_sz and iosz_gt_0
   by (simp add: unat_arith_simps bilbyFsMaxEbSize_def)

  have oaddr_no_of: " ObjAddr.offs\<^sub>f oaddr <  ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr"
   using oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
   by (clarsimp simp: is_valid_addr_def Let_def)

  have oaddr_le_eb_size: "ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr \<le> eb_size\<^sub>f (super\<^sub>f mount_st)"
   using oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
   by (clarsimp simp: is_valid_addr_def Let_def)

  have le_maxeb: "ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr \<le> bilbyFsMaxEbSize"
   using oaddr_le_eb_size inv_mount_st
   by (clarsimp simp add: inv_mount_st_def Let_def) unat_arith

  show ?thesis
   using maxeb_add le_maxeb
   by unat_arith
qed

lemma inv_mount_st_iosz_is_pow:
 "inv_mount_st mount_st \<Longrightarrow> is_pow_of_2 (io_size\<^sub>f (super\<^sub>f mount_st))"
   by (simp add: Let_def inv_mount_st_def)

lemma  oaddr_offs_pl_olen_le_align:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     oaddr: "\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid = TypBucket.Some oaddr"
  shows
 "ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr \<le>
    align32 (ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr, io_size\<^sub>f (super\<^sub>f mount_st))"
 using align32_ge[OF inv_mount_st_iosz_is_pow[OF inv_mount_st] oaddr_add_len_pl_iosz_no_of[OF inv_ostore inv_mount_st oaddr]]
 .

lemma oaddr_offs_pl_objhdr_le_align:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     oaddr: "\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid = TypBucket.Some oaddr"
  shows
 "ObjAddr.offs\<^sub>f oaddr + bilbyFsObjHeaderSize \<le>
    align32 (ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr, io_size\<^sub>f (super\<^sub>f mount_st))"
 using oaddr_offs_pl_olen_le_align[OF inv_ostore inv_mount_st oaddr]
 oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
 by (clarsimp simp: is_valid_addr_def bilbyFsObjHeaderSize_def bilbyFsMinObjSize_def) 
   unat_arith 

lemma  oaddr_offs_le_align:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     oaddr: "\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid = TypBucket.Some oaddr"
  shows
 "ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st) <
    align32 (ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr, io_size\<^sub>f (super\<^sub>f mount_st))"
  using oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
  oaddr_offs_pl_objhdr_le_align[OF inv_ostore inv_mount_st oaddr]
  by (clarsimp simp add: is_valid_addr_def Let_def bilbyFsObjHeaderSize_def bilbyFsMinObjSize_def)
   unat_arith

lemma oaddr_add_le_eb_size:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     oaddr: "\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid = TypBucket.Some oaddr"
  shows
 "unat (ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st)) +
    unat (align32 (ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr, io_size\<^sub>f (super\<^sub>f mount_st)) -
          (ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st)))
    \<le> unat (eb_size\<^sub>f (super\<^sub>f mount_st))"
proof -
  obtain x where xdef: "x = (ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st))" by simp
  obtain y where ydef: "y = align32 (ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr, io_size\<^sub>f (super\<^sub>f mount_st))" by simp

  have "x < y"
  using oaddr_offs_le_align[OF inv_ostore inv_mount_st oaddr]
  by (simp add: xdef ydef)

  hence "unat (y - x) = unat y - unat x"
   by unat_arith

  hence arith: "unat x + unat (y - x) = unat y"
   by unat_arith

  hence "unat y \<le> unat (eb_size\<^sub>f (super\<^sub>f mount_st))"
  apply (simp add: ydef)
  apply (rule align32_upper_bound[OF _ inv_mount_st_iosz_is_pow[OF inv_mount_st], simplified word_le_nat_alt])
   subgoal using oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr] by (clarsimp simp add: is_valid_addr_def) unat_arith
   subgoal using inv_mount_st by (simp add: inv_mount_st_def Let_def)
   subgoal using oaddr_add_len_pl_iosz_no_of[OF inv_ostore inv_mount_st oaddr] by simp
  done
  thus ?thesis by (simp add: xdef[symmetric] ydef[symmetric] arith)
qed

lemma align32_le_eb_size:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     oaddr: "\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid = TypBucket.Some oaddr"
  shows 
 "align32 (ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr, io_size\<^sub>f (super\<^sub>f mount_st))
       \<le> eb_size\<^sub>f (super\<^sub>f mount_st)"
proof -
  have le_eb_size: "ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr \<le> eb_size\<^sub>f (super\<^sub>f mount_st)"
    using oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr] by (clarsimp simp: is_valid_addr_def)

  have udvd_eb_size: "io_size\<^sub>f (super\<^sub>f mount_st) udvd eb_size\<^sub>f (super\<^sub>f mount_st)"
    using inv_mount_st by (simp add: inv_mount_st_def Let_def)

  have "ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr < ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr + io_size\<^sub>f (super\<^sub>f mount_st)"
    using oaddr_add_len_pl_iosz_no_of[OF inv_ostore inv_mount_st oaddr] by (simp)
  thus ?thesis
    by (rule align32_upper_bound[OF le_eb_size inv_mount_st_iosz_is_pow[OF inv_mount_st] udvd_eb_size])
qed

lemma align32_le_len_rbuf:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     oaddr: "\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid = TypBucket.Some oaddr"
  shows 
 "unat (align32 (ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr, io_size\<^sub>f (super\<^sub>f mount_st)))
       \<le> length (\<alpha>wa $ data\<^sub>f (rbuf\<^sub>f ostore_st))"
proof -
   have len_geq_ebsz: "length (\<alpha>wa $ data\<^sub>f (rbuf\<^sub>f ostore_st)) \<ge> unat (eb_size\<^sub>f (super\<^sub>f mount_st))"
     using inv_ostore apply (clarsimp simp add: inv_ostore_def Let_def buf_length_def)
     apply (simp only: word_unat.Rep_inject[symmetric])
     using  wordarray_length_leq_length[of "data\<^sub>f (rbuf\<^sub>f ostore_st)"]
     apply unat_arith
     done
  
  have "unat (align32 (ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr, io_size\<^sub>f (super\<^sub>f mount_st))) \<le> unat (eb_size\<^sub>f (super\<^sub>f mount_st))"  
    by (rule align32_le_eb_size[OF inv_ostore inv_mount_st oaddr, simplified word_le_nat_alt])
  thus ?thesis
    using len_geq_ebsz
    by (rule order.trans; simp?)
qed

lemma plus_no_of_unat_lift: 
  "(a::'a::len word )  \<le> a + b \<Longrightarrow>  unat (a+b) = unat a + unat b"
  by unat_arith 

lemma buf_take_slice_drop_len:
 "(buf_offs::U32) \<le> buf_offs + nb_bytes \<Longrightarrow>
  unat (buf_offs + nb_bytes) \<le> length (\<alpha>wa $ data\<^sub>f rbuf) \<Longrightarrow>
  unat (buf_offs + nb_bytes) \<le> length (\<alpha>wubi ubi_vol !(unat ebnum)) \<Longrightarrow>
  
  ndrop = (buf_offs+ nb_bytes) \<Longrightarrow>
 length (buf_take rbuf buf_offs @
            slice (unat buf_offs) (unat buf_offs + unat nb_bytes) (\<alpha>wubi ubi_vol !(unat ebnum) @ replicate (unat nb_bytes) 0xff) @
            buf_drop rbuf ndrop) = length (\<alpha>wa $ data\<^sub>f rbuf)"     
  by (simp add: buf_simps min_absorb2 plus_no_of_unat_lift)

definition
  read_pages_rbuf
where
 "read_pages_rbuf rbuf frm len ubib \<equiv>
  rbuf \<lparr>data\<^sub>f := WordArrayT.make
     (buf_take rbuf frm @ FunBucket.slice (unat frm) (unat frm+ unat len)
     (ubib @ replicate (unat len) 0xFF) @ buf_drop rbuf (frm+len)), bound\<^sub>f := frm+len\<rparr>"

lemma read_pages_buf_length:
 "frm \<le> frm+len \<Longrightarrow> unat (frm + len) \<le> length (\<alpha>wa $ data\<^sub>f rbuf) \<Longrightarrow>
 length (\<alpha>wa $ data\<^sub>f rbuf) = length ubib \<Longrightarrow>
 length (\<alpha>wa (data\<^sub>f (read_pages_rbuf rbuf frm len ubib))) = length (\<alpha>wa $ data\<^sub>f rbuf)"
  apply (simp add: read_pages_rbuf_def wordarray_make length_slice buf_simps)
  apply (subgoal_tac "(length ubib) \<ge> (unat frm)")
   prefer 2
  apply unat_arith
  apply (simp add: min_absorb1)
  apply (subgoal_tac "unat frm + unat len \<le> length ubib")
   apply (simp add: min_absorb1)
   apply unat_arith+
  done

lemma read_pages_buf_length':
 "frm \<le> frm+len \<Longrightarrow> unat (frm + len) \<le> length (\<alpha>wa $ data\<^sub>f rbuf) \<Longrightarrow>
 unat (frm + len) \<le> length ubib \<Longrightarrow>
 length (\<alpha>wa (data\<^sub>f (read_pages_rbuf rbuf frm len ubib))) = length (\<alpha>wa $ data\<^sub>f rbuf)"
  apply (simp add: read_pages_rbuf_def wordarray_make length_slice buf_simps)
  apply (subgoal_tac "(length ubib) \<ge> (unat frm)")
   prefer 2
  apply unat_arith
  apply (simp add: min_absorb1)
  apply (subgoal_tac "unat frm + unat len \<le> length ubib")
   apply (simp add: min_absorb1)
   apply unat_arith+
 done

lemma x_minus_x_mod_y_le_x:
  "(x::'a::len word) - x mod y \<le> x"
 by unat_arith

lemma oaddr_ebnum_rangeD:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  assumes inv_mount_st: "inv_mount_st mount_st"
  and     oaddr: "\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid = TypBucket.Some oaddr"
  and     ebnum: "ObjAddr.ebnum\<^sub>f oaddr \<noteq> wbuf_eb\<^sub>f ostore_st"
  shows
  "unat (ObjAddr.ebnum\<^sub>f oaddr) \<in> {unat bilbyFsFirstLogEbNum..length (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))}"
  using inv_bufsD[OF inv_ostore]
  apply clarsimp
  apply (erule ballE[where x="unat (ObjAddr.ebnum\<^sub>f oaddr)"])
   using  oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
   apply (clarsimp simp: is_valid_addr_def inv_ubi_vol_def)
   apply unat_arith
  apply (erule notE)
  using ebnum apply simp
  using oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
  apply (clarsimp simp add: is_valid_addr_def inv_ubi_vol_def)
  apply unat_arith
 done

lemma oaddr_offs_sb_mod_offs_le_offs_pl_olen:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  assumes inv_mount_st: "inv_mount_st mount_st"
  and     oaddr: "\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid = TypBucket.Some oaddr"
  shows 
  "ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st) \<le> ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr"
  using oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
  apply (clarsimp simp: is_valid_addr_def Let_def)
  apply unat_arith
  done

lemma read_obj_pages_in_buf_ret:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  assumes inv_mount_st: "inv_mount_st mount_st"
  and     oaddr: "\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid = TypBucket.Some oaddr"
  and     ebnum: "ObjAddr.ebnum\<^sub>f oaddr \<noteq> wbuf_eb\<^sub>f ostore_st"
  and     err: "\<And>ex buf'. \<exists>v. buf'\<lparr>data\<^sub>f := v\<rparr> = rbuf\<^sub>f ostore_st \<and> wordarray_length (data\<^sub>f buf') = eb_size\<^sub>f (super\<^sub>f mount_st) \<Longrightarrow> P ((ex, buf'), Error eBadF)"
  and     suc: "\<And>ex buf. buf = read_pages_rbuf (rbuf\<^sub>f ostore_st) (ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st))
    (align32 (ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr, io_size\<^sub>f (super\<^sub>f mount_st)) -
                      (ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st)))
  (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) ! unat (ObjAddr.ebnum\<^sub>f oaddr)) \<Longrightarrow>
  wellformed_buf buf \<Longrightarrow>
length (\<alpha>wa (data\<^sub>f buf)) = length (\<alpha>wa (data\<^sub>f (rbuf\<^sub>f ostore_st))) \<Longrightarrow>
    P ((ex, buf), R.Success ())"
  shows 
 "P (read_obj_pages_in_buf (ex, mount_st, OstoreState.ubi_vol\<^sub>f ostore_st, rbuf\<^sub>f ostore_st, oaddr))"
  unfolding read_obj_pages_in_buf_def[unfolded tuple_simps sanitizers]
  apply (simp add: Let_def)
  using inv_mount_st_io_size_not_0D[OF inv_mount_st]
  apply clarsimp
  apply (rule wubi_leb_read_ret[OF _ _ inv_ubi_volD[OF inv_ostore]])
     apply (rule inv_ostore_rbuf_lengthD[OF inv_ostore])
    apply (rule oaddr_add_le_eb_size[OF inv_ostore inv_mount_st oaddr])
   apply simp
   apply (rule err)
  using inv_ostore_rbuf_lengthD[OF inv_ostore]
   apply (clarsimp simp: buf_length_def)
  apply (simp, rule suc, simp add: read_pages_rbuf_def)
   apply (simp add: wellformed_buf_def )
   apply (simp only: wordarray_make)
   apply (cut_tac oaddr_offs_sb_mod_offs_le_offs_pl_olen[OF inv_ostore inv_mount_st oaddr])
   apply (cut_tac oaddr_offs_pl_olen_le_align[OF inv_ostore inv_mount_st oaddr])
   apply (cut_tac align32_le_eb_size[OF inv_ostore inv_mount_st oaddr])
   apply (cut_tac inv_ostore_rbuf_lengthD[OF inv_ostore, simplified buf_length_def Let_def])
   apply (cut_tac read_pages_buf_length'[symmetric,where frm="(ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st))"
       and len="(align32
                          (ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr, io_size\<^sub>f (super\<^sub>f mount_st)) -
                       (ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st)))"
      and rbuf="rbuf\<^sub>f ostore_st"
      and ubib="(\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) ! unat (ObjAddr.ebnum\<^sub>f oaddr))", symmetric]; simp?)   
     apply (simp add: wordarray_make read_pages_rbuf_def)
  using wordarray_length_leq_length[of "data\<^sub>f (rbuf\<^sub>f ostore_st)"]
     apply unat_arith
  using wordarray_length_leq_length[of "data\<^sub>f (rbuf\<^sub>f ostore_st)"]
    apply unat_arith
  using oaddr_ebnum_rangeD[OF inv_ostore inv_mount_st oaddr ebnum]
         inv_bufsD[OF inv_ostore]
         inv_ubi_volD[OF inv_ostore, simplified inv_ubi_vol_def]
         oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
         ebnum
         align32_le_eb_size[OF inv_ostore inv_mount_st oaddr, simplified word_le_nat_alt]
   apply clarsimp
  apply (cut_tac oaddr_offs_sb_mod_offs_le_offs_pl_olen[OF inv_ostore inv_mount_st oaddr])
  apply (cut_tac oaddr_offs_pl_olen_le_align[OF inv_ostore inv_mount_st oaddr])
  apply (cut_tac align32_le_eb_size[OF inv_ostore inv_mount_st oaddr])
  apply (cut_tac inv_ostore_rbuf_lengthD[OF inv_ostore, simplified buf_length_def Let_def])
  apply (cut_tac read_pages_buf_length'[symmetric,where frm="(ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st))"
       and len="(align32
                          (ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr, io_size\<^sub>f (super\<^sub>f mount_st)) -
                       (ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st)))"
      and rbuf="rbuf\<^sub>f ostore_st"
      and ubib="(\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) ! unat (ObjAddr.ebnum\<^sub>f oaddr))"]; simp?)
  apply (simp add: wordarray_make read_pages_rbuf_def)
  using wordarray_length_leq_length[of "data\<^sub>f (rbuf\<^sub>f ostore_st)"]
   apply unat_arith
  using oaddr_ebnum_rangeD[OF inv_ostore inv_mount_st oaddr ebnum]
         inv_bufsD[OF inv_ostore]
         inv_ubi_volD[OF inv_ostore, simplified inv_ubi_vol_def]
         oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
         ebnum
         align32_le_eb_size[OF inv_ostore inv_mount_st oaddr, simplified word_le_nat_alt]
  apply clarsimp
  done

lemma read_obj_pages_in_buf_ret':
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  assumes inv_mount_st: "inv_mount_st mount_st"
  and     oaddr: "\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid = TypBucket.Some oaddr"
  and     ebnum: "ObjAddr.ebnum\<^sub>f oaddr \<noteq> wbuf_eb\<^sub>f ostore_st"
  and     err: "\<And>ex buf'. \<exists>v. buf'\<lparr>data\<^sub>f := v\<rparr> = rbuf\<^sub>f ostore_st \<and> wordarray_length (data\<^sub>f buf') = eb_size\<^sub>f (super\<^sub>f mount_st) \<Longrightarrow> P ((ex, buf'), Error eBadF)"
  and     suc: "\<And>ex buf. buf = read_pages_rbuf (rbuf\<^sub>f ostore_st) (ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st))
    (align32 (ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr, io_size\<^sub>f (super\<^sub>f mount_st)) -
                      (ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st)))
  (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) ! unat (ObjAddr.ebnum\<^sub>f oaddr)) \<Longrightarrow>
  wellformed_buf' buf \<Longrightarrow>
length (\<alpha>wa (data\<^sub>f buf)) = length (\<alpha>wa (data\<^sub>f (rbuf\<^sub>f ostore_st))) \<Longrightarrow>
    P ((ex, buf), R.Success ())"
  shows 
 "P (read_obj_pages_in_buf (ex, mount_st, OstoreState.ubi_vol\<^sub>f ostore_st, rbuf\<^sub>f ostore_st, oaddr))"
  unfolding read_obj_pages_in_buf_def[unfolded tuple_simps sanitizers]
  apply (simp add: Let_def)
  using inv_mount_st_io_size_not_0D[OF inv_mount_st]
  apply clarsimp
  apply (rule wubi_leb_read_ret[OF _ _ inv_ubi_volD[OF inv_ostore]])
     apply (rule inv_ostore_rbuf_lengthD[OF inv_ostore])
    apply (rule oaddr_add_le_eb_size[OF inv_ostore inv_mount_st oaddr])
   apply simp
   apply (rule err)
  using inv_ostore_rbuf_lengthD[OF inv_ostore]
   apply (clarsimp simp: buf_length_def)
  apply (simp, rule suc, simp add: read_pages_rbuf_def)
   apply (simp add: wellformed_buf'_def )
   apply (cut_tac oaddr_offs_sb_mod_offs_le_offs_pl_olen[OF inv_ostore inv_mount_st oaddr])
   apply (cut_tac oaddr_offs_pl_olen_le_align[OF inv_ostore inv_mount_st oaddr])
   apply (cut_tac align32_le_eb_size[OF inv_ostore inv_mount_st oaddr])
   apply (cut_tac inv_ostore_rbuf_lengthD[OF inv_ostore, simplified buf_length_def Let_def])
   apply (cut_tac read_pages_buf_length'[symmetric,where frm="(ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st))"
       and len="(align32
                          (ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr, io_size\<^sub>f (super\<^sub>f mount_st)) -
                       (ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st)))"
      and rbuf="rbuf\<^sub>f ostore_st"
      and ubib="(\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) ! unat (ObjAddr.ebnum\<^sub>f oaddr))"]; simp?)
     apply (drule length_eq_imp_wordarray_length_eq[symmetric])
     apply (simp add: wordarray_make read_pages_rbuf_def)
  using wordarray_length_leq_length[of "data\<^sub>f (rbuf\<^sub>f ostore_st)"]
    apply unat_arith
  using oaddr_ebnum_rangeD[OF inv_ostore inv_mount_st oaddr ebnum]
         inv_bufsD[OF inv_ostore]
         inv_ubi_volD[OF inv_ostore, simplified inv_ubi_vol_def]
         oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
         ebnum
         align32_le_eb_size[OF inv_ostore inv_mount_st oaddr, simplified word_le_nat_alt]
   apply clarsimp
  apply (cut_tac oaddr_offs_sb_mod_offs_le_offs_pl_olen[OF inv_ostore inv_mount_st oaddr])
  apply (cut_tac oaddr_offs_pl_olen_le_align[OF inv_ostore inv_mount_st oaddr])
  apply (cut_tac align32_le_eb_size[OF inv_ostore inv_mount_st oaddr])
  apply (cut_tac inv_ostore_rbuf_lengthD[OF inv_ostore, simplified buf_length_def Let_def])
  apply (cut_tac read_pages_buf_length'[symmetric,where frm="(ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st))"
       and len="(align32
                          (ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr, io_size\<^sub>f (super\<^sub>f mount_st)) -
                       (ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st)))"
      and rbuf="rbuf\<^sub>f ostore_st"
      and ubib="(\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) ! unat (ObjAddr.ebnum\<^sub>f oaddr))"]; simp?)
  apply (simp add: wordarray_make read_pages_rbuf_def)
  using wordarray_length_leq_length[of "data\<^sub>f (rbuf\<^sub>f ostore_st)"]
   apply unat_arith
  using oaddr_ebnum_rangeD[OF inv_ostore inv_mount_st oaddr ebnum]
         inv_bufsD[OF inv_ostore]
         inv_ubi_volD[OF inv_ostore, simplified inv_ubi_vol_def]
         oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
         ebnum
         align32_le_eb_size[OF inv_ostore inv_mount_st oaddr, simplified word_le_nat_alt]
  apply clarsimp
  done

lemma ostore_maps_eq_rbuf_agnostic:
 " \<alpha>_ostore_runtime ostore_st = \<alpha>_ostore_uptodate ostore_st \<Longrightarrow>
 \<alpha>_ostore_runtime (ostore_st\<lparr>rbuf\<^sub>f := buf'\<rparr>) = \<alpha>_ostore_uptodate (ostore_st\<lparr>rbuf\<^sub>f := buf'\<rparr>)"
  apply (rule ext)
  apply (drule_tac x=x in fun_cong)
  apply (clarsimp simp add: \<alpha>_ostore_uptodate_def \<alpha>_ostore_runtime_def \<alpha>_updates_def \<alpha>_ostore_medium_def ostore_get_obj_def)
  apply (unfold ostore_get_obj_def)
  apply (fastforce simp add: \<alpha>_index_def split:option.splits)
 done

lemma inv_ostore_rbuf_agnostic:
  assumes
    "inv_ostore mount_st ostore_st"
    "buf'\<lparr>data\<^sub>f := v,bound\<^sub>f:= b\<rparr> = rbuf\<^sub>f ostore_st"
    "wordarray_length (data\<^sub>f buf') = eb_size\<^sub>f (super\<^sub>f mount_st)"
  shows
    "inv_ostore mount_st (ostore_st\<lparr>rbuf\<^sub>f := buf'\<rparr>)"
  using assms
  apply -
  apply (auto elim: inv_ostoreE intro!: inv_ostoreI)
         apply (simp add: buf_length_def)
        apply (force intro: ostore_maps_eq_rbuf_agnostic simp add: inv_ostore_simps)
       apply (force simp add: inv_ostore_simps)
      apply(clarsimp simp: inv_ostore_def inv_ostore_index_def Let_def)
      apply(erule_tac x=oid in ballE; clarsimp simp: is_valid_addr_def ostore_get_obj_def split: if_splits)
     apply (force intro: ostore_maps_eq_rbuf_agnostic simp add: inv_ostore_simps buf_length_def Let_def)
    apply (force intro: ostore_maps_eq_rbuf_agnostic simp add: inv_ostore_simps buf_length_def Let_def)
   apply(clarsimp simp: inv_ostore_def inv_ostore_fsm_def Let_def)
   apply(erule_tac x=oid in ballE; clarsimp simp: ostore_log_objects_def list_eb_log_wbuf_def)
  apply (force intro: ostore_maps_eq_rbuf_agnostic simp add: inv_ostore_simps buf_length_def Let_def)
  done

lemma \<alpha>_ostore_uptodate_rbuf_agnostic:
 "\<alpha>_ostore_uptodate (ostore_st\<lparr>rbuf\<^sub>f := rbuf\<rparr>) = \<alpha>_ostore_uptodate (ostore_st)"
 by (rule ext) (simp add: \<alpha>_ostore_uptodate_def \<alpha>_updates_def \<alpha>_ostore_medium_def)

lemma pObj_update_offs:
 "pObj xs offs \<lparr>Obj.offs\<^sub>f := offs\<rparr> = pObj xs offs"
 by (simp add: pObj_def pObjHeader_def Obj.make_def)

lemma oaddr_is_obj_addr_consistent:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     oaddr: "\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid = TypBucket.Some oaddr"
  shows
  "is_obj_addr_consistent (ostore_get_obj ostore_st oaddr) oaddr"
  using inv_ostore_indexD[OF inv_ostore]
  by (auto simp add: inv_ostore_index_def Let_def oaddr \<alpha>_index_def
      elim: ballE[where x=oid])

lemma drop_eq_increase:
 "List.drop n xs = List.drop n ys \<Longrightarrow> n \<le> m \<Longrightarrow> List.drop m xs = List.drop m ys"
by (metis drop_drop le_add_diff_inverse2)

lemma take_eq_decrease:
 "take n xs = take n ys \<Longrightarrow> m \<le> n \<Longrightarrow> take m xs = take m ys"
  by (metis min_absorb1 take_take)

lemma slice_sub_slice:
  "slice a b xs = slice a b ys \<Longrightarrow>
   a \<le> n \<Longrightarrow> m \<le> b \<Longrightarrow>
   a \<le> b \<Longrightarrow> n \<le> m \<Longrightarrow> 
   slice n m xs  = slice n m ys"
  by (simp add: slice_def) (metis  drop_eq_increase drop_take min_absorb1 take_take)


lemma ple32_slice_eq_no_add:
 " bilbyFsObjHeaderSize \<le> Obj.len\<^sub>f obj \<Longrightarrow>
    slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) xs =
    slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) ys \<Longrightarrow>
    offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
    n + 4 \<le> Obj.len\<^sub>f obj \<Longrightarrow>
    n < n+4 \<Longrightarrow>
    ple32 (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs + n) =
    ple32 (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) (offs + n)"
  apply (simp add: ple32_def)
  apply (rule arg_cong[where f=word_rcat])
  apply (rule arg_cong[where f=rev])
  apply (rule arg_cong[where f="take _"])
  apply (subgoal_tac "unat (offs + n) = unat offs + unat n")
   prefer 2
   apply unat_arith
  apply simp
  apply (simp add: slice_def)
  apply (erule drop_eq_increase)
  apply unat_arith
 done

lemma ple64_slice_eq_no_add:
 " bilbyFsObjHeaderSize \<le> Obj.len\<^sub>f obj \<Longrightarrow>
    slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) xs =
    slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) ys \<Longrightarrow>
    offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
    n + 8 \<le> Obj.len\<^sub>f obj \<Longrightarrow>
    n < n + 8 \<Longrightarrow>
    ple64 (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs + n) =
    ple64 (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) (offs + n)"
  apply (simp add: ple64_def)
  apply (rule arg_cong[where f=word_rcat])
  apply (rule arg_cong[where f=rev])
  apply (rule arg_cong[where f="take _"])
  apply (subgoal_tac "unat (offs + n) = unat offs + unat n")
   prefer 2
   apply unat_arith
  apply simp
  apply (simp add: slice_def)
  apply (erule drop_eq_increase)
  apply unat_arith
  done

lemma "xs = ys \<Longrightarrow> xs!1 = ys!1"
  "[]!0 = []!0"
  by simp+

lemma take_add_nth_eq_drop:
 "a + b \<le> length xs \<Longrightarrow> n < b \<Longrightarrow> take (a + b) xs ! (a + n) = List.drop a xs ! n"
  by simp

lemma u8_slice_eq_no_add:
 "bilbyFsObjHeaderSize \<le> Obj.len\<^sub>f obj \<Longrightarrow>
    FunBucket.slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) xs =
    FunBucket.slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) ys \<Longrightarrow>
    offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
    n < Obj.len\<^sub>f obj \<Longrightarrow>
   unat offs + unat (Obj.len\<^sub>f obj) \<le> length xs \<Longrightarrow>
   unat offs + unat (Obj.len\<^sub>f obj) \<le> length ys \<Longrightarrow>
unat offs + unat (Obj.len\<^sub>f obj) \<le> length xs \<Longrightarrow>
    take (unat offs + unat (Obj.len\<^sub>f obj)) xs ! unat (offs + n) =
    take (unat offs + unat (Obj.len\<^sub>f obj)) ys ! unat (offs + n)"
  apply (subgoal_tac "unat (offs + n) = unat offs + unat n")
   prefer 2
   apply unat_arith
  apply (simp add: slice_def)
  apply (subst take_add_nth_eq_drop, ((simp add: unat_arith_simps)[2])+)
  apply (subst take_add_nth_eq_drop, ((simp add: unat_arith_simps)[2])+)
  apply (simp add: drop_take)
  apply (drule arg_cong[where f="(\<lambda>xs. xs ! (unat n))"])
  apply (simp add: word_less_nat_alt)
 done

lemma pObjHeader_slice_eq:
  "bilbyFsObjHeaderSize \<le> Obj.len\<^sub>f obj \<Longrightarrow>
    FunBucket.slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) xs =
    FunBucket.slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) ys \<Longrightarrow>
    offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
    unat offs + unat (Obj.len\<^sub>f obj) \<le> length xs \<Longrightarrow>
    unat offs + unat (Obj.len\<^sub>f obj) \<le> length ys \<Longrightarrow>
    pObjHeader (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) offs =
    pObjHeader (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) offs"
  apply (simp add: pObjHeader_def Obj.make_def)
  apply (subst u8_slice_eq_no_add ple64_slice_eq_no_add ple32_slice_eq_no_add ple32_slice_eq_no_add[where n=0,simplified],
        ((simp add: bilbyFsObjHeaderSize_def unat_arith_simps)[2])+, simp)+
 done

lemma pObjHeader_take_hdrsz:
 "offs < offs + bilbyFsObjHeaderSize \<Longrightarrow>
 pObjHeader xs offs = pObjHeader (take (unat offs + unat bilbyFsObjHeaderSize) xs) offs"
 apply (simp add: pObjHeader_def Obj.make_def)
 apply (subst ple32_take, ((simp add: bilbyFsObjHeaderSize_def unat_arith_simps, unat_arith)[2])+)+
 apply (subst ple64_take, ((simp add: bilbyFsObjHeaderSize_def unat_arith_simps, unat_arith)[2])+)+
 apply (simp add: bilbyFsObjHeaderSize_def word_le_plus[simplified unat_plus_simple])
done

lemma pObjHeader_take_olen:
 "offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
bilbyFsObjHeaderSize \<le> Obj.len\<^sub>f obj \<Longrightarrow> 
 pObjHeader xs offs = pObjHeader (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) offs"
 apply (simp add: pObjHeader_def Obj.make_def)
 apply (subst ple64_take ple32_take , ((simp add: bilbyFsObjHeaderSize_def unat_arith_simps, unat_arith)[2])+, simp)+
 apply (frule order_class.order.strict_implies_order)
 apply (simp add: bilbyFsObjHeaderSize_def word_le_plus[simplified unat_plus_simple] )
 apply (subst nth_take[where n="(unat offs + unat (Obj.len\<^sub>f obj))"], unat_arith)+
 apply simp
done

lemma ple32_slice_eq:
 "slice (unat offs) (unat offs + unat olen) xs =
  slice (unat offs) (unat offs + unat olen) ys \<Longrightarrow>
  offs < offs + olen \<Longrightarrow>
  bilbyFsObjHeaderSize + n \<le> olen \<Longrightarrow>
  ple32 (take (unat offs + unat olen) xs) (offs + bilbyFsObjHeaderSize + n) =
  ple32 (take (unat offs + unat olen) ys) (offs + bilbyFsObjHeaderSize + n)"
  apply (simp add: ple32_def)
  apply (rule arg_cong[where f=word_rcat])
  apply (rule arg_cong[where f=rev])
  apply (rule arg_cong[where f="take 4"])
  apply (simp add: slice_def bilbyFsObjHeaderSize_def word_le_plus[simplified unat_plus_simple])
  apply (erule drop_eq_increase, unat_arith)
done

lemma ple64_slice_eq:
 "slice (unat offs) (unat offs + unat olen) xs =
  slice (unat offs) (unat offs + unat olen) ys \<Longrightarrow>
  offs < offs + olen \<Longrightarrow>
  bilbyFsObjHeaderSize + n \<le> olen \<Longrightarrow>
  ple64 (take (unat offs + unat olen) xs) (offs + bilbyFsObjHeaderSize + n) =
  ple64 (take (unat offs + unat olen) ys) (offs + bilbyFsObjHeaderSize + n)"
  apply (simp add: ple64_def)
  apply (rule arg_cong[where f=word_rcat])
  apply (rule arg_cong[where f=rev])
  apply (rule arg_cong[where f="take 8"])
  apply (simp add: slice_def bilbyFsObjHeaderSize_def word_le_plus[simplified unat_plus_simple])
  apply (erule drop_eq_increase, unat_arith)
done

lemma pObjInode_slice_eq: 
  "is_len_and_type_ok (0, Obj.len\<^sub>f obj) \<Longrightarrow>
    FunBucket.slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) xs =
    FunBucket.slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) ys \<Longrightarrow>
    offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
    pObjInode (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs + bilbyFsObjHeaderSize) =
    pObjInode (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) (offs + bilbyFsObjHeaderSize)"
  apply (simp add: pObjInode_def ObjInode.make_def)
  apply (subst ple64_slice_eq[where n=0, simplified] ple64_slice_eq ple32_slice_eq,
        ((simp add: otype_simps len_otype_ok bilbyFsObjHeaderSize_def)[2])+, simp)+
 done

lemma pObjData_slice_eq:
 "is_len_and_type_ok (1, Obj.len\<^sub>f obj) \<Longrightarrow>
    FunBucket.slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) xs =
    FunBucket.slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) ys \<Longrightarrow>
    offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
    pObjData (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs + bilbyFsObjHeaderSize) (Obj.len\<^sub>f obj) =
    pObjData (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) (offs + bilbyFsObjHeaderSize) (Obj.len\<^sub>f obj)"
  apply (simp add: pObjData_def ObjData.make_def)
  apply (subst ple64_slice_eq[where n=0, simplified], ((simp add:  otype_simps len_otype_ok bilbyFsObjHeaderSize_def | unat_arith)[2])+)
  apply (simp add:  otype_simps len_otype_ok bilbyFsObjHeaderSize_def)
  apply (rule arg_cong[where f=WordArrayT.make])
  apply (rule  slice_sub_slice[where a="unat offs" and b="unat offs + unat (Obj.len\<^sub>f obj)"])
      apply (simp add: slice_take)
     apply unat_arith
    apply (simp add: bilbyFsObjDataHeaderSize_def unat_arith_simps)
   apply unat_arith
  apply (simp add: bilbyFsObjDataHeaderSize_def unat_arith_simps)
 done

lemma pObjDel_slice_eq:
 "is_len_and_type_ok (3, Obj.len\<^sub>f obj) \<Longrightarrow>
    FunBucket.slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) xs =
    FunBucket.slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) ys \<Longrightarrow>
    offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
    pObjDel (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs + bilbyFsObjHeaderSize) =
    pObjDel (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) (offs + bilbyFsObjHeaderSize)"
  apply (simp add: pObjDel_def ObjDel.make_def)
  apply (erule (1) ple64_slice_eq[where n=0, simplified])
  apply (simp add: otype_simps len_otype_ok bilbyFsObjHeaderSize_def)
done

lemma pObjDentry_slice_eq:
assumes a: "unat ost + 4 < unat offs + unat (Obj.len\<^sub>f obj)"
assumes slice_eq: "slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) xs =
   slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) ys"
shows
 " offs < ost \<Longrightarrow>
  ost < ost + 8 \<Longrightarrow>
   offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
   (unat offs + unat (Obj.len\<^sub>f obj)) \<le> length xs \<Longrightarrow>
   (unat offs + unat (Obj.len\<^sub>f obj)) \<le> length ys \<Longrightarrow>
   pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost =
   pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) ost"
using slice_eq
  apply (simp add: pObjDentry_def Let_def ObjDentry.make_def)
  apply (subgoal_tac "ple16 (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (ost + 6) =
    ple16 (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) (ost + 6)")
  apply safe
     apply (simp  add: slice_def ple32_def)
     apply (drule drop_eq_increase[where m="unat ost"])
      apply unat_arith
     apply simp
    apply (frule word_le_plus[where c=4], simp)
    apply (simp add:  unat_plus_simple)
  
    apply (subgoal_tac "unat ost + 5 = unat offs + (unat ost - unat offs + 5)")
     prefer 2
     apply (frule word_le_plus[where c=4], simp)
     apply (thin_tac "ple16 _ _ = _ ")
     apply (simp add: unat_arith_simps)
    apply (simp only: pu8_def) 
    apply (rule arg_cong[where f=word_rcat])
    apply (simp only: slice_def fun_app_def)
    apply (drule drop_eq_increase[where m="unat (ost+4)"])
    apply simp
    apply (subgoal_tac "ost \<le> ost + 4")
      prefer 2
      apply (frule order_class.order.strict_implies_order[where b="ost + 8"])
      apply (simp only: unat_plus_simple)
      apply unat_arith
     apply (simp only: unat_arith_simps)
    apply simp
    using a
    apply (simp only: min_absorb1)
    apply (fold slice_def[simplified])
    apply (erule slice_sub_slice)
       using a apply fastforce+
   apply (rule arg_cong[where f=WordArrayT.make])
   apply (simp add: slice_def)
   apply (rule drop_eq_increase[where n="unat offs"])
   apply (simp add: drop_take)
   apply (erule take_eq_decrease)
   apply (frule order_class.order.strict_implies_order[where b="ost + 8"], (simp add: unat_plus_simple))
   apply unat_arith

  apply (simp  add: slice_def ple16_def)
  apply (drule drop_eq_increase[where m="unat (ost+6)"])
  apply (frule word_le_plus[where c=6], simp)
  apply (simp add: unat_plus_simple)
   apply unat_arith
  apply (simp only:)
 done

lemma of_trivial:
 assumes a:"v \<le> bilbyFsMaxEbSize + 8"
 and     b:"ost \<le> bilbyFsMaxEbSize"
 and     c: "0<v"
 shows "ost < ost + v"
proof -
 have ost_v_max: "ost < bilbyFsMaxEbSize + bilbyFsMaxEbSize + 8"
  using b by (simp add: bilbyFsMaxEbSize_def) unat_arith
 thus ?thesis
 using a c
 by (simp add: bilbyFsMaxEbSize_def unat_arith_simps) 
qed


lemma x0_le_8_pl_max_eb:
assumes a: "unat v \<le> unat offs + unat (Obj.len\<^sub>f obj)"
and b: " unat offs + unat (Obj.len\<^sub>f obj) \<le> unat bilbyFsMaxEbSize"
shows " 0 < 8 + (v::U32)"
proof -
  have v_le_max: "unat v \<le> unat bilbyFsMaxEbSize"
  using a b by (simp)

  thus ?thesis
  by (simp add: bilbyFsMaxEbSize_def unat_arith_simps)
qed

lemma x0_le_8_pl_max_eb':
assumes a: "v \<le> v'"
and b: "v' \<le> bilbyFsMaxEbSize"
shows " 0 < 8 + (v::U32)"
proof -
  have v_le_max: "v \<le> bilbyFsMaxEbSize"
  using a b by (simp)

  thus ?thesis
  by (simp add: bilbyFsMaxEbSize_def unat_arith_simps)
qed

lemma max_eb_size_pl_8:
 "v \<le> bilbyFsMaxEbSize \<Longrightarrow>
 v < (v::U32) + 8"
 by (simp add: bilbyFsMaxEbSize_def unat_arith_simps)

lemma xxx:
 "       unat (wordarray_length
                  (ObjDentry.name\<^sub>f (pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) ost)))
           \<le> unat bilbyFsMaxEbSize \<Longrightarrow>
           8 + wordarray_length
                (ObjDentry.name\<^sub>f (pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) ost))
           \<le> bilbyFsMaxEbSize + 8"
 by (simp add: bilbyFsMaxEbSize_def)
     unat_arith

lemma ost_pl_4_le_offs_pl_len:
assumes a:" length ys \<le> unat bilbyFsMaxEbSize"
and g: "ost + 8 + walen \<le> offs + Obj.len\<^sub>f obj"
and b:"  unat (walen) \<le> length ys"
and c: "  unat (walen) \<le> unat offs + unat (Obj.len\<^sub>f obj)"
and d:"  (ost::U32) < ost + 8"
and e:"  ost \<le> offs + Obj.len\<^sub>f obj"
and f: "  offs < offs + Obj.len\<^sub>f obj"
and h:"  unat (offs + Obj.len\<^sub>f obj) \<le> length ys"

 shows "unat ost + 4 < unat offs + unat (Obj.len\<^sub>f obj)"
proof -

 from d have d': "ost < ost + 4"
 by (simp add: unat_arith_simps) unat_arith

 have walen_le_max: "walen \<le> bilbyFsMaxEbSize"
  using b a by (simp add: unat_arith_simps)

 have ost_le_max: "ost \<le> bilbyFsMaxEbSize"
   using d e a f h by (simp add: unat_arith_simps bilbyFsMaxEbSize_def)

 obtain ost8 where ost8_def: "ost8 = ost + 8" by simp
 have lc: "ost8 \<le> ost8 + walen"
  proof (rule ccontr)
   assume cpos: "\<not>(ost8 \<le> ost8 + walen)"
   have ost8_neq_m1: "ost8 \<noteq> -1"
    apply (simp add: overflow_plus_one_self[symmetric])
    using ost_le_max ost8_def apply (simp add:  bilbyFsMaxEbSize_def  unat_arith_simps)
    done

   from cpos and walen_le_max have "ost8 \<in> {-1 - bilbyFsMaxEbSize.. -1}"
    apply simp
   using d 
    apply (simp add: bilbyFsMaxEbSize_def unat_arith_simps)
    apply unat_arith
    done
   hence "ost \<in> {-1 - bilbyFsMaxEbSize - 8 .. -1}"
    using d ost8_def
     by (clarsimp simp add: bilbyFsMaxEbSize_def)
      unat_arith

   hence "ost > bilbyFsMaxEbSize"
    by (simp add: bilbyFsMaxEbSize_def unat_arith_simps)

   thus "False"
     using e h f a by unat_arith
  qed

 show ?thesis
  using order_class.order.strict_implies_order[OF d'] 
     order_class.order.strict_implies_order[OF d]
      g 
     lc
   apply (simp add: unat_plus_simple)
   apply (simp only: word_le_nat_alt ost8_def)
   apply unat_arith
  done
qed

lemma ost_pl_4_le_offs_pl_wa_len:
assumes a:" wordarray_length (WordArrayT.make ys) \<le> bilbyFsMaxEbSize"
and g: "ost + 8 + walen \<le> offs + Obj.len\<^sub>f obj"
and b: "walen \<le> wordarray_length (WordArrayT.make ys)"
and c: "walen \<le> offs + (Obj.len\<^sub>f obj)"
and d: "(ost::U32) < ost + 8"
and e: "ost \<le> offs + Obj.len\<^sub>f obj"
and f: "offs < offs + Obj.len\<^sub>f obj"
and h: "offs + Obj.len\<^sub>f obj \<le> wordarray_length (WordArrayT.make ys)"

 shows "unat ost + 4 < unat offs + unat (Obj.len\<^sub>f obj)"
proof -

 from d have d': "ost < ost + 4"
 by (simp add: unat_arith_simps) unat_arith

 have walen_le_max: "walen \<le> bilbyFsMaxEbSize"
  using b a by (simp add: unat_arith_simps)

 have ost_le_max: "ost \<le> bilbyFsMaxEbSize"
   using d e a f h by (simp add: unat_arith_simps bilbyFsMaxEbSize_def)

 obtain ost8 where ost8_def: "ost8 = ost + 8" by simp
 have lc: "ost8 \<le> ost8 + walen"
  proof (rule ccontr)
   assume cpos: "\<not>(ost8 \<le> ost8 + walen)"
   have ost8_neq_m1: "ost8 \<noteq> -1"
    apply (simp add: overflow_plus_one_self[symmetric])
    using ost_le_max ost8_def apply (simp add:  bilbyFsMaxEbSize_def  unat_arith_simps)
    done

   from cpos and walen_le_max have "ost8 \<in> {-1 - bilbyFsMaxEbSize.. -1}"
    apply simp
   using d 
    apply (simp add: bilbyFsMaxEbSize_def unat_arith_simps)
    apply unat_arith
    done
   hence "ost \<in> {-1 - bilbyFsMaxEbSize - 8 .. -1}"
    using d ost8_def
     by (clarsimp simp add: bilbyFsMaxEbSize_def)
      unat_arith

   hence "ost > bilbyFsMaxEbSize"
    by (simp add: bilbyFsMaxEbSize_def unat_arith_simps)

   thus "False"
     using e h f a by unat_arith
  qed

 show ?thesis
  using order_class.order.strict_implies_order[OF d'] 
     order_class.order.strict_implies_order[OF d]
      g 
     lc
   apply (simp add: unat_plus_simple)
   apply (simp only: word_le_nat_alt ost8_def)
   apply unat_arith
  done
qed


lemma fold_triple_append_simp_gen:
 "fold (\<lambda>_ (a, b, c). (f a b, f' b, c @ f'' b)) ns (a, b, xs @ ys) =
  (case fold (\<lambda>_ (a, b, c). (f a b, f' b, c @ f'' b)) ns (a, b, ys) of
   (a, b,c) \<Rightarrow> (a, b, xs @ c))"
  by (induct  ns arbitrary: a b xs ys, simp_all)

lemmas fold_triple_append_simp = fold_triple_append_simp_gen[where ys=Nil, simplified]


lemma pArrObjDentry_slice_eq_induct:
"slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) xs =
   slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) ys \<Longrightarrow>
  offs < ost \<Longrightarrow>
  ost < ost + 8 \<Longrightarrow>
  ost \<le> offs + Obj.len\<^sub>f obj \<Longrightarrow>
  offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
  unat (offs + Obj.len\<^sub>f obj) \<le> length xs \<Longrightarrow>
  unat (offs + Obj.len\<^sub>f obj) \<le> length ys \<Longrightarrow>
  length xs \<le> unat bilbyFsMaxEbSize \<Longrightarrow>
  length ys \<le> unat bilbyFsMaxEbSize \<Longrightarrow>
  dentarr_offs_list_end_offs_pred (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost entriesno (offs + Obj.len\<^sub>f obj) \<Longrightarrow>
  dentarr_offs_list_drop_end_offs_pred (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost entriesno offs (offs + Obj.len\<^sub>f obj) \<Longrightarrow>
  (fold (\<lambda>_ (xsa, doffs, offslist).
                  let dentry = pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) doffs;
                      newoffs = doffs + 8 + wordarray_length (ObjDentry.name\<^sub>f dentry)
                  in (xsa @ [Option.Some dentry], newoffs, offslist @ [newoffs]))
          entriesno
          (accxs, ost, [])) =
     (fold (\<lambda>_ (xs, doffs, offslist).
                  let dentry = pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) doffs;
                      newoffs = doffs + 8 + wordarray_length (ObjDentry.name\<^sub>f dentry)
                  in (xs @ [Option.Some dentry], newoffs, offslist @ [newoffs]))
          entriesno
          (accxs, ost, [])) "
  apply (induct "entriesno" arbitrary:ost accxs)
   apply simp
  apply (simp)
  apply (drule_tac x="ost + 8 + wordarray_length (ObjDentry.name\<^sub>f (pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost))" in meta_spec)
  apply (drule_tac x="accxs @ [Option.Some (pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost)]" in meta_spec)
  apply (erule meta_impE)
   apply (simp add: Let_def dentarr_end_offs_simps)
   apply (subst (asm) snd_fold_append_simp)
   apply (cut_tac ost=ost in wa_length_ObjDentry_name_le[where xs="(take (unat offs + unat (Obj.len\<^sub>f obj)) xs)"])
   apply (subgoal_tac "ost <  ost + 8 +
            wordarray_length (ObjDentry.name\<^sub>f (pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost))")
    apply clarsimp
    apply unat_arith
   apply (subgoal_tac "\<exists>v. 8 +
           wordarray_length (ObjDentry.name\<^sub>f (pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost)) = v")
    apply (erule exE)
    apply (simp only: add.assoc)
    apply (subgoal_tac "v \<le> bilbyFsMaxEbSize + 8")
     apply (clarsimp simp add: )
     apply (erule of_trivial)
      apply unat_arith
     apply (erule x0_le_8_pl_max_eb)
     apply (simp add: plus_no_overflow_unat_lift)
    apply (simp add: unat_arith_simps bilbyFsMaxEbSize_def)
   apply simp
  apply (cut_tac ost=ost in wa_length_ObjDentry_name_le[where xs="(take (unat offs + unat (Obj.len\<^sub>f obj)) xs)"])
  apply (erule meta_impE)
   subgoal for a entriesno ost accxs
    apply (rule max_eb_size_pl_8)
     apply (simp add: dentarr_end_offs_simps Let_def)
     apply (erule_tac x="ost + 8 + wordarray_length (ObjDentry.name\<^sub>f (pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost))" in ballE)
      apply unat_arith
    apply (subst (asm) snd_fold_append_simp, fastforce)
   done

  apply (erule meta_impE)
   subgoal for a entriesno ost accxs
    apply (simp add: dentarr_end_offs_simps Let_def)
    apply (subst (asm) snd_fold_append_simp, fastforce)
   done

  apply (erule meta_impE)
   subgoal for a entriesno ost accxs
    apply (simp add: dentarr_drop_end_offs_simps Let_def)
    apply (subst (asm) snd_fold_append_simp)
    apply (erule_tac x="ost + 8 +
                   wordarray_length
                    (ObjDentry.name\<^sub>f
                      (pObjDentry (List.drop (unat offs) (take (unat offs + unat (Obj.len\<^sub>f obj)) xs))
                        (ost - offs)))" in ballE)
     prefer 2
     apply fastforce
    apply (clarsimp simp add: dentarr_end_offs_simps Let_def)
    apply (rename_tac offs'')
    apply (erule_tac x=offs'' in ballE, fastforce)
    apply (subst (asm) snd_fold_append_simp, fastforce)
   done

  apply (erule meta_impE)
   subgoal for a entriesno ost accxs
    apply (clarsimp simp: Let_def dentarr_drop_end_offs_simps)
    apply (rename_tac offs'')
    apply (subst (asm) snd_fold_append_simp)
    apply clarsimp
    apply (erule_tac x=offs'' in ballE)
     apply assumption
    
    apply (erule notE)
    apply (subgoal_tac "pObjDentry (List.drop (unat offs) (take (unat offs + unat (Obj.len\<^sub>f obj)) xs)) (ost - offs) = pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost")
     apply (simp only:)
    apply (fastforce simp: plus_no_overflow_unat_lift intro: pObjDentry_drop_eq[symmetric])
   done

  apply (simp add: Let_def  dentarr_end_offs_simps)
  apply (subgoal_tac "pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost = pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) ost")
   apply (simp add: Let_def)
   apply (subst fold_triple_append_simp, simp)
   apply (rule sym, subst  fold_triple_append_simp, rule sym, simp)
  apply (erule_tac x="ost + 8 +
                                  wordarray_length
                                   (ObjDentry.name\<^sub>f
                                     (pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost))" in ballE)
   apply clarsimp
   apply (rule pObjDentry_slice_eq)
          apply (erule ost_pl_4_le_offs_pl_len[where ys=xs], fastforce+)
    apply (fastforce dest: order_class.order.strict_implies_order[where a=offs and b=" offs + Obj.len\<^sub>f obj"] simp add: unat_plus_simple)+
  apply (subst (asm) snd_fold_append_simp )
  apply clarsimp
  done

lemma wa_length_ObjDentry_name_bound:
  "offs < ost \<Longrightarrow>
   ost < ost + 8 \<Longrightarrow>
   ost \<le> offs + Obj.len\<^sub>f obj \<Longrightarrow>
   offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
   offs + Obj.len\<^sub>f obj \<le> wordarray_length (WordArrayT.make xs) \<Longrightarrow>
   wordarray_length (ObjDentry.name\<^sub>f (pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost)) 
      \<le> wordarray_length (WordArrayT.make xs)"
  apply (cut_tac wa_length_ObjDentry_name_le[of "take (unat offs + unat (Obj.len\<^sub>f obj)) xs" ost])
  apply (cut_tac length_take[of "unat offs + unat (Obj.len\<^sub>f obj)" xs])
  apply (frule plus_no_overflow_unat_lift[of offs])
  apply (clarsimp simp: word_le_nat_alt unat_plus_simple)
  done

lemma pArrObjDentry_slice_eq_induct':
"slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) xs =
   slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) ys \<Longrightarrow>
  offs < ost \<Longrightarrow>
  ost < ost + 8 \<Longrightarrow>
  ost \<le> offs + Obj.len\<^sub>f obj \<Longrightarrow>
  offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
  offs + Obj.len\<^sub>f obj \<le> wordarray_length (WordArrayT.make xs) \<Longrightarrow>
  offs + Obj.len\<^sub>f obj \<le> wordarray_length (WordArrayT.make ys) \<Longrightarrow>
  wordarray_length (WordArrayT.make xs) \<le> bilbyFsMaxEbSize \<Longrightarrow>
  wordarray_length (WordArrayT.make ys) \<le> bilbyFsMaxEbSize \<Longrightarrow>
  dentarr_offs_list_end_offs_pred (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost entriesno (offs + Obj.len\<^sub>f obj) \<Longrightarrow>
  dentarr_offs_list_drop_end_offs_pred (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost entriesno offs (offs + Obj.len\<^sub>f obj) \<Longrightarrow>
  (fold (\<lambda>_ (xsa, doffs, offslist).
                  let dentry = pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) doffs;
                      newoffs = doffs + 8 + wordarray_length (ObjDentry.name\<^sub>f dentry)
                  in (xsa @ [Option.Some dentry], newoffs, offslist @ [newoffs]))
          entriesno
          (accxs, ost, [])) =
     (fold (\<lambda>_ (xs, doffs, offslist).
                  let dentry = pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) doffs;
                      newoffs = doffs + 8 + wordarray_length (ObjDentry.name\<^sub>f dentry)
                  in (xs @ [Option.Some dentry], newoffs, offslist @ [newoffs]))
          entriesno
          (accxs, ost, [])) "
  apply (induct "entriesno" arbitrary:ost accxs)
   apply simp
  apply (simp)
  apply (drule_tac x="ost + 8 + wordarray_length (ObjDentry.name\<^sub>f (pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost))" in meta_spec)
  apply (drule_tac x="accxs @ [Option.Some (pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost)]" in meta_spec)
  apply (erule meta_impE)
   apply (simp add: Let_def dentarr_end_offs_simps)
   apply (subst (asm) snd_fold_append_simp)
   apply (cut_tac ost = ost in wa_length_ObjDentry_name_bound[of offs _ obj xs]; simp?)
  
   (*apply (subgoal_tac "wordarray_length (ObjDentry.name\<^sub>f (pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost)) \<le> wordarray_length (WordArrayT.make ys)")*)
  thm wa_length_ObjDentry_name_le
   (*apply (cut_tac ost=ost in wa_length_ObjDentry_name_le[where xs="(take (unat offs + unat (Obj.len\<^sub>f obj)) xs)"])*)
   apply (subgoal_tac "ost <  ost + 8 +
            wordarray_length (ObjDentry.name\<^sub>f (pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost))")
    apply clarsimp
    apply unat_arith
   apply (subgoal_tac "\<exists>v. 8 +
           wordarray_length (ObjDentry.name\<^sub>f (pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost)) = v")
    apply (erule exE)
    apply (simp only: add.assoc)
    apply (subgoal_tac "v \<le> bilbyFsMaxEbSize + 8")
     apply (clarsimp simp add: )
     apply (erule of_trivial)
      apply unat_arith
     apply (erule x0_le_8_pl_max_eb')
     apply (simp add: plus_no_overflow_unat_lift)
    apply (simp add: unat_arith_simps bilbyFsMaxEbSize_def)
   apply simp
  apply (cut_tac ost=ost in wa_length_ObjDentry_name_le[where xs="(take (unat offs + unat (Obj.len\<^sub>f obj)) xs)"])
  apply (erule meta_impE)
   subgoal for a entriesno ost accxs
    apply (rule max_eb_size_pl_8)
     apply (simp add: dentarr_end_offs_simps Let_def)
     apply (erule_tac x="ost + 8 + wordarray_length (ObjDentry.name\<^sub>f (pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost))" in ballE)
      apply unat_arith
    apply (subst (asm) snd_fold_append_simp, fastforce)
   done

  apply (erule meta_impE)
   subgoal for a entriesno ost accxs
    apply (simp add: dentarr_end_offs_simps Let_def)
    apply (subst (asm) snd_fold_append_simp, fastforce)
   done

  apply (erule meta_impE)
   subgoal for a entriesno ost accxs
    apply (simp add: dentarr_drop_end_offs_simps Let_def)
    apply (subst (asm) snd_fold_append_simp)
    apply (erule_tac x="ost + 8 +
                   wordarray_length
                    (ObjDentry.name\<^sub>f
                      (pObjDentry (List.drop (unat offs) (take (unat offs + unat (Obj.len\<^sub>f obj)) xs))
                        (ost - offs)))" in ballE)
     prefer 2
     apply fastforce
    apply (clarsimp simp add: dentarr_end_offs_simps Let_def)
    apply (rename_tac offs'')
    apply (erule_tac x=offs'' in ballE, fastforce)
    apply (subst (asm) snd_fold_append_simp, fastforce)
   done

  apply (erule meta_impE)
   subgoal for a entriesno ost accxs
    apply (clarsimp simp: Let_def dentarr_drop_end_offs_simps)
    apply (rename_tac offs'')
    apply (subst (asm) snd_fold_append_simp)
    apply clarsimp
    apply (erule_tac x=offs'' in ballE)
     apply assumption
    
    apply (erule notE)
    apply (subgoal_tac "pObjDentry (List.drop (unat offs) (take (unat offs + unat (Obj.len\<^sub>f obj)) xs)) (ost - offs) = pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost")
     apply (simp only:)
    apply (fastforce simp: plus_no_overflow_unat_lift intro: pObjDentry_drop_eq'[symmetric])
   done

  apply (simp add: Let_def  dentarr_end_offs_simps)
  apply (subgoal_tac "pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost = pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) ost")
   apply (simp add: Let_def)
   apply (subst fold_triple_append_simp, simp)
   apply (rule sym, subst  fold_triple_append_simp, rule sym, simp)
  apply (erule_tac x="ost + 8 +
                                  wordarray_length
                                   (ObjDentry.name\<^sub>f
                                     (pObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) ost))" in ballE)
  apply clarsimp
  apply (frule plus_no_overflow_unat_lift[of offs])
  apply (frule plus_no_overflow_unat_lift)
  apply (cut_tac ost = ost in wa_length_ObjDentry_name_bound[of offs _ obj xs]; simp?)
  apply (cut_tac wordarray_length_leq_length[of "WordArrayT.make xs", simplified wordarray_make])
  apply (cut_tac wordarray_length_leq_length[of "WordArrayT.make ys", simplified wordarray_make])
  apply (rule pObjDentry_slice_eq; simp?)
    apply (erule ost_pl_4_le_offs_pl_wa_len[where ys=xs]; fastforce simp: word_le_nat_alt)
   apply (rule order.trans[of _ "unat (wordarray_length (WordArrayT.make xs))"]; simp add: word_le_nat_alt)
  apply (rule order.trans[of _ "unat (wordarray_length (WordArrayT.make ys))"]; simp add: word_le_nat_alt)
  apply (subst (asm) snd_fold_append_simp )
  apply clarsimp
  done

lemma conj_arg_cong:
 "a = b \<and> c \<Longrightarrow> f a = f b \<and> c"
 by (simp)

lemma pArrObjDentry_slice_eq:
assumes len_type: "is_len_and_type_ok (2, Obj.len\<^sub>f obj)"
assumes slice_eq: " slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) xs =
   slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) ys"
shows"
    offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
    unat (offs + Obj.len\<^sub>f obj) \<le> length xs \<Longrightarrow>
    unat (offs + Obj.len\<^sub>f obj) \<le> length ys \<Longrightarrow>
    length xs \<le> unat bilbyFsMaxEbSize \<Longrightarrow>
    length ys \<le> unat bilbyFsMaxEbSize \<Longrightarrow>
    otype\<^sub>f obj = bilbyFsObjTypeDentarr \<Longrightarrow>
  dentarr_otype_end_offs_pred (otype\<^sub>f obj) (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs+bilbyFsObjHeaderSize) (offs + Obj.len\<^sub>f obj) \<Longrightarrow>
  dentarr_otype_drop_end_offs_st_pred (otype\<^sub>f obj) (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs+bilbyFsObjHeaderSize) offs (offs + Obj.len\<^sub>f obj) \<Longrightarrow>
 (pArrObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs)
      (offs + bilbyFsObjHeaderSize + bilbyFsObjDentarrHeaderSize)
      (ple32 (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs + bilbyFsObjHeaderSize + 8))) =
 (pArrObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) ys)
      (offs + bilbyFsObjHeaderSize + bilbyFsObjDentarrHeaderSize)
      (ple32 (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) (offs + bilbyFsObjHeaderSize + 8)))"
 using assms apply -
  apply (subst ple32_slice_eq[where n=0, simplified] ple64_slice_eq ple32_slice_eq, simp+)
  apply (simp add: is_len_and_type_ok_def otype_simps bilbyFsObjHeaderSize_def, unat_arith)

  apply (simp only: pArrObjDentry_def prod.case_eq_if prod.sel)
  apply simp
  apply (rule conj_arg_cong[where f=ArrayT.make])
  apply simp
  apply (simp only: prod_eq_iff[symmetric])
  apply (erule  pArrObjDentry_slice_eq_induct)
           apply (simp add: is_len_and_type_ok_def otype_simps bilbyFsObjDentarrHeaderSize_def bilbyFsObjHeaderSize_def, unat_arith)
          apply (simp add: is_len_and_type_ok_def otype_simps bilbyFsObjDentarrHeaderSize_def bilbyFsObjHeaderSize_def, simp only: add.commute)
         apply (frule order_class.order.strict_implies_order, simp only: unat_plus_simple)
         apply (simp add: word_less_nat_alt ; unat_arith)
        apply (simp add: is_len_and_type_ok_def otype_simps bilbyFsObjDentarrHeaderSize_def bilbyFsObjHeaderSize_def, simp only: add.commute)
       apply (frule order_class.order.strict_implies_order, simp only: unat_plus_simple)
       apply (simp add: word_less_nat_alt ; unat_arith)
      apply simp+
   apply (simp add: dentarr_end_offs_simps,
          subst ple32_slice_eq[OF slice_eq[symmetric]];
         simp add: is_len_and_type_ok_def otype_simps bilbyFsObjHeaderSize_def, unat_arith?)

   apply (simp add: dentarr_drop_end_offs_simps)
   apply (subst ple32_slice_eq[OF slice_eq[symmetric]], simp+)
   apply (simp add: is_len_and_type_ok_def otype_simps bilbyFsObjHeaderSize_def, unat_arith)
   apply simp
done

lemma pArrObjDentry_slice_eq':
assumes len_type: "is_len_and_type_ok (2, Obj.len\<^sub>f obj)"
assumes slice_eq: " slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) xs =
   slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) ys"
shows"
    offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
    offs + Obj.len\<^sub>f obj \<le> wordarray_length (WordArrayT.make xs) \<Longrightarrow>
    offs + Obj.len\<^sub>f obj \<le> wordarray_length (WordArrayT.make ys) \<Longrightarrow>
    wordarray_length (WordArrayT.make xs) \<le> bilbyFsMaxEbSize \<Longrightarrow>
    wordarray_length (WordArrayT.make ys) \<le> bilbyFsMaxEbSize \<Longrightarrow>
    otype\<^sub>f obj = bilbyFsObjTypeDentarr \<Longrightarrow>
  dentarr_otype_end_offs_pred (otype\<^sub>f obj) (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs+bilbyFsObjHeaderSize) (offs + Obj.len\<^sub>f obj) \<Longrightarrow>
  dentarr_otype_drop_end_offs_st_pred (otype\<^sub>f obj) (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs+bilbyFsObjHeaderSize) offs (offs + Obj.len\<^sub>f obj) \<Longrightarrow>
 (pArrObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) xs)
      (offs + bilbyFsObjHeaderSize + bilbyFsObjDentarrHeaderSize)
      (ple32 (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs + bilbyFsObjHeaderSize + 8))) =
 (pArrObjDentry (take (unat offs + unat (Obj.len\<^sub>f obj)) ys)
      (offs + bilbyFsObjHeaderSize + bilbyFsObjDentarrHeaderSize)
      (ple32 (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) (offs + bilbyFsObjHeaderSize + 8)))"
 using assms apply -
  apply (subst ple32_slice_eq[where n=0, simplified] ple64_slice_eq ple32_slice_eq, simp+)
  apply (simp add: is_len_and_type_ok_def otype_simps bilbyFsObjHeaderSize_def, unat_arith)

  apply (simp only: pArrObjDentry_def prod.case_eq_if prod.sel)
  apply simp
  apply (rule conj_arg_cong[where f=ArrayT.make])
  apply simp
  apply (simp only: prod_eq_iff[symmetric])
  apply (erule  pArrObjDentry_slice_eq_induct')
           apply (simp add: is_len_and_type_ok_def otype_simps bilbyFsObjDentarrHeaderSize_def bilbyFsObjHeaderSize_def, unat_arith)
          apply (simp add: is_len_and_type_ok_def otype_simps bilbyFsObjDentarrHeaderSize_def bilbyFsObjHeaderSize_def, simp only: add.commute)
         apply (frule order_class.order.strict_implies_order, simp only: unat_plus_simple)
         apply (simp add: word_less_nat_alt ; unat_arith)
        apply (simp add: is_len_and_type_ok_def otype_simps bilbyFsObjDentarrHeaderSize_def bilbyFsObjHeaderSize_def, simp only: add.commute)
       apply (frule order_class.order.strict_implies_order, simp only: unat_plus_simple)
       apply (simp add: word_less_nat_alt ; unat_arith)
       apply simp+
   apply (simp add: dentarr_end_offs_simps,
          subst ple32_slice_eq[OF slice_eq[symmetric]];
         simp add: is_len_and_type_ok_def otype_simps bilbyFsObjHeaderSize_def, unat_arith?)

   apply (simp add: dentarr_drop_end_offs_simps)
   apply (subst ple32_slice_eq[OF slice_eq[symmetric]], simp+)
   apply (simp add: is_len_and_type_ok_def otype_simps bilbyFsObjHeaderSize_def, unat_arith)
   apply simp
  done

lemma ple32_slice_eq_4:
"slice (unat offs) (unat offs + unat olen) xs =
 slice (unat offs) (unat offs + unat olen) ys \<Longrightarrow>
  offs < offs + olen \<Longrightarrow>
  bilbyFsObjHeaderSize + n \<le> bilbyFsObjHeaderSize + n + 4 \<Longrightarrow>
  bilbyFsObjHeaderSize + n + 4 \<le> olen \<Longrightarrow>
  ple32 xs (offs + bilbyFsObjHeaderSize + n) =
  ple32 ys (offs + bilbyFsObjHeaderSize + n)"
  apply (simp add: ple32_def)
  apply (rule arg_cong[where f=word_rcat])
  apply (rule arg_cong[where f=rev])
  apply (subgoal_tac "\<exists>v. bilbyFsObjHeaderSize + n = v")
   apply (erule exE)
   apply (simp add: add.assoc)
   apply (subgoal_tac "offs \<le> offs + v")
    prefer 2
    apply (simp add: unat_arith_simps)
    apply unat_arith
   apply (simp add: slice_def bilbyFsObjHeaderSize_def word_le_plus[simplified unat_plus_simple])
   apply (simp add: take_drop)
   apply (erule slice_sub_slice[simplified slice_def fun_app_def])
       apply (drule less_to_le, simp add: unat_plus_simple| simp only: word_le_nat_alt )+
 done

lemma pObjDentarr_slice_eq:
 "is_len_and_type_ok (2, Obj.len\<^sub>f obj) \<Longrightarrow>
  slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) xs =
  slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) ys \<Longrightarrow>
  offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
  unat (offs + Obj.len\<^sub>f obj) \<le> length xs \<Longrightarrow>
  length xs \<le> unat bilbyFsMaxEbSize \<Longrightarrow>
  length ys \<le> unat bilbyFsMaxEbSize \<Longrightarrow>
  unat offs + unat (Obj.len\<^sub>f obj) \<le> length xs \<Longrightarrow>
  unat offs + unat (Obj.len\<^sub>f obj) \<le> length ys \<Longrightarrow>
  (otype\<^sub>f obj) = bilbyFsObjTypeDentarr \<Longrightarrow>
  dentarr_otype_end_offs_pred (otype\<^sub>f obj) (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs+bilbyFsObjHeaderSize) (offs + Obj.len\<^sub>f obj) \<Longrightarrow>
  dentarr_otype_drop_end_offs_st_pred (otype\<^sub>f obj) (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs+bilbyFsObjHeaderSize) offs (offs + Obj.len\<^sub>f obj) \<Longrightarrow>

    pObjDentarr (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs + bilbyFsObjHeaderSize) (Obj.len\<^sub>f obj) =
    pObjDentarr (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) (offs + bilbyFsObjHeaderSize) (Obj.len\<^sub>f obj)"
  apply (simp add: pObjDentarr_def ObjDentarr.make_def Let_def)
  apply (subst ple64_slice_eq[where n=0, simplified] ple64_slice_eq ple32_slice_eq,
        ((simp add: otype_simps len_otype_ok bilbyFsObjHeaderSize_def unat_arith_simps)[2])+, simp)+

  apply (frule less_to_le)
  apply (simp add: unat_plus_simple)
  apply (rule arg_cong[where f=prod.fst])
  apply (rule pArrObjDentry_slice_eq)
      apply (simp add: unat_plus_simple)+
  done

lemma pObjDentarr_slice_eq':
 "is_len_and_type_ok (2, Obj.len\<^sub>f obj) \<Longrightarrow>
  slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) xs =
  slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) ys \<Longrightarrow>
  offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
  wordarray_length (WordArrayT.make xs) \<le> bilbyFsMaxEbSize \<Longrightarrow>
  wordarray_length (WordArrayT.make ys) \<le> bilbyFsMaxEbSize \<Longrightarrow>
  offs + (Obj.len\<^sub>f obj) \<le> wordarray_length (WordArrayT.make xs) \<Longrightarrow>
  offs + (Obj.len\<^sub>f obj) \<le> wordarray_length (WordArrayT.make ys) \<Longrightarrow>
  (otype\<^sub>f obj) = bilbyFsObjTypeDentarr \<Longrightarrow>
  dentarr_otype_end_offs_pred (otype\<^sub>f obj) (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs+bilbyFsObjHeaderSize) (offs + Obj.len\<^sub>f obj) \<Longrightarrow>
  dentarr_otype_drop_end_offs_st_pred (otype\<^sub>f obj) (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs+bilbyFsObjHeaderSize) offs (offs + Obj.len\<^sub>f obj) \<Longrightarrow>

    pObjDentarr (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs + bilbyFsObjHeaderSize) (Obj.len\<^sub>f obj) =
    pObjDentarr (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) (offs + bilbyFsObjHeaderSize) (Obj.len\<^sub>f obj)"
  apply (simp add: pObjDentarr_def ObjDentarr.make_def Let_def)
  apply (subst ple64_slice_eq[where n=0, simplified] ple64_slice_eq ple32_slice_eq,
        ((simp add: otype_simps len_otype_ok bilbyFsObjHeaderSize_def unat_arith_simps)[2])+, simp)+

  apply (frule less_to_le)
  apply (simp add: unat_plus_simple)
  apply (rule arg_cong[where f=prod.fst])
  apply (rule pArrObjDentry_slice_eq')
      apply (simp add: unat_plus_simple)+
  done

lemma pObjSuper_slice_eq:
 "is_len_and_type_ok (4, Obj.len\<^sub>f obj) \<Longrightarrow>
  slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) xs =
   slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) ys \<Longrightarrow>
   offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
    pObjSuper (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs + bilbyFsObjHeaderSize) =
    pObjSuper (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) (offs + bilbyFsObjHeaderSize)"
  apply (simp add: pObjSuper_def ObjSuper.make_def Let_def)
  apply (subst ple32_slice_eq[where n=0, simplified] ple64_slice_eq ple32_slice_eq,
        ((simp add: otype_simps len_otype_ok bilbyFsObjHeaderSize_def unat_arith_simps)[2])+, simp)+
 done

lemma pObjUnion_slice_eq:
 "is_len_and_type_ok (otype\<^sub>f obj, Obj.len\<^sub>f obj) \<Longrightarrow>
  slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) xs =
  slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) ys \<Longrightarrow>
  offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
  unat (offs + Obj.len\<^sub>f obj) \<le> length xs \<Longrightarrow>
  length xs \<le> unat bilbyFsMaxEbSize \<Longrightarrow>
  length ys \<le> unat bilbyFsMaxEbSize \<Longrightarrow>
  unat offs + unat (Obj.len\<^sub>f obj) \<le> length xs \<Longrightarrow>
  unat offs + unat (Obj.len\<^sub>f obj) \<le> length ys \<Longrightarrow>
  pObjHeader ys offs = obj \<Longrightarrow>
  dentarr_otype_end_offs_pred (otype\<^sub>f obj) (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs+bilbyFsObjHeaderSize) (offs + Obj.len\<^sub>f obj) \<Longrightarrow>
  dentarr_otype_drop_end_offs_st_pred (otype\<^sub>f obj) (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs+bilbyFsObjHeaderSize) offs (offs + Obj.len\<^sub>f obj) \<Longrightarrow>

  pObjUnion (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (otype\<^sub>f obj) (Obj.len\<^sub>f obj)
     (offs + bilbyFsObjHeaderSize) =
  pObjUnion (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) (otype\<^sub>f obj) (Obj.len\<^sub>f obj)
     (offs + bilbyFsObjHeaderSize)"
  apply (simp add: pObjUnion_def')
  apply (case_tac "otype\<^sub>f (pObjHeader ys offs) = 0")
   apply (simp, rule pObjInode_slice_eq, simp+)
  apply (case_tac "otype\<^sub>f (pObjHeader ys offs) = 1")
   apply (simp, rule pObjData_slice_eq, simp+)
  apply (case_tac "otype\<^sub>f (pObjHeader ys offs) = 2")
   apply (simp)
   apply (rule pObjDentarr_slice_eq, (simp add: bilbyFsObjTypeDentarr_def )+)
  apply (case_tac "otype\<^sub>f (pObjHeader ys offs) = 3")
   apply (simp, rule pObjDel_slice_eq, simp+)
  apply (case_tac "otype\<^sub>f (pObjHeader ys offs) = 4")
   apply (simp, rule pObjSuper_slice_eq, simp+)
  done

lemma pObjUnion_slice_eq':
 "is_len_and_type_ok (otype\<^sub>f obj, Obj.len\<^sub>f obj) \<Longrightarrow>
  slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) xs =
  slice (unat offs) (unat offs + unat (Obj.len\<^sub>f obj)) ys \<Longrightarrow>
  offs < offs + Obj.len\<^sub>f obj \<Longrightarrow>
  wordarray_length (WordArrayT.make xs) \<le> bilbyFsMaxEbSize \<Longrightarrow>
  wordarray_length (WordArrayT.make ys) \<le> bilbyFsMaxEbSize \<Longrightarrow>
  offs + (Obj.len\<^sub>f obj) \<le> wordarray_length (WordArrayT.make xs) \<Longrightarrow>
  offs + (Obj.len\<^sub>f obj) \<le> wordarray_length (WordArrayT.make ys) \<Longrightarrow>
  pObjHeader ys offs = obj \<Longrightarrow>
  dentarr_otype_end_offs_pred (otype\<^sub>f obj) (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs+bilbyFsObjHeaderSize) (offs + Obj.len\<^sub>f obj) \<Longrightarrow>
  dentarr_otype_drop_end_offs_st_pred (otype\<^sub>f obj) (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (offs+bilbyFsObjHeaderSize) offs (offs + Obj.len\<^sub>f obj) \<Longrightarrow>

  pObjUnion (take (unat offs + unat (Obj.len\<^sub>f obj)) xs) (otype\<^sub>f obj) (Obj.len\<^sub>f obj)
     (offs + bilbyFsObjHeaderSize) =
  pObjUnion (take (unat offs + unat (Obj.len\<^sub>f obj)) ys) (otype\<^sub>f obj) (Obj.len\<^sub>f obj)
     (offs + bilbyFsObjHeaderSize)"
  apply (simp add: pObjUnion_def')
  apply (case_tac "otype\<^sub>f (pObjHeader ys offs) = 0")
   apply (simp, rule pObjInode_slice_eq, simp+)
  apply (case_tac "otype\<^sub>f (pObjHeader ys offs) = 1")
   apply (simp, rule pObjData_slice_eq, simp+)
  apply (case_tac "otype\<^sub>f (pObjHeader ys offs) = 2")
   apply (simp)
   apply (rule pObjDentarr_slice_eq', (simp add: bilbyFsObjTypeDentarr_def )+)
  apply (case_tac "otype\<^sub>f (pObjHeader ys offs) = 3")
   apply (simp, rule pObjDel_slice_eq, simp+)
  apply (case_tac "otype\<^sub>f (pObjHeader ys offs) = 4")
   apply (simp, rule pObjSuper_slice_eq, simp+)
  done


lemma pObj_eq:
 "is_valid_ObjHeader hdr ys \<Longrightarrow>
  dentarr_otype_end_offs_pred (otype\<^sub>f hdr) (take (unat (offs + Obj.len\<^sub>f hdr)) ys) (offs+bilbyFsObjHeaderSize) (offs + Obj.len\<^sub>f hdr) \<Longrightarrow>
  dentarr_otype_drop_end_offs_st_pred (otype\<^sub>f hdr) (take (unat (offs + Obj.len\<^sub>f hdr)) ys) (offs+bilbyFsObjHeaderSize) offs (offs + Obj.len\<^sub>f hdr) \<Longrightarrow>
  hdr = pObjHeader ys offs \<Longrightarrow>
  slice (unat offs) (unat offs + unat (Obj.len\<^sub>f hdr)) xs = slice (unat offs) (unat offs + unat (Obj.len\<^sub>f hdr)) ys \<Longrightarrow>
   offs < offs + Obj.len\<^sub>f hdr \<Longrightarrow>
 is_len_and_type_ok (otype\<^sub>f hdr, Obj.len\<^sub>f hdr) \<Longrightarrow>
  unat offs + unat (Obj.len\<^sub>f hdr) \<le> length xs \<Longrightarrow>
  unat offs + unat (Obj.len\<^sub>f hdr) \<le> length ys \<Longrightarrow>
  length ys \<le> unat bilbyFsMaxEbSize \<Longrightarrow>
  length xs \<le> unat bilbyFsMaxEbSize \<Longrightarrow>
 pObj xs offs = pObj ys offs"
   apply (simp (no_asm) add: pObj_def Let_def)
  apply (subgoal_tac "offs < offs + bilbyFsObjHeaderSize")
   apply (frule is_valid_ObjHeader_len)
   apply (frule (4) pObjHeader_slice_eq)
   apply (simp only: pObjHeader_take_olen[where xs=xs,symmetric])
  apply (subst  pObjHeader_take_olen[where xs=ys,symmetric], assumption+)+
   apply (rule trans[OF Obj.surjective])
   apply (rule sym)
   apply (rule trans[OF Obj.surjective])
   apply (simp add: is_valid_ObjHeader_def)
   apply (frule order_class.order.strict_implies_order[where b="offs + Obj.len\<^sub>f (pObjHeader ys offs)"])
   apply (rule pObjUnion_slice_eq, simp+)
         apply (simp only: unat_plus_simple)+
     apply (erule (1) pObjHeader_take_olen[symmetric])
     apply (clarsimp simp add: plus_no_overflow_unat_lift)+
  apply (frule is_valid_ObjHeader_len_facts)
  apply (clarsimp simp add: bilbyFsObjHeaderSize_def, unat_arith)
  done

lemma pObj_eq':
 "is_valid_ObjHeader hdr ys \<Longrightarrow>
  dentarr_otype_end_offs_pred (otype\<^sub>f hdr) (take (unat (offs + Obj.len\<^sub>f hdr)) ys) (offs+bilbyFsObjHeaderSize) (offs + Obj.len\<^sub>f hdr) \<Longrightarrow>
  dentarr_otype_drop_end_offs_st_pred (otype\<^sub>f hdr) (take (unat (offs + Obj.len\<^sub>f hdr)) ys) (offs+bilbyFsObjHeaderSize) offs (offs + Obj.len\<^sub>f hdr) \<Longrightarrow>
  hdr = pObjHeader ys offs \<Longrightarrow>
  slice (unat offs) (unat offs + unat (Obj.len\<^sub>f hdr)) xs = slice (unat offs) (unat offs + unat (Obj.len\<^sub>f hdr)) ys \<Longrightarrow>
   offs < offs + Obj.len\<^sub>f hdr \<Longrightarrow>
  is_len_and_type_ok (otype\<^sub>f hdr, Obj.len\<^sub>f hdr) \<Longrightarrow>
  offs + (Obj.len\<^sub>f hdr) \<le> wordarray_length (WordArrayT.make xs) \<Longrightarrow>
  offs + (Obj.len\<^sub>f hdr) \<le> wordarray_length (WordArrayT.make ys) \<Longrightarrow>
  wordarray_length (WordArrayT.make xs) \<le> bilbyFsMaxEbSize \<Longrightarrow>
  wordarray_length (WordArrayT.make ys) \<le> bilbyFsMaxEbSize \<Longrightarrow>
  pObj xs offs = pObj ys offs"
   apply (simp (no_asm) add: pObj_def Let_def)
  apply (subgoal_tac "offs < offs + bilbyFsObjHeaderSize")
   apply (frule is_valid_ObjHeader_len)
  apply (frule plus_no_overflow_unat_lift)
   apply (frule pObjHeader_slice_eq[rotated 1]; simp?)
     apply (rule order.trans[OF _ wordarray_length_leq_length[of "WordArrayT.make _", simplified wordarray_make]])
     apply (simp add: word_le_nat_alt)
    apply (rule order.trans[OF _ wordarray_length_leq_length[of "WordArrayT.make _", simplified wordarray_make]])
    apply (simp add: word_le_nat_alt)
   apply (simp only: pObjHeader_take_olen[where xs=xs,symmetric])
  apply (subst  pObjHeader_take_olen[where xs=ys,symmetric], assumption+)+
   apply (rule trans[OF Obj.surjective])
   apply (rule sym)
   apply (rule trans[OF Obj.surjective])
   apply (simp add: is_valid_ObjHeader_def)
   apply (frule order_class.order.strict_implies_order[where b="offs + Obj.len\<^sub>f (pObjHeader ys offs)"])
   apply (rule pObjUnion_slice_eq', simp+)
         apply (simp only: unat_plus_simple)+
     apply (erule (1) pObjHeader_take_olen[symmetric])
     apply (clarsimp simp add: plus_no_overflow_unat_lift)+
  apply (frule is_valid_ObjHeader_len_facts)
  apply (clarsimp simp add: bilbyFsObjHeaderSize_def, unat_arith)
 done

lemma slice_Nil:
 "length xs \<le> n \<Longrightarrow> slice n m xs = []"
 by (simp add: slice_def)

lemma slice_append':
 "m \<le> length xs \<Longrightarrow>
 slice n m (xs @ ys) = slice n m xs"
 by (simp add: slice_def)

lemma slice_eq:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     oaddr: "\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid = TypBucket.Some oaddr"
  and     xdef: "ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st) = x"
  and     ydef: "align32 (ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr, io_size\<^sub>f (super\<^sub>f mount_st)) = y"
  and     ebnum: "ObjAddr.ebnum\<^sub>f oaddr \<noteq> wbuf_eb\<^sub>f ostore_st"
  and  ubibdef: "\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) !
       unat (ObjAddr.ebnum\<^sub>f oaddr) = ubib"
  and  soffsdef: "(ObjAddr.offs\<^sub>f oaddr + 0x10) = soffs"
  shows
 "slice (unat soffs) (unat soffs + 4) (buf_take (rbuf\<^sub>f ostore_st) x @ slice (unat x) (unat x + unat (y - x)) (ubib @ replicate (unat (y - x)) 0xFF) @
     buf_drop (rbuf\<^sub>f ostore_st) y) =
    slice (unat soffs) (unat soffs + 4) ubib"
proof -
 have lenx: "length (buf_take (rbuf\<^sub>f ostore_st) x) = unat x"
   using oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
             inv_ostore_rbuf_lengthD[OF inv_ostore, simplified buf_length_def Let_def]
             wordarray_length_leq_length[of "data\<^sub>f (rbuf\<^sub>f ostore_st)"]
  by (clarsimp simp add: buf_simps xdef[symmetric] is_valid_addr_def)
   unat_arith

  have soffs_no_of: "soffs < soffs + 4"
  using oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
  by (clarsimp simp add: soffsdef[symmetric] is_valid_addr_def
    bilbyFsMinObjSize_def bilbyFsObjHeaderSize_def)
    unat_arith

 have x_le_soffs: "x \<le> soffs"
  using oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
  by (clarsimp simp add: xdef[symmetric] soffsdef[symmetric] is_valid_addr_def bilbyFsMinObjSize_def bilbyFsObjHeaderSize_def)
    unat_arith

   have x_le_soffs4: "unat x \<le> unat soffs + 4"
    using x_le_soffs soffs_no_of by unat_arith

  have  soffs4_le_y: "soffs + 4 \<le> y"
  using oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
        oaddr_offs_pl_objhdr_le_align[OF inv_ostore inv_mount_st oaddr]
  by (clarsimp simp add: ydef[symmetric] soffsdef[symmetric] bilbyFsObjHeaderSize_def is_valid_addr_def bilbyFsMinObjSize_def)
   unat_arith

  have y_arith: "unat x + unat (y - x) = unat y"
   using  x_le_soffs  soffs4_le_y soffs_no_of
    by unat_arith

  have soffs_x_dance: "(unat soffs - unat x + unat x) = unat soffs"
  using  le_add_diff_inverse2[OF x_le_soffs[simplified unat_arith_simps]] .
  
  have  lenubib: "length ubib = unat (eb_size\<^sub>f (super\<^sub>f mount_st))"
    using oaddr_ebnum_rangeD[OF inv_ostore inv_mount_st oaddr ebnum]
          inv_bufsD[OF inv_ostore]
          ebnum
          ubibdef[symmetric]
    by simp
  
 show ?thesis
  apply (subst slice_append)
  apply (simp add: lenx x_le_soffs4 min_absorb1)
   apply (simp add: slice_Nil lenx  x_le_soffs[simplified unat_arith_simps])
   apply (simp add: y_arith)
   apply (subst slice_append')
    apply (simp add: length_slice lenubib)
    apply (subst min_absorb2)
     apply (simp add: ydef[symmetric])
     using align32_le_eb_size[OF inv_ostore inv_mount_st oaddr, simplified word_le_nat_alt]
    apply (simp add:)
   using soffs4_le_y soffs_no_of 
   apply (simp add: unat_arith_simps)
   apply unat_arith
  apply (subst slice_append')
   apply (simp add: lenubib ydef[symmetric])
   using align32_le_eb_size[OF inv_ostore inv_mount_st oaddr, simplified word_le_nat_alt]
   apply simp
  apply (simp add: slice_def)
  using x_le_soffs x_le_soffs4 soffs4_le_y[simplified ]
  apply (simp add: take_drop )
  apply (subst min_absorb1)
   using soffs_no_of
   apply (simp add: unat_arith_simps, unat_arith)
  apply (simp add: soffs_x_dance)
 done
qed

lemma slice_eq2:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     oaddr: "\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid = TypBucket.Some oaddr"
  and     xdef: "ObjAddr.offs\<^sub>f oaddr - ObjAddr.offs\<^sub>f oaddr mod io_size\<^sub>f (super\<^sub>f mount_st) = x"
  and  ydef: "align32 (ObjAddr.offs\<^sub>f oaddr + ObjAddr.len\<^sub>f oaddr, io_size\<^sub>f (super\<^sub>f mount_st)) = y"
  and     ebnum: "ObjAddr.ebnum\<^sub>f oaddr \<noteq> wbuf_eb\<^sub>f ostore_st"
  and  ubibdef: "\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) !
       unat (ObjAddr.ebnum\<^sub>f oaddr) = ubib"
  and  offs: "ObjAddr.offs\<^sub>f oaddr = offs"
  and  olen: "(Obj.len\<^sub>f
                (pObjHeader (\<alpha>wa (data\<^sub>f (read_pages_rbuf (rbuf\<^sub>f ostore_st) x (y - x) ubib)))
                  (ObjAddr.offs\<^sub>f oaddr))) = olen"
  and  olen_oaddr: "ObjAddr.len\<^sub>f oaddr = olen"
  shows
 "slice (unat offs) (unat offs + unat olen) ubib =
  slice (unat offs) (unat offs + unat olen)
  (\<alpha>wa (data\<^sub>f (read_pages_rbuf (rbuf\<^sub>f ostore_st) x (y - x) ubib)))"
proof -
 have lenx: "length (buf_take (rbuf\<^sub>f ostore_st) x) = unat x"
   using oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
         inv_ostore_rbuf_lengthD[OF inv_ostore, simplified buf_length_def Let_def]
         wordarray_length_leq_length[of "data\<^sub>f (rbuf\<^sub>f ostore_st)"]
  by (clarsimp simp add: buf_simps xdef[symmetric] is_valid_addr_def)
   unat_arith

  have offs_no_of: "offs < offs + olen"
  using oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
  by (clarsimp simp add: offs[symmetric] olen[symmetric] is_valid_addr_def
    bilbyFsMinObjSize_def bilbyFsObjHeaderSize_def olen_oaddr)

 have x_le_soffs: "x \<le> offs"
  using oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
  by (clarsimp simp add: xdef[symmetric] offs[symmetric] is_valid_addr_def bilbyFsMinObjSize_def bilbyFsObjHeaderSize_def)
    unat_arith


   have x_le_offsolen: "unat x \<le> unat offs + unat olen"
    using x_le_soffs offs_no_of by unat_arith

  have  offsolen_le_y: "offs + olen \<le> y"
  using oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
         oaddr_offs_pl_olen_le_align[OF inv_ostore inv_mount_st oaddr]
  by (clarsimp simp add: ydef[symmetric] olen_oaddr[symmetric] offs[symmetric]
    is_valid_addr_def)

  have y_arith: "unat x + unat (y - x) = unat y"
   using  x_le_soffs  offsolen_le_y offs_no_of
    by unat_arith

  have soffs_x_dance: "(unat offs - unat x + unat x) = unat offs"
  using  le_add_diff_inverse2[OF x_le_soffs[simplified unat_arith_simps]] .
  
  have  lenubib: "length ubib = unat (eb_size\<^sub>f (super\<^sub>f mount_st))"
   using oaddr_is_valid_addr[OF inv_ostore inv_mount_st oaddr]
         ebnum
         inv_bufsD[OF inv_ostore]
         oaddr_ebnum_rangeD[OF inv_ostore inv_mount_st oaddr ebnum]
   by (clarsimp simp add: ubibdef[symmetric] is_valid_addr_def)
  
 show ?thesis
  apply (simp add: read_pages_rbuf_def wordarray_make)
  apply (subst slice_append)
  apply (simp add: lenx x_le_offsolen min_absorb1)
  apply (simp add: slice_Nil lenx  x_le_soffs[simplified unat_arith_simps])
  apply (simp add: y_arith)
  apply (subst slice_append')
   apply (simp add: length_slice lenubib)
   apply (subst min_absorb2)
    apply (simp add: ydef[symmetric])
    using align32_le_eb_size[OF inv_ostore inv_mount_st oaddr, simplified word_le_nat_alt]
    apply (simp add:)
   using offsolen_le_y offs_no_of 
   apply (simp add: unat_arith_simps)
   apply unat_arith
  apply (subst slice_append')
   apply (simp add: lenubib ydef[symmetric])
   using align32_le_eb_size[OF inv_ostore inv_mount_st oaddr, simplified word_le_nat_alt]
   apply simp
  apply (simp add: slice_def)
  using x_le_soffs x_le_offsolen offsolen_le_y[simplified ]
  apply (simp add: take_drop )
  apply (subst min_absorb1)
   using offs_no_of
   apply (simp add: unat_arith_simps, unat_arith)
  apply (simp add: soffs_x_dance)
 done
qed

lemma ple32_take_eq:
 "offs = offs' \<Longrightarrow>
slice (unat offs) (unat offs + 4) xs = slice (unat offs) (unat offs + 4) ys  \<Longrightarrow>
ple32 xs offs = ple32 ys offs'"
by (simp add: ple32_def slice_def drop_take)

lemma is_valid_ObjHeader_is_len_and_type_okD:
 "is_valid_ObjHeader hdr data \<Longrightarrow> is_len_and_type_ok (otype\<^sub>f hdr,Obj.len\<^sub>f hdr)"
 by (simp add: is_valid_ObjHeader_def)

lemma unat_lift_plus_simpleE:
 "(a::'a:: len word) < a + b \<Longrightarrow> a + b  \<le> c \<Longrightarrow>
  unat a + unat b \<le> unat c"
  by unat_arith

lemma handy_lemma: "a = Some b \<Longrightarrow> the a = b"
  by simp

lemma ostore_read_ret:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  assumes inv_mount_st: "inv_mount_st mount_st"
  assumes inv_\<alpha>_ostore: "inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st)"
  assumes suc: 
    "\<And>ex' ostore_st' obj.\<lbrakk> inv_ostore mount_st ostore_st';
    \<alpha>_ostore_uptodate ostore_st' oid = option.Some obj;
    inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st');
    \<alpha>_ostore_medium ostore_st' = \<alpha>_ostore_medium ostore_st;
    \<alpha>_updates ostore_st' = \<alpha>_updates ostore_st\<rbrakk> \<Longrightarrow> 
    P ((ex', ostore_st'), Success obj)"
  assumes err: 
    "\<And>ex' ostore_st' e.\<lbrakk> inv_ostore mount_st ostore_st' ;
    e \<in> {eIO, eNoMem, eInval, eBadF, eNoEnt};
    e = eNoEnt \<longleftrightarrow> \<alpha>_ostore_uptodate ostore_st' oid = option.None;
    inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st');
    \<alpha>_ostore_medium ostore_st' = \<alpha>_ostore_medium ostore_st;
    \<alpha>_updates ostore_st' = \<alpha>_updates ostore_st \<rbrakk> \<Longrightarrow> 
    P ((ex', ostore_st'), Error e)"
  shows "P (ostore_read (ex, mount_st, ostore_st, oid))"
  using [[goals_limit=1]]
  unfolding ostore_read_def[unfolded tuple_simps sanitizers]
  apply (clarsimp simp add: Let_def )
  apply (rule index_get_addr_ret)
   apply (simp add: error_def)
   apply (rule err[OF inv_ostore _ _ inv_\<alpha>_ostore])
      apply simp
     apply simp
     apply (simp add: dom_def )
  using dom_uptodate_eq_dom_index[OF inv_ostore]
     apply (simp add: )
     apply auto[1]
    apply simp
   apply simp
  apply simp
  apply (clarsimp)
  apply (rename_tac oaddr)
  apply (rule conjI)
   apply (clarsimp simp: Let_def)
   apply (rule deserialise_Obj_ret')
  using inv_ostore_wbuf_lengthD[OF inv_ostore, simplified buf_length_def Let_def] 
    inv_ostore_usedD[OF inv_ostore]
        apply (simp add:  wellformed_buf'_def )
  using inv_mount_st_eb_size_boundD[OF inv_mount_st]
    inv_ostore_wbuf_lengthD[OF inv_ostore, simplified buf_length_def Let_def]
       apply (simp add:)
      apply simp
      apply (erule (1) offs_pl_olen_le_used[OF inv_ostore ])
     apply (erule (1) offs_lt_offs_pl_hdr[OF inv_ostore])
    apply (simp add: error_def) (* try remove success_def *)
    apply (rule err)
         apply (simp add: inv_ostore_bound_upd[OF inv_ostore])
        apply force
       apply (rename_tac e)
       apply (subgoal_tac "e \<noteq> eNoEnt")
        prefer 2
        apply (force simp add: error_code_simps)
       apply (simp add: inv_ostore_runtimeD[OF inv_ostore_bound_upd[OF inv_ostore],symmetric] \<alpha>_index_def \<alpha>_ostore_runtime_def)
      apply (simp add: inv_\<alpha>_ostore_wbuf_bound_eq_eb_size[OF inv_ostore inv_\<alpha>_ostore])
     apply (simp add: \<alpha>_ostore_medium_def)
    apply (simp add: \<alpha>_updates_def buf_simps)
   apply (clarsimp split: R.splits)
   apply(rule conjI)
    prefer 2
    apply clarsimp
    apply(rule conjI)
     apply clarsimp
     apply (rule suc[OF inv_ostore_bound_upd[OF inv_ostore]])
        apply (drule sym[where s=oid])
        apply simp
  using inv_ostore_indexD[OF inv_ostore]
        apply (simp add: inv_ostore_index_def \<alpha>_index_def)
        apply (erule_tac x=oid in ballE)
  using inv_ostore_runtimeD[OF inv_ostore_bound_upd[OF inv_ostore],symmetric]
         apply(clarsimp simp: Let_def ostore_get_obj_def \<alpha>_ostore_runtime_def \<alpha>_index_def)
         apply (simp add: pObj_take pObj_offs success_def)
        apply clarsimp
       apply (simp add: inv_\<alpha>_ostore_wbuf_bound_eq_eb_size[OF inv_ostore inv_\<alpha>_ostore])
      apply (simp add: \<alpha>_ostore_medium_def)
     apply (simp add: \<alpha>_updates_def buf_simps)
    apply(clarsimp simp: success_def)
    apply (rule err)
         apply (simp add: inv_ostore_bound_upd[OF inv_ostore])
        apply (erule notE)
  using inv_ostore_indexD[OF inv_ostore]
        apply (simp add: inv_ostore_index_def)
        apply (erule_tac x=oid in ballE)
         apply (clarsimp simp add: Let_def ostore_get_obj_def)
         apply (frule handy_lemma[THEN sym])
         apply (simp add: \<alpha>_index_def pObj_take get_obj_oid_offs_agnostic)
         apply (subst pObj_take[symmetric]; simp)
        apply (simp add: dom_def \<alpha>_index_def)
       apply (simp add: error_code_simps)
    (* Copy-pasted (and tweaked) from above, begin: *)
  using inv_ostore_indexD[OF inv_ostore]
       apply (simp add: inv_ostore_index_def \<alpha>_index_def)
       apply (erule_tac x=oid in ballE)
        apply (simp add: )
  using inv_ostore_runtimeD[OF inv_ostore_bound_upd[OF inv_ostore],symmetric]
        apply (rule_tac x="pObj (\<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st))) (ObjAddr.offs\<^sub>f oaddr)" in exI)
        apply (clarsimp simp add: Let_def \<alpha>_ostore_runtime_def \<alpha>_index_def ostore_get_obj_def)
        apply (simp add: pObj_take pObj_offs)
    (* End *)
       apply (simp add: dom_def)
      apply (simp add: inv_\<alpha>_ostore_wbuf_bound_eq_eb_size[OF inv_ostore inv_\<alpha>_ostore])
     apply (simp add: \<alpha>_ostore_medium_def)
    apply (simp add: \<alpha>_updates_def buf_simps)
   apply(simp add: success_def)
  apply clarsimp
  apply (frule handy_lemma[THEN sym])
  apply (rule read_obj_pages_in_buf_ret'[OF inv_ostore inv_mount_st,where oid=oid])
     apply (fastforce simp add: dom_def)+
   apply (simp add: error_def)
   apply (rule err)
        apply clarsimp
        apply (rule_tac b="bound\<^sub>f buf'" in  inv_ostore_rbuf_agnostic[OF inv_ostore], simp)
        apply assumption
       apply simp
      apply (clarsimp simp add: error_code_simps)
      apply (simp add: \<alpha>_ostore_uptodate_rbuf_agnostic inv_ostore_runtimeD[OF inv_ostore,symmetric])
      apply (fastforce simp add: \<alpha>_ostore_runtime_def \<alpha>_index_def \<alpha>_updates_def \<alpha>_ostore_medium_def split:option.splits)
  using inv_\<alpha>_ostore apply (simp add: \<alpha>_ostore_uptodate_def \<alpha>_index_def \<alpha>_updates_def \<alpha>_ostore_medium_def)
    apply (simp add: \<alpha>_ostore_medium_def)
   apply (simp add: \<alpha>_updates_def buf_simps)
  apply clarsimp
  apply (erule deserialise_Obj_ret')
      apply simp
      apply (drule length_eq_imp_wordarray_length_eq; simp)
  using inv_ostore_rbuf_lengthD[OF inv_ostore, simplified buf_length_def Let_def]
    inv_mount_st_eb_size_boundD[OF inv_mount_st]
      apply unat_arith
     apply (simp add: read_pages_rbuf_def)
     apply (erule oaddr_offs_pl_objhdr_le_align[OF inv_ostore inv_mount_st])
    apply (drule oaddr_is_valid_addr[OF inv_ostore inv_mount_st])
    apply (clarsimp simp add: is_valid_addr_def bilbyFsObjHeaderSize_def bilbyFsMinObjSize_def)
    apply unat_arith
   apply(simp add: error_def)
   apply (rule err)
        apply (rule inv_ostore_rbuf_agnostic[OF inv_ostore, where v="data\<^sub>f (rbuf\<^sub>f ostore_st)" and b="bound\<^sub>f (rbuf\<^sub>f ostore_st)"])
         apply simp
        apply (simp add:  )
        apply (drule length_eq_imp_wordarray_length_eq)
  using inv_ostore_rbuf_lengthD[OF inv_ostore]
        apply (simp add: buf_simps)
       apply fastforce
      apply (clarsimp simp add: error_code_simps)
      apply (simp add: \<alpha>_ostore_uptodate_rbuf_agnostic inv_ostore_runtimeD[OF inv_ostore,symmetric])
      apply (fastforce simp add: \<alpha>_ostore_runtime_def \<alpha>_index_def \<alpha>_updates_def \<alpha>_ostore_medium_def split:option.splits)
  using inv_\<alpha>_ostore apply (simp add: \<alpha>_ostore_uptodate_def \<alpha>_index_def \<alpha>_updates_def \<alpha>_ostore_medium_def)
    apply (simp add: \<alpha>_ostore_medium_def)
   apply (simp add: \<alpha>_updates_def buf_simps)

  subgoal for _ _ obj offs
    apply (subgoal_tac "\<exists>x. ObjAddr.offs\<^sub>f (the (\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid)) -
                   ObjAddr.offs\<^sub>f (the (\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid)) mod io_size\<^sub>f (super\<^sub>f mount_st) = x")
     prefer 2
     apply fastforce
    apply (erule exE)
    apply (subgoal_tac "\<exists>y. align32 (ObjAddr.offs\<^sub>f (the (\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid)) +
                                          ObjAddr.len\<^sub>f (the (\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid)),
                                          io_size\<^sub>f (super\<^sub>f mount_st)) = y")
     prefer 2
     apply fastforce
    apply (erule exE)
    apply (subgoal_tac "\<exists>ubib. (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) !
                   unat (ObjAddr.ebnum\<^sub>f (the (\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid)))) = ubib")
     prefer 2
     apply fastforce
    apply (erule exE)
    apply (simp only:)
    apply (drule sym[where s=obj])
    apply (subgoal_tac "ostore_get_obj ostore_st (the (\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid)) = obj")
     prefer 2
     apply (erule trans[where t=obj, rotated])
     apply (simp add: ostore_get_obj_def pObj_offs pObj_update_offs)
     apply (subgoal_tac " unat (ple32 (\<alpha>wa (data\<^sub>f (read_pages_rbuf (rbuf\<^sub>f ostore_st) x (y - x) ubib)))
                (ObjAddr.offs\<^sub>f (the (\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid)) + 0x10)) =
             unat (ple32 (take (unat (ObjAddr.offs\<^sub>f (the (\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid))) +
                          unat (ObjAddr.len\<^sub>f (the (\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid))))
                     ubib)
              (ObjAddr.offs\<^sub>f (the (\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid)) + 0x10))")
      prefer 2
      apply (simp only:  word_unat.Rep_inject)
      apply (rule  ple32_take_eq, simp)
      apply (subst  slice_take)
       apply (drule oaddr_is_valid_addr[OF inv_ostore inv_mount_st])
       apply (clarsimp simp add: is_valid_addr_def bilbyFsObjHeaderSize_def bilbyFsMinObjSize_def)
       apply (simp only: unat_arith_simps)
       apply (unat_arith)
      apply (simp add: read_pages_rbuf_def wordarray_make)
      apply (erule (4) slice_eq[OF inv_ostore inv_mount_st])
      apply simp

     apply (rule pObj_eq')
               apply (fastforce simp add: )+
              apply (fastforce simp add: Let_def pObj_def)+
           apply (subst slice_take)   
            apply (frule oaddr_is_obj_addr_consistent[OF inv_ostore inv_mount_st])
            apply (drule is_obj_addr_consistent_lenD[symmetric])
            apply (unfold ostore_get_obj_def)
            apply (simp add: Let_def pObj_def pObjHeader_def Obj.make_def)
           apply (rule slice_eq2[OF inv_ostore inv_mount_st], simp+)
           apply (frule oaddr_is_obj_addr_consistent[OF inv_ostore inv_mount_st])
           apply (drule is_obj_addr_consistent_lenD[symmetric])
           apply (unfold ostore_get_obj_def, simp add: Let_def pObj_def pObjHeader_def Obj.make_def)
          apply (frule oaddr_is_obj_addr_consistent[OF inv_ostore inv_mount_st, THEN is_obj_addr_consistent_lenD])
          apply (drule oaddr_is_valid_addr[OF inv_ostore inv_mount_st])
          apply (fastforce simp add: Let_def pObj_def pObjHeader_def Obj.make_def is_valid_addr_def ostore_get_obj_def)
         apply (drule oaddr_is_valid_addr[OF inv_ostore inv_mount_st])
         apply (simp add: is_valid_addr_def)
      (* We could assume is_len_and_type_ok in the invariant but because we check it at runtime
       we only assume the minimum we need for the values we do not check *)
         apply (drule is_valid_ObjHeader_is_len_and_type_okD, simp)
        apply (frule oaddr_is_obj_addr_consistent[OF inv_ostore inv_mount_st])
        apply (frule oaddr_is_valid_addr[OF inv_ostore inv_mount_st])
        apply (drule_tac t=ubib in sym)
        apply (subgoal_tac "length
        (take (unat (ObjAddr.offs\<^sub>f (the (\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid))) +
               unat (ObjAddr.len\<^sub>f (the (\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid))))
          (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) !
           unat (ObjAddr.ebnum\<^sub>f (the (\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid))))) = unat (ObjAddr.offs\<^sub>f (the (\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid))) +
               unat (ObjAddr.len\<^sub>f (the (\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid)))")
         apply (subst word_le_nat_alt)
         apply (subst wordarray_length_ret')
          apply (clarsimp simp add: pObjHeader_def Obj.make_def is_valid_ObjHeader_def
                  is_valid_addr_def is_obj_addr_consistent_def ostore_get_obj_def
                  pObj_def Let_def
        simp del: length_take)
          apply (frule plus_no_overflow_unat_lift)
          apply (simp add: wordarray_make)
          apply (rule order.trans[of _ "unat bilbyFsMaxEbSize"])
           apply (rule order.trans[OF _ inv_mount_st_eb_size_boundD[OF inv_mount_st, simplified word_le_nat_alt]])
           apply (simp add: word_le_nat_alt)
          apply (simp add: bilbyFsMaxEbSize_def  max_word_def)
         apply (clarsimp simp add: pObjHeader_def Obj.make_def is_valid_ObjHeader_def
                is_valid_addr_def is_obj_addr_consistent_def ostore_get_obj_def
                pObj_def Let_def wordarray_make
                simp del: length_take)
         apply (frule plus_no_overflow_unat_lift; simp)
        apply (clarsimp simp add: )
        apply (frule (1) oaddr_ebnum_rangeD[OF inv_ostore inv_mount_st])
    using inv_bufsD[OF inv_ostore]
        apply clarsimp
        apply (erule ballE[where x="unat (ObjAddr.ebnum\<^sub>f (the (\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid)))"])
         apply (clarsimp simp add: is_valid_addr_def)
         apply (frule plus_no_overflow_unat_lift)
         apply (simp add: word_le_nat_alt)
        apply simp
       apply simp
       apply (frule oaddr_is_obj_addr_consistent[OF inv_ostore inv_mount_st, THEN is_obj_addr_consistent_lenD])
       apply (drule oaddr_is_valid_addr[OF inv_ostore inv_mount_st])
       apply (clarsimp simp: is_valid_addr_def pObj_def pObjHeader_def Obj.make_def ostore_get_obj_def)
       apply (drule length_eq_imp_wordarray_length_eq)
       apply (simp add: wordarray_make')
       apply (cut_tac inv_ostore_rbuf_lengthD[OF inv_ostore, simplified buf_length_def Let_def])
       apply simp
   
      apply (frule oaddr_is_obj_addr_consistent[OF inv_ostore inv_mount_st, THEN is_obj_addr_consistent_lenD])
      apply (drule oaddr_is_valid_addr[OF inv_ostore inv_mount_st])
      apply (clarsimp simp: is_valid_addr_def pObj_def pObjHeader_def Obj.make_def ostore_get_obj_def)
      apply (subst word_le_nat_alt)
      apply (rule order.trans[OF wordarray_length_leq_length])
      apply (simp add: wordarray_make)
      apply (frule plus_no_overflow_unat_lift)
      apply (subst linorder_class.min.coboundedI2)
       apply (rule order.trans[OF _ inv_mount_st_eb_size_boundD[OF inv_mount_st, simplified word_le_nat_alt]])
       apply (simp add: word_le_nat_alt)
      apply (simp add: bilbyFsMaxEbSize_def  max_word_def)
     apply simp
     apply (drule length_eq_imp_wordarray_length_eq)
     apply (simp add: wordarray_make')
    using inv_ostore_rbuf_lengthD[OF inv_ostore, simplified buf_length_def Let_def]
          inv_mount_st_eb_size_boundD[OF inv_mount_st]
     apply simp

    apply (subgoal_tac "get_obj_oid obj = oid")
     prefer 2
    using inv_ostore_indexD[OF inv_ostore]
     apply ( simp add: inv_ostore_index_def Let_def \<alpha>_index_def ostore_get_obj_def)
     apply (erule ballE[where x=oid])
      apply simp
     apply fastforce
    apply(simp add: success_def)
    apply (rule suc)
        apply (rule inv_ostore_rbuf_agnostic[OF inv_ostore, where v="data\<^sub>f (rbuf\<^sub>f ostore_st)" and b="bound\<^sub>f (rbuf\<^sub>f ostore_st)"])
         apply simp
        apply (drule length_eq_imp_wordarray_length_eq)
    using inv_ostore_rbuf_lengthD[OF inv_ostore]
        apply (simp add: buf_simps)
       apply (subst inv_ostore_runtimeD[OF inv_ostore_rbuf_agnostic[OF inv_ostore, where v="data\<^sub>f (rbuf\<^sub>f ostore_st)" and b="bound\<^sub>f (rbuf\<^sub>f ostore_st)", simplified],symmetric])
        apply (drule length_eq_imp_wordarray_length_eq)
    using inv_ostore_rbuf_lengthD[OF inv_ostore]
        apply (simp add: buf_simps)
       apply (case_tac "\<alpha>rbt (addrs\<^sub>f (index_st\<^sub>f ostore_st)) oid")
        apply simp
       apply (clarsimp simp add: Let_def \<alpha>_ostore_runtime_def \<alpha>_index_def ostore_get_obj_def )
    using inv_\<alpha>_ostore apply (simp add: \<alpha>_ostore_uptodate_def \<alpha>_index_def \<alpha>_updates_def \<alpha>_ostore_medium_def)
     apply (simp add: \<alpha>_ostore_medium_def)
    apply (simp add: \<alpha>_updates_def buf_simps)
    done
  done

end
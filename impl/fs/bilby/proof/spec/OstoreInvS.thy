(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory OstoreInvS
imports
  "../impl/BilbyFs_Shallow_Desugar_Tuples"
  "../impl/BilbyFs_ShallowConsts_Desugar_Tuples"
  "../spec/OstoreS"
  "../spec/SerialS"
  "../spec/UbiS"
  "../adt/BufferT"
  "../adt/RbtT"
  "HOL-Library.Sublist"
begin

definition
  \<alpha>_index :: "IndexState\<^sub>T \<Rightarrow> (ObjId \<rightharpoonup> ObjAddr\<^sub>T)"
where
 "\<alpha>_index index_st \<equiv> \<alpha>rbt (addrs\<^sub>f index_st)"

consts \<alpha>_fsm_gim :: "(ObjId,  GimNode\<^sub>T) Rbt \<Rightarrow> (ObjId \<rightharpoonup> GimNode\<^sub>T)"

definition
  nopad :: "U8 list \<Rightarrow> U8 list"
where
 "nopad xs \<equiv>
    dropWhile ((=) bilbyFsPadByte) xs"

lemma pTrans_termination[simp]:
 "is_valid_ObjHeader obj (d # data) \<Longrightarrow>
    Suc (length data) - unat (Obj.len\<^sub>f obj) < Suc (length data)"
 "is_valid_ObjHeader obj data \<Longrightarrow>
    (length data) - unat (Obj.len\<^sub>f obj) < (length data)"
  unfolding bilbyFsObjHeaderSize_def
  by (drule is_valid_ObjHeader_len_facts,
         clarsimp simp add: bilbyFsObjHeaderSize_def, unat_arith)+

type_synonym Trans = "Obj\<^sub>T list"
fun
  pTrans :: "U8 list \<Rightarrow> (U8 list \<times> Trans)"
where
 "pTrans [] = ([],[])"
|pTrans_Cons: "pTrans data =
    (let obj = pObj data 0
    \<comment>\<open> We stop at the first obviously invalid object. \<close>
     in if \<not>is_valid_ObjHeader obj data then
       (List.drop (max (unat bilbyFsObjHeaderSize) (unat (Obj.len\<^sub>f obj))) data, [])
     else if Obj.trans\<^sub>f obj = bilbyFsTransIn then
       (\<lambda>(d,os). (d, (obj#os))) (pTrans (List.drop (unat (Obj.len\<^sub>f obj)) data))
     else
       (List.drop (unat (Obj.len\<^sub>f obj)) data, [obj])
)"

lemma drop_0_eq[simp]:
  "\<exists>n. xs = List.drop n xs"
 by (rule_tac x=0 in exI, simp)

lemma pTrans_data_is_substring:
  "(\<exists>n. prod.fst (pTrans data) = List.drop n data)"
  by (induct data rule: pTrans.induct) (fastforce simp: Let_def prod.case_eq_if)+

lemma pTrans_length_helper:
assumes len: "is_valid_ObjHeader (pObj (d # data) 0) (d # data)"
shows
  "length (prod.fst (pTrans (List.drop (unat (Obj.len\<^sub>f (pObj (d # data) 0))) (d # data)))) < length (d # data)"
  using pTrans_data_is_substring apply clarsimp
  apply (drule_tac x="(List.drop (unat (Obj.len\<^sub>f (pObj (d # data) 0))) (d # data))" in meta_spec)
  using is_valid_ObjHeader_len[OF len]  apply (clarsimp simp: bilbyFsObjHeaderSize_def)
  apply unat_arith
 done

text {*
The termination proof above does not look at the shape of the returned
values of pTrans, it only shows that the size of the input
data list decreases.
To prove termination of \<alpha>_updates_fun we need to know that the returned data
list is smaller than the one received as argument.
I could not figure a way to reuse the termination proof above to show
that \<alpha>_updates_fun terminates. I wouldn't be surprise to see that there's
a simpler way to achieve my goal. If you find one, please educate me.
*}
lemma pTrans_termination_argument:
 "(nd#nds, o'#os) = pTrans (d#data) \<Longrightarrow> length (nd#nds) < length (d#data)"
  apply (clarsimp simp del: list.size split: if_splits
         simp : bilbyFsObjHeaderSize_def Let_def prod.case_eq_if)
  apply (fastforce dest: pTrans_length_helper simp: prod.case_eq_if)
  done

definition
  is_valid_addr :: "MountState\<^sub>T \<Rightarrow> OstoreState\<^sub>T \<Rightarrow> ObjAddr\<^sub>T \<Rightarrow> bool"
where
 "is_valid_addr mount_st ostore_st addr \<equiv>
    ebnum\<^sub>f addr < nb_eb\<^sub>f (super\<^sub>f mount_st) \<and>
    bilbyFsFirstLogEbNum \<le> ebnum\<^sub>f addr \<and>
    bilbyFsMinObjSize \<le> ObjAddr.len\<^sub>f addr \<and>
    offs\<^sub>f addr < offs\<^sub>f addr + ObjAddr.len\<^sub>f addr \<and>
    offs\<^sub>f addr + ObjAddr.len\<^sub>f addr \<le> eb_size\<^sub>f (super\<^sub>f mount_st) \<and>
    (ebnum\<^sub>f addr = wbuf_eb\<^sub>f ostore_st \<longrightarrow>
        (offs\<^sub>f addr + ObjAddr.len\<^sub>f addr \<le> used\<^sub>f ostore_st))"


text {* It turns out that transactions can be separated by few bilbyFsPadByte bytes. 
This happens when there isn't enough room for a padding object to fill up a
hardware page. Thus there cannot be such padding area at an offset corresponding
to the beginning of a page.
*}
function
  list_trans :: "U8 list \<Rightarrow> (U8 list \<times> Trans list)"
where
"list_trans data = 
    (case pTrans data of
      (_, []) \<Rightarrow> (data, []) \<comment>\<open> We return the beginning of an invalid transaction as it's obviously non-empty \<close>
    | ([],objs) \<Rightarrow> ([], [objs])
    | (newdata, objs) \<Rightarrow>
      \<comment>\<open>let objs = if length objs = 1 \<and>
                    @{term otype\<^sub>f} (objs!0) = bilbyFsObjTypePad then [] else objs
       in\<close> (\<lambda>(d,txs). (d,objs#txs)) (list_trans (nopad newdata)))"
  by pat_completeness auto
  termination
  apply (relation "measure length")
  apply (clarsimp simp del: pTrans.simps split:prod.splits)
  apply (case_tac "data")
   apply clarsimp
  apply (fastforce dest:pTrans_termination_argument
          simp: nopad_def dropWhile_eq_drop)
 done

definition
  list_trans_no_pad :: "U8 list \<Rightarrow> (U8 list \<times> Trans list)"
where
  "list_trans_no_pad data \<equiv>
    (case list_trans data of
     (rem, txs) \<Rightarrow>
     (rem, filter (\<lambda>tx. \<not> (length tx = 1 \<and> otype\<^sub>f (tx!0) = bilbyFsObjTypePad)) txs))"

lemma list_trans_no_pad_Cons[simp]:
 "list_trans_no_pad (x#xs) =
 (prod.fst (list_trans (x # xs)), 
  [tx\<leftarrow>prod.snd (list_trans (x # xs)).  \<not> (length tx = 1 \<and> otype\<^sub>f (tx!0) = bilbyFsObjTypePad)])"
  by (simp add: list_trans_no_pad_def prod.case_eq_if del: list_trans.simps)

lemma list_trans_no_pad_Nil[simp]:
 "list_trans_no_pad [] = ([], [])"
  by (simp add: list_trans_no_pad_def)


type_synonym EbLog = "Trans list"

definition
 list_eb_log :: "ubi_leb list \<Rightarrow> EbLog list"
where
 "list_eb_log wubi \<equiv>
   map (prod.snd o list_trans_no_pad) (List.drop (unat bilbyFsFirstLogEbNum) wubi)"

definition
  prune_ostore :: "Obj\<^sub>T \<Rightarrow> ostore_map \<Rightarrow> ostore_map"
where
 "prune_ostore del omap \<equiv>
  (\<lambda>oid. case omap oid of
         option.Some obj \<Rightarrow>
           if obj_is_deleted_by obj del then
             option.None
           else
             option.Some obj
        | option.None \<Rightarrow> option.None)"

definition
  trans_order :: "Obj\<^sub>T list \<Rightarrow> U64"
where
 "trans_order objs \<equiv> Obj.sqnum\<^sub>f ((sort_key Obj.sqnum\<^sub>f objs)!0)"
 
definition
  abstract_mount_\<alpha>_ostore :: "ubi_leb list \<Rightarrow> ostore_map"
where
 "abstract_mount_\<alpha>_ostore wubi \<equiv>
  let alltrans = (concat $ list_eb_log wubi);
      alltrans' = sort_key trans_order alltrans 
  in fold id (map ostore_update alltrans') Map.empty"
  
text {* @{term mount_\<alpha>_ostore} returns the logical representation of the object
store curently stored (synchronised) on medium. *}
definition
  mount_\<alpha>_ostore :: "ubi_leb list \<Rightarrow> ostore_map"
where
 "mount_\<alpha>_ostore wubi \<equiv> 
   let lel = list_eb_log wubi ;
       delobjs = concat $ concat $ map (map (filter obj_is_del)) lel;
       delfree_lel = map (map (filter (Not o obj_is_del))) lel;
       ostore_map = fold id (map (\<lambda>ltx. fold id (map ostore_update ltx)) delfree_lel) Map.empty
  in fold prune_ostore delobjs ostore_map"

definition
  ostore_get_obj :: "OstoreState\<^sub>T \<Rightarrow> ObjAddr\<^sub>T \<Rightarrow> Obj\<^sub>T"
where
 "ostore_get_obj ostore_st addr \<equiv>
  let buf = (if ebnum\<^sub>f addr = wbuf_eb\<^sub>f ostore_st then
               (\<alpha>wa $ data\<^sub>f $ wbuf\<^sub>f ostore_st)
             else
               \<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st)!(unat $ ebnum\<^sub>f addr))
  in pObj (take (unat (ObjAddr.offs\<^sub>f addr) + unat (ObjAddr.len\<^sub>f addr)) buf) (offs\<^sub>f addr)"

definition
 \<alpha>_ostore_medium :: "OstoreState\<^sub>T \<Rightarrow> ostore_map"
where
 "\<alpha>_ostore_medium ostore_st \<equiv> abstract_mount_\<alpha>_ostore (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))"
                            
text {* \<alpha>_updates: returns updates not synchronised to medium yet *}
definition
  \<alpha>_updates :: "OstoreState\<^sub>T \<Rightarrow> (ostore_map \<Rightarrow> ostore_map) list"
where
 "\<alpha>_updates ostore_st \<equiv>
  (map ostore_update $ prod.snd $ list_trans_no_pad 
    (buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st)))"

text {* \<alpha>_ostore_uptodate: returns the logical view of the object store when all
 updates are applied.
*}

definition
  \<alpha>_ostore_uptodate ::  "OstoreState\<^sub>T \<Rightarrow> ostore_map"
where
 "\<alpha>_ostore_uptodate ostore_st \<equiv>
    fold id (\<alpha>_updates ostore_st) (\<alpha>_ostore_medium ostore_st)"

definition
  \<alpha>_ostore_runtime :: "OstoreState\<^sub>T \<Rightarrow> ostore_map"
where
 "\<alpha>_ostore_runtime ostore_st oid \<equiv>
  (case (\<alpha>_index $ index_st\<^sub>f ostore_st) oid of
   option.None \<Rightarrow> option.None
   | option.Some addr \<Rightarrow>
       option.Some $ ostore_get_obj ostore_st addr)"

definition
 is_valid_ObjIn :: "Obj\<^sub>T \<Rightarrow> U8 list \<Rightarrow> bool"
where
 "is_valid_ObjIn obj buf \<equiv>
   is_valid_ObjHeader obj buf \<and> Obj.trans\<^sub>f (pObj buf 0) = bilbyFsTransIn"

definition
 is_valid_ObjCommit :: "Obj\<^sub>T \<Rightarrow> U8 list \<Rightarrow> bool"
where
 "is_valid_ObjCommit obj buf \<equiv>
   is_valid_ObjHeader obj buf \<and> Obj.trans\<^sub>f (pObj buf 0) = bilbyFsTransCommit"

lemma bilbyFsTrans_diff[simp]:
  "bilbyFsTransIn \<noteq> bilbyFsTransCommit"
  "bilbyFsTransCommit \<noteq> bilbyFsTransIn"
   unfolding bilbyFsTransIn_def bilbyFsTransCommit_def
   by simp+

lemmas is_valid_ObjTrans = is_valid_ObjIn_def is_valid_ObjCommit_def

lemma drop_n_ge_0:
  "0<n \<Longrightarrow> List.drop n (v # va) = List.drop (n - 1) va"
 by (case_tac n, simp+)

lemma is_valid_ObjHeader_drop_non_zero: 
 "is_valid_ObjHeader (pObj (v # va) 0) (v # va) \<Longrightarrow>
  List.drop (unat (Obj.len\<^sub>f (pObj (v # va) 0))) (v # va) = List.drop (unat (Obj.len\<^sub>f (pObj (v # va) 0)) - 1) (va)
 "
  apply (frule is_valid_ObjHeader_len_facts)
  apply (clarsimp simp:  bilbyFsObjHeaderSize_def unat_arith_simps)
  apply (simp add: drop_n_ge_0)
 done

lemma [simp]:
"is_valid_ObjIn (pObj (v # va) 0) (v # va) \<Longrightarrow>
            Suc (length va) - unat (Obj.len\<^sub>f (pObj (v # va) 0)) < Suc (length va)"
"is_valid_ObjCommit (pObj (v # va) 0) (v # va) \<Longrightarrow>
            Suc (length va) - unat (Obj.len\<^sub>f (pObj (v # va) 0)) < Suc (length va)"
by ((clarsimp simp: is_valid_ObjTrans is_valid_ObjHeader_def Let_def bilbyFsObjHeaderSize_def)
    ,unat_arith?)+

fun
  valid_trans :: "U8 list \<Rightarrow> bool"
where
"valid_trans [] = False"
|valid_trans_Cons: "valid_trans buf =
   (if is_valid_ObjIn (pObj buf 0) buf then
     valid_trans (List.drop (unat $ Obj.len\<^sub>f $ pObj buf 0) buf)
   else is_valid_ObjCommit (pObj buf 0) buf)"

declare valid_trans.simps[simp del]

lemma valid_trans_simps[simp]:
  "valid_trans [] = False"
  "is_valid_ObjIn (pObj xs 0) xs \<Longrightarrow>
    valid_trans xs = valid_trans (List.drop (unat $ Obj.len\<^sub>f $ pObj xs 0) xs)"
  "is_valid_ObjCommit (pObj xs 0) xs \<Longrightarrow>
    valid_trans xs = True"
    apply (simp add: valid_trans.simps)
   apply (case_tac xs, (clarsimp simp: is_valid_ObjHeader_len_facts valid_trans.simps is_valid_ObjTrans is_valid_ObjHeader_def bilbyFsObjHeaderSize_def )+)
  apply (case_tac xs, simp)
   apply (frule is_len_and_type_ok_hdr_szD)
   apply (simp add: bilbyFsObjHeaderSize_def, unat_arith)
  apply (simp add: valid_trans.simps is_valid_ObjTrans is_valid_ObjHeader_def)
 done  

lemma is_valid_Obj_diff:
  "is_valid_ObjCommit (pObj buf n) buf \<longrightarrow> \<not>is_valid_ObjIn (pObj buf n) buf"
  "is_valid_ObjIn (pObj buf n) buf \<longrightarrow> \<not>is_valid_ObjCommit (pObj buf n) buf"
  by (simp add: is_valid_ObjTrans)+

lemma Nil_not_valid_Obj[simp]:
  "is_valid_ObjHeader (pObj [] n) [] = False"
  "is_valid_ObjIn (pObj [] n) [] = False"
  "is_valid_ObjCommit (pObj [] n) [] = False"
  by (clarsimp simp add: is_valid_ObjTrans,
      frule is_valid_ObjHeader_len_facts,
      simp add: bilbyFsObjHeaderSize_def)+

fun
 trans_len :: "U8 list \<Rightarrow> nat"
where
trans_len_Nil: "trans_len [] = max (unat bilbyFsObjHeaderSize) (unat $ Obj.len\<^sub>f $ pObj [] 0)"
|trans_len_Cons: "trans_len buf =
   (if \<not>is_valid_ObjHeader (pObj buf 0) buf then
        max (unat bilbyFsObjHeaderSize) (unat $ Obj.len\<^sub>f $ pObj buf 0)
    else if is_valid_ObjIn (pObj buf 0) buf then
     (unat $ Obj.len\<^sub>f $ pObj buf 0) + trans_len (List.drop (unat $ Obj.len\<^sub>f $ pObj buf 0) buf)
    else
     unat $ Obj.len\<^sub>f $ pObj buf 0)"

declare trans_len.simps [simp del]
lemma trans_len_simps[simp]:
  "trans_len [] = max (unat bilbyFsObjHeaderSize) (unat $ Obj.len\<^sub>f $ pObj [] 0)"
  "is_valid_ObjIn (pObj xs 0) xs \<Longrightarrow>
    trans_len xs = (unat $ Obj.len\<^sub>f $ pObj xs 0) + trans_len (List.drop (unat $ Obj.len\<^sub>f $ pObj xs 0) xs)"
  "is_valid_ObjCommit (pObj xs 0) xs \<Longrightarrow>
    trans_len xs = unat (Obj.len\<^sub>f $ pObj xs 0)"
  apply (case_tac xs, (clarsimp simp: is_valid_ObjTrans is_valid_ObjHeader_def bilbyFsObjHeaderSize_def trans_len.simps)+)
  apply (case_tac xs, (clarsimp simp: is_valid_ObjTrans is_valid_ObjHeader_def bilbyFsObjHeaderSize_def trans_len.simps)+)
  apply (case_tac xs, (clarsimp simp: is_valid_ObjTrans, frule is_len_and_type_ok_hdr_szD, simp add: bilbyFsObjHeaderSize_def, unat_arith))
  apply (clarsimp simp: is_valid_ObjTrans, frule is_len_and_type_ok_hdr_szD,
         clarsimp simp add: bilbyFsObjHeaderSize_def trans_len.simps is_valid_ObjTrans, unat_arith)
 done

lemma trans_len_min_header[simp]:
  "unat bilbyFsObjHeaderSize - 1 < trans_len xs"
  apply (rule_tac x=xs in trans_len.cases)
   apply (fastforce simp: bilbyFsObjHeaderSize_def)
  apply (simp only: trans_len_Cons)
  apply (case_tac "is_valid_ObjIn (pObj (v # va) 0) (v # va)")
   apply (clarsimp simp: is_valid_Obj_diff is_valid_ObjTrans)
   apply (drule is_valid_ObjHeader_len, simp add: bilbyFsObjHeaderSize_def, unat_arith)
  apply (clarsimp simp: is_valid_ObjTrans)
  apply (auto dest!:  is_valid_ObjHeader_len[simplified bilbyFsObjHeaderSize_def], (simp add: bilbyFsObjHeaderSize_def | unat_arith)+)
 done

lemma hdr_sz_le_trans_len:
  "unat bilbyFsObjHeaderSize \<le> trans_len xs"
 using trans_len_min_header[where xs=xs] by simp

lemma trans_len_non_zero:
 "0 < trans_len xs"
 using trans_len_min_header
 by (drule_tac x=xs in meta_spec) fastforce

lemma take_non0:
 "xs \<noteq> [] \<Longrightarrow> 0 < n \<Longrightarrow>
   take n xs = hd xs#(take (n- 1) (tl xs))"
by (case_tac n, auto simp: take_Suc)

lemma prefix_length_le_Cons:
 "prefix xs (y#ys) \<Longrightarrow> length xs \<le> Suc (length ys)"
  using prefix_length_le by fastforce

function
  valid_list_trans :: "U8 list \<Rightarrow> bool"
where
"valid_list_trans [] = False"
|"valid_list_trans (b#buf) =
   (valid_trans (b#buf) \<and>
    (if nopad (List.drop (trans_len (b#buf)) (b#buf)) = [] then True
     else valid_list_trans (nopad (List.drop (trans_len (b#buf)) (b#buf)))))"

by pat_completeness simp+
termination
  apply (relation "measure (Suc o length)")
   apply simp
  apply (simp add: dropWhile_eq_drop nopad_def)
  apply (cut_tac xs="b # buf" in trans_len_non_zero)
  apply unat_arith
 done

definition
  valid_list_trans_no_pad :: "U8 list \<Rightarrow> bool"
where
  "valid_list_trans_no_pad buf \<equiv>
    valid_list_trans buf \<and> prod.snd (list_trans_no_pad buf) \<noteq> []"

lemma valid_list_trans_to_valid_trans:
 "valid_list_trans buf \<Longrightarrow> valid_trans buf"
by (erule valid_list_trans.elims, simp)

text {* \<alpha>_summary_updates: returns all the updates included in the summary.
This includes the updates already synchronised to medium i.e. wbuf[0:used] and
updates only applied in memory i.e. wbuf[used:sync_offs]. (Where wbuf[x:y] is the
slice of the WordArray U8 maching the medium contents for the erase-block in
question.)
*}
definition
  \<alpha>_summary_updates :: "OstoreState\<^sub>T \<Rightarrow> (ostore_map \<Rightarrow> ostore_map) list"
where
 "\<alpha>_summary_updates ostore_st \<equiv> 
   let offs = unat $ (used\<^sub>f ostore_st);
       buf = take offs (\<alpha>wa $ data\<^sub>f $ wbuf\<^sub>f ostore_st)
    in (map ostore_update $ prod.snd $ list_trans_no_pad buf)"

text {* inv_\<alpha>_step_updates: asserts inv is true no matter how many updates we apply. *}
definition
  inv_\<alpha>_step_updates :: "OstoreState\<^sub>T \<Rightarrow> bool"
where
 "inv_\<alpha>_step_updates ostore_st \<equiv>
   (let updates = \<alpha>_updates ostore_st
    in \<forall>n\<le>length updates.
     inv_\<alpha>_ostore (apply_n_updates n (\<alpha>_ostore_medium ostore_st) updates))"

definition
  sum_from_wbuf :: "Buffer\<^sub>T \<Rightarrow> Obj\<^sub>T"
where
 "sum_from_wbuf buf \<equiv> 
   let  data = \<alpha>wa $ data\<^sub>f buf ;
        offs = ple32 data (buf_length buf - 4)
   in pObj data offs"

text {*
 summary_map: builds a ostore_map from a summary.
 The resulting map should be the same as applying all updates returned by \<alpha>_summary_updates to an empty
 map. (see inv_sum_consistent)
*}

definition
 summary_map :: "ObjSummary\<^sub>T \<Rightarrow> OstoreState\<^sub>T \<Rightarrow> ostore_map"
where
 "summary_map summary ostore_st \<equiv>
  let nb_entry = unat $ nb_sum_entry\<^sub>f summary;
      entries = take nb_entry $ \<alpha>wa $ entries\<^sub>f summary;
      nodel = filter (Not o obj_sum_entry_is_del) entries;
      maps = map (\<lambda>entry. Map.empty(ObjSumEntry.id\<^sub>f entry \<mapsto> pObj (\<alpha>wa $ data\<^sub>f $ wbuf\<^sub>f ostore_st) (obj_sum_entry_offs entry))) nodel;
      omap = fold (++) maps Map.empty;
      dels = filter (obj_sum_entry_is_del) entries
  in fold (\<lambda>entry gos.
    (\<lambda>oid. if oid_is_deleted_by oid (ObjSumEntry.id\<^sub>f entry) then
              option.None
           else gos oid)) dels omap"

definition
  inv_sum_consistent :: "Obj\<^sub>T \<Rightarrow> OstoreState\<^sub>T \<Rightarrow> bool"
where
 "inv_sum_consistent sumobj ostore_st \<equiv>
   True
   \<comment>\<open> ignore summary consistency for now:
   @{term otype\<^sub>f} sumobj = bilbyFsObjTypeSum \<and>
   let sum = obj_osummary sumobj
   in summary_map sum ostore_st = fold id (\<alpha>_summary_updates ostore_st) Map.empty \<close>"

definition
  room_for_summary :: "MountState\<^sub>T \<Rightarrow> OstoreState\<^sub>T \<Rightarrow> bool"
where
 "room_for_summary mount_st ostore_st \<equiv>
   (\<not>no_summary\<^sub>f mount_st \<and> used\<^sub>f ostore_st \<noteq> (eb_size\<^sub>f $ super\<^sub>f mount_st)) \<longrightarrow>
     (unat (eb_size\<^sub>f $ super\<^sub>f mount_st) - unat (used\<^sub>f ostore_st) \<le> unat (serialise_size_summary_Obj (summary\<^sub>f ostore_st)))
    "

text {* 
Unless "used" equals "eb_size", there must be enough room for the summary
to be serialised. If "used" is equal to "eb_size", the summary's been
serialised already and can be read from the buffer.

nb_sum_entry constrain says that the maximum number of objects in
an erase-block has to be less than the number of min-size object that fit
in that buffer (this is an over-approximation because at least one of these
objects must be a summary).
*}
definition
  inv_ostore_summary :: "MountState\<^sub>T \<Rightarrow> OstoreState\<^sub>T \<Rightarrow> bool"
where
 "inv_ostore_summary mount_st ostore_st \<equiv>
 True
 \<comment>\<open> No summary invariant for now.
   let eb_size = @{term eb_size\<^sub>f} (@{term super\<^sub>f} mount_st)
   in @{term nb_sum_entry\<^sub>f} (@{term summary\<^sub>f} ostore_st) < (eb_size div bilbyFsMinObjSize) \<and>
   room_for_summary mount_st ostore_st \<and>
   (if @{term used\<^sub>f} ostore_st = eb_size then
    inv_sum_consistent (sum_from_wbuf (@{term wbuf\<^sub>f} ostore_st)) ostore_st
   else
     @{term used\<^sub>f} ostore_st < @{term used\<^sub>f} ostore_st + os_sum_sz ostore_st \<and> 
     @{term  ostore_st} + os_sum_sz ostore_st \<le> eb_size \<and>
     inv_sum_consistent ((@{term sum_obj\<^sub>f} ostore_st)\<lparr> @{term ounion\<^sub>f}:= TObjSummary (@{term summary\<^sub>f} ostore_st) \<rparr>) ostore_st)
     \<close>
  "

text {*
 inv_ostore_obj_meta: is the invariant of object meta data in
 relation to the object store state.
*}
definition
  inv_mem_ostore_obj :: "OstoreState\<^sub>T \<Rightarrow> Obj\<^sub>T \<Rightarrow> bool"
where
 "inv_mem_ostore_obj ostore_st obj \<equiv>
  Obj.sqnum\<^sub>f obj < OstoreState.next_sqnum\<^sub>f ostore_st \<and>
  ucast (otype\<^sub>f obj) = bilbyFsObjInode \<longrightarrow>
    (inum_from_obj_id $ get_obj_oid obj) < OstoreState.next_inum\<^sub>f ostore_st"


text {* @{term pollute_buf} ensures that the buffer does not contain a valid transaction
at offset @{term offs}. It does not matter what the value is as long as it's not
a valid transaction or padding, mount will stop at this offset.
Note that we could allow invalid to be prefixed by padding bytes but it's this is Ok for now.
We don't use pollute_buf at the moment because we do not care about crash-tolerance.
*}
definition
 pollute_buf :: "nat \<Rightarrow> U8 list \<Rightarrow> U8 list"
where
 "pollute_buf offs xs = xs[offs:=0xff]"

text {* list_eb_log_wbuf: returns the logical view of the log on-flash with the current
state of the buffer wbuf instead of the content of the corresponding erase-block.
*}
definition
 list_eb_log_wbuf :: "OstoreState\<^sub>T \<Rightarrow> EbLog list"
where
 "list_eb_log_wbuf ostore_st \<equiv>
  let eblogs = list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st));
      wbuflog = prod.snd (list_trans_no_pad (\<comment>\<open> pollute_buf \<close>buf_slice (wbuf\<^sub>f ostore_st) 0 (used\<^sub>f ostore_st)))
  in eblogs[unat (wbuf_eb\<^sub>f ostore_st) - unat bilbyFsFirstLogEbNum:=wbuflog]"

text {* Attempt at on-flash invariant.

It's composed of 3 level of invariant, the top-level being the on that talks
about the entire log and relation between objects: inv_flash
The next level talks about individual erase-blocks: inv_eb_log
Erase-blocks log are made of multiple transactions: inv_trans
Transactions are made of objects: inv_obj

*}
 
definition
  ostore_log_objects :: "EbLog list \<Rightarrow> Obj\<^sub>T list"
where
 "ostore_log_objects \<equiv> concat o concat "

definition
 inv_trans :: "Obj\<^sub>T list \<Rightarrow> bool"
where
 "inv_trans olist \<equiv> (\<forall>obj\<in>set olist. \<not>obj_is_del obj \<longrightarrow> inv_read_obj obj)"

definition
  inv_eb_log :: "EbLog \<Rightarrow> Obj\<^sub>T set \<Rightarrow> bool"
where
 "inv_eb_log tlist allobjs \<equiv>
     (let sumtrans = tlist!(length tlist - 1);
         sumobj = hd sumtrans ;
         sum = obj_osummary sumobj
     in length sumtrans = 1 \<and> otype\<^sub>f sumobj = bilbyFsObjTypeSum \<and>
        (\<forall>entry\<in>(set $ \<alpha>wa $ ObjSummary.entries\<^sub>f sum).
          let objs = set $ concat $ tlist
          in \<exists>obj. Obj.offs\<^sub>f obj = obj_sum_entry_offs entry \<and>
          get_obj_oid obj = ObjSumEntry.id\<^sub>f entry \<and>
          (obj_sum_entry_is_del entry \<longrightarrow>
            (otype\<^sub>f obj = bilbyFsObjTypeDel \<and>
             card {x. x \<in> allobjs \<and>
                      oid_is_deleted_by (get_obj_oid x) (ObjSumEntry.id\<^sub>f entry) \<and>
                      Obj.sqnum\<^sub>f obj < ObjSumEntry.sqnum\<^sub>f entry
                  } = unat (ObjSumEntry.count\<^sub>f entry))) \<and>
          Obj.len\<^sub>f obj = ObjSumEntry.len\<^sub>f entry) \<and>
          (\<forall>trans \<in> set(butlast tlist). inv_trans trans))"

definition
  obj_is_alive :: "Obj\<^sub>T \<Rightarrow> Obj\<^sub>T set \<Rightarrow> bool"
where
 "obj_is_alive obj all \<equiv>
  (\<forall>delobj \<in>{x. x\<in> all \<and> obj_is_del x}. \<not>obj_is_deleted_by obj delobj)"

definition
  inv_flash :: "EbLog list \<Rightarrow> bool"
where
 "inv_flash flash \<equiv> True
\<comment>\<open>
  let all = ostore_log_objects flash in
  (* The root inode exists, we don't really need to know that for the object store *)
  (* (\<exists>obj\<in>set all. get_obj_oid obj = obj_id_inode_mk bilbyFsRootIno \<and> obj_is_alive obj (set all)) \<and> *) 
  (* all sqnums are uniq *)
  (card (@{term Obj.sqnum\<^sub>f} ` set all) = length (map @{term Obj.sqnum\<^sub>f} all)) \<and>
  (\<forall>eblog\<in>set flash. inv_eb_log eblog (set all)) \<and>
  (* There is maximum 1 erase-block with garbage, (stripping out unmapped erase-blocks) *)
  length ((filter (op \<noteq> []) $ map (prod.fst o the) $ filter (op \<noteq> option.None) flash)) \<le> 1
  (*rel dentarr inode and inode data blocks? no cyclic dependencies in graph? *)
  \<close>"

definition
 is_obj_addr_consistent :: "Obj\<^sub>T \<Rightarrow> ObjAddr\<^sub>T \<Rightarrow> bool"
where
 "is_obj_addr_consistent obj addr \<equiv>
  Obj.sqnum\<^sub>f obj = ObjAddr.sqnum\<^sub>f addr \<and>
  Obj.offs\<^sub>f obj = ObjAddr.offs\<^sub>f addr \<and>
  Obj.len\<^sub>f obj = ObjAddr.len\<^sub>f addr"

definition
 inv_ostore_index :: "MountState\<^sub>T \<Rightarrow> OstoreState\<^sub>T \<Rightarrow> bool"
where
 "inv_ostore_index mount_st ostore_st \<equiv> 
  (\<forall>oid\<in>dom(\<alpha>_index $ index_st\<^sub>f ostore_st).
    let addr = the $ (\<alpha>_index $ index_st\<^sub>f ostore_st) oid;
        obj = ostore_get_obj ostore_st addr
     in is_valid_addr mount_st ostore_st addr \<and>
        is_obj_addr_consistent obj addr \<and>
        get_obj_oid obj = oid)"

definition
  inv_ostore_index_gim_disjoint :: "OstoreState\<^sub>T \<Rightarrow> bool"
where
 "inv_ostore_index_gim_disjoint ostore_st \<equiv>
   dom (\<alpha>_index $ index_st\<^sub>f ostore_st) \<inter> dom (\<alpha>_fsm_gim $ gim\<^sub>f $ fsm_st\<^sub>f ostore_st) = {}"

definition
 inv_fsm_st :: "MountState\<^sub>T \<Rightarrow> FsmState\<^sub>T \<Rightarrow> bool"
where
 "inv_fsm_st mount_st fsm_st \<equiv>
 length (\<alpha>wa $ dirty_space\<^sub>f $ fsm_st) = unat (nb_eb\<^sub>f $ super\<^sub>f mount_st) \<and>
 length (\<alpha>wa $ used_eb\<^sub>f $ fsm_st) = unat (nb_eb\<^sub>f $ super\<^sub>f mount_st)"

definition
 inv_ostore_fsm :: "MountState\<^sub>T \<Rightarrow> OstoreState\<^sub>T \<Rightarrow> bool"
where
 "inv_ostore_fsm mount_st ostore_st \<equiv>
 (\<alpha>wa $ used_eb\<^sub>f $ fsm_st\<^sub>f ostore_st) ! unat (wbuf_eb\<^sub>f ostore_st) \<noteq> 0 \<and>
\<comment>\<open> Count on each gimnode is equal to the number of objects with the same oid
   in the log \<close>
  (\<forall>oid \<in> dom(\<alpha>_fsm_gim $ gim\<^sub>f $ fsm_st\<^sub>f ostore_st).
   let gimnode = the $ (\<alpha>_fsm_gim $ gim\<^sub>f $ fsm_st\<^sub>f ostore_st) oid
   in unat (GimNode.count\<^sub>f gimnode) =
     card {x. x \<in> (set $ ostore_log_objects $ list_eb_log_wbuf ostore_st)  \<and>
              oid_is_deleted_by (get_obj_oid x) oid}) \<and>

\<comment>\<open> All Ubi erase-block with data are marked as used in the FSM @{term used_eb\<^sub>f} bit map \<close>
  (\<forall>ebnum\<in> {bilbyFsFirstLogEbNum..<nb_eb\<^sub>f (super\<^sub>f mount_st)}.
     (unat ebnum \<noteq> unat (wbuf_eb\<^sub>f ostore_st) \<longrightarrow>
     ((\<alpha>wubi $ OstoreState.ubi_vol\<^sub>f ostore_st)  ! (unat ebnum) = [] \<longleftrightarrow>
     ((\<alpha>wa $ used_eb\<^sub>f $ fsm_st\<^sub>f ostore_st) ! (unat ebnum) \<noteq> 0))))

\<comment>\<open> Dirty space book-keeping (commented out for now) \<close>
  \<comment>\<open> let ebnum = @{term wbuf_eb\<^sub>f} ostore_st in
  ((\<alpha>wa $ @{term used_eb\<^sub>f} $ @{term fsm_st\<^sub>f} ostore_st) ! (unat ebnum) \<noteq> 0)  \<longrightarrow>
   (let eb_log = list_eb_log_wbuf ostore_st ! (unat ebnum);
       eb_size =  unat (@{term eb_size\<^sub>f} (@{term super\<^sub>f} mount_st));
       nondirt = listsum (map (unat o @{term Obj.len\<^sub>f}) (concat eb_log)) ;
       nonused = (if ebnum = @{term wbuf_eb\<^sub>f} ostore_st then eb_size - unat (@{term used\<^sub>f} ostore_st) else 0) in
  (unat ((\<alpha>wa $ @{term dirty_space\<^sub>f} $ @{term fsm_st\<^sub>f} ostore_st) ! unat ebnum) = eb_size - nondirt - nonused))\<close>
"

definition
 inv_bufs :: "MountState\<^sub>T \<Rightarrow> OstoreState\<^sub>T \<Rightarrow> bool"
where
 "inv_bufs mount_st ostore_st \<equiv>
   inv_ubi_vol mount_st (OstoreState.ubi_vol\<^sub>f ostore_st) \<and>
   (\<forall>ebnum\<in>{unat bilbyFsFirstLogEbNum.. length ((\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st)))}.
    unat (wbuf_eb\<^sub>f ostore_st) \<noteq> ebnum \<longrightarrow>
    length ((\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))!ebnum) = unat (eb_size\<^sub>f (super\<^sub>f mount_st) )) \<and>
  (let synced = buf_take (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st);
       sync_to_used = buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st) in
   \<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) ! unat (wbuf_eb\<^sub>f ostore_st) = synced \<and>
   (sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st \<longrightarrow> valid_list_trans_no_pad sync_to_used) \<and>
   (used\<^sub>f ostore_st > 0 \<longrightarrow> valid_list_trans_no_pad synced) \<and>
   sort_key trans_order (prod.snd (list_trans_no_pad sync_to_used)) =
     prod.snd (list_trans_no_pad sync_to_used))
\<comment>\<open>
  (let nb_eb = @{term nb_eb\<^sub>f} (@{term super\<^sub>f} mount_st) in
   (\<forall>ebnum\<in>{bilbyFsFirstLogEbNum..nb_eb}.
      (case ubi_to_buf (@{term OstoreState.ubi_vol\<^sub>f} ostore_st) ebnum of
         option.None \<Rightarrow> True |
         option.Some buf \<Rightarrow> valid_list_trans buf)))
\<close>"

definition
  inv_log :: "Trans list list \<Rightarrow> Trans list \<Rightarrow> bool"
where
 "inv_log eb_log wbuf_log \<equiv>
  (\<forall>x\<in>set (concat eb_log).
   \<forall>y\<in>set (wbuf_log). trans_order x < trans_order y) \<and>
   inj_on trans_order (set $ concat $ eb_log @ [wbuf_log])"

definition
  inv_opad :: "Obj\<^sub>T \<Rightarrow> bool"
where
 "inv_opad opad \<equiv>
   magic\<^sub>f opad = bilbyFsMagic \<and>
   otype\<^sub>f opad = bilbyFsObjTypePad \<and> 
   trans\<^sub>f opad = bilbyFsTransCommit \<and>
   bilbyFsObjHeaderSize \<le> Obj.len\<^sub>f opad \<and>
   ounion\<^sub>f (opad) = ObjUnion.TObjPad () \<and>
   Obj.offs\<^sub>f opad = 0"


(*
From inv_ostore, we know that  used\<^sub>f ostore_st \<le> eb_size,
see lemma inv_ostore_used below.
*)

definition
  inv_ostore :: "MountState\<^sub>T \<Rightarrow> OstoreState\<^sub>T \<Rightarrow> bool"
where
 "inv_ostore mount_st ostore_st \<equiv>
  sync_offs\<^sub>f ostore_st \<le> used\<^sub>f ostore_st \<and>
  io_size\<^sub>f (super\<^sub>f mount_st) udvd sync_offs\<^sub>f ostore_st \<and>
  used\<^sub>f ostore_st \<le> eb_size\<^sub>f (super\<^sub>f mount_st) \<and>
  used\<^sub>f ostore_st < used\<^sub>f ostore_st + io_size\<^sub>f (super\<^sub>f mount_st) \<and>
  buf_length (rbuf\<^sub>f ostore_st) = eb_size\<^sub>f (super\<^sub>f mount_st) \<and>
  buf_length (wbuf\<^sub>f ostore_st) = eb_size\<^sub>f (super\<^sub>f mount_st) \<and>
  buf_bound (wbuf\<^sub>f ostore_st) = eb_size\<^sub>f (super\<^sub>f mount_st) \<and>
  wbuf_eb\<^sub>f ostore_st \<ge> bilbyFsFirstLogEbNum \<and>
  wbuf_eb\<^sub>f ostore_st < nb_eb\<^sub>f (super\<^sub>f mount_st) \<and>
  inv_opad (opad\<^sub>f ostore_st) \<and>
  \<alpha>_ostore_runtime ostore_st = \<alpha>_ostore_uptodate ostore_st \<and>
  inv_ostore_summary mount_st ostore_st \<and>
  inv_ostore_index mount_st ostore_st \<and>
  inv_ostore_index_gim_disjoint ostore_st \<and>
  inv_bufs mount_st ostore_st \<and>
  inv_fsm_st mount_st (fsm_st\<^sub>f ostore_st) \<and>
  inv_ostore_fsm mount_st ostore_st \<and>
  inv_flash (list_eb_log_wbuf ostore_st) \<and>
  inv_log (list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st)))
    (prod.snd $ list_trans_no_pad (buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st)))"

lemmas inv_ostore_simps =
  inv_ostore_def
  inv_ostore_summary_def
  inv_ostore_index_def
  inv_ostore_index_gim_disjoint_def
  inv_bufs_def
  inv_ostore_fsm_def
  inv_flash_def
  inv_eb_log_def


lemma inv_summaryD: "inv_ostore mount_st ostore_st \<Longrightarrow> inv_ostore_summary mount_st ostore_st"
by (simp add: inv_ostore_def)

lemma inv_ostore_wbuf_lengthD: "inv_ostore mount_st ostore_st \<Longrightarrow> buf_length (wbuf\<^sub>f ostore_st) = eb_size\<^sub>f (super\<^sub>f mount_st)"
by (simp add: inv_ostore_def)

lemma inv_ostore_rbuf_lengthD: "inv_ostore mount_st ostore_st \<Longrightarrow> buf_length (rbuf\<^sub>f ostore_st) = eb_size\<^sub>f (super\<^sub>f mount_st)"
by (simp add: inv_ostore_def)

lemma inv_ostore_wbuf_boundD: "inv_ostore mount_st ostore_st \<Longrightarrow> buf_bound (wbuf\<^sub>f ostore_st) = eb_size\<^sub>f (super\<^sub>f mount_st)"
by (simp add: inv_ostore_def)

lemma inv_ostore_usedD:
  "inv_ostore mount_st ostore_st \<Longrightarrow>
  used\<^sub>f ostore_st \<le> eb_size\<^sub>f (super\<^sub>f mount_st)"
by (clarsimp simp:inv_ostore_def)

\<comment>\<open> ALTERNATIVE proof which does not rely on @{thm wordarray_length_ret} \<close>
lemma inv_ostore_used_len_wbufD:
  "inv_ostore mount_st ostore_st \<Longrightarrow> inv_mount_st mount_st \<Longrightarrow> unat (used\<^sub>f ostore_st) \<le> length (\<alpha>wa $ data\<^sub>f $ wbuf\<^sub>f ostore_st)"
  apply (frule inv_ostore_wbuf_lengthD[THEN sym])
  apply (frule inv_ostore_usedD)
  apply (clarsimp simp: buf_simps word_le_nat_alt)
  apply (cut_tac wa = "data\<^sub>f (wbuf\<^sub>f ostore_st)" in wordarray_length_leq_length)
  apply simp
 done
(*
\<comment>\<open> ORIGINAL proof which relies on @{thm wordarray_length_ret} \<close>
lemma inv_ostore_used_len_wbufD:
  "inv_ostore mount_st ostore_st \<Longrightarrow> inv_mount_st mount_st \<Longrightarrow> unat (used\<^sub>f ostore_st) \<le> length (\<alpha>wa $ data\<^sub>f $ wbuf\<^sub>f ostore_st)"
  apply (frule inv_ostore_wbuf_lengthD[THEN sym])
  apply (frule inv_ostore_usedD)
  apply (clarsimp simp: word_unat.Rep_inject[symmetric] word_le_nat_alt buf_simps inv_mount_st_def Let_def wordarray_length_ret)
 done
*)
lemma inv_ostore_sync_offsD:
  "inv_ostore mount_st ostore_st \<Longrightarrow>  sync_offs\<^sub>f ostore_st \<le>  used\<^sub>f ostore_st"
by (clarsimp simp:inv_ostore_def)

lemma inv_ostore_fsmD:
  "inv_ostore mount_st ostore_st \<Longrightarrow> inv_ostore_fsm mount_st ostore_st"
by (clarsimp simp:inv_ostore_def)

lemma used_eq_sync_offs_means_no_update:
 "sync_offs\<^sub>f ostore_st = used\<^sub>f ostore_st \<Longrightarrow>
  \<alpha>_updates ostore_st = []"
 unfolding \<alpha>_updates_def by (simp add:  buf_simps)


lemma inv_bufsD[simplified inv_bufs_def Let_def]:
 "inv_ostore mount_st ostore_st \<Longrightarrow> inv_bufs mount_st ostore_st"
  by (simp add: inv_ostore_def)          

\<comment>\<open> ALTERNATIVE proof that does not rely on @{thm wordarray_length_ret} \<close>
lemma length_ubi_buf_eq_sync_offsD:
  "inv_ostore mount_st ostore_st \<Longrightarrow>
   inv_mount_st mount_st \<Longrightarrow>
  length (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) ! unat (wbuf_eb\<^sub>f ostore_st)) =
    unat (sync_offs\<^sub>f ostore_st)"
  apply (frule inv_bufsD)
  apply (subgoal_tac "unat (sync_offs\<^sub>f ostore_st) \<le> unat (buf_length (wbuf\<^sub>f ostore_st))")
   apply (cut_tac wa = "data\<^sub>f (wbuf\<^sub>f ostore_st)" in  wordarray_length_leq_length)
   apply (clarsimp simp: buf_simps min_absorb1)
  apply (frule inv_ostore_usedD)
  apply (clarsimp simp: inv_ostore_def buf_simps inv_mount_st_def Let_def, unat_arith+)
  done
(*
\<comment>\<open> ORIGINAL proof that relies on @{thm wordarray_length_ret} \<close>
lemma length_ubi_buf_eq_sync_offsD:
  "inv_ostore mount_st ostore_st \<Longrightarrow>
   inv_mount_st mount_st \<Longrightarrow>
  length (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) ! unat (wbuf_eb\<^sub>f ostore_st)) =
    unat (sync_offs\<^sub>f ostore_st)"
   apply (frule inv_bufsD)
  apply (subgoal_tac "unat (sync_offs\<^sub>f ostore_st) \<le> unat (buf_length (wbuf\<^sub>f ostore_st))")
   using wordarray_length_ret[where arr="data\<^sub>f (wbuf\<^sub>f ostore_st)"]
   apply (clarsimp simp:  inv_bufs_def buf_simps min_absorb1 Let_def)
   apply unat_arith
 apply (frule inv_ostore_usedD)
 apply (clarsimp simp: inv_ostore_def buf_simps inv_mount_st_def Let_def, unat_arith+)
done
*)
lemma inv_ubi_volD:
 "inv_ostore mount_st ostore_st \<Longrightarrow> inv_ubi_vol mount_st (OstoreState.ubi_vol\<^sub>f ostore_st)"
 by (drule inv_bufsD, clarsimp simp: inv_bufs_def)

lemma inv_ostore_indexD:
 "inv_ostore mount_st ostore_st \<Longrightarrow> inv_ostore_index mount_st ostore_st"
 by (clarsimp simp: inv_ostore_def)

\<comment>\<open> REQUIRES @{thm wordarray_length_ret} \<close>
lemma inv_ostore_eb_size_wbuf_eqD:
  "inv_ostore mount_st ostore_st  \<Longrightarrow>
   unat (eb_size\<^sub>f (super\<^sub>f mount_st)) = length (\<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st)))"
using wordarray_length_ret[where arr="(data\<^sub>f (wbuf\<^sub>f ostore_st))"]
by (clarsimp simp: inv_ostore_def Let_def buf_simps wordarray_length_ret)

\<comment>\<open> REQUIRES @{thm wordarray_length_ret} \<close>
lemma inv_ostore_eb_size_rbuf_eqD:
  "inv_ostore mount_st ostore_st  \<Longrightarrow>
   unat (eb_size\<^sub>f (super\<^sub>f mount_st)) = length (\<alpha>wa (data\<^sub>f (rbuf\<^sub>f ostore_st)))"
using wordarray_length_ret[where arr="(data\<^sub>f (rbuf\<^sub>f ostore_st))"]
by (clarsimp simp: inv_ostore_def Let_def buf_simps wordarray_length_ret)

\<comment>\<open> ALTERNATIVE proof that does not rely on @{thm wordarray_length_ret} \<close>
lemma inv_ostore_buf_boundD:
  "inv_ostore mount_st ostore_st \<Longrightarrow>
   unat (buf_bound (wbuf\<^sub>f ostore_st)) \<le> length (\<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st)))"
  using wordarray_length_leq_length[of "data\<^sub>f (wbuf\<^sub>f ostore_st)"]
  by (clarsimp simp: inv_ostore_def buf_simps)
(*
\<comment>\<open> ORIGINAL proof that relies on @{thm wordarray_length_ret} \<close>
lemma inv_ostore_buf_boundD:
  "inv_ostore mount_st ostore_st \<Longrightarrow>
   unat (buf_bound (wbuf\<^sub>f ostore_st)) \<le> length (\<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st)))"
using wordarray_length_ret[where arr="(data\<^sub>f (wbuf\<^sub>f ostore_st))",symmetric]
by (clarsimp simp: inv_ostore_def buf_simps)
*)
\<comment>\<open> REQUIRES @{thm wordarray_length_ret} \<close>
lemma inv_ostore_buf_bound_eqD:
  "inv_ostore mount_st ostore_st \<Longrightarrow>
   unat (buf_bound (wbuf\<^sub>f ostore_st)) = length (\<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st)))"
using wordarray_length_ret[where arr="(data\<^sub>f (wbuf\<^sub>f ostore_st))",symmetric]
by (clarsimp simp: inv_ostore_def buf_simps)

lemma inv_mount_st_no_summaryD:
  "inv_mount_st mount_st \<Longrightarrow> \<not> no_summary\<^sub>f mount_st"
 by (simp add: inv_mount_st_def Let_def)

lemma inv_logD[simplified inv_log_def]:
  "inv_ostore mount_st ostore_st \<Longrightarrow>
   inv_log (list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))) (prod.snd $ list_trans_no_pad (buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st)))"
 by (clarsimp simp add: inv_ostore_def Let_def)


lemma inv_ostore_used_no_overflowD:
 "inv_ostore mount_st ostore_st \<Longrightarrow> used\<^sub>f ostore_st < used\<^sub>f ostore_st + io_size\<^sub>f (super\<^sub>f mount_st)"
 by (clarsimp simp: inv_ostore_def)

lemma used_neq_sync_offs_means_updates_not_Nil:
assumes inv_ostore: "inv_ostore mount_st ostore_st"
shows
 "sync_offs\<^sub>f ostore_st \<noteq> used\<^sub>f ostore_st \<Longrightarrow>
  \<alpha>_updates ostore_st \<noteq> []"
 unfolding \<alpha>_updates_def 
using inv_bufsD[OF inv_ostore]  inv_ostore_sync_offsD[OF inv_ostore]
 by (fastforce simp add: valid_list_trans_no_pad_def)

lemma inv_mount_st_eb_size_boundD:
  "inv_mount_st mount_st \<Longrightarrow> eb_size\<^sub>f (super\<^sub>f mount_st) \<le> bilbyFsMaxEbSize"
 by (simp add: inv_mount_st_def Let_def)

lemma inv_fsm_stD[simplified inv_fsm_st_def]:
 "inv_ostore mount_st ostore_st \<Longrightarrow> inv_fsm_st mount_st (fsm_st\<^sub>f ostore_st)"
 by (clarsimp simp: inv_ostore_def)

lemma inv_ostore_wbuf_eb_rangeD:
 "inv_ostore mount_st ostore_st \<Longrightarrow>   wbuf_eb\<^sub>f ostore_st \<ge> bilbyFsFirstLogEbNum \<and>
  wbuf_eb\<^sub>f ostore_st < nb_eb\<^sub>f (super\<^sub>f mount_st)"
 by (clarsimp simp: inv_ostore_def)

lemma inv_opadD[simplified inv_opad_def]:
 "inv_ostore mount_st ostore_st \<Longrightarrow> inv_opad (opad\<^sub>f ostore_st)"
 by (simp add: inv_ostore_def)

definition
 valid_pad_obj :: "Obj\<^sub>T \<Rightarrow> bool"
where
 "valid_pad_obj obj \<equiv> otype\<^sub>f obj = bilbyFsObjTypePad \<and> is_valid_Obj obj \<and> Obj.offs\<^sub>f obj = 0"

lemma is_valid_ObjCommit_trans_len:
 "valid_pad_obj obj \<Longrightarrow> is_valid_ObjCommit obj (sObj obj) \<Longrightarrow> unat (Obj.len\<^sub>f obj) = length (sObj obj) \<Longrightarrow>  trans_len (sObj obj) = length (sObj obj)"
  apply (clarsimp simp add: is_valid_ObjTrans)
  apply (frule is_valid_ObjHeader_len_facts, clarsimp)
  apply (case_tac "sObj obj")
   apply (simp add: bilbyFsObjHeaderSize_def is_valid_ObjHeader_def)
  apply (simp add: trans_len_Cons)
  apply (rename_tac x xs)
  apply (clarsimp simp add: valid_pad_obj_def is_valid_ObjHeader_def)
  apply (drule_tac t="x#xs" in sym, simp add: Obj_inverse[where xs=Nil, simplified] is_valid_ObjTrans)
 done

lemma is_valid_ObjHeader_length_sObj:
 "valid_pad_obj obj \<Longrightarrow> is_valid_ObjHeader obj (sObj obj)  \<Longrightarrow> length (sObj obj) = unat (Obj.len\<^sub>f obj)"
  by (frule is_valid_ObjHeader_len_facts)
     (clarsimp simp: is_valid_ObjHeader_def length_sObj valid_pad_obj_def)


lemma inv_ostore_valid_pad_objD:
 "inv_ostore mount_st ostore_st \<Longrightarrow> valid_pad_obj (opad\<^sub>f ostore_st)"
 by (drule inv_opadD)  (clarsimp simp: inv_ostore_def valid_pad_obj_def is_valid_Obj_def)

lemma inv_ostoreI:
  assumes
    "sync_offs\<^sub>f ostore_st \<le> used\<^sub>f ostore_st"
    "io_size\<^sub>f (super\<^sub>f mount_st) udvd sync_offs\<^sub>f ostore_st"
    "used\<^sub>f ostore_st \<le> eb_size\<^sub>f (super\<^sub>f mount_st)"
    "used\<^sub>f ostore_st < used\<^sub>f ostore_st + io_size\<^sub>f (super\<^sub>f mount_st)"
    "buf_length (rbuf\<^sub>f ostore_st) = eb_size\<^sub>f (super\<^sub>f mount_st)"
    "buf_length (wbuf\<^sub>f ostore_st) = eb_size\<^sub>f (super\<^sub>f mount_st)"
    "buf_bound (wbuf\<^sub>f ostore_st) = eb_size\<^sub>f (super\<^sub>f mount_st)"
    "wbuf_eb\<^sub>f ostore_st \<ge> bilbyFsFirstLogEbNum"
    "wbuf_eb\<^sub>f ostore_st < nb_eb\<^sub>f (super\<^sub>f mount_st)"
    "inv_opad (opad\<^sub>f ostore_st)"
    "\<alpha>_ostore_runtime ostore_st = \<alpha>_ostore_uptodate ostore_st"
    "inv_ostore_summary mount_st ostore_st"
    "inv_ostore_index mount_st ostore_st"
    "inv_ostore_index_gim_disjoint ostore_st"
    "inv_bufs mount_st ostore_st"
    "inv_fsm_st mount_st (fsm_st\<^sub>f ostore_st)"
    "inv_ostore_fsm mount_st ostore_st"
    "inv_flash (list_eb_log_wbuf ostore_st)"
    "inv_log (list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st)))
    (prod.snd $ list_trans_no_pad (buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st)))"
  shows
    "inv_ostore mount_st ostore_st"
  using assms
  unfolding inv_ostore_def
  by fastforce

lemma inv_ostoreE:
  assumes
    "inv_ostore mount_st ostore_st"
    "sync_offs\<^sub>f ostore_st \<le> used\<^sub>f ostore_st \<Longrightarrow>
     io_size\<^sub>f (super\<^sub>f mount_st) udvd sync_offs\<^sub>f ostore_st \<Longrightarrow>
     used\<^sub>f ostore_st \<le> eb_size\<^sub>f (super\<^sub>f mount_st)\<Longrightarrow>
     used\<^sub>f ostore_st < used\<^sub>f ostore_st + io_size\<^sub>f (super\<^sub>f mount_st) \<Longrightarrow>
     buf_length (rbuf\<^sub>f ostore_st) = eb_size\<^sub>f (super\<^sub>f mount_st) \<Longrightarrow>
     buf_length (wbuf\<^sub>f ostore_st) = eb_size\<^sub>f (super\<^sub>f mount_st) \<Longrightarrow>
     buf_bound (wbuf\<^sub>f ostore_st) = eb_size\<^sub>f (super\<^sub>f mount_st) \<Longrightarrow>
     wbuf_eb\<^sub>f ostore_st \<ge> bilbyFsFirstLogEbNum \<Longrightarrow>
     wbuf_eb\<^sub>f ostore_st < nb_eb\<^sub>f (super\<^sub>f mount_st) \<Longrightarrow>
     inv_opad (opad\<^sub>f ostore_st) \<Longrightarrow>
     \<alpha>_ostore_runtime ostore_st = \<alpha>_ostore_uptodate ostore_st \<Longrightarrow>
     inv_ostore_summary mount_st ostore_st \<Longrightarrow>
     inv_ostore_index mount_st ostore_st \<Longrightarrow>
     inv_ostore_index_gim_disjoint ostore_st \<Longrightarrow>
     inv_bufs mount_st ostore_st \<Longrightarrow>
     inv_fsm_st mount_st (fsm_st\<^sub>f ostore_st) \<Longrightarrow>
     inv_ostore_fsm mount_st ostore_st \<Longrightarrow>
     inv_flash (list_eb_log_wbuf ostore_st) \<Longrightarrow>
     inv_log (list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st)))
       (prod.snd $ list_trans_no_pad (buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st))) \<Longrightarrow>
     thesis"
  shows "thesis"
  using assms
  unfolding inv_ostore_def
  by fastforce

end

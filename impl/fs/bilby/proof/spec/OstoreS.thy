(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory OstoreS
imports
  "../impl/BilbyFs_Shallow_Desugar_Tuples"
  "../impl/BilbyFs_ShallowConsts_Desugar_Tuples"
  "../adt/ArrayT"
begin

type_synonym ostore_map = "ObjId \<Rightarrow> Obj\<^sub>T option"

definition "obj_id_xinfo oid \<equiv> bilbyFsXinfoMask AND oid"

definition "obj_is_inode obj \<equiv> otype\<^sub>f obj = bilbyFsObjTypeInode"
definition "obj_is_dentarr obj \<equiv> otype\<^sub>f obj = bilbyFsObjTypeDentarr"
definition "obj_is_data obj \<equiv> otype\<^sub>f obj = bilbyFsObjTypeData"
definition "obj_is_pad obj \<equiv> otype\<^sub>f obj = bilbyFsObjTypePad"
definition "obj_is_super obj \<equiv> otype\<^sub>f obj = bilbyFsObjTypeSuper"
definition "obj_is_del obj \<equiv> otype\<^sub>f obj = bilbyFsObjTypeDel"
definition "obj_is_summary obj \<equiv> otype\<^sub>f obj = bilbyFsObjTypeSum"

definition
  oid_is_deleted_by :: "ObjId \<Rightarrow> ObjId \<Rightarrow> bool"
 where
 "oid_is_deleted_by oid delid \<equiv>
    (if obj_id_is_inode delid then
      inum_from_obj_id delid = inum_from_obj_id oid
    else if obj_id_is_dentarr delid then
      delid = oid
    else if obj_id_is_data delid then
      inum_from_obj_id delid = inum_from_obj_id oid \<and>
      obj_id_xinfo oid \<ge> obj_id_xinfo delid
    else
      False)"

definition
  obj_is_deleted_by :: "Obj\<^sub>T \<Rightarrow> Obj\<^sub>T \<Rightarrow> bool"
where
 "obj_is_deleted_by obj delobj \<equiv> 
   Obj.sqnum\<^sub>f obj < Obj.sqnum\<^sub>f delobj \<and>
   oid_is_deleted_by (get_obj_oid obj) (get_obj_oid delobj)"

definition
  max_opt_obj :: "Obj\<^sub>T option \<Rightarrow> Obj\<^sub>T option \<Rightarrow> Obj\<^sub>T option"
where
 "max_opt_obj o1 o2 \<equiv>
   case (o1, o2) of
     (option.None, v) \<Rightarrow> v
    | (v, option.None) \<Rightarrow> v
    | (option.Some o1, option.Some o2) \<Rightarrow>
      option.Some (if Obj.sqnum\<^sub>f o1 > Obj.sqnum\<^sub>f o2 then o1 else o2)"

text {* ostore_list_upd: is a helper function for ostore_update.
It captures the changes inflicted to the object store by the
list of object passed as argument. The list of object represent
an object store update, deletion object remove elements and
other objects get inserted or replace existing ones.

ostore_list_upd returns Some None if the list of objects indicates that
the oid passed as argument is deleted by the update and returns the object
if the update contains it.

We have to use a type option of option to differentiate the
case where the object was not found and the case where it is
deleted by the update.

Object was deleted : Some None
Object was added/overwrite: Some Some
Object didn't exist: None
*}
primrec
  ostore_list_upd :: "Obj\<^sub>T list \<Rightarrow> ObjId \<Rightarrow> Obj\<^sub>T option option"
where
"ostore_list_upd [] oid = option.None" |
"ostore_list_upd (x#xs) oid =
    (if obj_is_del x \<and> oid_is_deleted_by oid (get_obj_oid x) then
       option.Some option.None
     else
       (if get_obj_oid x = oid then
         option.Some (option.Some x)
        else ostore_list_upd xs oid))"

text {* Need to update ostore_list_upd to make delete
a second phase as it is required by mount. *}
definition
  ostore_delete :: "Obj\<^sub>T list \<Rightarrow> (ostore_map \<Rightarrow> ostore_map)"
where
  "ostore_delete objs gos = 
     (\<lambda>oid. case ostore_list_upd objs oid of
            option.None \<Rightarrow> gos oid
            | option.Some (option.None) \<Rightarrow> option.None
            | option.Some (option.Some v) \<Rightarrow> gos oid)"

definition
  ostore_update :: "Obj\<^sub>T list \<Rightarrow> (ostore_map \<Rightarrow> ostore_map)"
where
 "ostore_update objs gos =
   (\<lambda>oid. case ostore_list_upd objs oid of
          option.Some x \<Rightarrow> max_opt_obj x (gos oid) |
          option.None \<Rightarrow> gos oid)"


lemmas obj_id_is_defs_simps = obj_id_is_inode_def obj_id_is_dentarr_def obj_id_is_data_def

definition is_valid_dentarr_entries
where
  "is_valid_dentarr_entries entries = (\<forall>entry\<in>set entries. wordarray_length (name\<^sub>f entry) \<le> bilbyFsMaxNameLen)"

definition obj_odentarr :: "Obj\<^sub>T \<Rightarrow> ObjDentarr\<^sub>T"
where
 "obj_odentarr obj \<equiv> (case ounion\<^sub>f obj of TObjDentarr dentarr \<Rightarrow> dentarr)"

definition obj_oinode :: "Obj\<^sub>T \<Rightarrow> ObjInode\<^sub>T"
where
 "obj_oinode obj \<equiv> (case ounion\<^sub>f obj of TObjInode i \<Rightarrow> i)"

definition obj_odata :: "Obj\<^sub>T \<Rightarrow> ObjData\<^sub>T"
where
 "obj_odata obj \<equiv> (case ounion\<^sub>f obj of TObjData d \<Rightarrow> d)"

definition obj_osummary :: "Obj\<^sub>T \<Rightarrow> ObjSummary\<^sub>T"
where
 "obj_osummary obj \<equiv> (case ounion\<^sub>f obj of _ \<Rightarrow> undefined)"

primrec stripNone :: "'a Option\<^sub>T list \<Rightarrow> 'a list"
where
  "stripNone [] = []" |
  "stripNone (x#xs) = (case x of Option.None () \<Rightarrow> stripNone xs | Option.Some v \<Rightarrow> v#stripNone xs)"

definition obj_is_valid :: "Obj\<^sub>T \<Rightarrow> bool"
where
"obj_is_valid obj \<equiv>
  (obj_is_dentarr obj \<longrightarrow>
      (let entries = stripNone (\<alpha>a $ ObjDentarr.entries\<^sub>f $ obj_odentarr obj) in
      (distinct (map name\<^sub>f entries) \<and>
      length entries \<le> unat bilbyFsMaxNbDentarrEntries \<and>
      is_valid_dentarr_entries entries)))"

lemma obj_is_valid_valid_entries:
  "\<lbrakk> obj_is_valid x ; obj_is_dentarr x\<rbrakk> \<Longrightarrow>
    is_valid_dentarr_entries (stripNone $ \<alpha>a $ ObjDentarr.entries\<^sub>f $ obj_odentarr x)"
  by (simp add: Let_def obj_is_valid_def)

definition obj_inv_oid :: "Obj\<^sub>T \<Rightarrow> bool"
where
"obj_inv_oid obj \<equiv> (obj_is_inode obj \<or> obj_is_dentarr obj \<or> obj_is_data obj) \<longrightarrow>
                    obj_id_type (get_obj_oid obj) = ucast (otype\<^sub>f obj)"

definition
 inv_read_obj :: "Obj\<^sub>T \<Rightarrow> bool"
where
 "inv_read_obj obj \<equiv>
  obj_is_valid obj \<and> obj_inv_oid obj \<and> (obj_is_dentarr obj \<longrightarrow>
    (length $ stripNone $ \<alpha>a $ ObjDentarr.entries\<^sub>f $ obj_odentarr obj) > 0)"
(* FIXME: add something like @{otype\<^sub>f obj = otype_from_ounion obj} *)

text {* inv_\<alpha>_ostore: invariant on the object store \<alpha> projection (user point-of-view invariant *) *}
definition
 inv_\<alpha>_ostore :: "ostore_map \<Rightarrow> bool"
where
 "inv_\<alpha>_ostore os \<equiv>
  (\<forall>oid obj. os oid  = option.Some obj \<longrightarrow> (get_obj_oid obj = oid \<and> inv_read_obj obj))"

definition
  no_deleted_objs_list :: "Obj\<^sub>T list \<Rightarrow> bool"
where
  "no_deleted_objs_list xs \<equiv> (\<forall>entry\<in>set xs. \<not> obj_is_del entry)"

lemma ostore_list_upd_no_deleted[rule_format]:
  "\<And>objs. no_deleted_objs_list objs  \<longrightarrow>
         ostore_list_upd objs oid \<noteq> option.Some option.None"
  unfolding no_deleted_objs_list_def
  by (induct_tac objs, simp+)

fun
  apply_n_updates :: "nat \<Rightarrow> ostore_map \<Rightarrow> (ostore_map \<Rightarrow> ostore_map) list \<Rightarrow> ostore_map"
where
 "apply_n_updates n os_map os_updates = fold id (take n os_updates) os_map"

end

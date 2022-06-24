(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Shallow
imports
  "Cogent.ValueSemantics"
  "HOL-Word.Word_Bitwise"
Word_Lib.Word_Lemmas
  ShallowUtil
begin

type_synonym funtyp = "char list"

inductive_cases v_sem_letE: "\<xi> , \<gamma> \<turnstile> Let a b \<Down> b'"
inductive_cases v_sem_letBangE: "\<xi> , \<gamma> \<turnstile> LetBang vs a b \<Down> b'"
inductive_cases v_sem_litE: "\<xi> , \<gamma> \<turnstile> Lit l \<Down> v"
inductive_cases v_sem_customintE: "\<xi> , \<gamma> \<turnstile> CustomInt n l \<Down> v"
inductive_cases v_sem_primE: "\<xi> , \<gamma> \<turnstile> Prim p as \<Down> r"
inductive_cases v_sem_memberE: "\<xi> , \<gamma> \<turnstile> Member x f \<Down> r"
inductive_cases v_sem_tupleE: "\<xi> , \<gamma> \<turnstile> Tuple a b \<Down> r"
inductive_cases v_sem_if: " \<xi> , \<gamma> \<turnstile> If x t e \<Down> r"
inductive_cases v_sem_conE: "\<xi> , \<gamma> \<turnstile> Con i t x \<Down> r"
inductive_cases v_sem_esacE: "\<xi>, \<gamma> \<turnstile> Esac v  n \<Down> r"
inductive_cases v_sem_caseE:  "\<xi> , \<gamma> \<turnstile> Case x c m n \<Down> r"
inductive_cases v_sem_splitE: "\<xi> , \<gamma> \<turnstile> Split x e \<Down> e'"
inductive_cases v_sem_takeE: "\<xi> , \<gamma> \<turnstile> Take x f e \<Down> e'"
inductive_cases v_sem_putE: "\<xi> , \<gamma> \<turnstile> Put x f e \<Down> e'"
inductive_cases v_sem_castE: "\<xi> , \<gamma> \<turnstile> Cast \<tau> e \<Down> e'"
inductive_cases v_sem_custom_ucastE: "\<xi> , \<gamma> \<turnstile> CustomUCast \<tau> e \<Down> e'"
inductive_cases v_sem_custom_dcastE: "\<xi> , \<gamma> \<turnstile> CustomDCast \<tau> e \<Down> e'"
inductive_cases v_sem_structE: "\<xi> , \<gamma> \<turnstile> Struct ts xs \<Down> e'"
inductive_cases v_sem_AppE: "\<xi> , \<gamma> \<turnstile> App f v \<Down> e'"
inductive_cases v_sem_allE: "\<xi> , \<gamma> \<turnstile>* es \<Down> es'"
inductive_cases v_sem_all_NilE: "\<xi> , \<gamma> \<turnstile>* [] \<Down> es'"
inductive_cases v_sem_all_ConsE: "\<xi> , \<gamma> \<turnstile>* (e#es) \<Down> es'"
inductive_cases v_sem_unitE: "\<xi> , \<gamma> \<turnstile> Unit \<Down> r"
inductive_cases v_sem_promoteE: "\<xi>, \<gamma> \<turnstile> Promote \<tau> e \<Down> r"

lemmas v_sem_elims =
  v_sem_letE
  v_sem_letBangE
  v_sem_litE
  v_sem_customintE
  v_sem_primE
  v_sem_memberE
  v_sem_tupleE
  v_sem_if
  v_sem_conE
  v_sem_esacE
  v_sem_caseE
  v_sem_splitE
  v_sem_takeE
  v_sem_putE
  v_sem_castE
  v_sem_custom_ucastE
  v_sem_custom_dcastE
  v_sem_structE
  v_sem_AppE
  v_sem_allE
  v_sem_all_NilE
  v_sem_all_ConsE
  v_sem_unitE
  v_sem_promoteE

(* Should we use type class here, instead of using "defs (overloaded)"?
 * Christine's approach with type class looks more systematic.*)
consts valRel :: "(funtyp,'b) vabsfuns \<Rightarrow> 'a \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
overloading
 valRel_bool  \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> bool \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
 valRel_u8    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 8 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
 valRel_u16   \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 16 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
 valRel_u32   \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 32 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
 valRel_u64   \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 64 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
 valRel_unit  \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> unit \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
 valRel_pair  \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 'x \<times> 'y \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
 valRel_fun   \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"

(* it would be better to generate those automatically in ML *)
valRel_u1    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 1 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u2    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 2 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u3    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 3 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u4    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 4 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u5    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 5 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u6    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 6 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u7    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 7 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u9    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 9 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u10    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 10 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u11    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 11 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u12    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 12 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u13    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 13 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u14    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 14 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u15    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 15 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u17    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 17 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u18    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 18 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u19    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 19 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u20    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 20 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u21    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 21 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u22    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 22 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u23    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 23 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u24    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 24 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u25    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 25 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u26    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 26 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u27    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 27 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u28    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 28 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u29    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 29 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u30    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 30 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u31    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 31 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u33    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 33 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u34    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 34 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u35    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 35 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u36    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 36 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u37    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 37 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u38    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 38 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u39    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 39 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u40    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 40 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u41    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 41 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u42    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 42 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u43    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 43 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u44    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 44 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u45    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 45 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u46    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 46 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u47    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 47 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u48    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 48 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u49    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 49 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u50    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 50 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u51    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 51 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u52    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 52 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u53    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 53 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u54    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 54 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u55    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 55 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u56    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 56 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u57    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 57 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u58    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 58 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u59    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 59 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u60    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 60 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u61    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 61 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u62    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 62 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"
valRel_u63    \<equiv> "valRel :: (funtyp,'b) vabsfuns \<Rightarrow> 63 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool"

begin

fun valRel_bool :: "(funtyp,'b) vabsfuns \<Rightarrow> bool \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_bool \<xi> b v = (v = (vval.VPrim (LBool b)))"

fun valRel_u8 :: "(funtyp,'b) vabsfuns \<Rightarrow> 8 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u8 \<xi> w v = (v = vval.VPrim (LU8 w))"

fun valRel_u16 :: "(funtyp,'b) vabsfuns \<Rightarrow> 16 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u16 \<xi> w v = (v = vval.VPrim (LU16 w))"

fun valRel_u32 :: "(funtyp,'b) vabsfuns \<Rightarrow> 32 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u32 \<xi> w v = (v = vval.VPrim (LU32 w))"

fun valRel_u64 :: "(funtyp,'b) vabsfuns \<Rightarrow> 64 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u64 \<xi> w v = (v = vval.VPrim (LU64 w))"

fun valRel_unit :: "(funtyp,'b) vabsfuns \<Rightarrow> unit \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_unit \<xi> w v = (v = vval.VUnit)"

fun valRel_pair :: "(funtyp,'b) vabsfuns \<Rightarrow> 'x \<times> 'y \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_pair \<xi> p v = (\<exists> va vb. v = (vval.VProduct va vb) \<and> valRel \<xi> (fst p) va \<and> valRel \<xi> (snd p) vb)"

fun valRel_fun :: "(funtyp,'b) vabsfuns \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_fun \<xi> f f' =
((\<exists>e ts ls. f' = VFunction e ts ls \<and>
          (\<forall>x x' v'. valRel \<xi> x x' \<longrightarrow> (\<xi>, [x'] \<turnstile> specialise ls ts e \<Down> v') \<longrightarrow> valRel \<xi> (f x) v')) \<or>
  (\<exists>afun ts ls. f' = VAFunction afun ts ls \<and> (\<forall>x x' v'. valRel \<xi> x x' \<longrightarrow> \<xi> afun x' v' \<longrightarrow> valRel \<xi> (f x) v')))"


(* it would be better to generate those from ML *)

fun valRel_u1 :: "(funtyp,'b) vabsfuns \<Rightarrow> 1 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u1 \<xi> w v = (v = vval.VCustomInt 1 (unat w))"
fun valRel_u2 :: "(funtyp,'b) vabsfuns \<Rightarrow> 2 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u2 \<xi> w v = (v = vval.VCustomInt 2 (unat w))"
fun valRel_u3 :: "(funtyp,'b) vabsfuns \<Rightarrow> 3 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u3 \<xi> w v = (v = vval.VCustomInt 3 (unat w))"
fun valRel_u4 :: "(funtyp,'b) vabsfuns \<Rightarrow> 4 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u4 \<xi> w v = (v = vval.VCustomInt 4 (unat w))"
fun valRel_u5 :: "(funtyp,'b) vabsfuns \<Rightarrow> 5 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u5 \<xi> w v = (v = vval.VCustomInt 5 (unat w))"
fun valRel_u6 :: "(funtyp,'b) vabsfuns \<Rightarrow> 6 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u6 \<xi> w v = (v = vval.VCustomInt 6 (unat w))"
fun valRel_u7 :: "(funtyp,'b) vabsfuns \<Rightarrow> 7 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u7 \<xi> w v = (v = vval.VCustomInt 7 (unat w))"
fun valRel_u9 :: "(funtyp,'b) vabsfuns \<Rightarrow> 9 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u9 \<xi> w v = (v = vval.VCustomInt 9 (unat w))"
fun valRel_u10 :: "(funtyp,'b) vabsfuns \<Rightarrow> 10 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u10 \<xi> w v = (v = vval.VCustomInt 10 (unat w))"
fun valRel_u11 :: "(funtyp,'b) vabsfuns \<Rightarrow> 11 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u11 \<xi> w v = (v = vval.VCustomInt 11 (unat w))"
fun valRel_u12 :: "(funtyp,'b) vabsfuns \<Rightarrow> 12 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u12 \<xi> w v = (v = vval.VCustomInt 12 (unat w))"
fun valRel_u13 :: "(funtyp,'b) vabsfuns \<Rightarrow> 13 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u13 \<xi> w v = (v = vval.VCustomInt 13 (unat w))"
fun valRel_u14 :: "(funtyp,'b) vabsfuns \<Rightarrow> 14 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u14 \<xi> w v = (v = vval.VCustomInt 14 (unat w))"
fun valRel_u15 :: "(funtyp,'b) vabsfuns \<Rightarrow> 15 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u15 \<xi> w v = (v = vval.VCustomInt 15 (unat w))"
fun valRel_u17 :: "(funtyp,'b) vabsfuns \<Rightarrow> 17 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u17 \<xi> w v = (v = vval.VCustomInt 17 (unat w))"
fun valRel_u18 :: "(funtyp,'b) vabsfuns \<Rightarrow> 18 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u18 \<xi> w v = (v = vval.VCustomInt 18 (unat w))"
fun valRel_u19 :: "(funtyp,'b) vabsfuns \<Rightarrow> 19 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u19 \<xi> w v = (v = vval.VCustomInt 19 (unat w))"
fun valRel_u20 :: "(funtyp,'b) vabsfuns \<Rightarrow> 20 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u20 \<xi> w v = (v = vval.VCustomInt 20 (unat w))"
fun valRel_u21 :: "(funtyp,'b) vabsfuns \<Rightarrow> 21 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u21 \<xi> w v = (v = vval.VCustomInt 21 (unat w))"
fun valRel_u22 :: "(funtyp,'b) vabsfuns \<Rightarrow> 22 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u22 \<xi> w v = (v = vval.VCustomInt 22 (unat w))"
fun valRel_u23 :: "(funtyp,'b) vabsfuns \<Rightarrow> 23 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u23 \<xi> w v = (v = vval.VCustomInt 23 (unat w))"
fun valRel_u24 :: "(funtyp,'b) vabsfuns \<Rightarrow> 24 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u24 \<xi> w v = (v = vval.VCustomInt 24 (unat w))"
fun valRel_u25 :: "(funtyp,'b) vabsfuns \<Rightarrow> 25 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u25 \<xi> w v = (v = vval.VCustomInt 25 (unat w))"
fun valRel_u26 :: "(funtyp,'b) vabsfuns \<Rightarrow> 26 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u26 \<xi> w v = (v = vval.VCustomInt 26 (unat w))"
fun valRel_u27 :: "(funtyp,'b) vabsfuns \<Rightarrow> 27 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u27 \<xi> w v = (v = vval.VCustomInt 27 (unat w))"
fun valRel_u28 :: "(funtyp,'b) vabsfuns \<Rightarrow> 28 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u28 \<xi> w v = (v = vval.VCustomInt 28 (unat w))"
fun valRel_u29 :: "(funtyp,'b) vabsfuns \<Rightarrow> 29 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u29 \<xi> w v = (v = vval.VCustomInt 29 (unat w))"
fun valRel_u30 :: "(funtyp,'b) vabsfuns \<Rightarrow> 30 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u30 \<xi> w v = (v = vval.VCustomInt 30 (unat w))"
fun valRel_u31 :: "(funtyp,'b) vabsfuns \<Rightarrow> 31 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u31 \<xi> w v = (v = vval.VCustomInt 31 (unat w))"
fun valRel_u33 :: "(funtyp,'b) vabsfuns \<Rightarrow> 33 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u33 \<xi> w v = (v = vval.VCustomInt 33 (unat w))"
fun valRel_u34 :: "(funtyp,'b) vabsfuns \<Rightarrow> 34 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u34 \<xi> w v = (v = vval.VCustomInt 34 (unat w))"
fun valRel_u35 :: "(funtyp,'b) vabsfuns \<Rightarrow> 35 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u35 \<xi> w v = (v = vval.VCustomInt 35 (unat w))"
fun valRel_u36 :: "(funtyp,'b) vabsfuns \<Rightarrow> 36 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u36 \<xi> w v = (v = vval.VCustomInt 36 (unat w))"
fun valRel_u37 :: "(funtyp,'b) vabsfuns \<Rightarrow> 37 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u37 \<xi> w v = (v = vval.VCustomInt 37 (unat w))"
fun valRel_u38 :: "(funtyp,'b) vabsfuns \<Rightarrow> 38 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u38 \<xi> w v = (v = vval.VCustomInt 38 (unat w))"
fun valRel_u39 :: "(funtyp,'b) vabsfuns \<Rightarrow> 39 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u39 \<xi> w v = (v = vval.VCustomInt 39 (unat w))"
fun valRel_u40 :: "(funtyp,'b) vabsfuns \<Rightarrow> 40 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u40 \<xi> w v = (v = vval.VCustomInt 40 (unat w))"
fun valRel_u41 :: "(funtyp,'b) vabsfuns \<Rightarrow> 41 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u41 \<xi> w v = (v = vval.VCustomInt 41 (unat w))"
fun valRel_u42 :: "(funtyp,'b) vabsfuns \<Rightarrow> 42 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u42 \<xi> w v = (v = vval.VCustomInt 42 (unat w))"
fun valRel_u43 :: "(funtyp,'b) vabsfuns \<Rightarrow> 43 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u43 \<xi> w v = (v = vval.VCustomInt 43 (unat w))"
fun valRel_u44 :: "(funtyp,'b) vabsfuns \<Rightarrow> 44 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u44 \<xi> w v = (v = vval.VCustomInt 44 (unat w))"
fun valRel_u45 :: "(funtyp,'b) vabsfuns \<Rightarrow> 45 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u45 \<xi> w v = (v = vval.VCustomInt 45 (unat w))"
fun valRel_u46 :: "(funtyp,'b) vabsfuns \<Rightarrow> 46 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u46 \<xi> w v = (v = vval.VCustomInt 46 (unat w))"
fun valRel_u47 :: "(funtyp,'b) vabsfuns \<Rightarrow> 47 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u47 \<xi> w v = (v = vval.VCustomInt 47 (unat w))"
fun valRel_u48 :: "(funtyp,'b) vabsfuns \<Rightarrow> 48 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u48 \<xi> w v = (v = vval.VCustomInt 48 (unat w))"
fun valRel_u49 :: "(funtyp,'b) vabsfuns \<Rightarrow> 49 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u49 \<xi> w v = (v = vval.VCustomInt 49 (unat w))"
fun valRel_u50 :: "(funtyp,'b) vabsfuns \<Rightarrow> 50 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u50 \<xi> w v = (v = vval.VCustomInt 50 (unat w))"
fun valRel_u51 :: "(funtyp,'b) vabsfuns \<Rightarrow> 51 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u51 \<xi> w v = (v = vval.VCustomInt 51 (unat w))"
fun valRel_u52 :: "(funtyp,'b) vabsfuns \<Rightarrow> 52 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u52 \<xi> w v = (v = vval.VCustomInt 52 (unat w))"
fun valRel_u53 :: "(funtyp,'b) vabsfuns \<Rightarrow> 53 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u53 \<xi> w v = (v = vval.VCustomInt 53 (unat w))"
fun valRel_u54 :: "(funtyp,'b) vabsfuns \<Rightarrow> 54 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u54 \<xi> w v = (v = vval.VCustomInt 54 (unat w))"
fun valRel_u55 :: "(funtyp,'b) vabsfuns \<Rightarrow> 55 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u55 \<xi> w v = (v = vval.VCustomInt 55 (unat w))"
fun valRel_u56 :: "(funtyp,'b) vabsfuns \<Rightarrow> 56 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u56 \<xi> w v = (v = vval.VCustomInt 56 (unat w))"
fun valRel_u57 :: "(funtyp,'b) vabsfuns \<Rightarrow> 57 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u57 \<xi> w v = (v = vval.VCustomInt 57 (unat w))"
fun valRel_u58 :: "(funtyp,'b) vabsfuns \<Rightarrow> 58 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u58 \<xi> w v = (v = vval.VCustomInt 58 (unat w))"
fun valRel_u59 :: "(funtyp,'b) vabsfuns \<Rightarrow> 59 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u59 \<xi> w v = (v = vval.VCustomInt 59 (unat w))"
fun valRel_u60 :: "(funtyp,'b) vabsfuns \<Rightarrow> 60 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u60 \<xi> w v = (v = vval.VCustomInt 60 (unat w))"
fun valRel_u61 :: "(funtyp,'b) vabsfuns \<Rightarrow> 61 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u61 \<xi> w v = (v = vval.VCustomInt 61 (unat w))"
fun valRel_u62 :: "(funtyp,'b) vabsfuns \<Rightarrow> 62 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u62 \<xi> w v = (v = vval.VCustomInt 62 (unat w))"
fun valRel_u63 :: "(funtyp,'b) vabsfuns \<Rightarrow> 63 word \<Rightarrow> (funtyp,'b) vval \<Rightarrow> bool" where
  "valRel_u63 \<xi> w v = (v = vval.VCustomInt 63 (unat w))"



end

context value_sem
begin

text {* Shallow & deep embedding correspondence:
  deep embedding is a refinement of the shallow representation
*}
definition
  scorres :: "'s \<Rightarrow> (funtyp) expr \<Rightarrow> (funtyp,'a) vval env \<Rightarrow> (funtyp,'a) vabsfuns \<Rightarrow> bool"
where
  "scorres s d \<gamma> \<xi> \<equiv> (\<forall>r. (\<xi>, \<gamma> \<turnstile> d \<Down> r) \<longrightarrow> valRel \<xi> s r)"

(* Mechanism to pattern-match on shallow variables. *)
definition "shallow_tac__var x \<equiv> x"


text {* Straightforward rules. *}

lemma scorres_var:
  "valRel \<xi> s (\<gamma>!i) \<Longrightarrow> scorres (shallow_tac__var s) (Var i) \<gamma> \<xi>"
  unfolding scorres_def shallow_tac__var_def
  by fastforce

lemma scorres_unit:
  "scorres (u::unit) Unit \<gamma> \<xi>"
  by (clarsimp simp: scorres_def elim!: v_sem_elims)

lemma scorres_promote:
assumes "scorres x x' \<gamma> \<xi>"
shows "scorres x(Promote ts x') \<gamma> \<xi>"
  using assms
by (clarsimp simp:scorres_def elim!:v_sem_elims)

lemma scorres_let_desugar:
assumes
  "scorres v a \<gamma> \<xi>"
  "\<And>v' a'. valRel \<xi> v' a' \<Longrightarrow> scorres (s (shallow_tac__var v')) b (a'#\<gamma>) \<xi>"
shows
  "scorres (Let\<^sub>d\<^sub>s v s) (expr.Let a b) \<gamma> \<xi>"
  using assms
  by (auto simp:Let\<^sub>d\<^sub>s_def scorres_def shallow_tac__var_def elim!: v_sem_elims)

lemma scorres_let:
assumes
  "scorres v a \<gamma> \<xi>"
  "\<And>v' a'. valRel \<xi> v' a' \<Longrightarrow> scorres (s (shallow_tac__var v')) b (a'#\<gamma>) \<xi>"
shows
  "scorres (HOL.Let v s) (expr.Let a b) \<gamma> \<xi>"
  using assms
  by (auto simp: scorres_def shallow_tac__var_def elim!: v_sem_elims)

lemma scorres_letBang_desugar:
assumes
  "scorres v a \<gamma> \<xi>"
  "\<And>v' a'. valRel \<xi> v' a' \<Longrightarrow> scorres (s (shallow_tac__var v')) b (a'#\<gamma>) \<xi>"
shows
  "scorres (Let\<^sub>d\<^sub>s v s) (expr.LetBang vs a b) \<gamma> \<xi>"
  using assms
  by (auto simp: scorres_def Let\<^sub>d\<^sub>s_def shallow_tac__var_def elim!: v_sem_elims)

lemma scorres_letBang:
assumes
  "scorres v a \<gamma> \<xi>"
  "\<And>v' a'. valRel \<xi> v' a' \<Longrightarrow> scorres (s (shallow_tac__var v')) b (a'#\<gamma>) \<xi>"
shows
  "scorres (HOL.Let v s) (expr.LetBang vs a b) \<gamma> \<xi>"
  using assms
  by (auto simp: scorres_def shallow_tac__var_def elim!: v_sem_elims)

lemma scorres_if:
  assumes a: "scorres a a' \<gamma> \<xi>"
  assumes b: "scorres b b' \<gamma> \<xi>"
  assumes c: "scorres c c' \<gamma> \<xi>"
  shows "scorres (if a then b else c) (If a' b' c') \<gamma> \<xi>"
  using a b c
  by (fastforce simp: scorres_def elim!: v_sem_if split: if_splits)

lemma scorres_fun:
  (* Must match format for callee theorems. *)
  assumes "\<And>v v'. valRel \<xi> v v' \<Longrightarrow> scorres (f v) (specialise ls ts f') [v'] \<xi>"

  shows "scorres f (Fun f' ts ls) \<gamma> \<xi>"
  using assms
  by (auto simp: scorres_def elim!: v_sem_elims)


text {* Cumbersome rules for numbers and bools. *}

lemma scorres_lit:
  "\<And>b b'. b = b' \<Longrightarrow> scorres b (Lit (LBool b')) \<gamma> \<xi>"
  "\<And>w w'. w = w' \<Longrightarrow> scorres w (Lit (LU8 w')) \<gamma> \<xi>"
  "\<And>w w'. w = w' \<Longrightarrow> scorres w (Lit (LU16 w')) \<gamma> \<xi>"
  "\<And>w w'. w = w' \<Longrightarrow> scorres w (Lit (LU32 w')) \<gamma> \<xi>"
  "\<And>w w'. w = w' \<Longrightarrow> scorres w (Lit (LU64 w')) \<gamma> \<xi>"
  by (auto simp: scorres_def elim: v_sem_litE)

lemma scorres_prim_add:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x + y :: 8  word) (Prim (Plus U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x + y :: 16 word) (Prim (Plus U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x + y :: 32 word) (Prim (Plus U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x + y :: 64 word) (Prim (Plus U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_sub:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x - y :: 8  word) (Prim (Minus U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x - y :: 16 word) (Prim (Minus U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x - y :: 32 word) (Prim (Minus U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x - y :: 64 word) (Prim (Minus U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_times:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x * y :: 8  word) (Prim (Times U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x * y :: 16 word) (Prim (Times U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x * y :: 32 word) (Prim (Times U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x * y :: 64 word) (Prim (Times U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_divide:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_div x y :: 8  word) (Prim (Divide U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_div x y :: 16 word) (Prim (Divide U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_div x y :: 32 word) (Prim (Divide U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_div x y :: 64 word) (Prim (Divide U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_mod:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_mod x y :: 8  word) (Prim (Mod U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_mod x y :: 16 word) (Prim (Mod U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_mod x y :: 32 word) (Prim (Mod U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_mod x y :: 64 word) (Prim (Mod U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_not:
  "scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres (\<not> x) (Prim Not [x']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)

lemma scorres_prim_and:
  "scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x \<and> y) (Prim And [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)

lemma scorres_prim_or:
  "scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow> scorres (x \<or> y) (Prim Or [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)

lemma scorres_prim_gt:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) > y) (Prim (Gt U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) > y) (Prim (Gt U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) > y) (Prim (Gt U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) > y) (Prim (Gt U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_ge:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) \<ge> y) (Prim (Ge U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) \<ge> y) (Prim (Ge U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) \<ge> y) (Prim (Ge U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) \<ge> y) (Prim (Ge U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_lt:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) < y) (Prim (Lt U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) < y) (Prim (Lt U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) < y) (Prim (Lt U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) < y) (Prim (Lt U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_le:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) \<le> y) (Prim (Le U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) \<le> y) (Prim (Le U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) \<le> y) (Prim (Le U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) \<le> y) (Prim (Le U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_eq:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) = y) (Prim (Eq (Num U8 )) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) = y) (Prim (Eq (Num U16)) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) = y) (Prim (Eq (Num U32)) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) = y) (Prim (Eq (Num U64)) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: bool   ) = y) (Prim (Eq Bool     ) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_neq:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) \<noteq> y) (Prim (NEq (Num U8 )) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) \<noteq> y) (Prim (NEq (Num U16)) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) \<noteq> y) (Prim (NEq (Num U32)) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) \<noteq> y) (Prim (NEq (Num U64)) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: bool   ) \<noteq> y) (Prim (NEq Bool     ) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_bitand:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) AND y) (Prim (BitAnd U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) AND y) (Prim (BitAnd U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) AND y) (Prim (BitAnd U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) AND y) (Prim (BitAnd U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_bitor:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) OR y) (Prim (BitOr U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) OR y) (Prim (BitOr U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) OR y) (Prim (BitOr U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) OR y) (Prim (BitOr U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_bitxor:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 8  word) XOR y) (Prim (BitXor U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 16 word) XOR y) (Prim (BitXor U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 32 word) XOR y) (Prim (BitXor U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres ((x :: 64 word) XOR y) (Prim (BitXor U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_lshift:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_shift shiftl (x :: 8  word) y) (Prim (LShift U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_shift shiftl (x :: 16 word) y) (Prim (LShift U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_shift shiftl (x :: 32 word) y) (Prim (LShift U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_shift shiftl (x :: 64 word) y) (Prim (LShift U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_rshift:
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_shift shiftr (x :: 8  word) y) (Prim (RShift U8 ) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_shift shiftr (x :: 16 word) y) (Prim (RShift U16) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_shift shiftr (x :: 32 word) y) (Prim (RShift U32) [x', y']) \<gamma> \<xi>"
  "\<And>x x' y y'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres y y' \<gamma> \<xi> \<Longrightarrow>
    scorres (checked_shift shiftr (x :: 64 word) y) (Prim (RShift U64) [x', y']) \<gamma> \<xi>"
  by (fastforce elim!: v_sem_elims simp: scorres_def eval_prim_def)+

lemma scorres_prim_complement:
  "\<And>x x'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres (NOT (x::8  word)) (Prim (Complement U8 ) [x']) \<gamma> \<xi>"
  "\<And>x x'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres (NOT (x::16 word)) (Prim (Complement U16) [x']) \<gamma> \<xi>"
  "\<And>x x'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres (NOT (x::32 word)) (Prim (Complement U32) [x']) \<gamma> \<xi>"
  "\<And>x x'. scorres x x' \<gamma> \<xi> \<Longrightarrow> scorres (NOT (x::64 word)) (Prim (Complement U64) [x']) \<gamma> \<xi>"
  by (auto elim!: v_sem_elims simp: scorres_def eval_prim_def)

lemma scorres_cast:
  "\<And>x x'. scorres (x :: 8  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 8  word) (Cast U8  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 8  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 16 word) (Cast U16 x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 8  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (Cast U32 x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 8  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (Cast U64 x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 16 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 16 word) (Cast U16 x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 16 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (Cast U32 x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 16 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (Cast U64 x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (Cast U32 x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (Cast U64 x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (Cast U64 x') \<gamma> \<xi>"
  by (auto simp: scorres_def ucast_id elim!: v_sem_elims)



(* it would be better to generate those automatically in ML *)
lemma scorres_custom_ucast:
  "\<And>x x'. scorres (x :: 1  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 8 word) (CustomUCast U8  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 2  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 8 word) (CustomUCast U8  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 3  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 8 word) (CustomUCast U8  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 4  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 8 word) (CustomUCast U8  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 5  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 8 word) (CustomUCast U8  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 6  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 8 word) (CustomUCast U8  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 7  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 8 word) (CustomUCast U8  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 9  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 16 word) (CustomUCast U16  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 10  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 16 word) (CustomUCast U16  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 11  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 16 word) (CustomUCast U16  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 12  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 16 word) (CustomUCast U16  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 13  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 16 word) (CustomUCast U16  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 14  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 16 word) (CustomUCast U16  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 15  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 16 word) (CustomUCast U16  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 17  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (CustomUCast U32  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 18  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (CustomUCast U32  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 19  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (CustomUCast U32  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 20  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (CustomUCast U32  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 21  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (CustomUCast U32  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 22  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (CustomUCast U32  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 23  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (CustomUCast U32  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 24  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (CustomUCast U32  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 25  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (CustomUCast U32  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 26  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (CustomUCast U32  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 27  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (CustomUCast U32  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 28  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (CustomUCast U32  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 29  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (CustomUCast U32  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 30  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (CustomUCast U32  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 31  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 32 word) (CustomUCast U32  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 33  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 34  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 35  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 36  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 37  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 38  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 39  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 40  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 41  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 42  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 43  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 44  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 45  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 46  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 47  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 48  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 49  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 50  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 51  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 52  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 53  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 54  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 55  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 56  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 57  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 58  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 59  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 60  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 61  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 62  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  "\<And>x x'. scorres (x :: 63  word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 64 word) (CustomUCast U64  x') \<gamma> \<xi>"
  by (auto simp: scorres_def ucast_id ucast_nat_def elim!: v_sem_elims)


lemma scorres_custom_dcast:
   "\<And>x x'. scorres (x :: 8 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 1 word) (CustomDCast 1  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 8 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 2 word) (CustomDCast 2  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 8 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 3 word) (CustomDCast 3  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 8 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 4 word) (CustomDCast 4  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 8 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 5 word) (CustomDCast 5  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 8 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 6 word) (CustomDCast 6  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 8 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 7 word) (CustomDCast 7  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 16 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 9 word) (CustomDCast 9  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 16 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 10 word) (CustomDCast 10  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 16 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 11 word) (CustomDCast 11  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 16 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 12 word) (CustomDCast 12  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 16 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 13 word) (CustomDCast 13  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 16 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 14 word) (CustomDCast 14  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 16 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 15 word) (CustomDCast 15  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 17 word) (CustomDCast 17  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 18 word) (CustomDCast 18  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 19 word) (CustomDCast 19  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 20 word) (CustomDCast 20  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 21 word) (CustomDCast 21  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 22 word) (CustomDCast 22  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 23 word) (CustomDCast 23  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 24 word) (CustomDCast 24  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 25 word) (CustomDCast 25  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 26 word) (CustomDCast 26  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 27 word) (CustomDCast 27  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 28 word) (CustomDCast 28  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 29 word) (CustomDCast 29  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 30 word) (CustomDCast 30  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 32 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 31 word) (CustomDCast 31  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 33 word) (CustomDCast 33  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 34 word) (CustomDCast 34  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 35 word) (CustomDCast 35  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 36 word) (CustomDCast 36  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 37 word) (CustomDCast 37  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 38 word) (CustomDCast 38  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 39 word) (CustomDCast 39  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 40 word) (CustomDCast 40  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 41 word) (CustomDCast 41  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 42 word) (CustomDCast 42  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 43 word) (CustomDCast 43  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 44 word) (CustomDCast 44  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 45 word) (CustomDCast 45  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 46 word) (CustomDCast 46  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 47 word) (CustomDCast 47  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 48 word) (CustomDCast 48  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 49 word) (CustomDCast 49  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 50 word) (CustomDCast 50  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 51 word) (CustomDCast 51  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 52 word) (CustomDCast 52  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 53 word) (CustomDCast 53  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 54 word) (CustomDCast 54  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 55 word) (CustomDCast 55  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 56 word) (CustomDCast 56  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 57 word) (CustomDCast 57  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 58 word) (CustomDCast 58  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 59 word) (CustomDCast 59  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 60 word) (CustomDCast 60  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 61 word) (CustomDCast 61  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 62 word) (CustomDCast 62  x') \<gamma> \<xi>"
 "\<And>x x'. scorres (x :: 64 word) x' \<gamma> \<xi> \<Longrightarrow> scorres (ucast x :: 63 word) (CustomDCast 63  x') \<gamma> \<xi>"
  by (auto simp: scorres_def ucast_id word_size unat_def uint_ucast elim!: v_sem_elims)

text {* Rules for records and sums. *}

definition
  (* we pass \<xi> to fix the hidden type variables *)
  "shallow_tac_rec_field \<xi> field_name field_update field_num \<equiv>
     (\<forall>rec fs v v'.
        (valRel \<xi> rec (VRecord fs) \<longrightarrow> valRel \<xi> (field_name rec) (fs ! field_num))
        \<and>
        (valRel \<xi> v v' \<longrightarrow> valRel \<xi> rec (VRecord fs) \<longrightarrow>
         valRel \<xi> (field_update (\<lambda>_. v) rec) (VRecord (fs[field_num := v']))))"

lemma shallow_tac_rec_fieldI:
  assumes
    "\<And>rec fs. valRel \<xi> rec (VRecord fs) \<Longrightarrow> valRel \<xi> (field_name rec) (fs ! field_num)"
    "\<And>rec v fs v'.
        valRel \<xi> v v' \<Longrightarrow> valRel \<xi> rec (VRecord fs) \<Longrightarrow>
        valRel \<xi> (field_update (\<lambda>_. v) rec) (VRecord (fs[field_num := v']))"
  shows "shallow_tac_rec_field \<xi> field_name field_update field_num"
  using assms by (simp add: shallow_tac_rec_field_def)

lemma scorres_take:
assumes
  "shallow_tac_rec_field \<xi> field field_upd field'" (* first *)

  "scorres rec rec' \<gamma> \<xi>"
  "\<And>(rec :: 'rec) rec' v v'.
      valRel \<xi> rec rec' \<Longrightarrow> valRel \<xi> v v' \<Longrightarrow>
      scorres (cont (shallow_tac__var v) (shallow_tac__var rec))
              cont' (v' # rec' # \<gamma>) \<xi>"
shows
  "scorres (HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t rec field) (case_prod cont)) (Take rec' field' cont') \<gamma> \<xi>"
  using assms
  by (fastforce simp: scorres_def shallow_tac_rec_field_def shallow_tac__var_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def elim!: v_sem_elims)

lemma scorres_member:
assumes
  "shallow_tac_rec_field \<xi> field field_upd field'" (* first *)

  "scorres rec rec' \<gamma> \<xi>"
shows
  "scorres (field rec) (Member rec' field') \<gamma> \<xi>"
  using assms
  by (fastforce simp: scorres_def shallow_tac_rec_field_def elim!: v_sem_elims)

lemma scorres_put:
assumes
  "shallow_tac_rec_field \<xi> field field_upd field'" (* first *)

  "scorres rec rec' \<gamma> \<xi>"
  "scorres v v' \<gamma> \<xi>"
shows
  "scorres (field_upd (\<lambda>_. v) rec) (Put rec' field' v') \<gamma> \<xi>"
  using assms
  by (fastforce simp: scorres_def shallow_tac_rec_field_def shallow_tac__var_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def elim!: v_sem_elims)

lemmas scorres_simple_step =
  scorres_unit
  scorres_if
  scorres_let
  scorres_let_desugar
  scorres_letBang
  scorres_letBang_desugar
  scorres_cast
  scorres_custom_ucast
  scorres_custom_dcast
  scorres_prim_add
  scorres_prim_sub
  scorres_prim_times
  scorres_prim_divide
  scorres_prim_mod
  scorres_prim_and
  scorres_prim_or
  scorres_prim_not
  scorres_prim_eq
  scorres_prim_neq
  scorres_prim_gt
  scorres_prim_ge
  scorres_prim_lt
  scorres_prim_le
  scorres_prim_bitand
  scorres_prim_bitor
  scorres_prim_complement
  scorres_prim_bitxor
  scorres_prim_lshift
  scorres_prim_rshift
  scorres_promote


text {* NB: compiler expected to supply rules for: Struct, Promote, Con, Case, Esac *}

text {* Rule templates. *}
lemma scorres_con:
assumes
  "scorres x x' \<gamma> \<xi>" (* first *)

  "\<And>x x'. valRel \<xi> x x' \<Longrightarrow> valRel \<xi> (tcon x) (VSum tag x')"
shows
  "scorres (tcon x) (Con ts tag x') \<gamma> \<xi>"
  using assms
  by (clarsimp simp: scorres_def elim!: v_sem_elims)

lemma scorres_app:
  assumes "scorres f f' \<gamma> \<xi>" (* first *)
  assumes "scorres v v' \<gamma> \<xi>"
  shows "scorres (f v) (App f' v') \<gamma> \<xi>"
  using assms
  by (auto elim!: v_sem_elims simp: scorres_def shallow_tac__var_def)


(* these rules are currently unused *)
lemma scorres_split:
  "scorres v x \<gamma> \<xi> \<Longrightarrow>
   (\<And>a b a' b'. valRel \<xi> a a' \<Longrightarrow> valRel \<xi> b b' \<Longrightarrow>
                 scorres (s (shallow_tac__var a) (shallow_tac__var b)) e (a'#b'#\<gamma>) \<xi>) \<Longrightarrow>
   scorres (case v of (a, b) \<Rightarrow> s a b) (Split x e) \<gamma> \<xi>"
  unfolding scorres_def shallow_tac__var_def
  by (cases v) (auto simp: scorres_def elim!: v_sem_elims)

lemma scorres_tuple:
  assumes "scorres a a' \<gamma> \<xi>"
  assumes "scorres b b' \<gamma> \<xi>"
  shows "scorres (a, b) (Tuple a' b') \<gamma> \<xi>"
  using assms
  by (auto simp: scorres_def elim!: v_sem_tupleE)

end

end

(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

(*
 * Program specifications generated from:
 *   cd bilby/cogent/tests/antiquote-tests/test-wordarray
 *   cogent --fno-tuple-as-sugar --type-proof=WordArrayTest wordarray_simple_nodebug.cogent > WordArrayTest.thy
 *   make SRC=wordarray_simple_nodebug.cogent && cp main_pp_inferred.c wordarraytest.c
 *)
theory WordArrayTest
imports
  "../TypeProofGen"
  "../Cogent_Corres"
  "../Read_Table"
  "../Type_Relation_Generation"
begin

definition
  "abbreviatedType1 \<equiv> TSum [(''Error'', TUnit), (''Success'', TPrim (Num U64))]"

definition
  "abbreviatedType2 \<equiv> TSum [(''Error'', TUnit), (''Success'', TPrim (Num U32))]"

lemmas abbreviated_type_defs =
  abbreviatedType2_def
  abbreviatedType1_def

definition
  "u8_to_u64_type \<equiv> ([], (TPrim (Num U8), TPrim (Num U64)))"

definition
  "u8_to_u32_type \<equiv> ([], (TPrim (Num U8), TPrim (Num U32)))"

definition
  "u8_to_u16_type \<equiv> ([], (TPrim (Num U8), TPrim (Num U16)))"

definition
  "u64_to_u32_type \<equiv> ([], (TPrim (Num U64), TPrim (Num U32)))"

definition
  "u32_to_u8_type \<equiv> ([], (TPrim (Num U32), TPrim (Num U8)))"

definition
  "u32_to_u64_type \<equiv> ([], (TPrim (Num U32), TPrim (Num U64)))"

definition
  "u32_to_u16_type \<equiv> ([], (TPrim (Num U32), TPrim (Num U16)))"

definition
  "u16_to_u8_type \<equiv> ([], (TPrim (Num U16), TPrim (Num U8)))"

definition
  "u16_to_u32_type \<equiv> ([], (TPrim (Num U16), TPrim (Num U32)))"

definition
  "test_time_start_type \<equiv> ([], (TUnit, TUnit))"

definition
  "test_time_end_type \<equiv> ([], (TUnit, TUnit))"

definition
  "test_stack_probe_type \<equiv> ([], (TUnit, TUnit))"

definition
  "random_u32_type \<equiv> ([], (TUnit, TPrim (Num U32)))"

definition
  "cogent_log2_type \<equiv> ([], (TPrim (Num U32), TPrim (Num U32)))"

definition
  "wordarray_cmp_type \<equiv> ([], (TProduct (TCon ''WordArray'' [TPrim (Num U8)] ReadOnly) (TCon ''WordArray'' [TPrim (Num U8)] ReadOnly), TPrim Bool))"

definition
  "wordarray_get_0_type \<equiv> ([], (TProduct (TCon ''WordArray'' [TPrim (Num U32)] ReadOnly) (TPrim (Num U32)), TPrim (Num U32)))"

definition
  "wordarray_put_0_type \<equiv> ([], (TRecord [(TCon ''WordArray'' [TPrim (Num U32)] Writable, False), (TPrim (Num U32), False), (TPrim (Num U32), False)] Unboxed, TSum [(''Error'', TCon ''WordArray'' [TPrim (Num U32)] Writable), (''Success'', TCon ''WordArray'' [TPrim (Num U32)] Writable)]))"

definition
  "test_file_read_next_u32_type \<equiv> ([], (TCon ''File'' [] Writable, TSum [(''Error'', TCon ''File'' [] Writable), (''Success'', TProduct (TCon ''File'' [] Writable) (TPrim (Num U32)))]))"

definition
  "test_file_close_type \<equiv> ([], (TProduct (TCon ''SysState'' [] Writable) (TCon ''File'' [] Writable), TCon ''SysState'' [] Writable))"

definition
  "test_file_open_type \<equiv> ([], (TProduct (TCon ''SysState'' [] Writable) (TProduct (TPrim String) (TPrim String)), TSum [(''Error'', TCon ''SysState'' [] Writable), (''Success'', TProduct (TCon ''SysState'' [] Writable) (TCon ''File'' [] Writable))]))"

definition
  "wordarray_create_0_type \<equiv> ([], (TProduct (TCon ''SysState'' [] Writable) (TPrim (Num U32)), TSum [(''Error'', TCon ''SysState'' [] Writable), (''Success'', TProduct (TCon ''SysState'' [] Writable) (TCon ''WordArray'' [TPrim (Num U32)] Writable))]))"

definition
  "wordarray_free_0_type \<equiv> ([], (TProduct (TCon ''SysState'' [] Writable) (TCon ''WordArray'' [TPrim (Num U32)] Writable), TCon ''SysState'' [] Writable))"

definition
  "u16_to_u64_type \<equiv> ([], (TPrim (Num U16), TPrim (Num U64)))"

definition
  "u16_to_u64 \<equiv> Let (Var 0) (Let (App (AFun ''u16_to_u32'' []) (Var 0)) (App (AFun ''u32_to_u64'' []) (Var 0)))"

definition
  "min_u32_type \<equiv> ([], (TProduct (TPrim (Num U32)) (TPrim (Num U32)), TPrim (Num U32)))"

definition
  "min_u32 \<equiv> Split (Var 0) (Let (Prim (Lt U32) [Var 0, Var 1]) (If (Var 0) (Var 1) (Var 2)))"

definition
  "cogent_low_16_bits_type \<equiv> ([], (TPrim (Num U32), TPrim (Num U16)))"

definition
  "cogent_low_16_bits \<equiv> Let (Var 0) (Let (Lit (LU16 65535)) (Let (Cast U32 (Var 0)) (Let (Prim (BitAnd U32) [Var 2, Var 0]) (App (AFun ''u32_to_u16'' []) (Var 0)))))"

definition
  "cogent_high_16_bits_type \<equiv> ([], (TPrim (Num U32), TPrim (Num U16)))"

definition
  "cogent_high_16_bits \<equiv> Let (Var 0) (Let (Lit (LU32 4294901760)) (Let (Prim (BitAnd U32) [Var 1, Var 0]) (Let (Lit (LU8 16)) (Let (App (AFun ''u8_to_u32'' []) (Var 0)) (Let (Prim (RShift U32) [Var 2, Var 0]) (App (AFun ''u32_to_u16'' []) (Var 0)))))))"

definition
  "align64_type \<equiv> ([], (TProduct (TPrim (Num U64)) (TPrim (Num U64)), TPrim (Num U64)))"

definition
  "align64 \<equiv> Split (Var 0) (Let (Prim (Mod U64) [Var 0, Var 1]) (Let (Lit (LU8 0)) (Let (Cast U64 (Var 0)) (Let (Prim (NEq (Num U64)) [Var 2, Var 0]) (If (Var 0) (Let (Prim (Plus U64) [Var 4, Var 5]) (Let (Prim (Mod U64) [Var 5, Var 6]) (Prim (Minus U64) [Var 1, Var 0]))) (Var 4))))))"

definition
  "align32_type \<equiv> ([], (TProduct (TPrim (Num U32)) (TPrim (Num U32)), TPrim (Num U32)))"

definition
  "align32 \<equiv> Split (Var 0) (Let (Prim (Mod U32) [Var 0, Var 1]) (Let (Lit (LU8 0)) (Let (Cast U32 (Var 0)) (Let (Prim (NEq (Num U32)) [Var 2, Var 0]) (If (Var 0) (Let (Prim (Plus U32) [Var 4, Var 5]) (Let (Prim (Mod U32) [Var 5, Var 6]) (Prim (Minus U32) [Var 1, Var 0]))) (Var 4))))))"

definition
  "safe_add32_type \<equiv> ([], (TProduct (TPrim (Num U32)) (TPrim (Num U32)), abbreviatedType2))"

definition
  "safe_add32 \<equiv> Split (Var 0) (Let (Prim (Plus U32) [Var 0, Var 1]) (Let (Prim (Lt U32) [Var 0, Var 1]) (Let (Prim (Lt U32) [Var 1, Var 3]) (Let (Prim Cogent.Or [Var 1, Var 0]) (If (Var 0) (Let Unit (Let (Con [(''Error'', TUnit)] ''Error'' (Var 0)) (Promote [(''Error'', TUnit), (''Success'', TPrim (Num U32))] (Var 0)))) (Let (Con [(''Success'', TPrim (Num U32))] ''Success'' (Var 3)) (Promote [(''Error'', TUnit), (''Success'', TPrim (Num U32))] (Var 0))))))))"

definition
  "safe_add64_type \<equiv> ([], (TProduct (TPrim (Num U64)) (TPrim (Num U64)), abbreviatedType1))"

definition
  "safe_add64 \<equiv> Split (Var 0) (Let (Prim (Plus U64) [Var 0, Var 1]) (Let (Prim (Lt U64) [Var 0, Var 1]) (Let (Prim (Lt U64) [Var 1, Var 3]) (Let (Prim Cogent.Or [Var 1, Var 0]) (If (Var 0) (Let Unit (Let (Con [(''Error'', TUnit)] ''Error'' (Var 0)) (Promote [(''Error'', TUnit), (''Success'', TPrim (Num U64))] (Var 0)))) (Let (Con [(''Success'', TPrim (Num U64))] ''Success'' (Var 3)) (Promote [(''Error'', TUnit), (''Success'', TPrim (Num U64))] (Var 0))))))))"

definition
  "safe_sub32_type \<equiv> ([], (TProduct (TPrim (Num U32)) (TPrim (Num U32)), abbreviatedType2))"

definition
  "safe_sub32 \<equiv> Split (Var 0) (Let (Prim (Minus U32) [Var 0, Var 1]) (Let (Prim (Gt U32) [Var 0, Var 1]) (If (Var 0) (Let Unit (Let (Con [(''Error'', TUnit)] ''Error'' (Var 0)) (Promote [(''Error'', TUnit), (''Success'', TPrim (Num U32))] (Var 0)))) (Let (Con [(''Success'', TPrim (Num U32))] ''Success'' (Var 1)) (Promote [(''Error'', TUnit), (''Success'', TPrim (Num U32))] (Var 0))))))"

definition
  "safe_sub64_type \<equiv> ([], (TProduct (TPrim (Num U64)) (TPrim (Num U64)), abbreviatedType1))"

definition
  "safe_sub64 \<equiv> Split (Var 0) (Let (Prim (Minus U64) [Var 0, Var 1]) (Let (Prim (Gt U64) [Var 0, Var 1]) (If (Var 0) (Let Unit (Let (Con [(''Error'', TUnit)] ''Error'' (Var 0)) (Promote [(''Error'', TUnit), (''Success'', TPrim (Num U64))] (Var 0)))) (Let (Con [(''Success'', TPrim (Num U64))] ''Success'' (Var 1)) (Promote [(''Error'', TUnit), (''Success'', TPrim (Num U64))] (Var 0))))))"

definition
  "caller_type \<equiv> ([], (TCon ''SysState'' [] Writable, TCon ''SysState'' [] Writable))"

definition
  "caller \<equiv> Let (Var 0) (Let (Lit (LU8 4)) (Let (Cast U32 (Var 0)) (Let (Tuple (Var 2) (Var 0)) (Let (App (AFun ''wordarray_create_0'' []) (Var 0)) (Case (Var 0) ''Success'' (Split (Var 0) (Let (Lit (LU8 0)) (Let (App (AFun ''u8_to_u32'' []) (Var 0)) (Let (Lit (LU8 42)) (Let (App (AFun ''u8_to_u32'' []) (Var 0)) (Let (Struct [TCon ''WordArray'' [TPrim (Num U32)] Writable, TPrim (Num U32), TPrim (Num U32)] [Var 5, Var 2, Var 0]) (Let (App (AFun ''wordarray_put_0'' []) (Var 0)) (Case (Var 0) ''Success'' (LetBang (set [0]) (Let (Lit (LU8 0)) (Let (Cast U32 (Var 0)) (Let (Tuple (Var 2) (Var 0)) (App (AFun ''wordarray_get_0'' []) (Var 0))))) (Let (Tuple (Var 8) (Var 1)) (App (AFun ''wordarray_free_0'' []) (Var 0)))) (Let (Esac (Var 0)) (Let (Tuple (Var 8) (Var 0)) (App (AFun ''wordarray_free_0'' []) (Var 0)))))))))))) (Let (Esac (Var 0)) (Var 0)))))))"

definition
  "\<Xi> func_name' \<equiv> case func_name' of ''u8_to_u64'' \<Rightarrow> u8_to_u64_type | ''u8_to_u32'' \<Rightarrow> u8_to_u32_type | ''u8_to_u16'' \<Rightarrow> u8_to_u16_type | ''u64_to_u32'' \<Rightarrow> u64_to_u32_type | ''u32_to_u8'' \<Rightarrow> u32_to_u8_type | ''u32_to_u64'' \<Rightarrow> u32_to_u64_type | ''u32_to_u16'' \<Rightarrow> u32_to_u16_type | ''u16_to_u8'' \<Rightarrow> u16_to_u8_type | ''u16_to_u32'' \<Rightarrow> u16_to_u32_type | ''test_time_start'' \<Rightarrow> test_time_start_type | ''test_time_end'' \<Rightarrow> test_time_end_type | ''test_stack_probe'' \<Rightarrow> test_stack_probe_type | ''random_u32'' \<Rightarrow> random_u32_type | ''cogent_log2'' \<Rightarrow> cogent_log2_type | ''wordarray_cmp'' \<Rightarrow> wordarray_cmp_type | ''wordarray_get_0'' \<Rightarrow> wordarray_get_0_type | ''wordarray_put_0'' \<Rightarrow> wordarray_put_0_type | ''test_file_read_next_u32'' \<Rightarrow> test_file_read_next_u32_type | ''test_file_close'' \<Rightarrow> test_file_close_type | ''test_file_open'' \<Rightarrow> test_file_open_type | ''wordarray_create_0'' \<Rightarrow> wordarray_create_0_type | ''wordarray_free_0'' \<Rightarrow> wordarray_free_0_type | ''u16_to_u64'' \<Rightarrow> u16_to_u64_type | ''min_u32'' \<Rightarrow> min_u32_type | ''cogent_low_16_bits'' \<Rightarrow> cogent_low_16_bits_type | ''cogent_high_16_bits'' \<Rightarrow> cogent_high_16_bits_type | ''align64'' \<Rightarrow> align64_type | ''align32'' \<Rightarrow> align32_type | ''safe_add32'' \<Rightarrow> safe_add32_type | ''safe_add64'' \<Rightarrow> safe_add64_type | ''safe_sub32'' \<Rightarrow> safe_sub32_type | ''safe_sub64'' \<Rightarrow> safe_sub64_type | ''caller'' \<Rightarrow> caller_type"

definition
  "u16_to_u64_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some (TPrim (Num U16))] (TyTrSplit (Cons (Some TSK_L) (Cons None [])) [] TyTrLeaf [Some (TPrim (Num U32))] TyTrLeaf)"

definition
  "min_u32_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some (TPrim (Num U32)), Some (TPrim (Num U32))] (TyTrSplit (Cons (Some TSK_S) (Cons (Some TSK_S) (Cons None []))) [] TyTrLeaf [Some (TPrim Bool)] (TyTrSplit (Cons (Some TSK_L) (append (replicate 3 None) [])) [] TyTrLeaf [] (TyTrSplit (Cons None (Cons (Some TSK_S) (Cons (Some TSK_S) (Cons None [])))) [] TyTrLeaf [] TyTrLeaf)))"

definition
  "cogent_low_16_bits_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (append (replicate 2 None) []) [] TyTrLeaf [Some (TPrim (Num U16))] (TyTrSplit (Cons (Some TSK_L) (append (replicate 2 None) [])) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (Cons (Some TSK_L) (Cons None (Cons (Some TSK_L) (Cons None [])))) [] TyTrLeaf [Some (TPrim (Num U32))] TyTrLeaf)))"

definition
  "cogent_high_16_bits_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (append (replicate 2 None) []) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (Cons (Some TSK_L) (Cons (Some TSK_L) (Cons None []))) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (append (replicate 4 None) []) [] TyTrLeaf [Some (TPrim (Num U8))] (TyTrSplit (Cons (Some TSK_L) (append (replicate 4 None) [])) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (Cons (Some TSK_L) (Cons None (Cons (Some TSK_L) (append (replicate 3 None) [])))) [] TyTrLeaf [Some (TPrim (Num U32))] TyTrLeaf)))))"

definition
  "align64_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some (TPrim (Num U64)), Some (TPrim (Num U64))] (TyTrSplit (Cons (Some TSK_S) (Cons (Some TSK_S) (Cons None []))) [] TyTrLeaf [Some (TPrim (Num U64))] (TyTrSplit (append (replicate 4 None) []) [] TyTrLeaf [Some (TPrim (Num U8))] (TyTrSplit (Cons (Some TSK_L) (append (replicate 4 None) [])) [] TyTrLeaf [Some (TPrim (Num U64))] (TyTrSplit (Cons (Some TSK_L) (Cons None (Cons (Some TSK_L) (append (replicate 3 None) [])))) [] TyTrLeaf [Some (TPrim Bool)] (TyTrSplit (Cons (Some TSK_L) (append (replicate 6 None) [])) [] TyTrLeaf [] (TyTrSplit (append (replicate 4 None) (Cons (Some TSK_S) (Cons (Some TSK_S) (Cons None [])))) [] (TyTrSplit (append (replicate 4 None) (Cons (Some TSK_S) (Cons (Some TSK_S) (Cons None [])))) [] TyTrLeaf [Some (TPrim (Num U64))] (TyTrSplit (append (replicate 5 None) (Cons (Some TSK_L) (Cons (Some TSK_L) (Cons None [])))) [] TyTrLeaf [Some (TPrim (Num U64))] TyTrLeaf)) [] TyTrLeaf))))))"

definition
  "align32_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some (TPrim (Num U32)), Some (TPrim (Num U32))] (TyTrSplit (Cons (Some TSK_S) (Cons (Some TSK_S) (Cons None []))) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (append (replicate 4 None) []) [] TyTrLeaf [Some (TPrim (Num U8))] (TyTrSplit (Cons (Some TSK_L) (append (replicate 4 None) [])) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (Cons (Some TSK_L) (Cons None (Cons (Some TSK_L) (append (replicate 3 None) [])))) [] TyTrLeaf [Some (TPrim Bool)] (TyTrSplit (Cons (Some TSK_L) (append (replicate 6 None) [])) [] TyTrLeaf [] (TyTrSplit (append (replicate 4 None) (Cons (Some TSK_S) (Cons (Some TSK_S) (Cons None [])))) [] (TyTrSplit (append (replicate 4 None) (Cons (Some TSK_S) (Cons (Some TSK_S) (Cons None [])))) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (append (replicate 5 None) (Cons (Some TSK_L) (Cons (Some TSK_L) (Cons None [])))) [] TyTrLeaf [Some (TPrim (Num U32))] TyTrLeaf)) [] TyTrLeaf))))))"

definition
  "safe_add32_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some (TPrim (Num U32)), Some (TPrim (Num U32))] (TyTrSplit (Cons (Some TSK_S) (Cons (Some TSK_S) (Cons None []))) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (Cons (Some TSK_S) (Cons (Some TSK_L) (append (replicate 2 None) []))) [] TyTrLeaf [Some (TPrim Bool)] (TyTrSplit (Cons None (Cons (Some TSK_S) (Cons None (Cons (Some TSK_L) (Cons None []))))) [] TyTrLeaf [Some (TPrim Bool)] (TyTrSplit (Cons (Some TSK_L) (Cons (Some TSK_L) (append (replicate 4 None) []))) [] TyTrLeaf [Some (TPrim Bool)] (TyTrSplit (Cons (Some TSK_L) (append (replicate 6 None) [])) [] TyTrLeaf [] (TyTrSplit (append (replicate 3 None) (Cons (Some TSK_S) (append (replicate 3 None) []))) [] (TyTrSplit (append (replicate 3 None) (Cons (Some TSK_L) (append (replicate 3 None) []))) [] TyTrLeaf [Some TUnit] (TyTrSplit (Cons (Some TSK_L) (append (replicate 7 None) [])) [] TyTrLeaf [Some (TSum [(''Error'', TUnit)])] TyTrLeaf)) [] (TyTrSplit (append (replicate 3 None) (Cons (Some TSK_L) (append (replicate 3 None) []))) [] TyTrLeaf [Some (TSum [(''Success'', TPrim (Num U32))])] TyTrLeaf)))))))"

definition
  "safe_add64_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some (TPrim (Num U64)), Some (TPrim (Num U64))] (TyTrSplit (Cons (Some TSK_S) (Cons (Some TSK_S) (Cons None []))) [] TyTrLeaf [Some (TPrim (Num U64))] (TyTrSplit (Cons (Some TSK_S) (Cons (Some TSK_L) (append (replicate 2 None) []))) [] TyTrLeaf [Some (TPrim Bool)] (TyTrSplit (Cons None (Cons (Some TSK_S) (Cons None (Cons (Some TSK_L) (Cons None []))))) [] TyTrLeaf [Some (TPrim Bool)] (TyTrSplit (Cons (Some TSK_L) (Cons (Some TSK_L) (append (replicate 4 None) []))) [] TyTrLeaf [Some (TPrim Bool)] (TyTrSplit (Cons (Some TSK_L) (append (replicate 6 None) [])) [] TyTrLeaf [] (TyTrSplit (append (replicate 3 None) (Cons (Some TSK_S) (append (replicate 3 None) []))) [] (TyTrSplit (append (replicate 3 None) (Cons (Some TSK_L) (append (replicate 3 None) []))) [] TyTrLeaf [Some TUnit] (TyTrSplit (Cons (Some TSK_L) (append (replicate 7 None) [])) [] TyTrLeaf [Some (TSum [(''Error'', TUnit)])] TyTrLeaf)) [] (TyTrSplit (append (replicate 3 None) (Cons (Some TSK_L) (append (replicate 3 None) []))) [] TyTrLeaf [Some (TSum [(''Success'', TPrim (Num U64))])] TyTrLeaf)))))))"

definition
  "safe_sub32_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some (TPrim (Num U32)), Some (TPrim (Num U32))] (TyTrSplit (Cons (Some TSK_S) (Cons (Some TSK_L) (Cons None []))) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (Cons (Some TSK_S) (Cons (Some TSK_L) (append (replicate 2 None) []))) [] TyTrLeaf [Some (TPrim Bool)] (TyTrSplit (Cons (Some TSK_L) (append (replicate 4 None) [])) [] TyTrLeaf [] (TyTrSplit (Cons None (Cons (Some TSK_S) (append (replicate 3 None) []))) [] (TyTrSplit (Cons None (Cons (Some TSK_L) (append (replicate 3 None) []))) [] TyTrLeaf [Some TUnit] (TyTrSplit (Cons (Some TSK_L) (append (replicate 5 None) [])) [] TyTrLeaf [Some (TSum [(''Error'', TUnit)])] TyTrLeaf)) [] (TyTrSplit (Cons None (Cons (Some TSK_L) (append (replicate 3 None) []))) [] TyTrLeaf [Some (TSum [(''Success'', TPrim (Num U32))])] TyTrLeaf)))))"

definition
  "safe_sub64_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some (TPrim (Num U64)), Some (TPrim (Num U64))] (TyTrSplit (Cons (Some TSK_S) (Cons (Some TSK_L) (Cons None []))) [] TyTrLeaf [Some (TPrim (Num U64))] (TyTrSplit (Cons (Some TSK_S) (Cons (Some TSK_L) (append (replicate 2 None) []))) [] TyTrLeaf [Some (TPrim Bool)] (TyTrSplit (Cons (Some TSK_L) (append (replicate 4 None) [])) [] TyTrLeaf [] (TyTrSplit (Cons None (Cons (Some TSK_S) (append (replicate 3 None) []))) [] (TyTrSplit (Cons None (Cons (Some TSK_L) (append (replicate 3 None) []))) [] TyTrLeaf [Some TUnit] (TyTrSplit (Cons (Some TSK_L) (append (replicate 5 None) [])) [] TyTrLeaf [Some (TSum [(''Error'', TUnit)])] TyTrLeaf)) [] (TyTrSplit (Cons None (Cons (Some TSK_L) (append (replicate 3 None) []))) [] TyTrLeaf [Some (TSum [(''Success'', TPrim (Num U64))])] TyTrLeaf)))))"

definition
  "caller_typetree \<equiv> TyTrSplit (Cons (Some TSK_L) []) [] TyTrLeaf [Some (TCon ''SysState'' [] Writable)] (TyTrSplit (append (replicate 2 None) []) [] TyTrLeaf [Some (TPrim (Num U8))] (TyTrSplit (Cons (Some TSK_L) (append (replicate 2 None) [])) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (Cons (Some TSK_L) (Cons None (Cons (Some TSK_L) (Cons None [])))) [] TyTrLeaf [Some (TProduct (TCon ''SysState'' [] Writable) (TPrim (Num U32)))] (TyTrSplit (Cons (Some TSK_L) (append (replicate 4 None) [])) [] TyTrLeaf [Some (TSum [(''Error'', TCon ''SysState'' [] Writable), (''Success'', TProduct (TCon ''SysState'' [] Writable) (TCon ''WordArray'' [TPrim (Num U32)] Writable))])] (TyTrSplit (Cons (Some TSK_L) (append (replicate 5 None) [])) [] TyTrLeaf [] (TyTrSplit (append (replicate 6 None) []) [Some (TProduct (TCon ''SysState'' [] Writable) (TCon ''WordArray'' [TPrim (Num U32)] Writable))] (TyTrSplit (Cons (Some TSK_L) (append (replicate 6 None) [])) [] TyTrLeaf [Some (TCon ''SysState'' [] Writable), Some (TCon ''WordArray'' [TPrim (Num U32)] Writable)] (TyTrSplit (append (replicate 9 None) []) [] TyTrLeaf [Some (TPrim (Num U8))] (TyTrSplit (Cons (Some TSK_L) (append (replicate 9 None) [])) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (append (replicate 11 None) []) [] TyTrLeaf [Some (TPrim (Num U8))] (TyTrSplit (Cons (Some TSK_L) (append (replicate 11 None) [])) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (Cons (Some TSK_L) (Cons None (Cons (Some TSK_L) (append (replicate 2 None) (Cons (Some TSK_L) (append (replicate 7 None) [])))))) [] TyTrLeaf [Some (TRecord [(TCon ''WordArray'' [TPrim (Num U32)] Writable, False), (TPrim (Num U32), False), (TPrim (Num U32), False)] Unboxed)] (TyTrSplit (Cons (Some TSK_L) (append (replicate 13 None) [])) [] TyTrLeaf [Some (TSum [(''Error'', TCon ''WordArray'' [TPrim (Num U32)] Writable), (''Success'', TCon ''WordArray'' [TPrim (Num U32)] Writable)])] (TyTrSplit (Cons (Some TSK_L) (append (replicate 14 None) [])) [] TyTrLeaf [] (TyTrSplit (append (replicate 6 None) (Cons (Some TSK_S) (append (replicate 8 None) []))) [Some (TCon ''WordArray'' [TPrim (Num U32)] Writable)] (TyTrSplit (Cons (Some TSK_NS) (append (replicate 15 None) [])) [] (TyTrSplit (append (replicate 16 None) []) [] TyTrLeaf [Some (TPrim (Num U8))] (TyTrSplit (Cons (Some TSK_L) (append (replicate 16 None) [])) [] TyTrLeaf [Some (TPrim (Num U32))] (TyTrSplit (Cons (Some TSK_L) (Cons None (Cons (Some TSK_L) (append (replicate 15 None) [])))) [] TyTrLeaf [Some (TProduct (TCon ''WordArray'' [TPrim (Num U32)] ReadOnly) (TPrim (Num U32)))] TyTrLeaf))) [Some (TPrim (Num U32))] (TyTrSplit (Cons (Some TSK_L) (Cons (Some TSK_L) (append (replicate 6 None) (Cons (Some TSK_L) (append (replicate 8 None) []))))) [] TyTrLeaf [Some (TProduct (TCon ''SysState'' [] Writable) (TCon ''WordArray'' [TPrim (Num U32)] Writable))] TyTrLeaf)) [Some (TSum [(''Error'', TCon ''WordArray'' [TPrim (Num U32)] Writable)])] (TyTrSplit (Cons (Some TSK_L) (append (replicate 15 None) [])) [] TyTrLeaf [Some (TCon ''WordArray'' [TPrim (Num U32)] Writable)] (TyTrSplit (Cons (Some TSK_L) (append (replicate 7 None) (Cons (Some TSK_L) (append (replicate 8 None) [])))) [] TyTrLeaf [Some (TProduct (TCon ''SysState'' [] Writable) (TCon ''WordArray'' [TPrim (Num U32)] Writable))] TyTrLeaf))))))))))) [Some (TSum [(''Error'', TCon ''SysState'' [] Writable)])] (TyTrSplit (Cons (Some TSK_L) (append (replicate 6 None) [])) [] TyTrLeaf [Some (TCon ''SysState'' [] Writable)] TyTrLeaf)))))))"

ML {* open TTyping_Tactics *}

ML {*
val typing_helper_1_script : tac list = [
(RTac @{thm kind_tprim[where k = "{E,S,D}"]})
] *}


lemma typing_helper_1[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim (Num U16)) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_1_script |> EVERY *})
  done

ML {*
val typing_helper_2_script : tac list = [
(SimpTac ([],[(nth @{thms HOL.simp_thms} (25-1)),(nth @{thms HOL.simp_thms} (26-1))]))
] *}


lemma typing_helper_2[unfolded abbreviated_type_defs] :
  "list_all2 (kinding []) [] []"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_2_script |> EVERY *})
  done

ML {*
val typing_helper_3_script : tac list = [
(RTac @{thm kind_tprim[where k = "{E,S,D}"]})
] *}


lemma typing_helper_3[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim (Num U32)) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_3_script |> EVERY *})
  done

ML {*
val typing_helper_4_script : tac list = [
(RTac @{thm kind_tfun[where k = "{E,S,D}"]}),
(RTac @{thm typing_helper_1}),
(RTac @{thm typing_helper_3})
] *}


lemma typing_helper_4[unfolded abbreviated_type_defs] :
  "kinding [] (TFun (TPrim (Num U16)) (TPrim (Num U32))) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_4_script |> EVERY *})
  done

ML {*
val typing_helper_5_script : tac list = [
(RTac @{thm kind_tprim[where k = "{E,S,D}"]})
] *}


lemma typing_helper_5[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim (Num U64)) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_5_script |> EVERY *})
  done

ML {*
val typing_helper_6_script : tac list = [
(RTac @{thm kind_tfun[where k = "{E,S,D}"]}),
(RTac @{thm typing_helper_3}),
(RTac @{thm typing_helper_5})
] *}


lemma typing_helper_6[unfolded abbreviated_type_defs] :
  "kinding [] (TFun (TPrim (Num U32)) (TPrim (Num U64))) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_6_script |> EVERY *})
  done

ML {*
val typing_helper_7_script : tac list = [
(RTac @{thm kind_tprod[where k = "{E,S,D}"]}),
(RTac @{thm typing_helper_3}),
(RTac @{thm typing_helper_3})
] *}


lemma typing_helper_7[unfolded abbreviated_type_defs] :
  "kinding [] (TProduct (TPrim (Num U32)) (TPrim (Num U32))) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_7_script |> EVERY *})
  done

ML {*
val typing_helper_8_script : tac list = [
(RTac @{thm kind_tprim[where k = "{E,S,D}"]})
] *}


lemma typing_helper_8[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim Bool) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_8_script |> EVERY *})
  done

ML {*
val typing_helper_9_script : tac list = [
(RTac @{thm kind_tfun[where k = "{E,S,D}"]}),
(RTac @{thm typing_helper_3}),
(RTac @{thm typing_helper_1})
] *}


lemma typing_helper_9[unfolded abbreviated_type_defs] :
  "kinding [] (TFun (TPrim (Num U32)) (TPrim (Num U16))) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_9_script |> EVERY *})
  done

ML {*
val typing_helper_10_script : tac list = [
(RTac @{thm kind_tprim[where k = "{E,S,D}"]})
] *}


lemma typing_helper_10[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim (Num U8)) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_10_script |> EVERY *})
  done

ML {*
val typing_helper_11_script : tac list = [
(RTac @{thm kind_tfun[where k = "{E,S,D}"]}),
(RTac @{thm typing_helper_10}),
(RTac @{thm typing_helper_3})
] *}


lemma typing_helper_11[unfolded abbreviated_type_defs] :
  "kinding [] (TFun (TPrim (Num U8)) (TPrim (Num U32))) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_11_script |> EVERY *})
  done

ML {*
val typing_helper_12_script : tac list = [
(RTac @{thm kind_tprod[where k = "{E,S,D}"]}),
(RTac @{thm typing_helper_5}),
(RTac @{thm typing_helper_5})
] *}


lemma typing_helper_12[unfolded abbreviated_type_defs] :
  "kinding [] (TProduct (TPrim (Num U64)) (TPrim (Num U64))) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_12_script |> EVERY *})
  done

ML {*
val typing_helper_13_script : tac list = [
(RTac @{thm kind_tunit[where k = "{E,S,D}"]})
] *}


lemma typing_helper_13[unfolded abbreviated_type_defs] :
  "kinding [] TUnit {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_13_script |> EVERY *})
  done

ML {*
val typing_helper_14_script : tac list = [
(RTac @{thm kind_tsum[where k = "{E,S,D}"]}),
(SimpTac ([],[])),
(SimpTac ([],[])),
(RTac @{thm kind_all_cons}),
(RTac @{thm typing_helper_13}),
(RTac @{thm kind_all_empty})
] *}


lemma typing_helper_14[unfolded abbreviated_type_defs] :
  "kinding [] (TSum [(''Error'', TUnit)]) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_14_script |> EVERY *})
  done

ML {*
val typing_helper_15_script : tac list = [
(RTac @{thm kind_tsum[where k = "{E,S,D}"]}),
(SimpTac ([],[])),
(SimpTac ([],[])),
(RTac @{thm kind_all_cons}),
(RTac @{thm typing_helper_3}),
(RTac @{thm kind_all_empty})
] *}


lemma typing_helper_15[unfolded abbreviated_type_defs] :
  "kinding [] (TSum [(''Success'', TPrim (Num U32))]) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_15_script |> EVERY *})
  done

ML {*
val typing_helper_16_script : tac list = [
(RTac @{thm kind_tsum[where k = "{E,S,D}"]}),
(SimpTac ([],[])),
(SimpTac ([],[])),
(RTac @{thm kind_all_cons}),
(RTac @{thm typing_helper_5}),
(RTac @{thm kind_all_empty})
] *}


lemma typing_helper_16[unfolded abbreviated_type_defs] :
  "kinding [] (TSum [(''Success'', TPrim (Num U64))]) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_16_script |> EVERY *})
  done

ML {*
val typing_helper_17_script : tac list = [
(RTac @{thm kind_tcon[where k = "{E}"]}),
(RTac @{thm kind_all_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_17[unfolded abbreviated_type_defs] :
  "kinding [] (TCon ''SysState'' [] Writable) {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_17_script |> EVERY *})
  done

ML {*
val typing_helper_18_script : tac list = [
(RTac @{thm kind_tprim})
] *}


lemma typing_helper_18[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim (Num U32)) {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_18_script |> EVERY *})
  done

ML {*
val typing_helper_19_script : tac list = [
(RTac @{thm kind_tprod[where k = "{E}"]}),
(RTac @{thm typing_helper_17}),
(RTac @{thm typing_helper_18})
] *}


lemma typing_helper_19[unfolded abbreviated_type_defs] :
  "kinding [] (TProduct (TCon ''SysState'' [] Writable) (TPrim (Num U32))) {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_19_script |> EVERY *})
  done

ML {*
val typing_helper_20_script : tac list = [
(RTac @{thm kind_tcon}),
(RTac @{thm kind_all_cons}),
(RTac @{thm typing_helper_18}),
(RTac @{thm kind_all_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_20[unfolded abbreviated_type_defs] :
  "kinding [] (TCon ''WordArray'' [TPrim (Num U32)] Writable) {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_20_script |> EVERY *})
  done

ML {*
val typing_helper_21_script : tac list = [
(RTac @{thm kind_tprod}),
(RTac @{thm typing_helper_17}),
(RTac @{thm typing_helper_20})
] *}


lemma typing_helper_21[unfolded abbreviated_type_defs] :
  "kinding [] (TProduct (TCon ''SysState'' [] Writable) (TCon ''WordArray'' [TPrim (Num U32)] Writable)) {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_21_script |> EVERY *})
  done

ML {*
val typing_helper_22_script : tac list = [
(RTac @{thm kind_tsum[where k = "{E}"]}),
(SimpTac ([],[])),
(SimpTac ([],[])),
(RTac @{thm kind_all_cons}),
(RTac @{thm typing_helper_17}),
(RTac @{thm kind_all_cons}),
(RTac @{thm typing_helper_21}),
(RTac @{thm kind_all_empty})
] *}


lemma typing_helper_22[unfolded abbreviated_type_defs] :
  "kinding [] (TSum [(''Error'', TCon ''SysState'' [] Writable), (''Success'', TProduct (TCon ''SysState'' [] Writable) (TCon ''WordArray'' [TPrim (Num U32)] Writable))]) {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_22_script |> EVERY *})
  done

ML {*
val typing_helper_23_script : tac list = [
(RTac @{thm kind_tfun[where k = "{E,S,D}"]}),
(RTac @{thm typing_helper_19}),
(RTac @{thm typing_helper_22})
] *}


lemma typing_helper_23[unfolded abbreviated_type_defs] :
  "kinding [] (TFun (TProduct (TCon ''SysState'' [] Writable) (TPrim (Num U32))) (TSum [(''Error'', TCon ''SysState'' [] Writable), (''Success'', TProduct (TCon ''SysState'' [] Writable) (TCon ''WordArray'' [TPrim (Num U32)] Writable))])) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_23_script |> EVERY *})
  done

ML {*
val typing_helper_24_script : tac list = [
(RTac @{thm kind_trec[where k = "{E}"]}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_20}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_18}),
(RTac @{thm kind_record_cons1}),
(RTac @{thm typing_helper_18}),
(RTac @{thm kind_record_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_24[unfolded abbreviated_type_defs] :
  "kinding [] (TRecord [(TCon ''WordArray'' [TPrim (Num U32)] Writable, False), (TPrim (Num U32), False), (TPrim (Num U32), False)] Unboxed) {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_24_script |> EVERY *})
  done

ML {*
val typing_helper_25_script : tac list = [
(RTac @{thm kind_tsum[where k = "{E}"]}),
(SimpTac ([],[])),
(SimpTac ([],[])),
(RTac @{thm kind_all_cons}),
(RTac @{thm typing_helper_20}),
(RTac @{thm kind_all_cons}),
(RTac @{thm typing_helper_20}),
(RTac @{thm kind_all_empty})
] *}


lemma typing_helper_25[unfolded abbreviated_type_defs] :
  "kinding [] (TSum [(''Error'', TCon ''WordArray'' [TPrim (Num U32)] Writable), (''Success'', TCon ''WordArray'' [TPrim (Num U32)] Writable)]) {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_25_script |> EVERY *})
  done

ML {*
val typing_helper_26_script : tac list = [
(RTac @{thm kind_tfun[where k = "{E,S,D}"]}),
(RTac @{thm typing_helper_24}),
(RTac @{thm typing_helper_25})
] *}


lemma typing_helper_26[unfolded abbreviated_type_defs] :
  "kinding [] (TFun (TRecord [(TCon ''WordArray'' [TPrim (Num U32)] Writable, False), (TPrim (Num U32), False), (TPrim (Num U32), False)] Unboxed) (TSum [(''Error'', TCon ''WordArray'' [TPrim (Num U32)] Writable), (''Success'', TCon ''WordArray'' [TPrim (Num U32)] Writable)])) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_26_script |> EVERY *})
  done

ML {*
val typing_helper_27_script : tac list = [
(RTac @{thm kind_tprim})
] *}


lemma typing_helper_27[unfolded abbreviated_type_defs] :
  "kinding [] (TPrim (Num U32)) {S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_27_script |> EVERY *})
  done

ML {*
val typing_helper_28_script : tac list = [
(RTac @{thm kind_tcon[where k = "{S,D}"]}),
(RTac @{thm kind_all_cons}),
(RTac @{thm typing_helper_27}),
(RTac @{thm kind_all_empty}),
(SimpTac ([],[]))
] *}


lemma typing_helper_28[unfolded abbreviated_type_defs] :
  "kinding [] (TCon ''WordArray'' [TPrim (Num U32)] ReadOnly) {S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_28_script |> EVERY *})
  done

ML {*
val typing_helper_29_script : tac list = [
(RTac @{thm kind_tprod[where k = "{S,D}"]}),
(RTac @{thm typing_helper_28}),
(RTac @{thm typing_helper_27})
] *}


lemma typing_helper_29[unfolded abbreviated_type_defs] :
  "kinding [] (TProduct (TCon ''WordArray'' [TPrim (Num U32)] ReadOnly) (TPrim (Num U32))) {S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_29_script |> EVERY *})
  done

ML {*
val typing_helper_30_script : tac list = [
(RTac @{thm kind_tfun[where k = "{E,S,D}"]}),
(RTac @{thm typing_helper_29}),
(RTac @{thm typing_helper_3})
] *}


lemma typing_helper_30[unfolded abbreviated_type_defs] :
  "kinding [] (TFun (TProduct (TCon ''WordArray'' [TPrim (Num U32)] ReadOnly) (TPrim (Num U32))) (TPrim (Num U32))) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_30_script |> EVERY *})
  done

ML {*
val typing_helper_31_script : tac list = [
(RTac @{thm kind_tfun[where k = "{E,S,D}"]}),
(RTac @{thm typing_helper_21}),
(RTac @{thm typing_helper_17})
] *}


lemma typing_helper_31[unfolded abbreviated_type_defs] :
  "kinding [] (TFun (TProduct (TCon ''SysState'' [] Writable) (TCon ''WordArray'' [TPrim (Num U32)] Writable)) (TCon ''SysState'' [] Writable)) {E, S, D}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_31_script |> EVERY *})
  done

ML {*
val typing_helper_32_script : tac list = [
(RTac @{thm kind_tsum[where k = "{E}"]}),
(SimpTac ([],[])),
(SimpTac ([],[])),
(RTac @{thm kind_all_cons}),
(RTac @{thm typing_helper_20}),
(RTac @{thm kind_all_empty})
] *}


lemma typing_helper_32[unfolded abbreviated_type_defs] :
  "kinding [] (TSum [(''Error'', TCon ''WordArray'' [TPrim (Num U32)] Writable)]) {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_32_script |> EVERY *})
  done

ML {*
val typing_helper_33_script : tac list = [
(RTac @{thm kind_tsum[where k = "{E}"]}),
(SimpTac ([],[])),
(SimpTac ([],[])),
(RTac @{thm kind_all_cons}),
(RTac @{thm typing_helper_17}),
(RTac @{thm kind_all_empty})
] *}


lemma typing_helper_33[unfolded abbreviated_type_defs] :
  "kinding [] (TSum [(''Error'', TCon ''SysState'' [] Writable)]) {E}"
  apply (unfold abbreviated_type_defs)?
  apply (tactic {* map (fn t => DETERM (interpret_tac t @{context} 1)) typing_helper_33_script |> EVERY *})
  done

ML {*
val u16_to_u64_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_1})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_1}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_1})],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (2,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_1})])])),(RTac @{thm typing_afun'}),(SimpTac ([@{thm \<Xi>_def},@{thm u16_to_u32_type_def[unfolded abbreviated_type_defs]}],[])),(RTac @{thm typing_helper_2}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm typing_helper_4}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_1}]),(SimpTac ([],[]))],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (3,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_afun'}),(SimpTac ([@{thm \<Xi>_def},@{thm u32_to_u64_type_def[unfolded abbreviated_type_defs]}],[])),(RTac @{thm typing_helper_2}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm typing_helper_6}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[]))]
] *}


lemma u16_to_u64_typecorrect :
  "\<Xi>, fst u16_to_u64_type, (u16_to_u64_typetree, [Some (fst (snd u16_to_u64_type))]) T\<turnstile> u16_to_u64 : snd (snd u16_to_u64_type)"
  apply (simp add: u16_to_u64_type_def u16_to_u64_def u16_to_u64_typetree_def replicate_unfold abbreviated_type_defs)
  apply (tactic {* mk_ttsplit_tacs @{thm u16_to_u64_def} @{thm u16_to_u64_typetree_def} @{context} u16_to_u64_typecorrect_script
  |> map (fn t => DETERM (interpret_tac t @{context} 1)) |> EVERY *})
  done

ML {*
val min_u32_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_7})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_7}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (3,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})]),(1,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (3,[(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "3"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_8})],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_8}]),(SimpTac ([],[]))],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[]))],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[]))]
] *}


lemma min_u32_typecorrect :
  "\<Xi>, fst min_u32_type, (min_u32_typetree, [Some (fst (snd min_u32_type))]) T\<turnstile> min_u32 : snd (snd min_u32_type)"
  apply (simp add: min_u32_type_def min_u32_def min_u32_typetree_def replicate_unfold abbreviated_type_defs)
  apply (tactic {* mk_ttsplit_tacs @{thm min_u32_def} @{thm min_u32_typetree_def} @{context} min_u32_typecorrect_script
  |> map (fn t => DETERM (interpret_tac t @{context} 1)) |> EVERY *})
  done

ML {*
val cogent_low_16_bits_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_lit'}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_1})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_cast}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_1}]),(SimpTac ([],[])),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (4,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})]),(2,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (4,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "4"]}),(SimpTac ([@{thm empty_def}],[]))],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (5,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_afun'}),(SimpTac ([@{thm \<Xi>_def},@{thm u32_to_u16_type_def[unfolded abbreviated_type_defs]}],[])),(RTac @{thm typing_helper_2}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm typing_helper_9}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[]))]
] *}


lemma cogent_low_16_bits_typecorrect :
  "\<Xi>, fst cogent_low_16_bits_type, (cogent_low_16_bits_typetree, [Some (fst (snd cogent_low_16_bits_type))]) T\<turnstile> cogent_low_16_bits : snd (snd cogent_low_16_bits_type)"
  apply (simp add: cogent_low_16_bits_type_def cogent_low_16_bits_def cogent_low_16_bits_typetree_def replicate_unfold abbreviated_type_defs)
  apply (tactic {* mk_ttsplit_tacs @{thm cogent_low_16_bits_def} @{thm cogent_low_16_bits_typetree_def} @{context} cogent_low_16_bits_typecorrect_script
  |> map (fn t => DETERM (interpret_tac t @{context} 1)) |> EVERY *})
  done

ML {*
val cogent_high_16_bits_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_lit'}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (3,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})]),(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (3,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "3"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_lit'}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_10})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (5,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_10})])])),(RTac @{thm typing_afun'}),(SimpTac ([@{thm \<Xi>_def},@{thm u8_to_u32_type_def[unfolded abbreviated_type_defs]}],[])),(RTac @{thm typing_helper_2}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm typing_helper_11}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_10}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (6,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})]),(2,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (6,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "6"]}),(SimpTac ([@{thm empty_def}],[]))],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (7,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_afun'}),(SimpTac ([@{thm \<Xi>_def},@{thm u32_to_u16_type_def[unfolded abbreviated_type_defs]}],[])),(RTac @{thm typing_helper_2}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm typing_helper_9}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[]))]
] *}


lemma cogent_high_16_bits_typecorrect :
  "\<Xi>, fst cogent_high_16_bits_type, (cogent_high_16_bits_typetree, [Some (fst (snd cogent_high_16_bits_type))]) T\<turnstile> cogent_high_16_bits : snd (snd cogent_high_16_bits_type)"
  apply (simp add: cogent_high_16_bits_type_def cogent_high_16_bits_def cogent_high_16_bits_typetree_def replicate_unfold abbreviated_type_defs)
  apply (tactic {* mk_ttsplit_tacs @{thm cogent_high_16_bits_def} @{thm cogent_high_16_bits_typetree_def} @{context} cogent_high_16_bits_typecorrect_script
  |> map (fn t => DETERM (interpret_tac t @{context} 1)) |> EVERY *})
  done

ML {*
val align64_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_12})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_12}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (3,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})]),(1,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (3,[(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "3"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_lit'}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_10})],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_cast}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_10}]),(SimpTac ([],[])),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (6,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_5})]),(2,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (6,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "6"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_8})],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_8}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (7,[(4,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})]),(5,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (7,[(5,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "7"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (8,[(5,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})]),(6,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (8,[(6,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "8"]}),(SimpTac ([@{thm empty_def}],[]))],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (9,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_5})]),(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (9,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "9"]}),(SimpTac ([@{thm empty_def}],[]))],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[]))]
] *}


lemma align64_typecorrect :
  "\<Xi>, fst align64_type, (align64_typetree, [Some (fst (snd align64_type))]) T\<turnstile> align64 : snd (snd align64_type)"
  apply (simp add: align64_type_def align64_def align64_typetree_def replicate_unfold abbreviated_type_defs)
  apply (tactic {* mk_ttsplit_tacs @{thm align64_def} @{thm align64_typetree_def} @{context} align64_typecorrect_script
  |> map (fn t => DETERM (interpret_tac t @{context} 1)) |> EVERY *})
  done

ML {*
val align32_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_7})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_7}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (3,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})]),(1,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (3,[(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "3"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_lit'}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_10})],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_cast}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_10}]),(SimpTac ([],[])),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (6,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})]),(2,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (6,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "6"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_8})],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_8}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (7,[(4,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})]),(5,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (7,[(5,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "7"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (8,[(5,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})]),(6,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (8,[(6,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "8"]}),(SimpTac ([@{thm empty_def}],[]))],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (9,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})]),(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (9,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "9"]}),(SimpTac ([@{thm empty_def}],[]))],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[]))]
] *}


lemma align32_typecorrect :
  "\<Xi>, fst align32_type, (align32_typetree, [Some (fst (snd align32_type))]) T\<turnstile> align32 : snd (snd align32_type)"
  apply (simp add: align32_type_def align32_def align32_typetree_def replicate_unfold abbreviated_type_defs)
  apply (tactic {* mk_ttsplit_tacs @{thm align32_def} @{thm align32_typetree_def} @{context} align32_typecorrect_script
  |> map (fn t => DETERM (interpret_tac t @{context} 1)) |> EVERY *})
  done

ML {*
val safe_add32_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_7})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_7}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (3,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})]),(1,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (3,[(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "3"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (4,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})]),(1,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (4,[(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "4"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_8})],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (5,[(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})]),(3,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (5,[(3,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "5"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_8})],
KindingTacs [(RTac @{thm typing_helper_8})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (6,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_8})]),(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_8})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_8}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (6,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_8})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_8}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "6"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_8})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_8}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_unit}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}])],
KindingTacs [(RTac @{thm typing_helper_13})],
TypingTacs [(RTac @{thm typing_con}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_13}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_13}),(RTac @{thm kind_all_empty}),(SimpTac ([],[]))],
TypingTacs [(RTac @{thm typing_prom}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_14}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_13}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_3}),(RTac @{thm kind_all_empty}),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_con}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_3}),(RTac @{thm kind_all_empty}),(SimpTac ([],[]))],
TypingTacs [(RTac @{thm typing_prom}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_15}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_13}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_3}),(RTac @{thm kind_all_empty}),(SimpTac ([],[]))]
] *}


lemma safe_add32_typecorrect :
  "\<Xi>, fst safe_add32_type, (safe_add32_typetree, [Some (fst (snd safe_add32_type))]) T\<turnstile> safe_add32 : snd (snd safe_add32_type)"
  apply (simp add: safe_add32_type_def safe_add32_def safe_add32_typetree_def replicate_unfold abbreviated_type_defs)
  apply (tactic {* mk_ttsplit_tacs @{thm safe_add32_def} @{thm safe_add32_typetree_def} @{context} safe_add32_typecorrect_script
  |> map (fn t => DETERM (interpret_tac t @{context} 1)) |> EVERY *})
  done

ML {*
val safe_add64_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_12})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_12}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (3,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})]),(1,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (3,[(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "3"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (4,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})]),(1,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (4,[(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "4"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_8})],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (5,[(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})]),(3,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (5,[(3,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "5"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_8})],
KindingTacs [(RTac @{thm typing_helper_8})],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (6,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_8})]),(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_8})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_8}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (6,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_8})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_8}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "6"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_8})],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_8}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_unit}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}])],
KindingTacs [(RTac @{thm typing_helper_13})],
TypingTacs [(RTac @{thm typing_con}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_13}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_13}),(RTac @{thm kind_all_empty}),(SimpTac ([],[]))],
TypingTacs [(RTac @{thm typing_prom}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_14}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_13}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_5}),(RTac @{thm kind_all_empty}),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_con}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_5}),(RTac @{thm kind_all_empty}),(SimpTac ([],[]))],
TypingTacs [(RTac @{thm typing_prom}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_16}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_13}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_5}),(RTac @{thm kind_all_empty}),(SimpTac ([],[]))]
] *}


lemma safe_add64_typecorrect :
  "\<Xi>, fst safe_add64_type, (safe_add64_typetree, [Some (fst (snd safe_add64_type))]) T\<turnstile> safe_add64 : snd (snd safe_add64_type)"
  apply (simp add: safe_add64_type_def safe_add64_def safe_add64_typetree_def replicate_unfold abbreviated_type_defs)
  apply (tactic {* mk_ttsplit_tacs @{thm safe_add64_def} @{thm safe_add64_typetree_def} @{context} safe_add64_typecorrect_script
  |> map (fn t => DETERM (interpret_tac t @{context} 1)) |> EVERY *})
  done

ML {*
val safe_sub32_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_7})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_7}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (3,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})]),(1,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (3,[(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "3"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (4,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})]),(1,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (4,[(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "4"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_8})],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_8}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_unit}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}])],
KindingTacs [(RTac @{thm typing_helper_13})],
TypingTacs [(RTac @{thm typing_con}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_13}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_13}),(RTac @{thm kind_all_empty}),(SimpTac ([],[]))],
TypingTacs [(RTac @{thm typing_prom}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_14}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_13}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_3}),(RTac @{thm kind_all_empty}),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
TypingTacs [(RTac @{thm typing_con}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_3}),(RTac @{thm kind_all_empty}),(SimpTac ([],[]))],
TypingTacs [(RTac @{thm typing_prom}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_15}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_13}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_3}),(RTac @{thm kind_all_empty}),(SimpTac ([],[]))]
] *}


lemma safe_sub32_typecorrect :
  "\<Xi>, fst safe_sub32_type, (safe_sub32_typetree, [Some (fst (snd safe_sub32_type))]) T\<turnstile> safe_sub32 : snd (snd safe_sub32_type)"
  apply (simp add: safe_sub32_type_def safe_sub32_def safe_sub32_typetree_def replicate_unfold abbreviated_type_defs)
  apply (tactic {* mk_ttsplit_tacs @{thm safe_sub32_def} @{thm safe_sub32_typetree_def} @{context} safe_sub32_typecorrect_script
  |> map (fn t => DETERM (interpret_tac t @{context} 1)) |> EVERY *})
  done

ML {*
val safe_sub64_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_12})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_12}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (3,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})]),(1,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (3,[(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "3"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_5})],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_prim'}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (4,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})]),(1,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (4,[(1,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_5})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "4"]}),(SimpTac ([@{thm empty_def}],[]))],
KindingTacs [(RTac @{thm typing_helper_8})],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_8}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_unit}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}])],
KindingTacs [(RTac @{thm typing_helper_13})],
TypingTacs [(RTac @{thm typing_con}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_13}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_13}),(RTac @{thm kind_all_empty}),(SimpTac ([],[]))],
TypingTacs [(RTac @{thm typing_prom}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_14}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_13}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_5}),(RTac @{thm kind_all_empty}),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_5})],
TypingTacs [(RTac @{thm typing_con}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_5}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_5}),(RTac @{thm kind_all_empty}),(SimpTac ([],[]))],
TypingTacs [(RTac @{thm typing_prom}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_16}]),(SimpTac ([],[])),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_13}),(RTac @{thm kind_all_cons}),(RTac @{thm typing_helper_5}),(RTac @{thm kind_all_empty}),(SimpTac ([],[]))]
] *}


lemma safe_sub64_typecorrect :
  "\<Xi>, fst safe_sub64_type, (safe_sub64_typetree, [Some (fst (snd safe_sub64_type))]) T\<turnstile> safe_sub64 : snd (snd safe_sub64_type)"
  apply (simp add: safe_sub64_type_def safe_sub64_def safe_sub64_typetree_def replicate_unfold abbreviated_type_defs)
  apply (tactic {* mk_ttsplit_tacs @{thm safe_sub64_def} @{thm safe_sub64_typetree_def} @{context} safe_sub64_typecorrect_script
  |> map (fn t => DETERM (interpret_tac t @{context} 1)) |> EVERY *})
  done

ML {*
val caller_typecorrect_script : hints list = [
KindingTacs [(RTac @{thm typing_helper_17})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_17}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_17})],
TypingTacs [(RTac @{thm typing_lit'}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_10})],
KindingTacs [(RTac @{thm typing_helper_17})],
TypingTacs [(RTac @{thm typing_cast}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_10}]),(SimpTac ([],[])),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_17})],
TypingTacs [(RTac @{thm typing_tuple}),(SplitsTac (4,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})]),(2,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_17})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_17}]),(SimpTac ([],[])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_19})],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (5,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_19})])])),(RTac @{thm typing_afun'}),(SimpTac ([@{thm \<Xi>_def},@{thm wordarray_create_0_type_def[unfolded abbreviated_type_defs]}],[])),(RTac @{thm typing_helper_2}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm typing_helper_23}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_19}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_22})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_22}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_21})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_21}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_17})],
KindingTacs [(RTac @{thm typing_helper_20})],
TypingTacs [(RTac @{thm typing_lit'}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_10})],
KindingTacs [(RTac @{thm typing_helper_17})],
KindingTacs [(RTac @{thm typing_helper_20})],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (10,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_10})])])),(RTac @{thm typing_afun'}),(SimpTac ([@{thm \<Xi>_def},@{thm u8_to_u32_type_def[unfolded abbreviated_type_defs]}],[])),(RTac @{thm typing_helper_2}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm typing_helper_11}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_10}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_17})],
KindingTacs [(RTac @{thm typing_helper_20})],
TypingTacs [(RTac @{thm typing_lit'}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_10})],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_17})],
KindingTacs [(RTac @{thm typing_helper_20})],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (12,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_10})])])),(RTac @{thm typing_afun'}),(SimpTac ([@{thm \<Xi>_def},@{thm u8_to_u32_type_def[unfolded abbreviated_type_defs]}],[])),(RTac @{thm typing_helper_2}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm typing_helper_11}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_10}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_17})],
KindingTacs [(RTac @{thm typing_helper_20})],
TypingTacs [(RTac @{thm typing_struct'}),(RTac @{thm typing_all_cons}),(SplitsTac (13,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})]),(2,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})]),(5,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_20})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_20}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (13,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})]),(2,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_cons}),(SplitsTac (13,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[])),(RTac @{thm typing_all_empty'[where n = "13"]}),(SimpTac ([@{thm empty_def}],[])),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_24})],
KindingTacs [(RTac @{thm typing_helper_17})],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (14,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_24})])])),(RTac @{thm typing_afun'}),(SimpTac ([@{thm \<Xi>_def},@{thm wordarray_put_0_type_def[unfolded abbreviated_type_defs]}],[])),(RTac @{thm typing_helper_2}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm typing_helper_26}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_24}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_25})],
KindingTacs [(RTac @{thm typing_helper_17})],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_25}]),(SimpTac ([],[]))],
TTSplitBangTacs [(RTac @{thm ttsplit_bangI}),(SimpTac ([],[])),(SimpTac ([],[])),(ForceTac []),(RTac @{thm ttsplit_bang_innerI(5)}),(RTac @{thm typing_helper_20}),(SimpTac ([],[])),(RTac @{thm ttsplit_bang_innerI(1)}),(RTac @{thm ttsplit_bang_innerI(1)}),(RTac @{thm ttsplit_bang_innerI(1)}),(RTac @{thm ttsplit_bang_innerI(1)}),(RTac @{thm ttsplit_bang_innerI(1)}),(RTac @{thm ttsplit_bang_innerI(1)}),(RTac @{thm ttsplit_bang_innerI(2)}),(RTac @{thm typing_helper_17}),(RTac @{thm ttsplit_bang_innerI(1)}),(RTac @{thm ttsplit_bang_innerI(1)}),(RTac @{thm ttsplit_bang_innerI(1)}),(RTac @{thm ttsplit_bang_innerI(1)}),(RTac @{thm ttsplit_bang_innerI(1)}),(RTac @{thm ttsplit_bang_innerI(1)}),(RTac @{thm ttsplit_bang_innerI(1)}),(RTac @{thm ttsplit_bang_innerI(1)}),(RTac @{thm ttsplit_bang_innerI(6)})],
KindingTacs [(RTac @{thm typing_helper_28})],
TypingTacs [(RTac @{thm typing_lit'}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_10})],
KindingTacs [(RTac @{thm typing_helper_28})],
TypingTacs [(RTac @{thm typing_cast}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_10}]),(SimpTac ([],[])),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_28})],
TypingTacs [(RTac @{thm typing_tuple}),(SplitsTac (18,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_3})]),(2,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_28})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_28}]),(SimpTac ([],[])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3}]),(SimpTac ([],[]))],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (19,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_29})])])),(RTac @{thm typing_afun'}),(SimpTac ([@{thm \<Xi>_def},@{thm wordarray_get_0_type_def[unfolded abbreviated_type_defs]}],[])),(RTac @{thm typing_helper_2}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm typing_helper_30}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_29}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_20})],
KindingTacs [(RTac @{thm typing_helper_17})],
TypingTacs [(RTac @{thm typing_tuple}),(SplitsTac (17,[(0,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_3})]),(1,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_20})]),(8,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_17})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_3},@{thm typing_helper_17}]),(SimpTac ([],[])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_20}]),(SimpTac ([],[]))],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (18,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_21})])])),(RTac @{thm typing_afun'}),(SimpTac ([@{thm \<Xi>_def},@{thm wordarray_free_0_type_def[unfolded abbreviated_type_defs]}],[])),(RTac @{thm typing_helper_2}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm typing_helper_31}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_21}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_3})],
KindingTacs [(RTac @{thm typing_helper_32})],
KindingTacs [(RTac @{thm typing_helper_17})],
TypingTacs [(RTac @{thm typing_esac}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_32}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_20})],
KindingTacs [(RTac @{thm typing_helper_17})],
TypingTacs [(RTac @{thm typing_tuple}),(SplitsTac (17,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_20})]),(8,[(RTac @{thm split_comp.left}),(RTac @{thm typing_helper_17})])])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_17}]),(SimpTac ([],[])),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_20}]),(SimpTac ([],[]))],
TypingTacs [(RTac @{thm typing_app}),(SplitsTac (18,[(0,[(RTac @{thm split_comp.right}),(RTac @{thm typing_helper_21})])])),(RTac @{thm typing_afun'}),(SimpTac ([@{thm \<Xi>_def},@{thm wordarray_free_0_type_def[unfolded abbreviated_type_defs]}],[])),(RTac @{thm typing_helper_2}),(SimpTac ([],[])),(SimpTac ([],[])),(RTac @{thm exI[where x = "{E,S,D}"]}),(RTac @{thm typing_helper_31}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac []),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_21}]),(SimpTac ([],[]))],
KindingTacs [(RTac @{thm typing_helper_33})],
TypingTacs [(RTac @{thm typing_esac}),(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_33}]),(SimpTac ([],[]))],
TypingTacs [(RTac @{thm typing_var}),(SimpTac ([@{thm empty_def}],[])),(WeakeningTac [@{thm typing_helper_17}]),(SimpTac ([],[]))]
] *}


lemma caller_typecorrect :
  "\<Xi>, fst caller_type, (caller_typetree, [Some (fst (snd caller_type))]) T\<turnstile> caller : snd (snd caller_type)"
  apply (simp add: caller_type_def caller_def caller_typetree_def replicate_unfold abbreviated_type_defs)
  apply (tactic {* mk_ttsplit_tacs @{thm caller_def} @{thm caller_typetree_def} @{context} caller_typecorrect_script
  |> map (fn t => DETERM (interpret_tac t @{context} 1)) |> EVERY *})
  done


(* Manual specification for abstract functions *)
definition
  "u8_to_u32 \<sigma>x \<sigma>x'= (case \<sigma>x of (\<sigma>, UPrim (LU8 x)) \<Rightarrow> \<sigma>x' = (\<sigma>, UPrim (LU32 (ucast x))))"

definition
  "wordarray_get_0 args ret \<equiv> case args of
     (\<sigma>, UProduct (UPtr wa_ptr _) (UPrim (LU32 i))) \<Rightarrow>
       case \<sigma> wa_ptr of
         Some (UAbstract (Abstyp_WordArray_U32 (vals, ptr))) \<Rightarrow>
           ret = (\<sigma>, UPrim (LU32 (if unat i < length vals then vals ! unat i else 0)))"

definition
  "wordarray_put_0 args ret \<equiv> case args of
     (\<sigma>, URecord [(UPtr wa_ptr wa_ptr_repr, _),
                  (UPrim (LU32 i), _),
                  (UPrim (LU32 val), _)]) \<Rightarrow>
        case \<sigma> wa_ptr of
          Some (UAbstract (Abstyp_WordArray_U32 (vals, ptr))) \<Rightarrow>
            ret =
             (if unat i < length vals
              then (\<sigma>(wa_ptr := Some (UAbstract (Abstyp_WordArray_U32 (vals[unat i := val], ptr)))),
                    USum ''Success'' (UPtr wa_ptr wa_ptr_repr) [(''Success'', wa_ptr_repr)])
              else (\<sigma>, USum ''Error'' (UPtr wa_ptr wa_ptr_repr) [(''Error'', wa_ptr_repr)]))"

definition
  "\<xi> func_name \<equiv> case func_name of
    ''cogent_log2'' \<Rightarrow> undefined
  | ''random_u32'' \<Rightarrow> undefined
  | ''test_file_close'' \<Rightarrow> undefined
  | ''test_file_open'' \<Rightarrow> undefined
  | ''test_file_read_next_u32'' \<Rightarrow> undefined
  | ''test_stack_probe'' \<Rightarrow> undefined
  | ''test_time_end'' \<Rightarrow> undefined
  | ''test_time_start'' \<Rightarrow> undefined
  | ''u16_to_u32'' \<Rightarrow> undefined
  | ''u16_to_u8'' \<Rightarrow> undefined
  | ''u32_to_u16'' \<Rightarrow> undefined
  | ''u32_to_u64'' \<Rightarrow> undefined
  | ''u32_to_u8'' \<Rightarrow> undefined
  | ''u64_to_u32'' \<Rightarrow> undefined
  | ''u8_to_u16'' \<Rightarrow> undefined
  | ''u8_to_u32'' \<Rightarrow> u8_to_u32
  | ''u8_to_u64'' \<Rightarrow> undefined
  | ''wordarray_cmp'' \<Rightarrow> undefined
  | ''wordarray_create_0'' \<Rightarrow> undefined
  | ''wordarray_free_0'' \<Rightarrow> undefined
  | ''wordarray_get_0'' \<Rightarrow> wordarray_get_0
  | ''wordarray_put_0'' \<Rightarrow> wordarray_put_0"

ML {*
val caller_typing_bucket =
  mk_ttsplit_tacs_final @{thm caller_def} @{thm caller_typetree_def} @{context} caller_typecorrect_script
  |> map (fn t => fn ctxt => t ctxt 1)
  |> get_typing_bucket @{context} "caller"
*}

new_C_include_dir "stdlib"
new_C_include_dir "../../cogent/tests/antiquote-tests/test-wordarray"
new_C_include_dir "../../cogent/tests/antiquote-tests/plat/console"

install_C_file "wordarraytest.c"
autocorres [no_opt, ts_rules=nondet] "wordarraytest.c"

(* C type and value relations *)
instantiation unit_t_C :: cogent_C_val begin
  definition type_rel_unit_t_C_def: "type_rel r (_ :: unit_t_C itself) \<equiv> r = RUnit"
  definition val_rel_unit_t_C_def: "val_rel uv (_ :: unit_t_C) \<equiv> uv = UUnit"
  instance ..
end

instantiation WordArray_u8_C :: cogent_C_val begin
  definition type_rel_WordArray_u8_C_def:
    "type_rel r (_ :: WordArray_u8_C itself) \<equiv> r = RCon ''WordArray'' [RPrim (Num U8)]"
  definition val_rel_WordArray_u8_C_def:
    "val_rel uv (arr :: WordArray_u8_C) \<equiv>
       \<exists>vals ptr. uv = UAbstract (Abstyp_WordArray_U8 (vals, Ptr ptr)) \<and>
                val_rel (UPtr ptr (RPtr (RPrim (Num U8)))) (WordArray_u8_C.values_C arr)"
  instance ..
end

instantiation WordArray_u32_C :: cogent_C_val begin
  definition type_rel_WordArray_u32_C_def:
    "type_rel r (_ :: WordArray_u32_C itself) \<equiv> r = RCon ''WordArray'' [RPrim (Num U32)]"
  definition val_rel_WordArray_u32_C_def:
    "val_rel uv (arr :: WordArray_u32_C) \<equiv>
       \<exists>vals ptr. uv = UAbstract (Abstyp_WordArray_U32 (vals, Ptr ptr)) \<and>
                val_rel (UPtr ptr (RPtr (RPrim (Num U32)))) (WordArray_u32_C.values_C arr)"
  instance ..
end

instantiation SysState_t_C :: cogent_C_val begin
  definition type_rel_SysState_t_C_def:
    "type_rel r (_ :: SysState_t_C itself) \<equiv> r = RCon ''SysState'' []"
  definition val_rel_SysState_t_C_def:
    "val_rel uv (_ :: SysState_t_C) \<equiv> uv = UAbstract Abstyp_SysState"
  instance ..
end

local_setup {* fn lthy => local_setup_val_rel_type_rel "wordarraytest.c" lthy *}
find_theorems name:val_rel_ -name:word
lemmas val_rel_simps = 
  val_rel_word val_rel_ptr_def val_rel_unit_def val_rel_unit_t_C_def
  val_rel_t1_C_def val_rel_t2_C_def val_rel_t3_C_def val_rel_t4_C_def 
  val_rel_t5_C_def val_rel_t6_C_def val_rel_t7_C_def val_rel_t8_C_def 
  val_rel_t9_C_def val_rel_t10_C_def val_rel_t11_C_def val_rel_t12_C_def 
  val_rel_t13_C_def val_rel_t18_C_def val_rel_t40_C_def val_rel_t61_C_def 
  val_rel_t64_C_def val_rel_t67_C_def val_rel_t75_C_def val_rel_t80_C_def 
  val_rel_t119_C_def val_rel_t123_C_def val_rel_WordArray_u8_C_def val_rel_WordArray_u32_C_def

class cogent_C_heap = cogent_C_val +
  fixes is_valid    :: "lifted_globals \<Rightarrow> 'a ptr \<Rightarrow> bool"
  fixes heap        :: "lifted_globals \<Rightarrow> 'a ptr \<Rightarrow> 'a"
  fixes heap_update :: "(('a ptr \<Rightarrow> 'a) \<Rightarrow> 'a ptr \<Rightarrow> 'a) \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals"

instantiation WordArray_u8_C :: cogent_C_heap
begin
  definition is_valid_WordArray_u8_C_def: "is_valid \<equiv> is_valid_WordArray_u8_C"
  definition heap_WordArray_u8_C_def: "heap \<equiv> heap_WordArray_u8_C"
  definition heap_WordArray_u8_C_update_def: "heap_update \<equiv> heap_WordArray_u8_C_update"
  instance ..
end

instantiation WordArray_u32_C :: cogent_C_heap
begin
  definition is_valid_WordArray_u32_C_def: "is_valid \<equiv> is_valid_WordArray_u32_C"
  definition heap_WordArray_u32_C_def: "heap \<equiv> heap_WordArray_u32_C"
  definition heap_WordArray_u32_C_update_def: "heap_update \<equiv> heap_WordArray_u32_C_update"
  instance ..
end

axiomatization where wordarray_create_0_corres:
  "val_rel x x' \<Longrightarrow>
   update_sem_init.corres abs_typing abs_repr srel (App (AFun ''wordarray_create_0'' []) (Var 0))
     (do retval \<leftarrow> wordarraytest.wordarray_create_0' x'; gets (\<lambda>_. retval) od)
     \<xi> (x # \<gamma>) \<Xi> (Some t # \<Gamma>') \<sigma> s"

axiomatization where wordarray_free_0_corres:
  "val_rel x x' \<Longrightarrow>
   update_sem_init.corres abs_typing abs_repr srel (App (AFun ''wordarray_free_0'' []) (Var 0))
     (do retval \<leftarrow> wordarraytest.wordarray_free_0' x'; gets (\<lambda>_. retval) od)
     \<xi> (x # \<gamma>) \<Xi> (Some t # \<Gamma>') \<sigma> s"

locale WordArrayTest = wordarraytest begin
  definition "abs_repr' a \<equiv> case a of
      Abstyp_WordArray_U8 _ \<Rightarrow> (''WordArray'', [RPrim (Num U8)])
    | Abstyp_WordArray_U32 _ \<Rightarrow> (''WordArray'', [RPrim (Num U32)])
    | Abstyp_SysState \<Rightarrow> (''SysState'', [])"

  definition "abs_typing' a name \<tau>s sig (r :: ptrtyp set) (w :: ptrtyp set) \<equiv>
    r = {} \<and> w = {} \<and> sig \<noteq> Unboxed \<and>
    (case a of
      Abstyp_WordArray_U8 _ \<Rightarrow> name = ''WordArray'' \<and> \<tau>s = [TPrim (Num U8)]
    | Abstyp_WordArray_U32 _ \<Rightarrow> name = ''WordArray'' \<and> \<tau>s = [TPrim (Num U32)]
    | Abstyp_SysState \<Rightarrow> name = ''SysState'' \<and> \<tau>s = [])"
end

sublocale WordArrayTest \<subseteq>
  update_sem_init abs_typing' abs_repr'
  apply (unfold abs_repr'_def[abs_def] abs_typing'_def[abs_def])
  apply unfold_locales

        apply (clarsimp split: abstyp.splits)
          apply (case_tac s, simp_all)[]
         apply (case_tac s, simp_all)[]
        apply (case_tac s, simp_all)[]

       apply simp

      apply simp

     apply simp

    apply simp

   apply (clarsimp split: abstyp.splits)
     apply (case_tac s, (case_tac s', simp_all)+)[]
    apply (case_tac s, (case_tac s', simp_all)+)[]
   apply (case_tac s, (case_tac s', simp_all)+)[]

  apply (clarsimp split: abstyp.splits)
  done

(* FIXME: syntax translations from UpdateSemantics are not available in WordArrayTest‽ *)
context WordArrayTest begin

thm wordarray_create_0'_def
thm wordarray_free_0'_def
thm wordarray_put_0'_def
thm wordarray_get_0'_def
thm caller_def caller'_def

lemma return_exn_simp:
  "do ret <- A;
      _ <- guard (\<lambda>_. True);
      _ <- gets (\<lambda>_. x :: c_exntype);
      _ <- guard (\<lambda>_. True);
      _ <- gets (\<lambda>_. ());
      _ <- guard (\<lambda>_. True);
      gets (\<lambda>_. ret) od = A"
  by simp

(* Relation between program heaps *)
definition
  heap_rel_ptr ::
  "(funtyp, abstyp, ptrtyp) store \<Rightarrow> lifted_globals \<Rightarrow>
   ('a :: cogent_C_heap) ptr \<Rightarrow> bool"
where
  "heap_rel_ptr \<sigma> h p \<equiv>
   (\<forall>uv.
     \<sigma> (ptr_val p) = Some uv \<longrightarrow>
     type_rel (uval_repr uv) TYPE('a) \<longrightarrow>
     is_valid h p \<and> val_rel uv (heap h p))"

definition
  "heap_rel_WordArray_u32_C \<sigma> h p \<equiv>
   (\<forall>uv.
       \<sigma> (ptr_val p) = Some uv \<longrightarrow>
       type_rel (uval_repr uv) TYPE(WordArray_u32_C) \<longrightarrow>
       (\<exists>vals ptr. uv = UAbstract (Abstyp_WordArray_U32 (vals, ptr)) \<and>
        is_valid h p \<and>
        val_rel (UAbstract (Abstyp_WordArray_U32 (vals, ptr))) (heap h p) \<and>
        unat (WordArray_u32_C.len_C (heap h p)) = length vals \<and>
        0 <=s WordArray_u32_C.len_C (heap h p) \<and>
        (\<forall>(i::word32) < ucast (WordArray_u32_C.len_C (heap h p)).
           c_guard (WordArray_u32_C.values_C (heap h p) +\<^sub>p uint i) \<and>
           is_valid_w32 h (WordArray_u32_C.values_C (heap h p) +\<^sub>p uint i) \<and>
           heap_w32 h (WordArray_u32_C.values_C (heap h p) +\<^sub>p uint i) = vals ! unat i)))"

definition heap_rel :: "(funtyp, abstyp, ptrtyp) store \<Rightarrow> lifted_globals \<Rightarrow> bool"
where
  "heap_rel \<sigma> h \<equiv>
   (\<forall>(p :: WordArray_u8_C ptr).   heap_rel_ptr \<sigma> h p) \<and> (* TODO *)
   (\<forall>(p :: WordArray_u32_C ptr).  heap_rel_WordArray_u32_C \<sigma> h p)"

definition state_rel :: "((funtyp, abstyp, ptrtyp) store \<times> lifted_globals) set"
where
  "state_rel = {(\<sigma>, h). heap_rel \<sigma> h}"


(* To be proven *)
thm wordarray_put_0_def
lemma wordarray_put_0_corres:
  "val_rel x x' \<Longrightarrow>
   corres state_rel (App (AFun ''wordarray_put_0'' []) (Var 0))
     (do retval \<leftarrow> wordarray_put_0' x'; gets (\<lambda>_. retval) od)
     \<xi> (x # \<gamma>) \<Xi> (Some (TRecord [(TCon ''WordArray'' [TPrim (Num U32)] Writable, False), (TPrim (Num U32), False), (TPrim (Num U32), False)] Unboxed) # \<Gamma>') \<sigma> s"
  apply (rule corres_app_abstract)
    apply (simp add: \<xi>_def)
   apply (monad_eq simp: wordarray_put_0'_def)
   apply (clarsimp simp add: state_rel_def heap_rel_def)
   apply (erule_tac x="arr_C x'" in allE)
   apply (clarsimp simp: heap_rel_WordArray_u32_C_def)
   apply (clarsimp simp add: val_rel_simps type_rel_WordArray_u32_C_def)
   apply (erule u_t_recE, simp)
   apply (erule uval_typing_record.cases, simp_all) 
   apply (erule uval_typing.cases, simp_all)
  apply (clarsimp simp: is_valid_WordArray_u32_C_def)
   apply (erule impE)
    apply (force dest: abs_typing_repr)
   apply (clarsimp simp: is_valid_WordArray_u32_C_def)
   apply (erule_tac x="scast (idx_C x')" in allE)
   apply (simp add: heap_WordArray_u32_C_def)
   apply (erule impE)
    apply (simp add: word_not_le)
    apply (subst (asm) scast_eq_ucast)
     apply (simp add: word_msb_sint not_le[symmetric])
     apply (drule word_sle_def[THEN iffD1])
     apply simp
    apply simp
   apply simp

  apply (monad_eq simp: wordarray_put_0'_def wordarray_put_0_def val_rel_simps)
  apply (clarsimp simp: state_rel_def)
  apply (frule heap_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1])
  apply clarsimp
  apply (erule_tac x="arr_C x'" in allE)
  apply (clarsimp simp: heap_rel_WordArray_u32_C_def heap_WordArray_u32_C_def)
  apply (erule u_t_recE)
  apply (erule uval_typing_record.cases, simp_all)
  apply (erule uval_typing.cases, simp_all)
  apply clarsimp
  apply (frule abs_typing_repr)
  apply (clarsimp simp: type_rel_WordArray_u32_C_def)
  apply (case_tac "scast (WordArray_u32_C.len_C (heap_WordArray_u32_C s (arr_C x'))) \<le> idx_C x'")

   apply (clarsimp simp: TAG_ENUM_Success_def TAG_ENUM_Error_def)
   apply (subst (asm) scast_eq_ucast)
    apply (simp add: word_msb_sint not_le[symmetric])
    apply (drule word_sle_def[THEN iffD1])
    apply simp
   apply (unat_arith)
   apply (simp add: unat_ucast_upcast is_up)

  apply (clarsimp simp: heap_rel_def TAG_ENUM_Success_def TAG_ENUM_Error_def)
  apply (rule exI)+
  apply (rule conjI)

   apply (clarsimp simp: heap_rel_ptr_def)
   apply (rule conjI)
    apply simp
   apply simp
  apply (erule uval_typing_record.cases, simp_all)
  apply clarsimp
  apply (erule uval_typing.cases, simp_all)
  apply (erule uval_typing_record.cases, simp_all) 
  apply (erule uval_typing.cases, simp_all)
  apply clarify
  apply (subgoal_tac "(idx_C x') = val_C x'")
  sorry


(* alternate proof attempt *)
lemma word32_small_shift_eq:
  "\<lbrakk> 0 < k; k < 32;
     (x :: word32) < 2^(32 - k);
     y < 2^(32 - k);
      x << k = y << k \<rbrakk> \<Longrightarrow>
    x = y"
  apply (rule word_unat.Rep_eqD)
  apply (drule unat_cong)
  apply (subst (asm) shiftl_t2n)+
  apply (subst (asm) unat_mult_simple)
   apply (drule unat_mono)
   apply (drule mult_less_mono2[where k = "unat (2 ^ k :: word32)" and i = "unat x"])
    apply (rule unat_1_0[THEN iffD1])
    apply (rule word_1_le_power)
    apply simp
   apply (subst (asm) unat_power_lower, simp)+
   apply (subst (asm) power_add[symmetric], simp)
  apply (subst (asm) unat_mult_simple[where y = y])
   apply (drule unat_mono[where a = y])
   apply (drule mult_less_mono2[where k = "unat (2 ^ k :: word32)" and i = "unat y"])
    apply (rule unat_1_0[THEN iffD1])
    apply (rule word_1_le_power)
    apply simp
   apply (subst (asm) unat_power_lower, simp)+
   apply (subst (asm) power_add[symmetric], simp)
  apply simp
  done

lemma ptr_aligned_plus2:
  assumes aligned: "ptr_aligned (p +\<^sub>p i)"
  shows "ptr_aligned (p::'a::mem_type ptr)"
proof -
  have "int (align_of TYPE('a)) dvd (i * int (size_of TYPE('a)))"
    by (metis dvd_mult zdvd_int align_size_of)
  with aligned show ?thesis
    apply (case_tac p, simp add: ptr_aligned_def ptr_add_def scast_id)
    apply (simp only: unat_simps len_signed)
    apply (drule dvd_mod_imp_dvd[OF _ align])
    apply (fastforce elim: dvd_plus_eq_left[THEN iffD1, rotated]
                     simp: dvd_mod[OF _ align] align_size_of)
    done
qed

lemma wordarray_put_0_corres:
  "val_rel x x' \<Longrightarrow>
   corres state_rel (App (AFun ''wordarray_put_0'' []) (Var 0))
     (do retval \<leftarrow> wordarray_put_0' x'; gets (\<lambda>_. retval) od)
     \<xi> (x # \<gamma>) \<Xi>
     (Some (TRecord
              [(TCon ''WordArray'' [TPrim (Num U32)] Writable, False),
               (TPrim (Num U32), False), (TPrim (Num U32), False)] Unboxed) # \<Gamma>')
     \<sigma> s"
  apply (rule corres_app_abstract)
    apply (simp add: \<xi>_def)
   apply (monad_eq simp: wordarray_put_0'_def)
   apply (clarsimp simp add: state_rel_def heap_rel_def)
   apply (erule_tac x="t3_C.arr_C x'" in allE)
   apply (clarsimp simp: heap_rel_WordArray_u32_C_def)
   apply (clarsimp simp add: val_rel_simps type_rel_WordArray_u32_C_def)
   apply (erule uval_typing.cases uval_typing_record.cases, simp_all)+
   apply clarify
   apply (thin_tac "Num U32 = lit_type (LU32 (t3_C.idx_C x'))") (* FIXME: simplifier loop *)
   apply (thin_tac "Num U32 = lit_type (LU32 (t3_C.val_C x'))")
   apply clarsimp
   apply (erule impE)
    apply (force dest: abs_typing_repr)
   apply (clarsimp simp: is_valid_WordArray_u32_C_def)
   apply (erule_tac x="scast (t3_C.idx_C x')" in allE)
   apply (simp add: heap_WordArray_u32_C_def)
   apply (erule impE)
    apply (simp add: word_not_le)
    apply (subst (asm) scast_eq_ucast)
     apply (simp add: word_msb_sint not_le[symmetric])
     apply (drule word_sle_def[THEN iffD1])
     apply simp
    apply simp
   apply simp

  apply (monad_eq simp: wordarray_put_0'_def wordarray_put_0_def val_rel_simps)
  apply (clarsimp simp: state_rel_def heap_rel_def)
  apply (frule_tac x="t3_C.arr_C x'" in spec)
  apply (clarsimp simp: heap_rel_WordArray_u32_C_def heap_WordArray_u32_C_def)
  apply (erule uval_typing.cases uval_typing_record.cases, simp_all)+
  apply clarify
  apply (thin_tac "Num U32 = lit_type (LU32 (t3_C.idx_C x'))") (* FIXME: simplifier loop *)
  apply (thin_tac "Num U32 = lit_type (LU32 (t3_C.val_C x'))")
  apply clarsimp
  apply (drule abs_typing_repr)
  apply (clarsimp simp: type_rel_WordArray_u32_C_def)
  apply (subst (asm) scast_eq_ucast,
           simp add: word_msb_sint not_le[symmetric],
           drule word_sle_def[THEN iffD1], simp)+
  apply (subgoal_tac "unat (WordArray_u32_C.len_C (heap_WordArray_u32_C s (t3_C.arr_C x')))
                    = unat (ucast (WordArray_u32_C.len_C (heap_WordArray_u32_C s (t3_C.arr_C x'))) :: word32)")
   prefer 2
   apply (simp add: unat_ucast_upcast is_up)
  apply clarsimp
  apply (rule_tac x="if unat (idx_C x') < length vals
                     then \<sigma>(ptr_val (arr_C x') \<mapsto>
                            UAbstract (Abstyp_WordArray_U32 (vals[unat (idx_C x') := val_C x'], ptr)))
                     else \<sigma>" in exI)
  apply (rule_tac x="if unat (idx_C x') < length vals
                     then USum ''Success'' (UPtr (ptr_val (arr_C x')) (RCon ''WordArray'' [RPrim (Num U32)]))
                            [(''Success'', RCon ''WordArray'' [RPrim (Num U32)])]
                     else USum ''Error'' (UPtr (ptr_val (arr_C x')) (RCon ''WordArray'' [RPrim (Num U32)]))
                            [(''Error'', RCon ''WordArray'' [RPrim (Num U32)])]" in exI)
  apply clarsimp
  apply (rule conjI)
   (* The heap gets updated *)
   apply (clarsimp simp: heap_rel_ptr_def[abs_def] abs_repr'_def)
   apply (clarsimp simp: type_rel_WordArray_u8_C_def)
   apply (rule conjI)
    (* WordArray_U8 heap is unaffected *)
    apply (fastforce simp: is_valid_WordArray_u8_C_def heap_WordArray_u8_C_def)

   (* WordArray_U32 heap update *)
   apply (intro conjI impI allI)
     apply (rename_tac p)
     apply (clarsimp simp: heap_rel_WordArray_u32_C_def
                           heap_WordArray_u32_C_def is_valid_WordArray_u32_C_def)
     apply (subgoal_tac "t3_C.idx_C x' < ucast (WordArray_u32_C.len_C (heap_WordArray_u32_C s (t3_C.arr_C x')))")
     prefer 2
      apply (rule unat_less_impl_less)
      apply (simp add: unat_ucast_upcast is_up)
     apply clarsimp
     apply (intro conjI impI)
       apply (fastforce simp: val_rel_WordArray_u32_C_def val_rel_ptr_def)
      apply (rule allI, rename_tac i)
      apply (rule conjI)
       apply clarsimp
       apply (subgoal_tac "i = idx_C x'")
        apply simp
       apply (frule_tac x=i in spec)
       apply (clarsimp simp: ptr_add_def c_guard_def)
       apply (rule word32_small_shift_eq[where k = 2, simplified shiftl_t2n, simplified])
         apply (subst word_not_le[symmetric], clarsimp)
         apply (clarsimp simp: c_null_guard_def)
         defer (* i < 2^30 *)
        defer
       apply (metis mult.commute[where 'a = word32])
      apply clarsimp
      apply (subgoal_tac "i \<noteq> idx_C x'")
       apply simp
      apply (clarsimp simp: ptr_add_def c_guard_def)
     apply (drule_tac x=p in spec)
     apply (clarsimp simp: heap_rel_WordArray_u32_C_def is_valid_WordArray_u32_C_def heap_WordArray_u32_C_def)
  oops

lemma wordarray_get_0_corres:
  "val_rel x x' \<Longrightarrow> 
   corres state_rel (App (AFun ''wordarray_get_0'' []) (Var 0))
     (do retval \<leftarrow> wordarray_get_0' x'; gets (\<lambda>_. retval) od)
     \<xi> (x # \<gamma>) \<Xi> (Some (TProduct (TCon ''WordArray'' [TPrim (Num U32)] ReadOnly) (TPrim (Num U32))) # \<Gamma>') \<sigma> s"
  apply (rule corres_app_abstract)
    apply (simp add: \<xi>_def)
   apply (monad_eq simp: wordarray_get_0'_def)
   apply (clarsimp simp add: state_rel_def heap_rel_def)
   apply (erule_tac x="t2_C.p1_C x'" in allE)
   apply (clarsimp simp: heap_rel_WordArray_u32_C_def)
   apply (clarsimp simp add: val_rel_simps type_rel_WordArray_u32_C_def)
   apply (erule u_t_productE, clarsimp)
   apply (erule uval_typing.cases, simp_all)
   apply (erule impE)
    apply (force dest: abs_typing_repr)
   apply (clarsimp simp: is_valid_WordArray_u32_C_def)
   apply (erule_tac x="scast (t2_C.p2_C x')" in allE)
   apply (simp add: heap_WordArray_u32_C_def)
   apply (erule impE)
    apply (simp add: word_not_le)
    apply (subst (asm) scast_eq_ucast)
     apply (simp add: word_msb_sint not_le[symmetric])
     apply (drule word_sle_def[THEN iffD1])
     apply simp
    apply simp
   apply simp

  apply (monad_eq simp: wordarray_get_0'_def wordarray_get_0_def val_rel_simps)
  apply (clarsimp simp: state_rel_def)
  apply (frule heap_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1])
  apply clarsimp
  apply (erule_tac x="t2_C.p1_C x'" in allE)
  apply (clarsimp simp: heap_rel_WordArray_u32_C_def heap_WordArray_u32_C_def)
  apply (erule u_t_productE)
  apply (erule uval_typing.cases, simp_all)
  apply clarsimp
  apply (drule abs_typing_repr)
  apply (clarsimp simp: type_rel_WordArray_u32_C_def)
  apply (subgoal_tac "s' = s")
   prefer 2
   apply (case_tac "scast (WordArray_u32_C.len_C (heap_WordArray_u32_C s (t2_C.p1_C x'))) \<le> t2_C.p2_C x'")
    apply simp
   apply simp
  apply clarsimp
  apply (subst (asm) scast_eq_ucast,
           simp add: word_msb_sint not_le[symmetric],
           drule word_sle_def[THEN iffD1], simp)+
  apply (subgoal_tac "unat (WordArray_u32_C.len_C (heap_WordArray_u32_C s (t2_C.p1_C x')))
                    = unat (ucast (WordArray_u32_C.len_C (heap_WordArray_u32_C s (t2_C.p1_C x'))) :: word32)")
   prefer 2
   apply (simp add: unat_ucast_upcast is_up)
  apply clarsimp

  apply (intro conjI impI)
   apply (erule_tac x="scast (t2_C.p2_C x')" in allE)
   apply (clarsimp simp: word_not_le)
   apply (subgoal_tac "t2_C.p2_C x' < ucast (WordArray_u32_C.len_C (heap_WordArray_u32_C s (t2_C.p1_C x')))")
    prefer 2
    apply (rule unat_less_impl_less)
    apply (simp add: unat_ucast_upcast is_up)
   apply clarsimp

  apply (simp add: le_def[symmetric])
  apply (erule impE)
   apply (rule word_le_nat_alt[THEN iffD2])
   apply simp
  apply simp
  done

lemma u8_to_u32_corres:
  "val_rel x x' \<Longrightarrow>
   corres srel (App (AFun ''u8_to_u32'' []) (Var 0))
     (do retval \<leftarrow> u8_to_u32' x'; gets (\<lambda>_. retval) od)
     \<xi> (x # \<gamma>) \<Xi> (Some (TPrim (Num U8)) # \<Gamma>') \<sigma> s"
  apply (rule corres_app_abstract)
     apply (simp add: \<xi>_def)
    apply (simp add: u8_to_u32'_def[simplified] snd_return)  
   apply (simp add: u8_to_u32'_def u8_to_u32_def in_return val_rel_word)
  done


lemma corres_case_t13_C_Success:
  "\<lbrakk> x < length \<Gamma>';
     \<Gamma>' ! x = Some (TSum [(''Error'', TCon ''SysState'' [] Writable),
                          (''Success'', TProduct (TCon ''SysState'' [] Writable)
                                                 (TCon ''WordArray'' [TPrim (Num U32)] Writable))]);
     [] \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1 | \<Gamma>2;
     val_rel (\<gamma> ! x) x';
     case \<gamma> ! x of
       USum vtag vval vtyps \<Rightarrow>
         if t13_C.tag_C x' = TAG_ENUM_Success
         then ''Success'' = vtag \<and> val_rel vval (t13_C.Success_C x')
         else ''Success'' \<noteq> vtag \<and>
               val_rel (USum vtag vval [x\<leftarrow>vtyps . fst x \<noteq> ''Success''])
                (t123_C.Error_C_update (\<lambda>_. t13_C.Error_C x')
                   (t123_C.tag_C_update (\<lambda>_. t13_C.tag_C x') (t123_C 0 NULL)));
     \<Xi>', [], \<Gamma>1 \<turnstile> Var x : TSum [(''Error'', TCon ''SysState'' [] Writable),
                                 (''Success'', TProduct (TCon ''SysState'' [] Writable)
                                                        (TCon ''WordArray'' [TPrim (Num U32)] Writable))];
     \<Xi>', [], Some (TProduct (TCon ''SysState'' [] Writable)
                            (TCon ''WordArray'' [TPrim (Num U32)] Writable)) # \<Gamma>2 \<turnstile> match : t;
     \<Xi>', [], Some (TSum [(''Error'', TCon ''SysState'' [] Writable)]) # \<Gamma>2 \<turnstile> not_match : t;
     \<And>a a'. val_rel a a' \<Longrightarrow>
             corres srel match (match' a') \<xi>' (a # \<gamma>) \<Xi>'
               (Some (TProduct (TCon ''SysState'' [] Writable)
                               (TCon ''WordArray'' [TPrim (Num U32)] Writable)) # \<Gamma>2) \<sigma> s;
     \<And>r r'. val_rel r r' \<Longrightarrow>
             corres srel not_match (not_match' r') \<xi>' (r # \<gamma>) \<Xi>'
               (Some (TSum [(''Error'', TCon ''SysState'' [] Writable)]) # \<Gamma>2) \<sigma> s
     \<rbrakk> \<Longrightarrow>
     corres srel
       (Case (Var x) ''Success'' match not_match)
       (condition (\<lambda>_. t13_C.tag_C x' = TAG_ENUM_Success)
           (match' (t13_C.Success_C x'))
           (do x \<leftarrow> gets (\<lambda>_. t123_C.Error_C_update (\<lambda>_. t13_C.Error_C x')
                                (t123_C.tag_C_update (\<lambda>_. t13_C.tag_C x') (t123_C 0 NULL)));
               not_match' x od))
         \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  apply simp
  apply (rule corres_case
    [where \<tau>s = "[(''Error'', TCon ''SysState'' [] Writable),
                  (''Success'', TProduct (TCon ''SysState'' [] Writable)
                                         (TCon ''WordArray'' [TPrim (Num U32)] Writable))]"
       and tag = "''Success''" and tag' = "TAG_ENUM_Success"
       and get_tag' = "t13_C.tag_C" and get_A' = "t13_C.Success_C"
       and wrap_rest' = "\<lambda>x'. t123_C.Error_C_update (\<lambda>_. t13_C.Error_C x')
                (t123_C.tag_C_update (\<lambda>_. t13_C.tag_C x') (t123_C 0 NULL))"
    , simplified])
  by auto

lemma corres_case_t4_C_Success:
  "\<lbrakk> x < length \<Gamma>';
    \<Gamma>' ! x = Some (TSum [(''Error'', TCon ''WordArray'' [TPrim (Num U32)] Writable),
                         (''Success'', TCon ''WordArray'' [TPrim (Num U32)] Writable)]);
    [] \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1 | \<Gamma>2;
    val_rel (\<gamma> ! x) x';
    case \<gamma> ! x of
      USum vtag vval vtyps \<Rightarrow>
        if t4_C.tag_C x' = TAG_ENUM_Success
        then ''Success'' = vtag \<and> val_rel vval (t4_C.Success_C x')
        else ''Success'' \<noteq> vtag \<and>
               val_rel (USum vtag vval [x\<leftarrow>vtyps . fst x \<noteq> ''Success''])
                (t119_C.Error_C_update (\<lambda>_. t4_C.Error_C x')
                  (t119_C.tag_C_update (\<lambda>_. t4_C.tag_C x') (t119_C 0 NULL)));
    \<Xi>', [], \<Gamma>1 \<turnstile> Var x : TSum [(''Error'', TCon ''WordArray'' [TPrim (Num U32)] Writable),
                                (''Success'', TCon ''WordArray'' [TPrim (Num U32)] Writable)];
    \<Xi>', [], Some (TCon ''WordArray'' [TPrim (Num U32)] Writable) # \<Gamma>2 \<turnstile> match : t;
    \<Xi>', [], Some (TSum [(''Error'', TCon ''WordArray'' [TPrim (Num U32)] Writable)]) # \<Gamma>2 \<turnstile> not_match : t;
    \<And>a a'. val_rel a a' \<Longrightarrow>
            corres srel match (match' a') \<xi>' (a # \<gamma>) \<Xi>'
              (Some (TCon ''WordArray'' [TPrim (Num U32)] Writable) # \<Gamma>2) \<sigma> s;
    \<And>r r'. val_rel r r' \<Longrightarrow>
            corres srel not_match (not_match' r') \<xi>' (r # \<gamma>) \<Xi>'
              (Some (TSum [(''Error'', TCon ''WordArray'' [TPrim (Num U32)] Writable)]) # \<Gamma>2) \<sigma> s
   \<rbrakk> \<Longrightarrow>
   corres srel (Case (Var x) ''Success'' match not_match)
     (condition (\<lambda>_. t4_C.tag_C x' = TAG_ENUM_Success)
           (match' (t4_C.Success_C x'))
           (do x \<leftarrow> gets (\<lambda>_. t119_C.Error_C_update (\<lambda>_. t4_C.Error_C x')
                                (t119_C.tag_C_update (\<lambda>_. t4_C.tag_C x') (t119_C 0 NULL)));
               not_match' x od))
     \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  apply simp
  apply (rule corres_case
    [where \<tau>s = "[(''Error'', TCon ''WordArray'' [TPrim (Num U32)] Writable),
                  (''Success'', TCon ''WordArray'' [TPrim (Num U32)] Writable)]"
       and tag = "''Success''" and tag' = "TAG_ENUM_Success"
       and get_tag' = "t4_C.tag_C" and get_A' = "t4_C.Success_C"
       and wrap_rest' = "\<lambda>x'. t119_C.Error_C_update (\<lambda>_. t4_C.Error_C x')
                (t119_C.tag_C_update (\<lambda>_. t4_C.tag_C x') (t119_C 0 NULL))"
    , simplified
    ])
  by auto

lemma corres_letbang'_4:
  assumes split\<Gamma>: "split_bang [] is \<Gamma>' \<Gamma>1 \<Gamma>2"
  assumes typing_x: "\<Xi>', [], \<Gamma>1 \<turnstile> x : t"
  assumes has_kind: " [] \<turnstile>  t :\<kappa>  k"
  assumes kind_escapable: "E \<in> k"
  assumes corres_x: "corres srel x (do r1 \<leftarrow> x1'; r2 \<leftarrow> x2' r1; r3 \<leftarrow> x3' r1 r2; x4' r1 r2 r3 od) \<xi>' \<gamma> \<Xi>' \<Gamma>1 \<sigma> s"
  assumes corres_cont: "\<And>v v' \<sigma>' s'. val_rel v (v'::'a::cogent_C_val) \<Longrightarrow> 
                      corres srel y (y' v') \<xi>' (v # \<gamma>) \<Xi>' (Some t # \<Gamma>2) \<sigma>' s'"
  shows "corres srel (LetBang is x y)
    (do r1 \<leftarrow> x1'; r2 \<leftarrow> x2' r1; r3 \<leftarrow> x3' r1 r2; r4 \<leftarrow> x4' r1 r2 r3; y' r4 od) \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
  using assms
    corres_letbang[where
      x'="do r1 \<leftarrow> x1'; r2 \<leftarrow> x2' r1; r3 \<leftarrow> x3' r1 r2; x4' r1 r2 r3 od",
      simplified bind_assoc]
  by blast

(* Top-level proof *)
lemma caller_corres:
  "val_rel a a' \<Longrightarrow>
   corres state_rel caller (caller' a') \<xi> [a] \<Xi> [Some (fst (snd caller_type))] \<sigma> s"
  apply (simp only: fst_conv snd_conv caller_def caller'_def caller_type_def)
  apply (subst return_exn_simp)
  apply (subst guard_True_bind)+
  apply (rule corres_let)
     apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
    apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
   apply (rule corres_var)
   apply simp
  apply (rule corres_let)
     apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *}) back
    apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
   apply (rule corres_lit)
   apply (simp add: val_rel_word)
  apply (rule corres_let)
     apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
    apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
   apply (rule corres_cast)
    apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
   apply simp
  apply (rule corres_let)
     apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *}) back
    apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
   apply (rule corres_tuple)
   apply (simp add: val_rel_t11_C_def)
  apply (rule corres_let)
     apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *}) back
    apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
   apply (rule wordarray_create_0_corres)
   apply simp
  apply (subst gets_to_return, subst bind_return) back back back back back back back
  apply (rule corres_case_t13_C_Success)
           apply simp
          apply simp
         apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
        apply simp
       apply (fastforce simp: val_rel_t13_C_def val_rel_t123_C_def TAG_ENUM_Error_def TAG_ENUM_Success_def)
      apply (simp, tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
     apply (simp, tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
    apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
   apply (rule corres_split_lazy[where ?p1.0="t12_C.p1_C" and ?p2.0="t12_C.p2_C"])
         apply simp
        apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
       apply (simp add: val_rel_t12_C_def)
      apply simp
     apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
    apply (simp, tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
   apply (rule corres_let)
      apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
     apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
    apply (rule corres_lit)
    apply (simp add: val_rel_word)
   apply (rule corres_let)
      apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *}) back
     apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
    apply (rule u8_to_u32_corres)
    apply simp
   apply (rule corres_let)
      apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
     apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
    apply (rule corres_lit)
    apply (simp add: val_rel_word)
   apply (rule corres_let)
      apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
     apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
    apply (rule u8_to_u32_corres)
    apply simp
   apply (rule corres_let)
      apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
     apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
    apply (rule corres_struct[where xs="[5,2,0]", simplified, folded gets_to_return])
    apply (simp add: val_rel_t3_C_def)
   apply (rule corres_let)
      apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
     apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
    apply (rule wordarray_put_0_corres)
    apply simp
   apply (rule corres_case_t4_C_Success)
           apply simp
          apply simp
         apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
        apply simp
       apply (fastforce simp: val_rel_t4_C_def val_rel_t119_C_def TAG_ENUM_Success_def TAG_ENUM_Error_def)
      apply (simp, tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
     apply (simp, tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
    apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
   apply (rule corres_letbang'_4)
         apply (simp, tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
        apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
       apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
      apply simp
     apply (rule corres_let)
        apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *}) back
       apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
      apply (rule corres_lit)
      apply (simp add: val_rel_word)
     apply (rule corres_let)
        apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *}) back
       apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
      apply (rule corres_cast)
       apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
      apply simp
     apply (rule corres_let)
        apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *}) back
       apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
      apply (rule corres_tuple)
      apply (simp add: val_rel_t2_C_def)
     apply (rule wordarray_get_0_corres)
     apply simp
    apply (rule corres_let)
       apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *}) back
      apply (simp, tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
     apply (rule corres_tuple)
     apply (simp add: val_rel_t12_C_def)
    apply (rule wordarray_free_0_corres)
    apply simp
   apply (rule corres_let)
      apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
     apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
    apply (rule_tac get_val'=t119_C.Error_C in corres_esac)
       apply simp
      apply simp
     apply simp
    apply (clarsimp simp: val_rel_t119_C_def)
   apply (rule corres_let)
      apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *}) back
     apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
    apply (rule corres_tuple)
    apply (simp add: val_rel_t12_C_def)
   apply (rule wordarray_free_0_corres)
   apply simp
  apply (rule corres_let)
     apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
    apply (tactic {* map (fn t => rtac t 1) caller_typing_bucket |> APPEND_LIST *})
   apply (rule_tac get_val'=t123_C.Error_C in corres_esac)
      apply simp
     apply simp
    apply simp
   apply (clarsimp simp: val_rel_t123_C_def)
  apply (rule corres_var)
  apply simp
  done

(* ghetto find_theorems template *)
ML {*
caller_typing_bucket
|> filter (fn t =>
     Pattern.matches_subterm @{theory}
       (Proof_Context.read_term_pattern @{context}
          "_, _, _ \<turnstile> Split _ _ : _",
        prop_of t))
*}

end

end

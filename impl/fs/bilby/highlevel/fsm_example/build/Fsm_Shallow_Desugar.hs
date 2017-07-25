{-
This build info header is now disabled by --fno-gen-header.
--------------------------------------------------------------------------------
We strongly discourage users from generating individual files for Isabelle
proofs, as it will end up with an inconsistent collection of output files (i.e.
Isabelle input files).
-}

-- NOTE: this file is modified based on the generated one!!!

{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -F -pgmFderive -optF-F #-}

module Fsm_Shallow_Desugar where
import Data.Bits ((.&.), (.|.), complement, xor, shiftL, shiftR)
import qualified Data.Map as M
import Data.Word (Word8, Word16, Word32, Word64)
import FFI (CUbiVolInfo, CUbiDevInfo, CRbt)
import Prelude (not, div, mod, fromIntegral, undefined, (+), (-), (*), (&&), (||), (>), (>=), (<), (<=), (==), (/=),
                Char, String, Int, Bool(..), Eq, Ord, Show, return, error, (<$>), (<*>))
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen


word64Max :: Word64
word64Max = (18446744073709551615 :: Word64)

word32Max :: Word32
word32Max = (4294967295 :: Word32)

bilbyFsFirstLogEbNum :: Word32
bilbyFsFirstLogEbNum = fromIntegral (2 :: Word8) :: Word32

eNoMem :: Word32
eNoMem = fromIntegral (12 :: Word8) :: Word32

type WordArray a = [a]

type UbiVolInfo = CUbiVolInfo

type UbiDevInfo = CUbiDevInfo

data SysState

data RbtNode k v

type Rbt k v = CRbt k v

type Array a = [a]

type WordArrayIndex = Word32

type WordArrayCopyP a = R34 (WordArray a) (WordArray a) Word32 Word32 Word32

type WordArrayFindSubP a = R32 (WordArray a) (WordArray a) Word32

type WordArrayPutP a = R8 (WordArray a) Word32 a

type WordArraySetP a = R33 (WordArray a) Word32 Word32 a

type WordArrayCloneP a b = R31 SysState (WordArray a)

type WordArraySliceP a = R33 SysState (WordArray a) Word32 Word32

type Seq64_bodyParam acc obsv rbrk = R0 acc obsv Word64

type Seq32_stepParam = Word32 -> Word32

type Seq32_simple_bodyParam acc = acc

type Seq32_simple_body acc = acc -> acc

type Seq32_bodyParam acc obsv rbrk = R0 acc obsv Word32

type Seq32SimpleParam acc = R16 Word32 Word32 Word32 (acc -> acc) acc

type RR c a b = R31 c (V41 b a)

type R a b = V41 b a

type RbtCreateR k v = V41 SysState (R31 SysState (Rbt k v))

type Result a b = V41 b a

type Option a = V43 () a

type RbtModifyR k v acc = R39 (Rbt k v) (V43 () (RbtNode k v)) acc

type OptElemAO a acc obsv = R30 (V43 () a) acc obsv

type OptElemA a acc = R29 (V43 () a) acc

type ObjType = Word8

type ObjTrans = Word8

type ObjSuper = R26 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word64

type ObjSumEntry = R23 Word64 Word64 Word32 Word32 Word16

type ObjSummary = R28 Word32 (WordArray (R23 Word64 Word64 Word32 Word32 Word16)) Word32

type ObjInodeFlags = Word32

type ObjIdInode = Word64

type ObjIdDentarr = Word64

type ObjIdData = Word64

type ObjId = Word64

type ObjInode = R22 Word64 Word64 Word64 Word64 Word64 Word32 Word32 Word32 Word32 Word32

type ObjDentry = R24 Word32 Word8 Word16 (WordArray Word8)

type ObjDel = R19 Word64

type ObjData = R21 Word64 (WordArray Word8)

type LoopResult a b = V40 b a

type LRR acc brk = R31 acc (V40 brk ())

type Seq32_body acc obsv rbrk = R0 acc obsv Word32 -> R31 acc (V40 rbrk ())

type Seq32Param acc obsv rbrk = R17 Word32 Word32 Word32 (R0 acc obsv Word32 -> R31 acc (V40 rbrk ())) acc obsv

type Seq32StepFParam acc obsv rbrk = R18 Word32 Word32 (Word32 -> Word32) (R0 acc obsv Word32 -> R31 acc (V40 rbrk ())) acc obsv

type Seq64_body acc obsv rbrk = R0 acc obsv Word64 -> R31 acc (V40 rbrk ())

type Seq64Param acc obsv rbrk = R17 Word64 Word64 Word64 (R0 acc obsv Word64 -> R31 acc (V40 rbrk ())) acc obsv

type WordArrayMapRE a acc rbrk = R31 (R31 (WordArray a) acc) (V40 rbrk ())

type GimNode = R10 Word16 Word64

type RbtGimNode = RbtNode Word64 (R10 Word16 Word64)

type FsmState = R27 Word32 (WordArray Word8) (WordArray Word32) (Rbt Word64 (R10 Word16 Word64))

type FreeF a = R31 SysState a -> SysState

type FreeAccF a acc obsv = R33 SysState a acc obsv -> R31 SysState acc

type FindResult = V42 Word32 ()

type ErrCode = Word32

type ElemB a rbrk = R14 a rbrk

type ElemAO a acc obsv = R13 a acc obsv

type RbtElemAO k v acc obsv = R13 (RbtNode k v) acc obsv

type RbtCondF k v acc obsv = R13 (RbtNode k v) acc obsv -> Bool

type RbtConsumeF k v acc obsv = R13 (RbtNode k v) acc obsv -> acc

type RbtCondEraseP k v acc obsv = R37 (Rbt k v) k (R13 (RbtNode k v) acc obsv -> Bool) (R13 (RbtNode k v) acc obsv -> acc) acc obsv

type RbtFilterP k v acc obsv = R35 (Rbt k v) k k (R13 (RbtNode k v) acc obsv -> Bool) (R13 (RbtNode k v) acc obsv -> acc) acc obsv

type RbtIterateF k v acc obsv rbrk = R13 (RbtNode k v) acc obsv -> V40 (R31 rbrk (RbtNode k v)) (R31 acc (RbtNode k v))

type RbtIterateNoBreakF k v acc obsv = R13 (RbtNode k v) acc obsv -> R31 acc (RbtNode k v)

type RbtIterateNoBreakP k v acc obsv = R36 (Rbt k v) k k (R13 (RbtNode k v) acc obsv -> R31 acc (RbtNode k v)) acc obsv

type RbtModifyF k v acc obsv = R13 (RbtNode k v) acc obsv -> R31 (RbtNode k v) acc

type RbtModifyP k v acc obsv = R38 (Rbt k v) k (R13 (RbtNode k v) acc obsv -> R31 (RbtNode k v) acc) (RbtNode k v) acc obsv

type WordArrayFoldF a acc obsv rbrk = R13 a acc obsv -> V40 rbrk acc

type WordArrayFoldP a acc obsv rbrk = R4 (WordArray a) Word32 Word32 (R13 a acc obsv -> V40 rbrk acc) acc obsv

type WordArrayFoldNoBreakF a acc obsv = R13 a acc obsv -> acc

type WordArrayFoldNoBreakP a acc obsv = R4 (WordArray a) Word32 Word32 (R13 a acc obsv -> acc) acc obsv

type WordArrayMapF a acc obsv rbrk = R13 a acc obsv -> R31 (R31 a acc) (V40 rbrk ())

type WordArrayMapP a acc obsv rbrk = R4 (WordArray a) Word32 Word32 (R13 a acc obsv -> R31 (R31 a acc) (V40 rbrk ())) acc obsv

type WordArrayMapNoBreakF a acc obsv = R13 a acc obsv -> R31 a acc

type WordArrayMapNoBreakP a acc obsv = R4 (WordArray a) Word32 Word32 (R13 a acc obsv -> R31 a acc) acc obsv

type ElemA a acc = R12 a acc

type WordArrayModifyF a acc obsv = R13 a acc obsv -> R12 a acc

type WordArrayModifyP a acc obsv = R7 (WordArray a) Word32 (R13 a acc obsv -> R12 a acc) acc obsv

type CString = WordArray Word8

type ArrayUseValueF a acc obsv = R13 a acc obsv -> acc

type ArrayUseMaybeValueF a acc obsv = R30 (V43 () a) acc obsv -> acc

type ArrayModifyF a acc = R29 (V43 () a) acc -> R29 (V43 () a) acc

type ArrayMapNoBreakF a acc obsv = R30 (V43 () a) acc obsv -> R31 (V43 () a) acc

type ArrayMapF a acc obsv rbrk = R30 (V43 () a) acc obsv -> V40 (R31 (V43 () a) rbrk) (R31 (V43 () a) acc)

type ArrayMapExF a acc obsv rbrk = R13 a acc obsv -> V40 (R14 a rbrk) (R12 a acc)

type ArrayFoldNoBreakF a acc obsv = R13 a acc obsv -> acc

type ArrayFoldF a acc obsv rbrk = R13 a acc obsv -> V40 rbrk acc

type ArrayFilterF a acc obsv = R13 a acc obsv -> R31 acc (V41 a ())

type ArrayFilterP a acc obsv = R2 (Array a) (R13 a acc obsv -> R31 acc (V41 a ())) acc obsv

type ArrayFoldNoBreakP a acc obsv = R2 (Array a) (R13 a acc obsv -> acc) acc obsv

type ArrayFoldP a acc obsv rbrk = R2 (Array a) (R13 a acc obsv -> V40 rbrk acc) acc obsv

type ArrayFreeP a = R3 (Array a) (R31 SysState a -> SysState) SysState

type ArrayMapExP a acc obsv rbrk = R4 (Array a) Word32 Word32 (R13 a acc obsv -> V40 (R14 a rbrk) (R12 a acc)) acc obsv

type ArrayMapNoBreakP a acc obsv = R4 (Array a) Word32 Word32 (R30 (V43 () a) acc obsv -> R31 (V43 () a) acc) acc obsv

type ArrayMapP a acc obsv rbrk = R4 (Array a) Word32 Word32 (R30 (V43 () a) acc obsv -> V40 (R31 (V43 () a) rbrk) (R31 (V43 () a) acc)) acc obsv

type ArrayModifyP a acc = R6 (Array a) Word32 (R29 (V43 () a) acc -> R29 (V43 () a) acc) acc

type ArrayReplaceP a = R5 (Array a) Word32 a (R31 SysState a -> SysState) SysState

type ArrayUseMaybeValueP a acc obsv = R7 (Array a) Word32 (R30 (V43 () a) acc obsv -> acc) acc obsv

type ArrayUseValueP a acc obsv = R7 (Array a) Word32 (R13 a acc obsv -> acc) acc obsv

type ObjDentarr = R20 Word64 Word32 (Array (R24 Word32 Word8 Word16 (WordArray Word8)))

type ObjUnion =
     V44 (R21 Word64 (WordArray Word8)) (R19 Word64) (R20 Word64 Word32 (Array (R24 Word32 Word8 Word16 (WordArray Word8)))) (R22 Word64 Word64 Word64 Word64 Word64 Word32 Word32 Word32 Word32 Word32) ()
       (R28 Word32 (WordArray (R23 Word64 Word64 Word32 Word32 Word16)) Word32)
       (R26 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word64)

type Obj =
     R25 Word32 Word32 Word64 Word32 Word32 Word8 Word8
       (V44 (R21 Word64 (WordArray Word8)) (R19 Word64) (R20 Word64 Word32 (Array (R24 Word32 Word8 Word16 (WordArray Word8)))) (R22 Word64 Word64 Word64 Word64 Word64 Word32 Word32 Word32 Word32 Word32) ()
          (R28 Word32 (WordArray (R23 Word64 Word64 Word32 Word32 Word16)) Word32)
          (R26 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word64))

type MountState =
     R11 Word32 Word32 (R26 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word64)
       (R25 Word32 Word32 Word64 Word32 Word32 Word8 Word8
          (V44 (R21 Word64 (WordArray Word8)) (R19 Word64) (R20 Word64 Word32 (Array (R24 Word32 Word8 Word16 (WordArray Word8)))) (R22 Word64 Word64 Word64 Word64 Word64 Word32 Word32 Word32 Word32 Word32) ()
             (R28 Word32 (WordArray (R23 Word64 Word64 Word32 Word32 Word16)) Word32)
             (R26 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word64)))
       Word32
       UbiVolInfo
       UbiDevInfo
       Bool

type ArrB a rbrk = R9 a rbrk

type ArrA a acc = R1 a acc

u8_to_u64 :: Word8 -> Word64
u8_to_u64 = undefined

u8_to_u32 :: Word8 -> Word32
u8_to_u32 = undefined

u8_to_u16 :: Word8 -> Word16
u8_to_u16 = undefined

u64_to_u32 :: Word64 -> Word32
u64_to_u32 = undefined

u64_to_u16 :: Word64 -> Word16
u64_to_u16 = undefined

u32_to_u8 :: Word32 -> Word8
u32_to_u8 = undefined

u32_to_u64 :: Word32 -> Word64
u32_to_u64 = undefined

u32_to_u16 :: Word32 -> Word16
u32_to_u16 = undefined

u16_to_u8 :: Word16 -> Word8
u16_to_u8 = undefined

u16_to_u32 :: Word16 -> Word32
u16_to_u32 = undefined

random_u32 :: () -> Word32
random_u32 = undefined

cogent_log2 :: Word32 -> Word32
cogent_log2 = undefined

wordarray_cmp :: R31 (WordArray Word8) (WordArray Word8) -> Bool
wordarray_cmp = undefined

wordarray_copy :: R34 (WordArray a) (WordArray a) Word32 Word32 Word32 -> WordArray a
wordarray_copy = undefined

wordarray_get :: R31 (WordArray a) Word32 -> a
wordarray_get = undefined

wordarray_length :: WordArray a -> Word32
wordarray_length = undefined

wordarray_put2 :: R8 (WordArray a) Word32 a -> WordArray a
wordarray_put2 = undefined

wordarray_set :: R33 (WordArray a) Word32 Word32 a -> WordArray a
wordarray_set = undefined

wordarray_u8_as_u32 :: WordArray Word8 -> Word32
wordarray_u8_as_u32 = undefined

wordarray_free :: R31 SysState (WordArray a) -> SysState
wordarray_free = undefined

seq32_simple :: R16 Word32 Word32 Word32 (acc -> acc) acc -> acc
seq32_simple = undefined

freeRbtNode :: R31 SysState (RbtNode k v) -> SysState
freeRbtNode = undefined

rbtnode_get_key :: RbtNode k v -> k
rbtnode_get_key = undefined

rbtnode_get_val :: RbtNode k v -> v
rbtnode_get_val = undefined

rbtnode_put_key :: R31 (RbtNode k v) k -> RbtNode k v
rbtnode_put_key = undefined

rbtnode_put_val :: R31 (RbtNode k v) v -> RbtNode k v
rbtnode_put_val = undefined

rbt_free :: R31 SysState (Rbt k v) -> SysState
rbt_free = undefined

wordarray_clone_rr :: R31 SysState (WordArray a) -> R31 SysState (V41 () (WordArray b))
wordarray_clone_rr = undefined

wordarray_slice :: R33 SysState (WordArray a) Word32 Word32 -> R31 SysState (V41 () (WordArray a))
wordarray_slice = undefined

rbt_create :: SysState -> V41 SysState (R31 SysState (Rbt k v))
rbt_create = undefined

newRbtNode :: SysState -> V41 SysState (R31 SysState (RbtNode k v))
newRbtNode = undefined

rbt_get_value :: R31 (Rbt k v) k -> V41 () v
rbt_get_value = undefined

rbt_next :: R31 (Rbt k v) k -> V41 () k
rbt_next = undefined

wordarray_create :: R31 SysState Word32 -> V41 SysState (R31 SysState (WordArray a))
wordarray_create = undefined

wordarray_create_nz :: R31 SysState Word32 -> V41 SysState (R31 SysState (WordArray a))
wordarray_create_nz = undefined

wordarray_put :: R8 (WordArray a) Word32 a -> V41 (WordArray a) (WordArray a)
wordarray_put = undefined

seq32 :: R17 Word32 Word32 Word32 (R0 acc obsv Word32 -> R31 acc (V40 rbrk ())) acc obsv -> R31 acc (V40 rbrk ())
seq32 = undefined

seq32_rev :: R17 Word32 Word32 Word32 (R0 acc obsv Word32 -> R31 acc (V40 rbrk ())) acc obsv -> R31 acc (V40 rbrk ())
seq32_rev = undefined

seq32_stepf :: R18 Word32 Word32 (Word32 -> Word32) (R0 acc obsv Word32 -> R31 acc (V40 rbrk ())) acc obsv -> R31 acc (V40 rbrk ())
seq32_stepf = undefined

seq64 :: R17 Word64 Word64 Word64 (R0 acc obsv Word64 -> R31 acc (V40 rbrk ())) acc obsv -> R31 acc (V40 rbrk ())
seq64 = undefined

wordarray_findsub :: R32 (WordArray a) (WordArray a) Word32 -> V42 Word32 ()
wordarray_findsub = undefined

rbt_cond_erase :: R37 (Rbt k v) k (R13 (RbtNode k v) acc obsv -> Bool) (R13 (RbtNode k v) acc obsv -> acc) acc obsv -> R31 (Rbt k v) acc
rbt_cond_erase = undefined

rbt_filter :: R35 (Rbt k v) k k (R13 (RbtNode k v) acc obsv -> Bool) (R13 (RbtNode k v) acc obsv -> acc) acc obsv -> R31 (Rbt k v) acc
rbt_filter = undefined

rbt_iterate :: R36 (Rbt k v) k k (R13 (RbtNode k v) acc obsv -> V40 (R31 rbrk (RbtNode k v)) (R31 acc (RbtNode k v))) acc obsv -> V40 (R31 (Rbt k v) rbrk) (R31 (Rbt k v) acc)
rbt_iterate = undefined

rbt_iterate_no_break :: R36 (Rbt k v) k k (R13 (RbtNode k v) acc obsv -> R31 acc (RbtNode k v)) acc obsv -> R31 (Rbt k v) acc
rbt_iterate_no_break = undefined

rbt_modify :: R38 (Rbt k v) k (R13 (RbtNode k v) acc obsv -> R31 (RbtNode k v) acc) (RbtNode k v) acc obsv -> R39 (Rbt k v) (V43 () (RbtNode k v)) acc
rbt_modify = undefined

wordarray_fold :: R4 (WordArray a) Word32 Word32 (R13 a acc obsv -> V40 rbrk acc) acc obsv -> V40 rbrk acc
wordarray_fold = undefined

wordarray_fold_no_break :: R4 (WordArray a) Word32 Word32 (R13 a acc obsv -> acc) acc obsv -> acc
wordarray_fold_no_break = undefined

wordarray_map :: R4 (WordArray a) Word32 Word32 (R13 a acc obsv -> R31 (R31 a acc) (V40 rbrk ())) acc obsv -> R31 (R31 (WordArray a) acc) (V40 rbrk ())
wordarray_map = undefined

wordarray_map_no_break :: R4 (WordArray a) Word32 Word32 (R13 a acc obsv -> R31 a acc) acc obsv -> R31 (WordArray a) acc
wordarray_map_no_break = undefined

wordarray_print :: WordArray Word8 -> ()
wordarray_print = undefined

array_fold_no_break :: R2 (Array a) (R13 a acc obsv -> acc) acc obsv -> acc
array_fold_no_break = undefined

array_fold :: R2 (Array a) (R13 a acc obsv -> V40 rbrk acc) acc obsv -> V40 rbrk acc
array_fold = undefined

array_free :: R3 (Array a) (R31 SysState a -> SysState) SysState -> SysState
array_free = undefined

array_use_maybe_value :: R7 (Array a) Word32 (R30 (V43 () a) acc obsv -> acc) acc obsv -> acc
array_use_maybe_value = undefined

array_use_value :: R7 (Array a) Word32 (R13 a acc obsv -> acc) acc obsv -> acc
array_use_value = undefined

array_create :: R31 SysState Word32 -> V41 SysState (R31 SysState (Array a))
array_create = undefined

array_exists :: R31 (Array a) Word32 -> Bool
array_exists = undefined

array_filter :: R2 (Array a) (R13 a acc obsv -> R31 acc (V41 a ())) acc obsv -> R1 (Array a) acc
array_filter = undefined

array_length :: Array a -> Word32
array_length = undefined

array_map :: R4 (Array a) Word32 Word32 (R30 (V43 () a) acc obsv -> V40 (R31 (V43 () a) rbrk) (R31 (V43 () a) acc)) acc obsv -> V40 (R31 (Array a) rbrk) (R31 (Array a) acc)
array_map = undefined

array_map_no_break :: R4 (Array a) Word32 Word32 (R30 (V43 () a) acc obsv -> R31 (V43 () a) acc) acc obsv -> R31 (Array a) acc
array_map_no_break = undefined

array_nb_elem :: Array a -> Word32
array_nb_elem = undefined

array_remove :: R31 (Array a) Word32 -> R31 (Array a) (V43 () a)
array_remove = undefined

array_replace :: R5 (Array a) Word32 a (R31 SysState a -> SysState) SysState -> R31 (R31 SysState (Array a)) (V41 () ())
array_replace = undefined

array_map_ex :: R4 (Array a) Word32 Word32 (R13 a acc obsv -> V40 (R14 a rbrk) (R12 a acc)) acc obsv -> V40 (R9 (Array a) rbrk) (R1 (Array a) acc)
array_map_ex = undefined

array_modify :: R6 (Array a) Word32 (R29 (V43 () a) acc -> R29 (V43 () a) acc) acc -> R1 (Array a) acc
array_modify = undefined

wordarray_modify :: R7 (WordArray a) Word32 (R13 a acc obsv -> R12 a acc) acc obsv -> R1 (WordArray a) acc
wordarray_modify = undefined

u16_to_u64 :: Word16 -> Word64
u16_to_u64 __ds_var_0 = let x = __ds_var_0 in u32_to_u64 (u16_to_u32 x)

to_u64 :: Word64 -> Word64
to_u64 __ds_var_0 = let x = __ds_var_0 in x

to_u32 :: Word32 -> Word32
to_u32 __ds_var_0 = let x = __ds_var_0 in x

to_u16 :: Word16 -> Word16
to_u16 __ds_var_0 = let x = __ds_var_0 in x

min_u64 :: R31 Word64 Word64 -> Word64
min_u64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R31{p1 = __shallow_v45, p2 = __shallow_v46} = __ds_var_0 in __shallow_v45
      in
      let __ds_var_2 = __ds_var_1
          b = let R31{p1 = __shallow_v47, p2 = __shallow_v48} = __ds_var_1 in __shallow_v48
        in if (a < b) then a else b

min_u32 :: R31 Word32 Word32 -> Word32
min_u32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R31{p1 = __shallow_v49, p2 = __shallow_v50} = __ds_var_0 in __shallow_v49
      in
      let __ds_var_2 = __ds_var_1
          b = let R31{p1 = __shallow_v51, p2 = __shallow_v52} = __ds_var_1 in __shallow_v52
        in if (a < b) then a else b

in_range_u32 :: R32 Word32 Word32 Word32 -> Bool
in_range_u32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        needle = let R32{p1 = __shallow_v53, p2 = __shallow_v54, p3 = __shallow_v55} = __ds_var_0 in __shallow_v53
      in
      let __ds_var_2 = __ds_var_1
          from = let R32{p1 = __shallow_v56, p2 = __shallow_v57, p3 = __shallow_v58} = __ds_var_1 in __shallow_v57
        in
        let __ds_var_3 = __ds_var_2
            to = let R32{p1 = __shallow_v59, p2 = __shallow_v60, p3 = __shallow_v61} = __ds_var_2 in __shallow_v61
          in if ((needle >= from) && (needle < to)) then True else False

cogent_low_16_bits :: Word32 -> Word16
cogent_low_16_bits __ds_var_0 = let x = __ds_var_0 in u32_to_u16 (x .&. (fromIntegral (65535 :: Word16) :: Word32))

cogent_high_16_bits :: Word32 -> Word16
cogent_high_16_bits __ds_var_0 = let x = __ds_var_0 in u32_to_u16 ((x .&. (4294901760 :: Word32)) `shiftR` fromIntegral (u8_to_u32 (16 :: Word8)))

align64 :: R31 Word64 Word64 -> Word64
align64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        x = let R31{p1 = __shallow_v62, p2 = __shallow_v63} = __ds_var_0 in __shallow_v62
      in
      let __ds_var_2 = __ds_var_1
          powof2 = let R31{p1 = __shallow_v64, p2 = __shallow_v65} = __ds_var_1 in __shallow_v65
        in ((x + (powof2 - (fromIntegral (1 :: Word8) :: Word64))) .&. complement (powof2 - (fromIntegral (1 :: Word8) :: Word64)))

align32 :: R31 Word32 Word32 -> Word32
align32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        x = let R31{p1 = __shallow_v66, p2 = __shallow_v67} = __ds_var_0 in __shallow_v66
      in
      let __ds_var_2 = __ds_var_1
          powof2 = let R31{p1 = __shallow_v68, p2 = __shallow_v69} = __ds_var_1 in __shallow_v69
        in ((x + (powof2 - (fromIntegral (1 :: Word8) :: Word32))) .&. complement (powof2 - (fromIntegral (1 :: Word8) :: Word32)))

wordarray_free' :: R15 SysState (WordArray a) -> SysState
wordarray_free' __ds_var_0
  = let __ds_var_2 = __ds_var_0
        ex = let R15{ex = __shallow_v70, obj = __shallow_v71} = __ds_var_0 in __shallow_v70
      in
      let __ds_var_1 = __ds_var_2
          obj = let R15{ex = __shallow_v72, obj = __shallow_v73} = __ds_var_2 in __shallow_v73
        in wordarray_free R31{p1 = ex, p2 = obj}

safe_add32 :: R31 Word32 Word32 -> V41 () Word32
safe_add32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R31{p1 = __shallow_v74, p2 = __shallow_v75} = __ds_var_0 in __shallow_v74
      in
      let __ds_var_2 = __ds_var_1
          b = let R31{p1 = __shallow_v76, p2 = __shallow_v77} = __ds_var_1 in __shallow_v77
        in let r = (a + b) in if ((r < a) || (r < b)) then Error () else Success r

safe_add64 :: R31 Word64 Word64 -> V41 () Word64
safe_add64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R31{p1 = __shallow_v78, p2 = __shallow_v79} = __ds_var_0 in __shallow_v78
      in
      let __ds_var_2 = __ds_var_1
          b = let R31{p1 = __shallow_v80, p2 = __shallow_v81} = __ds_var_1 in __shallow_v81
        in let r = (a + b) in if ((r < a) || (r < b)) then Error () else Success r

safe_sub32 :: R31 Word32 Word32 -> V41 () Word32
safe_sub32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R31{p1 = __shallow_v82, p2 = __shallow_v83} = __ds_var_0 in __shallow_v82
      in
      let __ds_var_2 = __ds_var_1
          b = let R31{p1 = __shallow_v84, p2 = __shallow_v85} = __ds_var_1 in __shallow_v85
        in let r = (a - b) in if (r > a) then Error () else Success r

safe_sub64 :: R31 Word64 Word64 -> V41 () Word64
safe_sub64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R31{p1 = __shallow_v86, p2 = __shallow_v87} = __ds_var_0 in __shallow_v86
      in
      let __ds_var_2 = __ds_var_1
          b = let R31{p1 = __shallow_v88, p2 = __shallow_v89} = __ds_var_1 in __shallow_v89
        in let r = (a - b) in if (r > a) then Error () else Success r

wordarray_clone :: R31 SysState (WordArray a) -> V41 SysState (R31 SysState (WordArray a))
wordarray_clone __ds_var_0
  = let __ds_var_1 = __ds_var_0
        ex = let R31{p1 = __shallow_v90, p2 = __shallow_v91} = __ds_var_0 in __shallow_v90
      in
      let __ds_var_2 = __ds_var_1
          src = let R31{p1 = __shallow_v92, p2 = __shallow_v93} = __ds_var_1 in __shallow_v93
        in
        let size = wordarray_length src in
          let __ds_var_3 = wordarray_create R31{p1 = ex, p2 = size} in
            case __ds_var_3 of
              Error ex94 -> Error ex94
              __ds_var_4 -> let __ds_var_5 = (\ (Success __shallow_v95) -> __shallow_v95) __ds_var_4 in
                              let __ds_var_6 = __ds_var_5
                                  ex96 = let R31{p1 = __shallow_v97, p2 = __shallow_v98} = __ds_var_5 in __shallow_v97
                                in
                                let __ds_var_7 = __ds_var_6
                                    dest = let R31{p1 = __shallow_v99, p2 = __shallow_v100} = __ds_var_6 in __shallow_v100
                                  in Success R31{p1 = ex96, p2 = wordarray_copy R34{p1 = dest, p2 = src, p3 = fromIntegral (0 :: Word8) :: Word32, p4 = fromIntegral (0 :: Word8) :: Word32, p5 = size}}

wordarray_get_bounded :: R31 (WordArray a) Word32 -> V41 () a
wordarray_get_bounded __ds_var_0
  = let __ds_var_1 = __ds_var_0
        arr = let R31{p1 = __shallow_v101, p2 = __shallow_v102} = __ds_var_0 in __shallow_v101
      in
      let __ds_var_2 = __ds_var_1
          idx = let R31{p1 = __shallow_v103, p2 = __shallow_v104} = __ds_var_1 in __shallow_v104
        in if (idx < wordarray_length arr) then Success (wordarray_get R31{p1 = arr, p2 = idx}) else Error ()

freeOptRbtNode :: R31 SysState (V43 () (RbtNode k v)) -> SysState
freeOptRbtNode __ds_var_0
  = let __ds_var_1 = __ds_var_0
        ex = let R31{p1 = __shallow_v105, p2 = __shallow_v106} = __ds_var_0 in __shallow_v105
      in
      let __ds_var_2 = __ds_var_1
          optnode = let R31{p1 = __shallow_v107, p2 = __shallow_v108} = __ds_var_1 in __shallow_v108
        in
        case optnode of
          None __ds_var_3 -> let __ds_var_5 = __ds_var_3 in ex
          __ds_var_4 -> let node = (\ (Some __shallow_v109) -> __shallow_v109) __ds_var_4 in freeRbtNode R31{p1 = ex, p2 = node}

rbtFTrue :: R13 (RbtNode k v) acc obsv -> Bool
rbtFTrue __ds_var_0 = let __ds_var_1 = __ds_var_0 in True

copy_n :: R13 a Word32 (WordArray a) -> R31 a Word32
copy_n __ds_var_0
  = let __ds_var_2 = __ds_var_0
        elem = let R13{elem = __shallow_v110, acc = __shallow_v111, obsv = __shallow_v112} = __ds_var_0 in __shallow_v110
      in
      let __ds_var_3 = __ds_var_2
          idx = let R13{elem = __shallow_v113, acc = __shallow_v114, obsv = __shallow_v115} = __ds_var_2 in __shallow_v114
        in
        let __ds_var_1 = __ds_var_3
            afrm = let R13{elem = __shallow_v116, acc = __shallow_v117, obsv = __shallow_v118} = __ds_var_3 in __shallow_v118
          in R31{p1 = wordarray_get R31{p1 = afrm, p2 = idx}, p2 = (idx + (fromIntegral (1 :: Word8) :: Word32))}

fsm_init ::
         R32 SysState
           (R11 Word32 Word32 (R26 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word64)
              (R25 Word32 Word32 Word64 Word32 Word32 Word8 Word8
                 (V44 (R21 Word64 (WordArray Word8)) (R19 Word64) (R20 Word64 Word32 (Array (R24 Word32 Word8 Word16 (WordArray Word8)))) (R22 Word64 Word64 Word64 Word64 Word64 Word32 Word32 Word32 Word32 Word32) ()
                    (R28 Word32 (WordArray (R23 Word64 Word64 Word32 Word32 Word16)) Word32)
                    (R26 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word64)))
              Word32
              UbiVolInfo
              UbiDevInfo
              Bool)
           (R27 Word32 (WordArray Word8) (WordArray Word32) (Rbt Word64 (R10 Word16 Word64)))
           -> R31 SysState (V41 (R31 Word32 (R27 Word32 (WordArray Word8) (WordArray Word32) (Rbt Word64 (R10 Word16 Word64)))) (R27 Word32 (WordArray Word8) (WordArray Word32) (Rbt Word64 (R10 Word16 Word64))))
fsm_init __ds_var_0
  = let __ds_var_1 = __ds_var_0
        ex = let R32{p1 = __shallow_v119, p2 = __shallow_v120, p3 = __shallow_v121} = __ds_var_0 in __shallow_v119
      in
      let __ds_var_2 = __ds_var_1
          mount_st = let R32{p1 = __shallow_v122, p2 = __shallow_v123, p3 = __shallow_v124} = __ds_var_1 in __shallow_v123
        in
        let __ds_var_3 = __ds_var_2
            fsm_st = let R32{p1 = __shallow_v125, p2 = __shallow_v126, p3 = __shallow_v127} = __ds_var_2 in __shallow_v127
          in
          let nb_eb
                = let R26{nb_eb = __shallow_v136, eb_size = __shallow_v137, io_size = __shallow_v138, nb_reserved_gc = __shallow_v139, nb_reserved_del = __shallow_v140, cur_eb = __shallow_v141, cur_offs = __shallow_v142,
                          last_inum = __shallow_v143, next_sqnum = __shallow_v144}
                        = let R11{eb_recovery = __shallow_v128, eb_recovery_offs = __shallow_v129, super = __shallow_v130, obj_sup = __shallow_v131, super_offs = __shallow_v132, vol = __shallow_v133,
                                  dev = __shallow_v134, no_summary = __shallow_v135}
                                = mount_st
                            in __shallow_v130
                    in __shallow_v136
            in
            let __ds_var_4 = wordarray_create R31{p1 = ex, p2 = nb_eb} in
              case __ds_var_4 of
                Error ex145 -> R31{p1 = ex145, p2 = Error R31{p1 = fromIntegral (12 :: Word8) :: Word32, p2 = fsm_st}}
                __ds_var_5 -> let __ds_var_6 = (\ (Success __shallow_v146) -> __shallow_v146) __ds_var_5 in
                                let __ds_var_7 = __ds_var_6
                                    ex147 = let R31{p1 = __shallow_v148, p2 = __shallow_v149} = __ds_var_6 in __shallow_v148
                                  in
                                  let __ds_var_8 = __ds_var_7
                                      used_eb = let R31{p1 = __shallow_v150, p2 = __shallow_v151} = __ds_var_7 in __shallow_v151
                                    in
                                    let __ds_var_9 = wordarray_create R31{p1 = ex147, p2 = nb_eb} in
                                      case __ds_var_9 of
                                        Error ex152 -> let ex153 = wordarray_free R31{p1 = ex152, p2 = used_eb} in R31{p1 = ex153, p2 = Error R31{p1 = fromIntegral (12 :: Word8) :: Word32, p2 = fsm_st}}
                                        __ds_var_10 -> let __ds_var_11 = (\ (Success __shallow_v154) -> __shallow_v154) __ds_var_10 in
                                                         let __ds_var_12 = __ds_var_11
                                                             ex155 = let R31{p1 = __shallow_v156, p2 = __shallow_v157} = __ds_var_11 in __shallow_v156
                                                           in
                                                           let __ds_var_13 = __ds_var_12
                                                               dirty_space = let R31{p1 = __shallow_v158, p2 = __shallow_v159} = __ds_var_12 in __shallow_v159
                                                             in
                                                             let __ds_var_14 = rbt_create ex155 in
                                                               case __ds_var_14 of
                                                                 Error ex160 -> let ex161 = wordarray_free R31{p1 = ex160, p2 = used_eb} in
                                                                                  let ex162 = wordarray_free R31{p1 = ex161, p2 = dirty_space} in
                                                                                    R31{p1 = ex162, p2 = Error R31{p1 = fromIntegral (12 :: Word8) :: Word32, p2 = fsm_st}}
                                                                 __ds_var_15 -> let __ds_var_16 = (\ (Success __shallow_v163) -> __shallow_v163) __ds_var_15 in
                                                                                  let __ds_var_17 = __ds_var_16
                                                                                      ex164 = let R31{p1 = __shallow_v165, p2 = __shallow_v166} = __ds_var_16 in __shallow_v165
                                                                                    in
                                                                                    let __ds_var_18 = __ds_var_17
                                                                                        gim = let R31{p1 = __shallow_v167, p2 = __shallow_v168} = __ds_var_17 in __shallow_v168
                                                                                      in
                                                                                      let nb_free_eb
                                                                                            = (let R26{nb_eb = __shallow_v177, eb_size = __shallow_v178, io_size = __shallow_v179, nb_reserved_gc = __shallow_v180,
                                                                                                       nb_reserved_del = __shallow_v181, cur_eb = __shallow_v182, cur_offs = __shallow_v183, last_inum = __shallow_v184,
                                                                                                       next_sqnum = __shallow_v185}
                                                                                                     = let R11{eb_recovery = __shallow_v169, eb_recovery_offs = __shallow_v170, super = __shallow_v171,
                                                                                                               obj_sup = __shallow_v172, super_offs = __shallow_v173, vol = __shallow_v174, dev = __shallow_v175,
                                                                                                               no_summary = __shallow_v176}
                                                                                                             = mount_st
                                                                                                         in __shallow_v171
                                                                                                 in __shallow_v177
                                                                                                 - (fromIntegral (2 :: Word8) :: Word32))
                                                                                        in
                                                                                        R31{p1 = ex164,
                                                                                            p2 =
                                                                                              Success
                                                                                                ((((fsm_st :: R27 Word32 (WordArray Word8) (WordArray Word32) (Rbt Word64 (R10 Word16 Word64))){used_eb = used_eb} ::
                                                                                                     R27 Word32 (WordArray Word8) (WordArray Word32) (Rbt Word64 (R10 Word16 Word64))){dirty_space = dirty_space}
                                                                                                    :: R27 Word32 (WordArray Word8) (WordArray Word32) (Rbt Word64 (R10 Word16 Word64))){gim = gim}
                                                                                                   :: R27 Word32 (WordArray Word8) (WordArray Word32) (Rbt Word64 (R10 Word16 Word64))){nb_free_eb = nb_free_eb}}

data R0 t1 t2 t3 = R0{acc :: t1, obsv :: t2, idx :: t3}

data R1 t1 t2 = R1{arr :: t1, acc :: t2}

data R2 t1 t2 t3 t4 = R2{arr :: t1, f :: t2, acc :: t3, obsv :: t4}

data R3 t1 t2 t3 = R3{arr :: t1, f :: t2, ex :: t3}

data R4 t1 t2 t3 t4 t5 t6 = R4{arr :: t1, frm :: t2, to :: t3, f :: t4, acc :: t5, obsv :: t6}

data R5 t1 t2 t3 t4 t5 = R5{arr :: t1, idx :: t2, elem :: t3, f :: t4, ex :: t5}

data R6 t1 t2 t3 t4 = R6{arr :: t1, idx :: t2, f :: t3, acc :: t4}

data R7 t1 t2 t3 t4 t5 = R7{arr :: t1, idx :: t2, f :: t3, acc :: t4, obsv :: t5}

data R8 t1 t2 t3 = R8{arr :: t1, idx :: t2, val :: t3}

data R9 t1 t2 = R9{arr :: t1, rbrk :: t2}

data R10 t1 t2 = R10{count :: t1, sqnum :: t2}

data R11 t1 t2 t3 t4 t5 t6 t7 t8 = R11{eb_recovery :: t1, eb_recovery_offs :: t2, super :: t3, obj_sup :: t4, super_offs :: t5, vol :: t6, dev :: t7, no_summary :: t8} deriving (Eq, Ord, Show)

data R12 t1 t2 = R12{elem :: t1, acc :: t2}

data R13 t1 t2 t3 = R13{elem :: t1, acc :: t2, obsv :: t3}

data R14 t1 t2 = R14{elem :: t1, rbrk :: t2}

data R15 t1 t2 = R15{ex :: t1, obj :: t2}

data R16 t1 t2 t3 t4 t5 = R16{frm :: t1, to :: t2, step :: t3, f :: t4, acc :: t5}

data R17 t1 t2 t3 t4 t5 t6 = R17{frm :: t1, to :: t2, step :: t3, f :: t4, acc :: t5, obsv :: t6}

data R18 t1 t2 t3 t4 t5 t6 = R18{frm :: t1, to :: t2, stepf :: t3, f :: t4, acc :: t5, obsv :: t6}

data R19 t1 = R19{id :: t1} deriving (Show)

data R20 t1 t2 t3 = R20{id :: t1, nb_dentry :: t2, entries :: t3} deriving (Show)

data R21 t1 t2 = R21{id :: t1, odata :: t2} deriving (Show)

data R22 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 = R22{id :: t1, size :: t2, atime_sec :: t3, ctime_sec :: t4, mtime_sec :: t5, nlink :: t6, uid :: t7, gid :: t8, mode :: t9, flags :: t10} deriving (Show)

data R23 t1 t2 t3 t4 t5 = R23{id :: t1, sqnum :: t2, len :: t3, del_flags_and_offs :: t4, count :: t5} deriving (Show)

data R24 t1 t2 t3 t4 = R24{ino :: t1, dtype :: t2, nlen :: t3, name :: t4} deriving (Show)

data R25 t1 t2 t3 t4 t5 t6 t7 t8 = R25{magic :: t1, crc :: t2, sqnum :: t3, offs :: t4, len :: t5, trans :: t6, otype :: t7, ounion :: t8} deriving (Show)

data R26 t1 t2 t3 t4 t5 t6 t7 t8 t9 = R26{nb_eb :: t1, eb_size :: t2, io_size :: t3, nb_reserved_gc :: t4, nb_reserved_del :: t5, cur_eb :: t6, cur_offs :: t7, last_inum :: t8, next_sqnum :: t9} deriving (Show)

data R27 t1 t2 t3 t4 = R27{nb_free_eb :: t1, used_eb :: t2, dirty_space :: t3, gim :: t4} deriving (Eq, Ord, Show)

data R28 t1 t2 t3 = R28{nb_sum_entry :: t1, entries :: t2, sum_offs :: t3} deriving (Show)

data R29 t1 t2 = R29{oelem :: t1, acc :: t2}

data R30 t1 t2 t3 = R30{oelem :: t1, acc :: t2, obsv :: t3}

data R31 t1 t2 = R31{p1 :: t1, p2 :: t2}

data R32 t1 t2 t3 = R32{p1 :: t1, p2 :: t2, p3 :: t3}

data R33 t1 t2 t3 t4 = R33{p1 :: t1, p2 :: t2, p3 :: t3, p4 :: t4}

data R34 t1 t2 t3 t4 t5 = R34{p1 :: t1, p2 :: t2, p3 :: t3, p4 :: t4, p5 :: t5}

data R35 t1 t2 t3 t4 t5 t6 t7 = R35{rbt :: t1, frm :: t2, to :: t3, cond :: t4, f :: t5, acc :: t6, obsv :: t7}

data R36 t1 t2 t3 t4 t5 t6 = R36{rbt :: t1, frm :: t2, to :: t3, f :: t4, acc :: t5, obsv :: t6}

data R37 t1 t2 t3 t4 t5 t6 = R37{rbt :: t1, key :: t2, cond :: t3, f :: t4, acc :: t5, obsv :: t6}

data R38 t1 t2 t3 t4 t5 t6 = R38{rbt :: t1, key :: t2, f :: t3, node :: t4, acc :: t5, obsv :: t6}

data R39 t1 t2 t3 = R39{rbt :: t1, optnode :: t2, acc :: t3}

data V40 t1 t2 = Break t1
               | Iterate t2

data V41 t1 t2 = Error t1
               | Success t2

data V42 t1 t2 = Found t1
               | NotFound t2

data V43 t1 t2 = None t1
               | Some t2

data V44 t1 t2 t3 t4 t5 t6 t7 = TObjData t1
                              | TObjDel t2
                              | TObjDentarr t3
                              | TObjInode t4
                              | TObjPad t5
                              | TObjSummary t6
                              | TObjSuper t7
                              deriving (Show)

{-!
deriving instance Arbitrary (R21 t1 t2)
deriving instance Arbitrary (R19 t1)
deriving instance Arbitrary (R24 t1 t2 t3 t4)
deriving instance Arbitrary (R20 t1 t2 t3)
deriving instance Arbitrary (R22 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10)
deriving instance Arbitrary (R23 t1 t2 t3 t4 t5)
deriving instance Arbitrary (R28 t1 t2 t3)
deriving instance Arbitrary (V44 t1 t2 t3 t4 t5 t6 t7)
deriving instance Arbitrary (R25 t1 t2 t3 t4 t5 t6 t7 t8)
deriving instance Arbitrary (R11 t1 t2 t3 t4 t5 t6 t7 t8 t9)
deriving instance Arbitrary (R10 t1 t2)
deriving instance Arbitrary (R27 t1 t2 t3 t4)
!-}

instance Arbitrary ObjSuper where
  arbitrary = R26 <$> frequency [(2, return 0), (8, elements [0..1000])]
                  <*> arbitrary
                  <*> arbitrary
                  <*> arbitrary
                  <*> arbitrary
                  <*> arbitrary
                  <*> arbitrary
                  <*> arbitrary
                  <*> arbitrary


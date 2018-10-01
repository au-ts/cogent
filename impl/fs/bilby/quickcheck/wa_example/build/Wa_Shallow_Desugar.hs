{-
This build info header is now disabled by --fno-gen-header.
--------------------------------------------------------------------------------
We strongly discourage users from generating individual files for Isabelle
proofs, as it will end up with an inconsistent collection of output files (i.e.
Isabelle input files).
-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PartialTypeSignatures #-}
module Wa_Shallow_Desugar where
import Data.Bits ((.&.), (.|.), complement, xor, shiftL, shiftR)
import Data.Word (Word8, Word16, Word32, Word64)
import Prelude (not, div, mod, fromIntegral, undefined, (+), (-), (*), (&&), (||), (>), (>=), (<), (<=), (==), (/=), Char, String, Int, Bool(..))

data R0 t1 t2 = R0{ex :: t1, obj :: t2}

data R1 t1 t2 = R1{arr :: t1, acc :: t2}

data R2 t1 t2 = R2{arr :: t1, rbrk :: t2}

data R3 t1 t2 t3 t4 t5 = R3{arr :: t1, idx :: t2, f :: t3, acc :: t4, obsv :: t5}

data R4 t1 t2 = R4{elem :: t1, acc :: t2}

data R5 t1 t2 t3 t4 t5 t6 = R5{arr :: t1, frm :: t2, to :: t3, f :: t4, acc :: t5, obsv :: t6}

data R6 t1 t2 t3 = R6{elem :: t1, acc :: t2, obsv :: t3}

data R7 t1 t2 = R7{elem :: t1, rbrk :: t2}

data V8 t1 t2 = V8_Found t1
              | V8_NotFound t2

data R9 t1 t2 t3 t4 t5 t6 = R9{frm :: t1, to :: t2, stepf :: t3, f :: t4, acc :: t5, obsv :: t6}

data R10 t1 t2 t3 t4 t5 t6 = R10{frm :: t1, to :: t2, step :: t3, f :: t4, acc :: t5, obsv :: t6}

data V11 t1 t2 = V11_Break t1
               | V11_Iterate t2

data R12 t1 t2 = R12{oelem :: t1, acc :: t2}

data R13 t1 t2 t3 = R13{oelem :: t1, acc :: t2, obsv :: t3}

data V14 t1 t2 = V14_None t1
               | V14_Some t2

data V15 t1 t2 = V15_Error t1
               | V15_Success t2

data R16 t1 t2 t3 t4 t5 = R16{frm :: t1, to :: t2, step :: t3, f :: t4, acc :: t5}

data R17 t1 t2 t3 = R17{acc :: t1, obsv :: t2, idx :: t3}

data R18 t1 t2 = R18{p1 :: t1, p2 :: t2}

data R19 t1 t2 t3 t4 = R19{p1 :: t1, p2 :: t2, p3 :: t3, p4 :: t4}

data R20 t1 t2 t3 = R20{arr :: t1, idx :: t2, val :: t3}

data R21 t1 t2 t3 = R21{p1 :: t1, p2 :: t2, p3 :: t3}

data R22 t1 t2 t3 t4 t5 = R22{p1 :: t1, p2 :: t2, p3 :: t3, p4 :: t4, p5 :: t5}

word64Max :: Word64
word64Max = (18446744073709551615 :: Word64)

word32Max :: Word32
word32Max = (4294967295 :: Word32)

data WordArray a

data View a

data SysState

type WordArrayIndex = Word32

type WordArrayCopyP a = R22 (WordArray a) (WordArray a) Word32 Word32 Word32

type WordArrayFindSubP a = R21 (WordArray a) (WordArray a) Word32

type WordArrayPutP a = R20 (WordArray a) Word32 a

type WordArraySetP a = R19 (WordArray a) Word32 Word32 a

type WordArrayView a = View (WordArray a)

type WordArrayCloneP a b = R18 SysState (WordArray a)

type WordArraySliceP a = R19 SysState (WordArray a) Word32 Word32

type Seq64_bodyParam acc obsv rbrk = R17 acc obsv Word64

type Seq32_stepParam = Word32 -> Word32

type Seq32_simple_bodyParam acc = acc

type Seq32_simple_body acc = acc -> acc

type Seq32_bodyParam acc obsv rbrk = R17 acc obsv Word32

type Seq32SimpleParam acc = R16 Word32 Word32 Word32 (acc -> acc) acc

type Result a e = V15 e a

type ResultWith c a e = R18 c (V15 e a)

type RR c a e = R18 c (V15 e a)

type R a e = V15 e a

type Option a = V14 () a

type OptElemAO a acc obsv = R13 (V14 () a) acc obsv

type OptElemA a acc = R12 (V14 () a) acc

type LoopResult a b = V11 b a

type LRR acc brk = R18 acc (V11 brk ())

type Seq32_body acc obsv rbrk = R17 acc obsv Word32 -> R18 acc (V11 rbrk ())

type Seq32Param acc obsv rbrk = R10 Word32 Word32 Word32 (R17 acc obsv Word32 -> R18 acc (V11 rbrk ())) acc obsv

type Seq32StepFParam acc obsv rbrk = R9 Word32 Word32 (Word32 -> Word32) (R17 acc obsv Word32 -> R18 acc (V11 rbrk ())) acc obsv

type Seq64_body acc obsv rbrk = R17 acc obsv Word64 -> R18 acc (V11 rbrk ())

type Seq64Param acc obsv rbrk = R10 Word64 Word64 Word64 (R17 acc obsv Word64 -> R18 acc (V11 rbrk ())) acc obsv

type WordArrayMapRE a acc rbrk = R18 (R18 (WordArray a) acc) (V11 rbrk ())

type FreeF a = R18 SysState a -> SysState

type FreeAccF a acc obsv = R19 SysState a acc obsv -> R18 SysState acc

type FindResult = V8 Word32 ()

type ErrCode = Word32

type ElemB a rbrk = R7 a rbrk

type ElemAO a acc obsv = R6 a acc obsv

type WordArrayFoldF a acc obsv rbrk = R6 a acc obsv -> V11 rbrk acc

type WordArrayFoldP a acc obsv rbrk = R5 (WordArray a) Word32 Word32 (R6 a acc obsv -> V11 rbrk acc) acc obsv

type WordArrayFoldNoBreakF a acc obsv = R6 a acc obsv -> acc

type WordArrayFoldNoBreakP a acc obsv = R5 (WordArray a) Word32 Word32 (R6 a acc obsv -> acc) acc obsv

type WordArrayMapF a acc obsv rbrk = R6 a acc obsv -> R18 (R18 a acc) (V11 rbrk ())

type WordArrayMapP a acc obsv rbrk = R5 (WordArray a) Word32 Word32 (R6 a acc obsv -> R18 (R18 a acc) (V11 rbrk ())) acc obsv

type WordArrayMapNoBreakF a acc obsv = R6 a acc obsv -> R18 a acc

type WordArrayMapNoBreakP a acc obsv = R5 (WordArray a) Word32 Word32 (R6 a acc obsv -> R18 a acc) acc obsv

type ElemA a acc = R4 a acc

type WordArrayModifyF a acc obsv = R6 a acc obsv -> R4 a acc

type WordArrayModifyP a acc obsv = R3 (WordArray a) Word32 (R6 a acc obsv -> R4 a acc) acc obsv

type CString = WordArray Word8

type ArrB a rbrk = R2 a rbrk

type ArrA a acc = R1 a acc

u64_to_u32 :: Word64 -> Word32
u64_to_u32 = undefined

u64_to_u16 :: Word64 -> Word16
u64_to_u16 = undefined

u32_to_u8 :: Word32 -> Word8
u32_to_u8 = undefined

u32_to_u16 :: Word32 -> Word16
u32_to_u16 = undefined

u16_to_u8 :: Word16 -> Word8
u16_to_u8 = undefined

random_u32 :: () -> Word32
random_u32 = undefined

cogent_warn_u64 :: Word64 -> ()
cogent_warn_u64 = undefined

cogent_warn_u32 :: Word32 -> ()
cogent_warn_u32 = undefined

cogent_warn_u16 :: Word16 -> ()
cogent_warn_u16 = undefined

cogent_warn :: String -> ()
cogent_warn = undefined

cogent_log2 :: Word32 -> Word32
cogent_log2 = undefined

cogent_debug_u64_hex :: Word64 -> ()
cogent_debug_u64_hex = undefined

cogent_debug_u64 :: Word64 -> ()
cogent_debug_u64 = undefined

cogent_debug_u32_oct :: Word32 -> ()
cogent_debug_u32_oct = undefined

cogent_debug_u32_hex :: Word32 -> ()
cogent_debug_u32_hex = undefined

cogent_debug_u32 :: Word32 -> ()
cogent_debug_u32 = undefined

cogent_debug :: String -> ()
cogent_debug = undefined

cogent_assert2 :: R18 String Bool -> ()
cogent_assert2 = undefined

cogent_assert :: Bool -> ()
cogent_assert = undefined

wordarray_cmp :: R18 (WordArray Word8) (WordArray Word8) -> Bool
wordarray_cmp = undefined

wordarray_copy :: R22 (WordArray a) (WordArray a) Word32 Word32 Word32 -> WordArray a
wordarray_copy = undefined

wordarray_fold' :: R19 (WordArray a) (R21 acc obsv a -> acc) acc obsv -> acc
wordarray_fold' = undefined

wordarray_get :: R18 (WordArray a) Word32 -> a
wordarray_get = undefined

wordarray_length :: WordArray a -> Word32
wordarray_length = undefined

wordarray_map' :: R19 (WordArray a) (R21 acc obsv a -> R18 acc a) acc obsv -> R18 (WordArray a) acc
wordarray_map' = undefined

wordarray_put2 :: R20 (WordArray a) Word32 a -> WordArray a
wordarray_put2 = undefined

wordarray_set :: R19 (WordArray a) Word32 Word32 a -> WordArray a
wordarray_set = undefined

wordarray_split :: R18 (WordArray a) Word32 -> R18 (WordArray a) (WordArray a)
wordarray_split = undefined

wordarray_take :: R18 (WordArray a) Word32 -> WordArray a
wordarray_take = undefined

wordarray_u8_as_u32 :: WordArray Word8 -> Word32
wordarray_u8_as_u32 = undefined

wordarray_map_view :: R18 (View (WordArray a)) (a -> a) -> View (WordArray a)
wordarray_map_view = undefined

wordarray_unview :: View (WordArray a) -> WordArray a
wordarray_unview = undefined

wordarray_view :: R19 (WordArray a) Word32 Word32 Word32 -> View (WordArray a)
wordarray_view = undefined

wordarray_free :: R18 SysState (WordArray a) -> SysState
wordarray_free = undefined

seq32_simple :: R16 Word32 Word32 Word32 (acc -> acc) acc -> acc
seq32_simple = undefined

wordarray_clone_rr :: R18 SysState (WordArray a) -> R18 SysState (V15 () (WordArray b))
wordarray_clone_rr = undefined

wordarray_slice :: R19 SysState (WordArray a) Word32 Word32 -> R18 SysState (V15 () (WordArray a))
wordarray_slice = undefined

wordarray_create :: R18 SysState Word32 -> V15 SysState (R18 SysState (WordArray a))
wordarray_create = undefined

wordarray_create_nz :: R18 SysState Word32 -> V15 SysState (R18 SysState (WordArray a))
wordarray_create_nz = undefined

wordarray_put :: R20 (WordArray a) Word32 a -> V15 (WordArray a) (WordArray a)
wordarray_put = undefined

seq32 :: R10 Word32 Word32 Word32 (R17 acc obsv Word32 -> R18 acc (V11 rbrk ())) acc obsv -> R18 acc (V11 rbrk ())
seq32 = undefined

seq32_rev :: R10 Word32 Word32 Word32 (R17 acc obsv Word32 -> R18 acc (V11 rbrk ())) acc obsv -> R18 acc (V11 rbrk ())
seq32_rev = undefined

seq32_stepf :: R9 Word32 Word32 (Word32 -> Word32) (R17 acc obsv Word32 -> R18 acc (V11 rbrk ())) acc obsv -> R18 acc (V11 rbrk ())
seq32_stepf = undefined

seq64 :: R10 Word64 Word64 Word64 (R17 acc obsv Word64 -> R18 acc (V11 rbrk ())) acc obsv -> R18 acc (V11 rbrk ())
seq64 = undefined

wordarray_findsub :: R21 (WordArray a) (WordArray a) Word32 -> V8 Word32 ()
wordarray_findsub = undefined

wordarray_fold :: R5 (WordArray a) Word32 Word32 (R6 a acc obsv -> V11 rbrk acc) acc obsv -> V11 rbrk acc
wordarray_fold = undefined

wordarray_fold_no_break :: R5 (WordArray a) Word32 Word32 (R6 a acc obsv -> acc) acc obsv -> acc
wordarray_fold_no_break = undefined

wordarray_map :: R5 (WordArray a) Word32 Word32 (R6 a acc obsv -> R18 (R18 a acc) (V11 rbrk ())) acc obsv -> R18 (R18 (WordArray a) acc) (V11 rbrk ())
wordarray_map = undefined

wordarray_map_no_break :: R5 (WordArray a) Word32 Word32 (R6 a acc obsv -> R18 a acc) acc obsv -> R18 (WordArray a) acc
wordarray_map_no_break = undefined

wordarray_print :: WordArray Word8 -> ()
wordarray_print = undefined

wordarray_modify :: R3 (WordArray a) Word32 (R6 a acc obsv -> R4 a acc) acc obsv -> R1 (WordArray a) acc
wordarray_modify = undefined

snd :: R18 a b -> b
snd __ds_var_0
  = let __ds_var_2 = __ds_var_0
        __ds_var_1 = let R18{p1 = __shallow_v23, p2 = __shallow_v24} = __ds_var_0 in __shallow_v23
      in
      let __ds_var_3 = __ds_var_2
          b = let R18{p1 = __shallow_v25, p2 = __shallow_v26} = __ds_var_2 in __shallow_v26
        in let __ds_var_4 = __ds_var_1 in b

second :: R18 (b -> b') (R18 a b) -> R18 a b'
second __ds_var_0
  = let __ds_var_2 = __ds_var_0
        f = let R18{p1 = __shallow_v27, p2 = __shallow_v28} = __ds_var_0 in __shallow_v27
      in
      let __ds_var_3 = __ds_var_2
          __ds_var_1 = let R18{p1 = __shallow_v29, p2 = __shallow_v30} = __ds_var_2 in __shallow_v30
        in
        let __ds_var_4 = __ds_var_1
            a = let R18{p1 = __shallow_v31, p2 = __shallow_v32} = __ds_var_1 in __shallow_v31
          in
          let __ds_var_5 = __ds_var_4
              b = let R18{p1 = __shallow_v33, p2 = __shallow_v34} = __ds_var_4 in __shallow_v34
            in R18{p1 = a, p2 = f b}

min_u64 :: R18 Word64 Word64 -> Word64
min_u64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R18{p1 = __shallow_v35, p2 = __shallow_v36} = __ds_var_0 in __shallow_v35
      in
      let __ds_var_2 = __ds_var_1
          b = let R18{p1 = __shallow_v37, p2 = __shallow_v38} = __ds_var_1 in __shallow_v38
        in if (a < b) then a else b

min_u32 :: R18 Word32 Word32 -> Word32
min_u32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R18{p1 = __shallow_v39, p2 = __shallow_v40} = __ds_var_0 in __shallow_v39
      in
      let __ds_var_2 = __ds_var_1
          b = let R18{p1 = __shallow_v41, p2 = __shallow_v42} = __ds_var_1 in __shallow_v42
        in if (a < b) then a else b

in_range_u32 :: R21 Word32 Word32 Word32 -> Bool
in_range_u32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        needle = let R21{p1 = __shallow_v43, p2 = __shallow_v44, p3 = __shallow_v45} = __ds_var_0 in __shallow_v43
      in
      let __ds_var_2 = __ds_var_1
          from = let R21{p1 = __shallow_v46, p2 = __shallow_v47, p3 = __shallow_v48} = __ds_var_1 in __shallow_v47
        in
        let __ds_var_3 = __ds_var_2
            to = let R21{p1 = __shallow_v49, p2 = __shallow_v50, p3 = __shallow_v51} = __ds_var_2 in __shallow_v51
          in if ((needle >= from) && (needle < to)) then True else False

fst :: R18 a b -> a
fst __ds_var_0
  = let __ds_var_2 = __ds_var_0
        a = let R18{p1 = __shallow_v52, p2 = __shallow_v53} = __ds_var_0 in __shallow_v52
      in
      let __ds_var_3 = __ds_var_2
          __ds_var_1 = let R18{p1 = __shallow_v54, p2 = __shallow_v55} = __ds_var_2 in __shallow_v55
        in let __ds_var_4 = __ds_var_1 in a

first :: R18 (a -> a') (R18 a b) -> R18 a' b
first __ds_var_0
  = let __ds_var_2 = __ds_var_0
        f = let R18{p1 = __shallow_v56, p2 = __shallow_v57} = __ds_var_0 in __shallow_v56
      in
      let __ds_var_3 = __ds_var_2
          __ds_var_1 = let R18{p1 = __shallow_v58, p2 = __shallow_v59} = __ds_var_2 in __shallow_v59
        in
        let __ds_var_4 = __ds_var_1
            a = let R18{p1 = __shallow_v60, p2 = __shallow_v61} = __ds_var_1 in __shallow_v60
          in
          let __ds_var_5 = __ds_var_4
              b = let R18{p1 = __shallow_v62, p2 = __shallow_v63} = __ds_var_4 in __shallow_v63
            in R18{p1 = f a, p2 = b}

cogent_low_16_bits :: Word32 -> Word16
cogent_low_16_bits __ds_var_0 = let x = __ds_var_0 in u32_to_u16 (x .&. (65535 :: Word32))

cogent_high_16_bits :: Word32 -> Word16
cogent_high_16_bits __ds_var_0 = let x = __ds_var_0 in u32_to_u16 ((x .&. (4294901760 :: Word32)) `shiftR` fromIntegral (16 :: Word32))

cogent_debug_u8 :: Word8 -> ()
cogent_debug_u8 __ds_var_0 = let x = __ds_var_0 in cogent_debug_u32 (fromIntegral x :: Word32)

cogent_debug_u16 :: Word16 -> ()
cogent_debug_u16 __ds_var_0 = let x = __ds_var_0 in cogent_debug_u32 (fromIntegral x :: Word32)

cogent_debug_bool :: Bool -> ()
cogent_debug_bool __ds_var_0 = let bool = __ds_var_0 in if bool then cogent_debug "true" else cogent_debug "false"

align64 :: R18 Word64 Word64 -> Word64
align64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        x = let R18{p1 = __shallow_v64, p2 = __shallow_v65} = __ds_var_0 in __shallow_v64
      in
      let __ds_var_2 = __ds_var_1
          powof2 = let R18{p1 = __shallow_v66, p2 = __shallow_v67} = __ds_var_1 in __shallow_v67
        in ((x + (powof2 - (1 :: Word64))) .&. complement (powof2 - (1 :: Word64)))

align32 :: R18 Word32 Word32 -> Word32
align32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        x = let R18{p1 = __shallow_v68, p2 = __shallow_v69} = __ds_var_0 in __shallow_v68
      in
      let __ds_var_2 = __ds_var_1
          powof2 = let R18{p1 = __shallow_v70, p2 = __shallow_v71} = __ds_var_1 in __shallow_v71
        in ((x + (powof2 - (1 :: Word32))) .&. complement (powof2 - (1 :: Word32)))

wordarray_length_u8 :: WordArray Word8 -> Word32
wordarray_length_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_length arg

wordarray_free' :: R0 SysState (WordArray a) -> SysState
wordarray_free' __ds_var_0
  = let __ds_var_2 = __ds_var_0
        ex = let R0{ex = __shallow_v72, obj = __shallow_v73} = __ds_var_0 in __shallow_v72
      in
      let __ds_var_1 = __ds_var_2
          obj = let R0{ex = __shallow_v74, obj = __shallow_v75} = __ds_var_2 in __shallow_v75
        in wordarray_free R18{p1 = ex, p2 = obj}

wordarray_free_u8 :: R18 SysState (WordArray Word8) -> SysState
wordarray_free_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_free arg

error :: b -> V15 b a
error __ds_var_0 = let b = __ds_var_0 in V15_Error b

safe_add32 :: R18 Word32 Word32 -> V15 () Word32
safe_add32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R18{p1 = __shallow_v76, p2 = __shallow_v77} = __ds_var_0 in __shallow_v76
      in
      let __ds_var_2 = __ds_var_1
          b = let R18{p1 = __shallow_v78, p2 = __shallow_v79} = __ds_var_1 in __shallow_v79
        in let r = (a + b) in if ((r < a) || (r < b)) then V15_Error () else V15_Success r

safe_add64 :: R18 Word64 Word64 -> V15 () Word64
safe_add64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R18{p1 = __shallow_v80, p2 = __shallow_v81} = __ds_var_0 in __shallow_v80
      in
      let __ds_var_2 = __ds_var_1
          b = let R18{p1 = __shallow_v82, p2 = __shallow_v83} = __ds_var_1 in __shallow_v83
        in let r = (a + b) in if ((r < a) || (r < b)) then V15_Error () else V15_Success r

safe_sub32 :: R18 Word32 Word32 -> V15 () Word32
safe_sub32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R18{p1 = __shallow_v84, p2 = __shallow_v85} = __ds_var_0 in __shallow_v84
      in
      let __ds_var_2 = __ds_var_1
          b = let R18{p1 = __shallow_v86, p2 = __shallow_v87} = __ds_var_1 in __shallow_v87
        in let r = (a - b) in if (r > a) then V15_Error () else V15_Success r

safe_sub64 :: R18 Word64 Word64 -> V15 () Word64
safe_sub64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R18{p1 = __shallow_v88, p2 = __shallow_v89} = __ds_var_0 in __shallow_v88
      in
      let __ds_var_2 = __ds_var_1
          b = let R18{p1 = __shallow_v90, p2 = __shallow_v91} = __ds_var_1 in __shallow_v91
        in let r = (a - b) in if (r > a) then V15_Error () else V15_Success r

success :: a -> V15 b a
success __ds_var_0 = let a = __ds_var_0 in V15_Success a

wordarray_clone :: R18 SysState (WordArray a) -> V15 SysState (R18 SysState (WordArray a))
wordarray_clone __ds_var_0
  = let __ds_var_1 = __ds_var_0
        ex = let R18{p1 = __shallow_v92, p2 = __shallow_v93} = __ds_var_0 in __shallow_v92
      in
      let __ds_var_2 = __ds_var_1
          src = let R18{p1 = __shallow_v94, p2 = __shallow_v95} = __ds_var_1 in __shallow_v95
        in
        let size = wordarray_length src in
          let __ds_var_3 = wordarray_create R18{p1 = ex, p2 = size} in
            case __ds_var_3 of
              V15_Error ex96 -> V15_Error ex96
              __ds_var_4 -> let __ds_var_5 = (\ (V15_Success __shallow_v97) -> __shallow_v97) __ds_var_4 in
                              let __ds_var_6 = __ds_var_5
                                  ex98 = let R18{p1 = __shallow_v99, p2 = __shallow_v100} = __ds_var_5 in __shallow_v99
                                in
                                let __ds_var_7 = __ds_var_6
                                    dest = let R18{p1 = __shallow_v101, p2 = __shallow_v102} = __ds_var_6 in __shallow_v102
                                  in V15_Success R18{p1 = ex98, p2 = wordarray_copy R22{p1 = dest, p2 = src, p3 = (0 :: Word32), p4 = (0 :: Word32), p5 = size}}

wordarray_clone_u8 :: R18 SysState (WordArray Word8) -> V15 SysState (R18 SysState (WordArray Word8))
wordarray_clone_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_clone arg

wordarray_create_nz_u8 :: R18 SysState Word32 -> V15 SysState (R18 SysState (WordArray Word8))
wordarray_create_nz_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_create_nz arg

wordarray_create_u8 :: R18 SysState Word32 -> V15 SysState (R18 SysState (WordArray Word8))
wordarray_create_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_create arg

wordarray_get_bounded :: R18 (WordArray a) Word32 -> V15 () a
wordarray_get_bounded __ds_var_0
  = let __ds_var_1 = __ds_var_0
        arr = let R18{p1 = __shallow_v103, p2 = __shallow_v104} = __ds_var_0 in __shallow_v103
      in
      let __ds_var_2 = __ds_var_1
          idx = let R18{p1 = __shallow_v105, p2 = __shallow_v106} = __ds_var_1 in __shallow_v106
        in if (idx < wordarray_length arr) then V15_Success (wordarray_get R18{p1 = arr, p2 = idx}) else V15_Error ()

wordarray_get_bounded_u8 :: R18 (WordArray Word8) Word32 -> V15 () Word8
wordarray_get_bounded_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_get_bounded arg

wordarray_put_u8 :: R20 (WordArray Word8) Word32 Word8 -> V15 (WordArray Word8) (WordArray Word8)
wordarray_put_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_put arg

optionToResult :: V14 () a -> V15 () a
optionToResult __ds_var_0
  = case __ds_var_0 of
      V14_None __ds_var_1 -> let __ds_var_3 = __ds_var_1 in V15_Error ()
      __ds_var_2 -> let a = (\ (V14_Some __shallow_v107) -> __shallow_v107) __ds_var_2 in V15_Success a

resultToOption :: V15 e a -> V14 () a
resultToOption __ds_var_0
  = case __ds_var_0 of
      V15_Error __ds_var_1 -> let __ds_var_3 = __ds_var_1 in V14_None ()
      __ds_var_2 -> let a = (\ (V15_Success __shallow_v108) -> __shallow_v108) __ds_var_2 in V14_Some a

wordarray_map_u8 :: R5 (WordArray Word8) Word32 Word32 (R6 Word8 Word8 Word8 -> R18 (R18 Word8 Word8) (V11 () ())) Word8 Word8 -> R18 (R18 (WordArray Word8) Word8) (V11 () ())
wordarray_map_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_map arg

copy_n :: R6 a Word32 (WordArray a) -> R18 a Word32
copy_n __ds_var_0
  = let __ds_var_2 = __ds_var_0
        elem = let R6{elem = __shallow_v109, acc = __shallow_v110, obsv = __shallow_v111} = __ds_var_0 in __shallow_v109
      in
      let __ds_var_3 = __ds_var_2
          idx = let R6{elem = __shallow_v112, acc = __shallow_v113, obsv = __shallow_v114} = __ds_var_2 in __shallow_v113
        in
        let __ds_var_1 = __ds_var_3
            afrm = let R6{elem = __shallow_v115, acc = __shallow_v116, obsv = __shallow_v117} = __ds_var_3 in __shallow_v117
          in R18{p1 = wordarray_get R18{p1 = afrm, p2 = idx}, p2 = (idx + (1 :: Word32))}

map_body_f :: R6 Word8 Word8 Word8 -> R18 (R18 Word8 Word8) (V11 () ())
map_body_f __ds_var_0
  = let __ds_var_2 = __ds_var_0
        elem = let R6{elem = __shallow_v118, acc = __shallow_v119, obsv = __shallow_v120} = __ds_var_0 in __shallow_v118
      in
      let __ds_var_3 = __ds_var_2
          acc = let R6{elem = __shallow_v121, acc = __shallow_v122, obsv = __shallow_v123} = __ds_var_2 in __shallow_v122
        in
        let __ds_var_1 = __ds_var_3
            obsv = let R6{elem = __shallow_v124, acc = __shallow_v125, obsv = __shallow_v126} = __ds_var_3 in __shallow_v126
          in let acc' = (acc + elem) in if (acc' < obsv) then R18{p1 = R18{p1 = acc', p2 = acc'}, p2 = V11_Iterate ()} else R18{p1 = R18{p1 = elem, p2 = acc}, p2 = V11_Break ()}

modify_body_f :: R6 Word8 Word8 Bool -> R4 Word8 Word8
modify_body_f __ds_var_0
  = let __ds_var_2 = __ds_var_0
        elem = let R6{elem = __shallow_v127, acc = __shallow_v128, obsv = __shallow_v129} = __ds_var_0 in __shallow_v127
      in
      let __ds_var_3 = __ds_var_2
          acc = let R6{elem = __shallow_v130, acc = __shallow_v131, obsv = __shallow_v132} = __ds_var_2 in __shallow_v131
        in
        let __ds_var_1 = __ds_var_3
            obsv = let R6{elem = __shallow_v133, acc = __shallow_v134, obsv = __shallow_v135} = __ds_var_3 in __shallow_v135
          in if obsv then R4{elem = (elem + acc), acc = (elem + acc)} else R4{elem = elem, acc = acc}

wordarray_modify_u8 :: R3 (WordArray Word8) Word32 (R6 Word8 Word8 Bool -> R4 Word8 Word8) Word8 Bool -> R1 (WordArray Word8) Word8
wordarray_modify_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_modify arg

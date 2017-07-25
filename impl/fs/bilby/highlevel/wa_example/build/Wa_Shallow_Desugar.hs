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

word64Max :: Word64
word64Max = (18446744073709551615 :: Word64)

word32Max :: Word32
word32Max = (4294967295 :: Word32)

type WordArray a = [a]

data SysState

type WordArrayIndex = Word32

type WordArrayCopyP a = R18 (WordArray a) (WordArray a) Word32 Word32 Word32

type WordArrayFindSubP a = R16 (WordArray a) (WordArray a) Word32

type WordArrayPutP a = R4 (WordArray a) Word32 a

type WordArraySetP a = R17 (WordArray a) Word32 Word32 a

type WordArrayCloneP a b = R15 SysState (WordArray a)

type WordArraySliceP a = R17 SysState (WordArray a) Word32 Word32

type Seq64_bodyParam acc obsv rbrk = R0 acc obsv Word64

type Seq32_stepParam = Word32 -> Word32

type Seq32_simple_bodyParam acc = acc

type Seq32_simple_body acc = acc -> acc

type Seq32_bodyParam acc obsv rbrk = R0 acc obsv Word32

type Seq32SimpleParam acc = R10 Word32 Word32 Word32 (acc -> acc) acc

type RR c a b = R15 c (V20 b a)

type R a b = V20 b a

type Result a b = V20 b a

type Option a = V22 () a

type OptElemAO a acc obsv = R14 (V22 () a) acc obsv

type OptElemA a acc = R13 (V22 () a) acc

type LoopResult a b = V19 b a

type LRR acc brk = R15 acc (V19 brk ())

type Seq32_body acc obsv rbrk = R0 acc obsv Word32 -> R15 acc (V19 rbrk ())

type Seq32Param acc obsv rbrk = R11 Word32 Word32 Word32 (R0 acc obsv Word32 -> R15 acc (V19 rbrk ())) acc obsv

type Seq32StepFParam acc obsv rbrk = R12 Word32 Word32 (Word32 -> Word32) (R0 acc obsv Word32 -> R15 acc (V19 rbrk ())) acc obsv

type Seq64_body acc obsv rbrk = R0 acc obsv Word64 -> R15 acc (V19 rbrk ())

type Seq64Param acc obsv rbrk = R11 Word64 Word64 Word64 (R0 acc obsv Word64 -> R15 acc (V19 rbrk ())) acc obsv

type WordArrayMapRE a acc rbrk = R15 (R15 (WordArray a) acc) (V19 rbrk ())

type FreeF a = R15 SysState a -> SysState

type FreeAccF a acc obsv = R17 SysState a acc obsv -> R15 SysState acc

type FindResult = V21 Word32 ()

type ErrCode = Word32

type ElemB a rbrk = R8 a rbrk

type ElemAO a acc obsv = R7 a acc obsv

type WordArrayFoldF a acc obsv rbrk = R7 a acc obsv -> V19 rbrk acc

type WordArrayFoldP a acc obsv rbrk = R2 (WordArray a) Word32 Word32 (R7 a acc obsv -> V19 rbrk acc) acc obsv

type WordArrayFoldNoBreakF a acc obsv = R7 a acc obsv -> acc

type WordArrayFoldNoBreakP a acc obsv = R2 (WordArray a) Word32 Word32 (R7 a acc obsv -> acc) acc obsv

type WordArrayMapF a acc obsv rbrk = R7 a acc obsv -> R15 (R15 a acc) (V19 rbrk ())

type WordArrayMapP a acc obsv rbrk = R2 (WordArray a) Word32 Word32 (R7 a acc obsv -> R15 (R15 a acc) (V19 rbrk ())) acc obsv

type WordArrayMapNoBreakF a acc obsv = R7 a acc obsv -> R15 a acc

type WordArrayMapNoBreakP a acc obsv = R2 (WordArray a) Word32 Word32 (R7 a acc obsv -> R15 a acc) acc obsv

type ElemA a acc = R6 a acc

type WordArrayModifyF a acc obsv = R7 a acc obsv -> R6 a acc

type WordArrayModifyP a acc obsv = R3 (WordArray a) Word32 (R7 a acc obsv -> R6 a acc) acc obsv

type CString = WordArray Word8

type ArrB a rbrk = R5 a rbrk

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

wordarray_cmp :: R15 (WordArray Word8) (WordArray Word8) -> Bool
wordarray_cmp = undefined

wordarray_copy :: R18 (WordArray a) (WordArray a) Word32 Word32 Word32 -> WordArray a
wordarray_copy = undefined

wordarray_get :: R15 (WordArray a) Word32 -> a
wordarray_get = undefined

wordarray_length :: WordArray a -> Word32
wordarray_length = undefined

wordarray_put2 :: R4 (WordArray a) Word32 a -> WordArray a
wordarray_put2 = undefined

wordarray_set :: R17 (WordArray a) Word32 Word32 a -> WordArray a
wordarray_set = undefined

wordarray_u8_as_u32 :: WordArray Word8 -> Word32
wordarray_u8_as_u32 = undefined

wordarray_free :: R15 SysState (WordArray a) -> SysState
wordarray_free = undefined

seq32_simple :: R10 Word32 Word32 Word32 (acc -> acc) acc -> acc
seq32_simple = undefined

wordarray_clone_rr :: R15 SysState (WordArray a) -> R15 SysState (V20 () (WordArray b))
wordarray_clone_rr = undefined

wordarray_slice :: R17 SysState (WordArray a) Word32 Word32 -> R15 SysState (V20 () (WordArray a))
wordarray_slice = undefined

wordarray_create :: R15 SysState Word32 -> V20 SysState (R15 SysState (WordArray a))
wordarray_create = undefined

wordarray_create_nz :: R15 SysState Word32 -> V20 SysState (R15 SysState (WordArray a))
wordarray_create_nz = undefined

wordarray_put :: R4 (WordArray a) Word32 a -> V20 (WordArray a) (WordArray a)
wordarray_put = undefined

seq32 :: R11 Word32 Word32 Word32 (R0 acc obsv Word32 -> R15 acc (V19 rbrk ())) acc obsv -> R15 acc (V19 rbrk ())
seq32 = undefined

seq32_rev :: R11 Word32 Word32 Word32 (R0 acc obsv Word32 -> R15 acc (V19 rbrk ())) acc obsv -> R15 acc (V19 rbrk ())
seq32_rev = undefined

seq32_stepf :: R12 Word32 Word32 (Word32 -> Word32) (R0 acc obsv Word32 -> R15 acc (V19 rbrk ())) acc obsv -> R15 acc (V19 rbrk ())
seq32_stepf = undefined

seq64 :: R11 Word64 Word64 Word64 (R0 acc obsv Word64 -> R15 acc (V19 rbrk ())) acc obsv -> R15 acc (V19 rbrk ())
seq64 = undefined

wordarray_findsub :: R16 (WordArray a) (WordArray a) Word32 -> V21 Word32 ()
wordarray_findsub = undefined

wordarray_fold :: R2 (WordArray a) Word32 Word32 (R7 a acc obsv -> V19 rbrk acc) acc obsv -> V19 rbrk acc
wordarray_fold = undefined

wordarray_fold_no_break :: R2 (WordArray a) Word32 Word32 (R7 a acc obsv -> acc) acc obsv -> acc
wordarray_fold_no_break = undefined

wordarray_map :: R2 (WordArray a) Word32 Word32 (R7 a acc obsv -> R15 (R15 a acc) (V19 rbrk ())) acc obsv -> R15 (R15 (WordArray a) acc) (V19 rbrk ())
wordarray_map = undefined

wordarray_map_no_break :: R2 (WordArray a) Word32 Word32 (R7 a acc obsv -> R15 a acc) acc obsv -> R15 (WordArray a) acc
wordarray_map_no_break = undefined

wordarray_print :: WordArray Word8 -> ()
wordarray_print = undefined

wordarray_modify :: R3 (WordArray a) Word32 (R7 a acc obsv -> R6 a acc) acc obsv -> R1 (WordArray a) acc
wordarray_modify = undefined

u16_to_u64 :: Word16 -> Word64
u16_to_u64 __ds_var_0 = let x = __ds_var_0 in u32_to_u64 (u16_to_u32 x)

to_u64 :: Word64 -> Word64
to_u64 __ds_var_0 = let x = __ds_var_0 in x

to_u32 :: Word32 -> Word32
to_u32 __ds_var_0 = let x = __ds_var_0 in x

to_u16 :: Word16 -> Word16
to_u16 __ds_var_0 = let x = __ds_var_0 in x

min_u64 :: R15 Word64 Word64 -> Word64
min_u64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R15{p1 = __shallow_v23, p2 = __shallow_v24} = __ds_var_0 in __shallow_v23
      in
      let __ds_var_2 = __ds_var_1
          b = let R15{p1 = __shallow_v25, p2 = __shallow_v26} = __ds_var_1 in __shallow_v26
        in if (a < b) then a else b

min_u32 :: R15 Word32 Word32 -> Word32
min_u32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R15{p1 = __shallow_v27, p2 = __shallow_v28} = __ds_var_0 in __shallow_v27
      in
      let __ds_var_2 = __ds_var_1
          b = let R15{p1 = __shallow_v29, p2 = __shallow_v30} = __ds_var_1 in __shallow_v30
        in if (a < b) then a else b

in_range_u32 :: R16 Word32 Word32 Word32 -> Bool
in_range_u32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        needle = let R16{p1 = __shallow_v31, p2 = __shallow_v32, p3 = __shallow_v33} = __ds_var_0 in __shallow_v31
      in
      let __ds_var_2 = __ds_var_1
          from = let R16{p1 = __shallow_v34, p2 = __shallow_v35, p3 = __shallow_v36} = __ds_var_1 in __shallow_v35
        in
        let __ds_var_3 = __ds_var_2
            to = let R16{p1 = __shallow_v37, p2 = __shallow_v38, p3 = __shallow_v39} = __ds_var_2 in __shallow_v39
          in if ((needle >= from) && (needle < to)) then True else False

cogent_low_16_bits :: Word32 -> Word16
cogent_low_16_bits __ds_var_0 = let x = __ds_var_0 in u32_to_u16 (x .&. (fromIntegral (65535 :: Word16) :: Word32))

cogent_high_16_bits :: Word32 -> Word16
cogent_high_16_bits __ds_var_0 = let x = __ds_var_0 in u32_to_u16 ((x .&. (4294901760 :: Word32)) `shiftR` fromIntegral (u8_to_u32 (16 :: Word8)))

align64 :: R15 Word64 Word64 -> Word64
align64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        x = let R15{p1 = __shallow_v40, p2 = __shallow_v41} = __ds_var_0 in __shallow_v40
      in
      let __ds_var_2 = __ds_var_1
          powof2 = let R15{p1 = __shallow_v42, p2 = __shallow_v43} = __ds_var_1 in __shallow_v43
        in ((x + (powof2 - (fromIntegral (1 :: Word8) :: Word64))) .&. complement (powof2 - (fromIntegral (1 :: Word8) :: Word64)))

align32 :: R15 Word32 Word32 -> Word32
align32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        x = let R15{p1 = __shallow_v44, p2 = __shallow_v45} = __ds_var_0 in __shallow_v44
      in
      let __ds_var_2 = __ds_var_1
          powof2 = let R15{p1 = __shallow_v46, p2 = __shallow_v47} = __ds_var_1 in __shallow_v47
        in ((x + (powof2 - (fromIntegral (1 :: Word8) :: Word32))) .&. complement (powof2 - (fromIntegral (1 :: Word8) :: Word32)))

wordarray_length_u8 :: WordArray Word8 -> Word32
wordarray_length_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_length arg

wordarray_free' :: R9 SysState (WordArray a) -> SysState
wordarray_free' __ds_var_0
  = let __ds_var_2 = __ds_var_0
        ex = let R9{ex = __shallow_v48, obj = __shallow_v49} = __ds_var_0 in __shallow_v48
      in
      let __ds_var_1 = __ds_var_2
          obj = let R9{ex = __shallow_v50, obj = __shallow_v51} = __ds_var_2 in __shallow_v51
        in wordarray_free R15{p1 = ex, p2 = obj}

wordarray_free_u8 :: R15 SysState (WordArray Word8) -> SysState
wordarray_free_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_free arg

safe_add32 :: R15 Word32 Word32 -> V20 () Word32
safe_add32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R15{p1 = __shallow_v52, p2 = __shallow_v53} = __ds_var_0 in __shallow_v52
      in
      let __ds_var_2 = __ds_var_1
          b = let R15{p1 = __shallow_v54, p2 = __shallow_v55} = __ds_var_1 in __shallow_v55
        in let r = (a + b) in if ((r < a) || (r < b)) then Error () else Success r

safe_add64 :: R15 Word64 Word64 -> V20 () Word64
safe_add64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R15{p1 = __shallow_v56, p2 = __shallow_v57} = __ds_var_0 in __shallow_v56
      in
      let __ds_var_2 = __ds_var_1
          b = let R15{p1 = __shallow_v58, p2 = __shallow_v59} = __ds_var_1 in __shallow_v59
        in let r = (a + b) in if ((r < a) || (r < b)) then Error () else Success r

safe_sub32 :: R15 Word32 Word32 -> V20 () Word32
safe_sub32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R15{p1 = __shallow_v60, p2 = __shallow_v61} = __ds_var_0 in __shallow_v60
      in
      let __ds_var_2 = __ds_var_1
          b = let R15{p1 = __shallow_v62, p2 = __shallow_v63} = __ds_var_1 in __shallow_v63
        in let r = (a - b) in if (r > a) then Error () else Success r

safe_sub64 :: R15 Word64 Word64 -> V20 () Word64
safe_sub64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R15{p1 = __shallow_v64, p2 = __shallow_v65} = __ds_var_0 in __shallow_v64
      in
      let __ds_var_2 = __ds_var_1
          b = let R15{p1 = __shallow_v66, p2 = __shallow_v67} = __ds_var_1 in __shallow_v67
        in let r = (a - b) in if (r > a) then Error () else Success r

wordarray_clone :: R15 SysState (WordArray a) -> V20 SysState (R15 SysState (WordArray a))
wordarray_clone __ds_var_0
  = let __ds_var_1 = __ds_var_0
        ex = let R15{p1 = __shallow_v68, p2 = __shallow_v69} = __ds_var_0 in __shallow_v68
      in
      let __ds_var_2 = __ds_var_1
          src = let R15{p1 = __shallow_v70, p2 = __shallow_v71} = __ds_var_1 in __shallow_v71
        in
        let size = wordarray_length src in
          let __ds_var_3 = wordarray_create R15{p1 = ex, p2 = size} in
            case __ds_var_3 of
              Error ex72 -> Error ex72
              __ds_var_4 -> let __ds_var_5 = (\ (Success __shallow_v73) -> __shallow_v73) __ds_var_4 in
                              let __ds_var_6 = __ds_var_5
                                  ex74 = let R15{p1 = __shallow_v75, p2 = __shallow_v76} = __ds_var_5 in __shallow_v75
                                in
                                let __ds_var_7 = __ds_var_6
                                    dest = let R15{p1 = __shallow_v77, p2 = __shallow_v78} = __ds_var_6 in __shallow_v78
                                  in Success R15{p1 = ex74, p2 = wordarray_copy R18{p1 = dest, p2 = src, p3 = fromIntegral (0 :: Word8) :: Word32, p4 = fromIntegral (0 :: Word8) :: Word32, p5 = size}}

wordarray_clone_u8 :: R15 SysState (WordArray Word8) -> V20 SysState (R15 SysState (WordArray Word8))
wordarray_clone_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_clone arg

wordarray_create_nz_u8 :: SysState -> V20 SysState (R15 SysState (WordArray Word8))
wordarray_create_nz_u8 __ds_var_0 = let ex = __ds_var_0 in wordarray_create_nz R15{p1 = ex, p2 = fromIntegral (1 :: Word8) :: Word32}

wordarray_create_u8 :: SysState -> V20 SysState (R15 SysState (WordArray Word8))
wordarray_create_u8 __ds_var_0 = let ex = __ds_var_0 in wordarray_create R15{p1 = ex, p2 = fromIntegral (1 :: Word8) :: Word32}

wordarray_get_bounded :: R15 (WordArray a) Word32 -> V20 () a
wordarray_get_bounded __ds_var_0
  = let __ds_var_1 = __ds_var_0
        arr = let R15{p1 = __shallow_v79, p2 = __shallow_v80} = __ds_var_0 in __shallow_v79
      in
      let __ds_var_2 = __ds_var_1
          idx = let R15{p1 = __shallow_v81, p2 = __shallow_v82} = __ds_var_1 in __shallow_v82
        in if (idx < wordarray_length arr) then Success (wordarray_get R15{p1 = arr, p2 = idx}) else Error ()

wordarray_get_bounded_u8 :: R15 (WordArray Word8) Word32 -> V20 () Word8
wordarray_get_bounded_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_get_bounded arg

wordarray_put_u8 :: R4 (WordArray Word8) Word32 Word8 -> V20 (WordArray Word8) (WordArray Word8)
wordarray_put_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_put arg

wordarray_map_u8 :: R2 (WordArray Word8) Word32 Word32 (R7 Word8 Word8 Word8 -> R15 (R15 Word8 Word8) (V19 () ())) Word8 Word8 -> R15 (R15 (WordArray Word8) Word8) (V19 () ())
wordarray_map_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_map arg

copy_n :: R7 a Word32 (WordArray a) -> R15 a Word32
copy_n __ds_var_0
  = let __ds_var_2 = __ds_var_0
        elem = let R7{elem = __shallow_v83, acc = __shallow_v84, obsv = __shallow_v85} = __ds_var_0 in __shallow_v83
      in
      let __ds_var_3 = __ds_var_2
          idx = let R7{elem = __shallow_v86, acc = __shallow_v87, obsv = __shallow_v88} = __ds_var_2 in __shallow_v87
        in
        let __ds_var_1 = __ds_var_3
            afrm = let R7{elem = __shallow_v89, acc = __shallow_v90, obsv = __shallow_v91} = __ds_var_3 in __shallow_v91
          in R15{p1 = wordarray_get R15{p1 = afrm, p2 = idx}, p2 = (idx + (fromIntegral (1 :: Word8) :: Word32))}

map_body_f :: R7 Word8 Word8 Word8 -> R15 (R15 Word8 Word8) (V19 () ())
map_body_f __ds_var_0
  = let __ds_var_2 = __ds_var_0
        elem = let R7{elem = __shallow_v92, acc = __shallow_v93, obsv = __shallow_v94} = __ds_var_0 in __shallow_v92
      in
      let __ds_var_3 = __ds_var_2
          acc = let R7{elem = __shallow_v95, acc = __shallow_v96, obsv = __shallow_v97} = __ds_var_2 in __shallow_v96
        in
        let __ds_var_1 = __ds_var_3
            obsv = let R7{elem = __shallow_v98, acc = __shallow_v99, obsv = __shallow_v100} = __ds_var_3 in __shallow_v100
          in let acc' = (acc + elem) in if (acc' < obsv) then R15{p1 = R15{p1 = acc', p2 = acc'}, p2 = Iterate ()} else R15{p1 = R15{p1 = elem, p2 = acc}, p2 = Break ()}

wordarray_modify_u8 :: R3 (WordArray Word8) Word32 (R7 Word8 Word8 Bool -> R6 Word8 Word8) Word8 Bool -> R1 (WordArray Word8) Word8
wordarray_modify_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_modify arg

data R0 t1 t2 t3 = R0{acc :: t1, obsv :: t2, idx :: t3}

data R1 t1 t2 = R1{arr :: t1, acc :: t2}

data R2 t1 t2 t3 t4 t5 t6 = R2{arr :: t1, frm :: t2, to :: t3, f :: t4, acc :: t5, obsv :: t6}

data R3 t1 t2 t3 t4 t5 = R3{arr :: t1, idx :: t2, f :: t3, acc :: t4, obsv :: t5}

data R4 t1 t2 t3 = R4{arr :: t1, idx :: t2, val :: t3}

data R5 t1 t2 = R5{arr :: t1, rbrk :: t2}

data R6 t1 t2 = R6{elem :: t1, acc :: t2}

data R7 t1 t2 t3 = R7{elem :: t1, acc :: t2, obsv :: t3}

data R8 t1 t2 = R8{elem :: t1, rbrk :: t2}

data R9 t1 t2 = R9{ex :: t1, obj :: t2}

data R10 t1 t2 t3 t4 t5 = R10{frm :: t1, to :: t2, step :: t3, f :: t4, acc :: t5}

data R11 t1 t2 t3 t4 t5 t6 = R11{frm :: t1, to :: t2, step :: t3, f :: t4, acc :: t5, obsv :: t6}

data R12 t1 t2 t3 t4 t5 t6 = R12{frm :: t1, to :: t2, stepf :: t3, f :: t4, acc :: t5, obsv :: t6}

data R13 t1 t2 = R13{oelem :: t1, acc :: t2}

data R14 t1 t2 t3 = R14{oelem :: t1, acc :: t2, obsv :: t3}

data R15 t1 t2 = R15{p1 :: t1, p2 :: t2}

data R16 t1 t2 t3 = R16{p1 :: t1, p2 :: t2, p3 :: t3}

data R17 t1 t2 t3 t4 = R17{p1 :: t1, p2 :: t2, p3 :: t3, p4 :: t4}

data R18 t1 t2 t3 t4 t5 = R18{p1 :: t1, p2 :: t2, p3 :: t3, p4 :: t4, p5 :: t5}

data V19 t1 t2 = Break t1
               | Iterate t2

data V20 t1 t2 = Error t1
               | Success t2

data V21 t1 t2 = Found t1
               | NotFound t2

data V22 t1 t2 = None t1
               | Some t2

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
module Search_Shallow_Desugar where
import Data.Bits ((.&.), (.|.), complement, xor, shiftL, shiftR)
import Data.Word (Word8, Word16, Word32, Word64)
import Prelude (not, div, mod, fromIntegral, undefined, (+), (-), (*), (&&), (||), (>), (>=), (<), (<=), (==), (/=), Char, String, Int, Bool(..))

word64Max :: Word64
word64Max = (18446744073709551615 :: Word64)

word32Max :: Word32
word32Max = (4294967295 :: Word32)

type SysState = ()

type CString = [Char]

type Buffer = [Word8]

type WordArrayIndex = Word32

type Seq64_bodyParam acc obsv rbrk = R0 acc obsv Word64

type Seq32_stepParam = Word32 -> Word32

type Seq32_simple_bodyParam acc = acc

type Seq32_simple_body acc = acc -> acc

type Seq32_bodyParam acc obsv rbrk = R0 acc obsv Word32

type Seq32SimpleParam acc = R6 Word32 Word32 Word32 (acc -> acc) acc

type RR c a b = R12 c (V16 b a)

type R a b = V16 b a

type Result a b = V16 b a

type Option a = V17 () a

type OptElemAO a acc obsv = R11 (V17 () a) acc obsv

type OptElemA a acc = R10 (V17 () a) acc

type LoopResult a b = V15 b a

type LRR acc brk = R12 acc (V15 brk ())

type Seq32_body acc obsv rbrk = R0 acc obsv Word32 -> R12 acc (V15 rbrk ())

type Seq32Param acc obsv rbrk = R7 Word32 Word32 Word32 (R0 acc obsv Word32 -> R12 acc (V15 rbrk ())) acc obsv

type Seq32StepFParam acc obsv rbrk = R8 Word32 Word32 (Word32 -> Word32) (R0 acc obsv Word32 -> R12 acc (V15 rbrk ())) acc obsv

type Seq64_body acc obsv rbrk = R0 acc obsv Word64 -> R12 acc (V15 rbrk ())

type Seq64Param acc obsv rbrk = R7 Word64 Word64 Word64 (R0 acc obsv Word64 -> R12 acc (V15 rbrk ())) acc obsv

type Index = Word32

type FreeF a = R12 SysState a -> SysState

type FreeAccF a acc obsv = R14 SysState a acc obsv -> R12 SysState acc

type ErrCode = Word32

type ElemB a rbrk = R5 a rbrk

type ElemAO a acc obsv = R4 a acc obsv

type ElemA a acc = R3 a acc

type Node = R9 Word32 CString

type ArrB a rbrk = R2 a rbrk

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

seq32_simple :: R6 Word32 Word32 Word32 (acc -> acc) acc -> acc
seq32_simple = undefined

seq32 :: R7 Word32 Word32 Word32 (R0 acc obsv Word32 -> R12 acc (V15 rbrk ())) acc obsv -> R12 acc (V15 rbrk ())
seq32 = undefined

seq32_rev :: R7 Word32 Word32 Word32 (R0 acc obsv Word32 -> R12 acc (V15 rbrk ())) acc obsv -> R12 acc (V15 rbrk ())
seq32_rev = undefined

seq32_stepf :: R8 Word32 Word32 (Word32 -> Word32) (R0 acc obsv Word32 -> R12 acc (V15 rbrk ())) acc obsv -> R12 acc (V15 rbrk ())
seq32_stepf = undefined

seq64 :: R7 Word64 Word64 Word64 (R0 acc obsv Word64 -> R12 acc (V15 rbrk ())) acc obsv -> R12 acc (V15 rbrk ())
seq64 = undefined

free_Node :: R12 SysState (R9 Word32 CString) -> SysState
free_Node = undefined

malloc_Node :: SysState -> R12 SysState (V16 Word32 (R9 Word32 CString))
malloc_Node = undefined

array_print :: R12 SysState CString -> SysState
array_print = undefined

free_CString :: R12 SysState CString -> SysState
free_CString = undefined

string_cmp :: R12 CString CString -> Bool
string_cmp = undefined

deserialise_CString :: R14 SysState Buffer Word32 Word32 -> R12 SysState (V16 Word32 (R12 CString Word32))
deserialise_CString = undefined

deserialise_U32 :: R13 SysState Buffer Word32 -> R13 SysState Word32 Word32
deserialise_U32 = undefined

u16_to_u64 :: Word16 -> Word64
u16_to_u64 __ds_var_0 = let x = __ds_var_0 in u32_to_u64 (u16_to_u32 x)

to_u64 :: Word64 -> Word64
to_u64 __ds_var_0 = let x = __ds_var_0 in x

to_u32 :: Word32 -> Word32
to_u32 __ds_var_0 = let x = __ds_var_0 in x

to_u16 :: Word16 -> Word16
to_u16 __ds_var_0 = let x = __ds_var_0 in x

min_u64 :: R12 Word64 Word64 -> Word64
min_u64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R12{p1 = __shallow_v18, p2 = __shallow_v19} = __ds_var_0 in __shallow_v18
      in
      let __ds_var_2 = __ds_var_1
          b = let R12{p1 = __shallow_v20, p2 = __shallow_v21} = __ds_var_1 in __shallow_v21
        in if (a < b) then a else b

min_u32 :: R12 Word32 Word32 -> Word32
min_u32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R12{p1 = __shallow_v22, p2 = __shallow_v23} = __ds_var_0 in __shallow_v22
      in
      let __ds_var_2 = __ds_var_1
          b = let R12{p1 = __shallow_v24, p2 = __shallow_v25} = __ds_var_1 in __shallow_v25
        in if (a < b) then a else b

in_range_u32 :: R13 Word32 Word32 Word32 -> Bool
in_range_u32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        needle = let R13{p1 = __shallow_v26, p2 = __shallow_v27, p3 = __shallow_v28} = __ds_var_0 in __shallow_v26
      in
      let __ds_var_2 = __ds_var_1
          from = let R13{p1 = __shallow_v29, p2 = __shallow_v30, p3 = __shallow_v31} = __ds_var_1 in __shallow_v30
        in
        let __ds_var_3 = __ds_var_2
            to = let R13{p1 = __shallow_v32, p2 = __shallow_v33, p3 = __shallow_v34} = __ds_var_2 in __shallow_v34
          in if ((needle >= from) && (needle < to)) then True else False

cogent_low_16_bits :: Word32 -> Word16
cogent_low_16_bits __ds_var_0 = let x = __ds_var_0 in u32_to_u16 (x .&. (fromIntegral (65535 :: Word16) :: Word32))

cogent_high_16_bits :: Word32 -> Word16
cogent_high_16_bits __ds_var_0 = let x = __ds_var_0 in u32_to_u16 ((x .&. (4294901760 :: Word32)) `shiftR` fromIntegral (u8_to_u32 (16 :: Word8)))

align64 :: R12 Word64 Word64 -> Word64
align64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        x = let R12{p1 = __shallow_v35, p2 = __shallow_v36} = __ds_var_0 in __shallow_v35
      in
      let __ds_var_2 = __ds_var_1
          powof2 = let R12{p1 = __shallow_v37, p2 = __shallow_v38} = __ds_var_1 in __shallow_v38
        in ((x + (powof2 - (fromIntegral (1 :: Word8) :: Word64))) .&. complement (powof2 - (fromIntegral (1 :: Word8) :: Word64)))

align32 :: R12 Word32 Word32 -> Word32
align32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        x = let R12{p1 = __shallow_v39, p2 = __shallow_v40} = __ds_var_0 in __shallow_v39
      in
      let __ds_var_2 = __ds_var_1
          powof2 = let R12{p1 = __shallow_v41, p2 = __shallow_v42} = __ds_var_1 in __shallow_v42
        in ((x + (powof2 - (fromIntegral (1 :: Word8) :: Word32))) .&. complement (powof2 - (fromIntegral (1 :: Word8) :: Word32)))

safe_add32 :: R12 Word32 Word32 -> V16 () Word32
safe_add32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R12{p1 = __shallow_v43, p2 = __shallow_v44} = __ds_var_0 in __shallow_v43
      in
      let __ds_var_2 = __ds_var_1
          b = let R12{p1 = __shallow_v45, p2 = __shallow_v46} = __ds_var_1 in __shallow_v46
        in let r = (a + b) in if ((r < a) || (r < b)) then Error () else Success r

safe_add64 :: R12 Word64 Word64 -> V16 () Word64
safe_add64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R12{p1 = __shallow_v47, p2 = __shallow_v48} = __ds_var_0 in __shallow_v47
      in
      let __ds_var_2 = __ds_var_1
          b = let R12{p1 = __shallow_v49, p2 = __shallow_v50} = __ds_var_1 in __shallow_v50
        in let r = (a + b) in if ((r < a) || (r < b)) then Error () else Success r

safe_sub32 :: R12 Word32 Word32 -> V16 () Word32
safe_sub32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R12{p1 = __shallow_v51, p2 = __shallow_v52} = __ds_var_0 in __shallow_v51
      in
      let __ds_var_2 = __ds_var_1
          b = let R12{p1 = __shallow_v53, p2 = __shallow_v54} = __ds_var_1 in __shallow_v54
        in let r = (a - b) in if (r > a) then Error () else Success r

safe_sub64 :: R12 Word64 Word64 -> V16 () Word64
safe_sub64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R12{p1 = __shallow_v55, p2 = __shallow_v56} = __ds_var_0 in __shallow_v55
      in
      let __ds_var_2 = __ds_var_1
          b = let R12{p1 = __shallow_v57, p2 = __shallow_v58} = __ds_var_1 in __shallow_v58
        in let r = (a - b) in if (r > a) then Error () else Success r

deserialise_Node :: R13 SysState Buffer Word32 -> R12 SysState (V16 Word32 (R12 (R9 Word32 CString) Word32))
deserialise_Node __ds_var_0
  = let __ds_var_1 = __ds_var_0
        ex = let R13{p1 = __shallow_v59, p2 = __shallow_v60, p3 = __shallow_v61} = __ds_var_0 in __shallow_v59
      in
      let __ds_var_2 = __ds_var_1
          buf = let R13{p1 = __shallow_v62, p2 = __shallow_v63, p3 = __shallow_v64} = __ds_var_1 in __shallow_v63
        in
        let __ds_var_3 = __ds_var_2
            idx = let R13{p1 = __shallow_v65, p2 = __shallow_v66, p3 = __shallow_v67} = __ds_var_2 in __shallow_v67
          in
          let __ds_var_4 = malloc_Node ex
              ex68 = let R12{p1 = __shallow_v69, p2 = __shallow_v70} = malloc_Node ex in __shallow_v69
            in
            let __ds_var_5 = __ds_var_4
                r = let R12{p1 = __shallow_v71, p2 = __shallow_v72} = __ds_var_4 in __shallow_v72
              in
              case r of
                Success node ->
                  let __ds_var_7 = deserialise_U32 R13{p1 = ex68, p2 = buf, p3 = idx}
                      ex73 = let R13{p1 = __shallow_v74, p2 = __shallow_v75, p3 = __shallow_v76} = deserialise_U32 R13{p1 = ex68, p2 = buf, p3 = idx} in __shallow_v74
                    in
                    let __ds_var_8 = __ds_var_7
                        l = let R13{p1 = __shallow_v77, p2 = __shallow_v78, p3 = __shallow_v79} = __ds_var_7 in __shallow_v78
                      in
                      let __ds_var_9 = __ds_var_8
                          idx' = let R13{p1 = __shallow_v80, p2 = __shallow_v81, p3 = __shallow_v82} = __ds_var_8 in __shallow_v82
                        in
                        let __ds_var_10 = deserialise_CString R14{p1 = ex73, p2 = buf, p3 = idx', p4 = l} in
                          let __ds_var_11 = __ds_var_10
                              ex83 = let R12{p1 = __shallow_v84, p2 = __shallow_v85} = __ds_var_10 in __shallow_v84
                            in
                            let __ds_var_12 = __ds_var_11
                                r86 = let R12{p1 = __shallow_v87, p2 = __shallow_v88} = __ds_var_11 in __shallow_v88
                              in
                              case r86 of
                                Success __ds_var_13 ->
                                  let __ds_var_15 = __ds_var_13
                                      key = let R12{p1 = __shallow_v89, p2 = __shallow_v90} = __ds_var_13 in __shallow_v89
                                    in
                                    let __ds_var_16 = __ds_var_15
                                        idx'' = let R12{p1 = __shallow_v91, p2 = __shallow_v92} = __ds_var_15 in __shallow_v92
                                      in R12{p1 = ex83, p2 = Success R12{p1 = ((node :: R9 Word32 CString){len = l} :: R9 Word32 CString){key = key}, p2 = idx''}}
                                __ds_var_14 ->
                                  let err = (\ (Error __shallow_v93) -> __shallow_v93) __ds_var_14 in let ex94 = free_Node R12{p1 = ex83, p2 = node} in R12{p1 = ex94, p2 = Error err}
                __ds_var_6 ->
                  let err = (\ (Error __shallow_v95) -> __shallow_v95) __ds_var_6 in R12{p1 = ex68, p2 = Error err}

cmp_inc :: R0 (R12 SysState Word32) (R12 Buffer CString) Word32 -> R12 (R12 SysState Word32) (V15 (R9 Word32 CString) ())
cmp_inc __ds_var_0
  = let __ds_var_1 = __ds_var_0
        __ds_var_2 = let R0{acc = __shallow_v96, obsv = __shallow_v97, idx = __shallow_v98} = __ds_var_0 in __shallow_v96
      in
      let __ds_var_3 = __ds_var_2
          ex = let R12{p1 = __shallow_v99, p2 = __shallow_v100} = __ds_var_2 in __shallow_v99
        in
        let __ds_var_4 = __ds_var_3
            idx = let R12{p1 = __shallow_v101, p2 = __shallow_v102} = __ds_var_3 in __shallow_v102
          in
          let r = __ds_var_1
              __ds_var_5 = let R0{acc = __shallow_v103, obsv = __shallow_v104, idx = __shallow_v105} = __ds_var_1 in __shallow_v104
            in
            let __ds_var_6 = __ds_var_5
                buf = let R12{p1 = __shallow_v106, p2 = __shallow_v107} = __ds_var_5 in __shallow_v106
              in
              let __ds_var_7 = __ds_var_6
                  str = let R12{p1 = __shallow_v108, p2 = __shallow_v109} = __ds_var_6 in __shallow_v109
                in
                let __ds_var_8 = deserialise_Node R13{p1 = ex, p2 = buf, p3 = idx}
                    ex110 = let R12{p1 = __shallow_v111, p2 = __shallow_v112} = deserialise_Node R13{p1 = ex, p2 = buf, p3 = idx} in __shallow_v111
                  in
                  let __ds_var_9 = __ds_var_8
                      r113 = let R12{p1 = __shallow_v114, p2 = __shallow_v115} = __ds_var_8 in __shallow_v115
                    in
                    case r113 of
                      Success __ds_var_10 ->
                        let __ds_var_12 = __ds_var_10
                            node = let R12{p1 = __shallow_v116, p2 = __shallow_v117} = __ds_var_10 in __shallow_v116
                          in
                          let __ds_var_13 = __ds_var_12
                              idx' = let R12{p1 = __shallow_v118, p2 = __shallow_v119} = __ds_var_12 in __shallow_v119
                            in
                            let __ds_var_14 = string_cmp R12{p1 = let R9{len = __shallow_v120, key = __shallow_v121} = node in __shallow_v121, p2 = str} in
                              if __ds_var_14 then R12{p1 = R12{p1 = ex110, p2 = idx'}, p2 = Break node} else
                                let __ds_var_15 = node
                                    len = let R9{len = __shallow_v122, key = __shallow_v123} = node in __shallow_v122
                                  in
                                  let node124 = __ds_var_15
                                      key = let R9{len = __shallow_v125, key = __shallow_v126} = __ds_var_15 in __shallow_v126
                                    in let ex127 = free_Node R12{p1 = ex110, p2 = node124} in R12{p1 = R12{p1 = ex127, p2 = idx'}, p2 = Iterate ()}
                      __ds_var_11 ->
                        let err = (\ (Error __shallow_v128) -> __shallow_v128) __ds_var_11 in R12{p1 = R12{p1 = ex110, p2 = idx}, p2 = Iterate ()}

find_str :: R13 SysState Buffer CString -> R12 SysState (V17 () (R9 Word32 CString))
find_str __ds_var_0
  = let __ds_var_1 = __ds_var_0
        ex = let R13{p1 = __shallow_v129, p2 = __shallow_v130, p3 = __shallow_v131} = __ds_var_0 in __shallow_v129
      in
      let __ds_var_2 = __ds_var_1
          buf = let R13{p1 = __shallow_v132, p2 = __shallow_v133, p3 = __shallow_v134} = __ds_var_1 in __shallow_v133
        in
        let __ds_var_3 = __ds_var_2
            s = let R13{p1 = __shallow_v135, p2 = __shallow_v136, p3 = __shallow_v137} = __ds_var_2 in __shallow_v137
          in
          let __ds_var_5
                = seq32
                    R7{frm = u8_to_u32 (0 :: Word8), to = u8_to_u32 (3 :: Word8), step = u8_to_u32 (1 :: Word8), f = cmp_inc, acc = R12{p1 = ex, p2 = fromIntegral (0 :: Word8) :: Word32}, obsv = R12{p1 = buf, p2 = s}}
              __ds_var_4
                = let R12{p1 = __shallow_v138, p2 = __shallow_v139}
                        = seq32
                            R7{frm = u8_to_u32 (0 :: Word8), to = u8_to_u32 (3 :: Word8), step = u8_to_u32 (1 :: Word8), f = cmp_inc, acc = R12{p1 = ex, p2 = fromIntegral (0 :: Word8) :: Word32},
                               obsv = R12{p1 = buf, p2 = s}}
                    in __shallow_v138
            in
            let __ds_var_6 = __ds_var_5
                r = let R12{p1 = __shallow_v140, p2 = __shallow_v141} = __ds_var_5 in __shallow_v141
              in
              let __ds_var_8 = __ds_var_4
                  ex142 = let R12{p1 = __shallow_v143, p2 = __shallow_v144} = __ds_var_4 in __shallow_v143
                in
                let __ds_var_9 = __ds_var_8
                    __ds_var_7 = let R12{p1 = __shallow_v145, p2 = __shallow_v146} = __ds_var_8 in __shallow_v146
                  in
                  let __ds_var_10 = __ds_var_7 in
                    case r of
                      Iterate __ds_var_11 ->
                        let __ds_var_13 = __ds_var_11 in R12{p1 = ex142, p2 = None ()}
                      __ds_var_12 ->
                        let node = (\ (Break __shallow_v147) -> __shallow_v147) __ds_var_12 in R12{p1 = ex142, p2 = Some node}

data R0 t1 t2 t3 = R0{acc :: t1, obsv :: t2, idx :: t3}

data R1 t1 t2 = R1{arr :: t1, acc :: t2}

data R2 t1 t2 = R2{arr :: t1, rbrk :: t2}

data R3 t1 t2 = R3{elem :: t1, acc :: t2}

data R4 t1 t2 t3 = R4{elem :: t1, acc :: t2, obsv :: t3}

data R5 t1 t2 = R5{elem :: t1, rbrk :: t2}

data R6 t1 t2 t3 t4 t5 = R6{frm :: t1, to :: t2, step :: t3, f :: t4, acc :: t5}

data R7 t1 t2 t3 t4 t5 t6 = R7{frm :: t1, to :: t2, step :: t3, f :: t4, acc :: t5, obsv :: t6}

data R8 t1 t2 t3 t4 t5 t6 = R8{frm :: t1, to :: t2, stepf :: t3, f :: t4, acc :: t5, obsv :: t6}

data R9 t1 t2 = R9{len :: t1, key :: t2}

data R10 t1 t2 = R10{oelem :: t1, acc :: t2}

data R11 t1 t2 t3 = R11{oelem :: t1, acc :: t2, obsv :: t3}

data R12 t1 t2 = R12{p1 :: t1, p2 :: t2}

data R13 t1 t2 t3 = R13{p1 :: t1, p2 :: t2, p3 :: t3}

data R14 t1 t2 t3 t4 = R14{p1 :: t1, p2 :: t2, p3 :: t3, p4 :: t4}

data V15 t1 t2 = Break t1
               | Iterate t2

data V16 t1 t2 = Error t1
               | Success t2

data V17 t1 t2 = None t1
               | Some t2

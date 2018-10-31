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
import qualified Data.Tuple.Select as Tup
import qualified Data.Tuple.Update as Tup
import Data.Word (Word8, Word16, Word32, Word64)
import Prelude (not, div, mod, fromIntegral, undefined, (+), (-), (*), (&&), (||), (>), (>=), (<), (<=), (==), (/=), Char, String, Int, Show, Bool(..))

data R0 t1 t2 = R0{ex :: t1, obj :: t2}
                  deriving Show

data R1 t1 t2 = R1{arr :: t1, acc :: t2}
                  deriving Show

data R2 t1 t2 = R2{arr :: t1, rbrk :: t2}
                  deriving Show

data R3 t1 t2 t3 t4 t5 = R3{arr :: t1, idx :: t2, f :: t3, acc :: t4, obsv :: t5}
                           deriving Show

data R4 t1 t2 = R4{elem :: t1, acc :: t2}
                  deriving Show

data R5 t1 t2 t3 t4 t5 t6 = R5{arr :: t1, frm :: t2, to :: t3, f :: t4, acc :: t5, obsv :: t6}
                              deriving Show

data R6 t1 t2 t3 = R6{elem :: t1, acc :: t2, obsv :: t3}
                     deriving Show

data R7 t1 t2 = R7{elem :: t1, rbrk :: t2}
                  deriving Show

data V8 t1 t2 = V8_Found t1
              | V8_NotFound t2
                  deriving Show

data R9 t1 t2 t3 t4 t5 t6 = R9{frm :: t1, to :: t2, stepf :: t3, f :: t4, acc :: t5, obsv :: t6}
                              deriving Show

data R10 t1 t2 t3 t4 t5 t6 = R10{frm :: t1, to :: t2, step :: t3, f :: t4, acc :: t5, obsv :: t6}
                               deriving Show

data V11 t1 t2 = V11_Break t1
               | V11_Iterate t2
                   deriving Show

data R12 t1 t2 = R12{oelem :: t1, acc :: t2}
                   deriving Show

data R13 t1 t2 t3 = R13{oelem :: t1, acc :: t2, obsv :: t3}
                      deriving Show

data V14 t1 t2 = V14_None t1
               | V14_Some t2
                   deriving Show

data V15 t1 t2 = V15_Error t1
               | V15_Success t2
                   deriving Show

data R16 t1 t2 t3 t4 t5 = R16{frm :: t1, to :: t2, step :: t3, f :: t4, acc :: t5}
                            deriving Show

data R17 t1 t2 t3 = R17{acc :: t1, obsv :: t2, idx :: t3}
                      deriving Show

data R18 t1 t2 = R18{p1 :: t1, p2 :: t2}
                   deriving Show

data R19 t1 t2 t3 t4 = R19{p1 :: t1, p2 :: t2, p3 :: t3, p4 :: t4}
                         deriving Show

data R20 t1 t2 t3 = R20{arr :: t1, idx :: t2, val :: t3}
                      deriving Show

data R21 t1 t2 t3 = R21{p1 :: t1, p2 :: t2, p3 :: t3}
                      deriving Show

data R22 t1 t2 t3 t4 t5 = R22{p1 :: t1, p2 :: t2, p3 :: t3, p4 :: t4, p5 :: t5}
                            deriving Show

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

type U64_to_u32_ArgT = Word64

type U64_to_u32_RetT = Word32

u64_to_u32 :: U64_to_u32_ArgT -> U64_to_u32_RetT
u64_to_u32 = undefined

type U64_to_u16_ArgT = Word64

type U64_to_u16_RetT = Word16

u64_to_u16 :: U64_to_u16_ArgT -> U64_to_u16_RetT
u64_to_u16 = undefined

type U32_to_u8_ArgT = Word32

type U32_to_u8_RetT = Word8

u32_to_u8 :: U32_to_u8_ArgT -> U32_to_u8_RetT
u32_to_u8 = undefined

type U32_to_u16_ArgT = Word32

type U32_to_u16_RetT = Word16

u32_to_u16 :: U32_to_u16_ArgT -> U32_to_u16_RetT
u32_to_u16 = undefined

type U16_to_u8_ArgT = Word16

type U16_to_u8_RetT = Word8

u16_to_u8 :: U16_to_u8_ArgT -> U16_to_u8_RetT
u16_to_u8 = undefined

type Random_u32_ArgT = ()

type Random_u32_RetT = Word32

random_u32 :: Random_u32_ArgT -> Random_u32_RetT
random_u32 = undefined

type Cogent_warn_u64_ArgT = Word64

type Cogent_warn_u64_RetT = ()

cogent_warn_u64 :: Cogent_warn_u64_ArgT -> Cogent_warn_u64_RetT
cogent_warn_u64 = undefined

type Cogent_warn_u32_ArgT = Word32

type Cogent_warn_u32_RetT = ()

cogent_warn_u32 :: Cogent_warn_u32_ArgT -> Cogent_warn_u32_RetT
cogent_warn_u32 = undefined

type Cogent_warn_u16_ArgT = Word16

type Cogent_warn_u16_RetT = ()

cogent_warn_u16 :: Cogent_warn_u16_ArgT -> Cogent_warn_u16_RetT
cogent_warn_u16 = undefined

type Cogent_warn_ArgT = String

type Cogent_warn_RetT = ()

cogent_warn :: Cogent_warn_ArgT -> Cogent_warn_RetT
cogent_warn = undefined

type Cogent_log2_ArgT = Word32

type Cogent_log2_RetT = Word32

cogent_log2 :: Cogent_log2_ArgT -> Cogent_log2_RetT
cogent_log2 = undefined

type Cogent_debug_u64_hex_ArgT = Word64

type Cogent_debug_u64_hex_RetT = ()

cogent_debug_u64_hex :: Cogent_debug_u64_hex_ArgT -> Cogent_debug_u64_hex_RetT
cogent_debug_u64_hex = undefined

type Cogent_debug_u64_ArgT = Word64

type Cogent_debug_u64_RetT = ()

cogent_debug_u64 :: Cogent_debug_u64_ArgT -> Cogent_debug_u64_RetT
cogent_debug_u64 = undefined

type Cogent_debug_u32_oct_ArgT = Word32

type Cogent_debug_u32_oct_RetT = ()

cogent_debug_u32_oct :: Cogent_debug_u32_oct_ArgT -> Cogent_debug_u32_oct_RetT
cogent_debug_u32_oct = undefined

type Cogent_debug_u32_hex_ArgT = Word32

type Cogent_debug_u32_hex_RetT = ()

cogent_debug_u32_hex :: Cogent_debug_u32_hex_ArgT -> Cogent_debug_u32_hex_RetT
cogent_debug_u32_hex = undefined

type Cogent_debug_u32_ArgT = Word32

type Cogent_debug_u32_RetT = ()

cogent_debug_u32 :: Cogent_debug_u32_ArgT -> Cogent_debug_u32_RetT
cogent_debug_u32 = undefined

type Cogent_debug_ArgT = String

type Cogent_debug_RetT = ()

cogent_debug :: Cogent_debug_ArgT -> Cogent_debug_RetT
cogent_debug = undefined

type Cogent_assert2_ArgT = R18 String Bool

type Cogent_assert2_RetT = ()

cogent_assert2 :: Cogent_assert2_ArgT -> Cogent_assert2_RetT
cogent_assert2 = undefined

type Cogent_assert_ArgT = Bool

type Cogent_assert_RetT = ()

cogent_assert :: Cogent_assert_ArgT -> Cogent_assert_RetT
cogent_assert = undefined

type Wordarray_cmp_ArgT = R18 (WordArray Word8) (WordArray Word8)

type Wordarray_cmp_RetT = Bool

wordarray_cmp :: Wordarray_cmp_ArgT -> Wordarray_cmp_RetT
wordarray_cmp = undefined

type Wordarray_copy_ArgT a = R22 (WordArray a) (WordArray a) Word32 Word32 Word32

type Wordarray_copy_RetT a = WordArray a

wordarray_copy :: Wordarray_copy_ArgT a -> Wordarray_copy_RetT a
wordarray_copy = undefined

type Wordarray_fold'_ArgT a acc obsv = R19 (WordArray a) (R21 acc obsv a -> acc) acc obsv

type Wordarray_fold'_RetT a acc obsv = acc

wordarray_fold' :: Wordarray_fold'_ArgT a acc obsv -> Wordarray_fold'_RetT a acc obsv
wordarray_fold' = undefined

type Wordarray_get_ArgT a = R18 (WordArray a) Word32

type Wordarray_get_RetT a = a

wordarray_get :: Wordarray_get_ArgT a -> Wordarray_get_RetT a
wordarray_get = undefined

type Wordarray_length_ArgT a = WordArray a

type Wordarray_length_RetT a = Word32

wordarray_length :: Wordarray_length_ArgT a -> Wordarray_length_RetT a
wordarray_length = undefined

type Wordarray_map'_ArgT a acc obsv = R19 (WordArray a) (R21 acc obsv a -> R18 acc a) acc obsv

type Wordarray_map'_RetT a acc obsv = R18 (WordArray a) acc

wordarray_map' :: Wordarray_map'_ArgT a acc obsv -> Wordarray_map'_RetT a acc obsv
wordarray_map' = undefined

type Wordarray_map__ArgT a = R18 (WordArray a) (a -> a)

type Wordarray_map__RetT a = WordArray a

wordarray_map_ :: Wordarray_map__ArgT a -> Wordarray_map__RetT a
wordarray_map_ = undefined

type Wordarray_put2_ArgT a = R20 (WordArray a) Word32 a

type Wordarray_put2_RetT a = WordArray a

wordarray_put2 :: Wordarray_put2_ArgT a -> Wordarray_put2_RetT a
wordarray_put2 = undefined

type Wordarray_set_ArgT a = R19 (WordArray a) Word32 Word32 a

type Wordarray_set_RetT a = WordArray a

wordarray_set :: Wordarray_set_ArgT a -> Wordarray_set_RetT a
wordarray_set = undefined

type Wordarray_split_ArgT a = R18 (WordArray a) Word32

type Wordarray_split_RetT a = R18 (WordArray a) (WordArray a)

wordarray_split :: Wordarray_split_ArgT a -> Wordarray_split_RetT a
wordarray_split = undefined

type Wordarray_take_ArgT a = R18 (WordArray a) Word32

type Wordarray_take_RetT a = WordArray a

wordarray_take :: Wordarray_take_ArgT a -> Wordarray_take_RetT a
wordarray_take = undefined

type Wordarray_u8_as_u32_ArgT = WordArray Word8

type Wordarray_u8_as_u32_RetT = Word32

wordarray_u8_as_u32 :: Wordarray_u8_as_u32_ArgT -> Wordarray_u8_as_u32_RetT
wordarray_u8_as_u32 = undefined

type Wordarray_map_view_ArgT a = R18 (View (WordArray a)) (a -> a)

type Wordarray_map_view_RetT a = View (WordArray a)

wordarray_map_view :: Wordarray_map_view_ArgT a -> Wordarray_map_view_RetT a
wordarray_map_view = undefined

type Wordarray_unview_ArgT a = View (WordArray a)

type Wordarray_unview_RetT a = WordArray a

wordarray_unview :: Wordarray_unview_ArgT a -> Wordarray_unview_RetT a
wordarray_unview = undefined

type Wordarray_view_ArgT a = R19 (WordArray a) Word32 Word32 Word32

type Wordarray_view_RetT a = View (WordArray a)

wordarray_view :: Wordarray_view_ArgT a -> Wordarray_view_RetT a
wordarray_view = undefined

type Wordarray_free_ArgT a = R18 SysState (WordArray a)

type Wordarray_free_RetT a = SysState

wordarray_free :: Wordarray_free_ArgT a -> Wordarray_free_RetT a
wordarray_free = undefined

type Seq32_simple_ArgT acc = R16 Word32 Word32 Word32 (acc -> acc) acc

type Seq32_simple_RetT acc = acc

seq32_simple :: Seq32_simple_ArgT acc -> Seq32_simple_RetT acc
seq32_simple = undefined

type Wordarray_clone_rr_ArgT a b = R18 SysState (WordArray a)

type Wordarray_clone_rr_RetT a b = R18 SysState (V15 () (WordArray b))

wordarray_clone_rr :: Wordarray_clone_rr_ArgT a b -> Wordarray_clone_rr_RetT a b
wordarray_clone_rr = undefined

type Wordarray_slice_ArgT a = R19 SysState (WordArray a) Word32 Word32

type Wordarray_slice_RetT a = R18 SysState (V15 () (WordArray a))

wordarray_slice :: Wordarray_slice_ArgT a -> Wordarray_slice_RetT a
wordarray_slice = undefined

type Wordarray_create_ArgT a = R18 SysState Word32

type Wordarray_create_RetT a = V15 SysState (R18 SysState (WordArray a))

wordarray_create :: Wordarray_create_ArgT a -> Wordarray_create_RetT a
wordarray_create = undefined

type Wordarray_create_nz_ArgT a = R18 SysState Word32

type Wordarray_create_nz_RetT a = V15 SysState (R18 SysState (WordArray a))

wordarray_create_nz :: Wordarray_create_nz_ArgT a -> Wordarray_create_nz_RetT a
wordarray_create_nz = undefined

type Wordarray_put_ArgT a = R20 (WordArray a) Word32 a

type Wordarray_put_RetT a = V15 (WordArray a) (WordArray a)

wordarray_put :: Wordarray_put_ArgT a -> Wordarray_put_RetT a
wordarray_put = undefined

type Seq32_ArgT acc obsv rbrk = R10 Word32 Word32 Word32 (R17 acc obsv Word32 -> R18 acc (V11 rbrk ())) acc obsv

type Seq32_RetT acc obsv rbrk = R18 acc (V11 rbrk ())

seq32 :: Seq32_ArgT acc obsv rbrk -> Seq32_RetT acc obsv rbrk
seq32 = undefined

type Seq32_rev_ArgT acc obsv rbrk = R10 Word32 Word32 Word32 (R17 acc obsv Word32 -> R18 acc (V11 rbrk ())) acc obsv

type Seq32_rev_RetT acc obsv rbrk = R18 acc (V11 rbrk ())

seq32_rev :: Seq32_rev_ArgT acc obsv rbrk -> Seq32_rev_RetT acc obsv rbrk
seq32_rev = undefined

type Seq32_stepf_ArgT acc obsv rbrk = R9 Word32 Word32 (Word32 -> Word32) (R17 acc obsv Word32 -> R18 acc (V11 rbrk ())) acc obsv

type Seq32_stepf_RetT acc obsv rbrk = R18 acc (V11 rbrk ())

seq32_stepf :: Seq32_stepf_ArgT acc obsv rbrk -> Seq32_stepf_RetT acc obsv rbrk
seq32_stepf = undefined

type Seq64_ArgT acc obsv rbrk = R10 Word64 Word64 Word64 (R17 acc obsv Word64 -> R18 acc (V11 rbrk ())) acc obsv

type Seq64_RetT acc obsv rbrk = R18 acc (V11 rbrk ())

seq64 :: Seq64_ArgT acc obsv rbrk -> Seq64_RetT acc obsv rbrk
seq64 = undefined

type Wordarray_findsub_ArgT a = R21 (WordArray a) (WordArray a) Word32

type Wordarray_findsub_RetT a = V8 Word32 ()

wordarray_findsub :: Wordarray_findsub_ArgT a -> Wordarray_findsub_RetT a
wordarray_findsub = undefined

type Wordarray_fold_ArgT a acc obsv rbrk = R5 (WordArray a) Word32 Word32 (R6 a acc obsv -> V11 rbrk acc) acc obsv

type Wordarray_fold_RetT a acc obsv rbrk = V11 rbrk acc

wordarray_fold :: Wordarray_fold_ArgT a acc obsv rbrk -> Wordarray_fold_RetT a acc obsv rbrk
wordarray_fold = undefined

type Wordarray_fold_no_break_ArgT a acc obsv = R5 (WordArray a) Word32 Word32 (R6 a acc obsv -> acc) acc obsv

type Wordarray_fold_no_break_RetT a acc obsv = acc

wordarray_fold_no_break :: Wordarray_fold_no_break_ArgT a acc obsv -> Wordarray_fold_no_break_RetT a acc obsv
wordarray_fold_no_break = undefined

type Wordarray_map_ArgT a acc obsv rbrk = R5 (WordArray a) Word32 Word32 (R6 a acc obsv -> R18 (R18 a acc) (V11 rbrk ())) acc obsv

type Wordarray_map_RetT a acc obsv rbrk = R18 (R18 (WordArray a) acc) (V11 rbrk ())

wordarray_map :: Wordarray_map_ArgT a acc obsv rbrk -> Wordarray_map_RetT a acc obsv rbrk
wordarray_map = undefined

type Wordarray_map_no_break_ArgT a acc obsv = R5 (WordArray a) Word32 Word32 (R6 a acc obsv -> R18 a acc) acc obsv

type Wordarray_map_no_break_RetT a acc obsv = R18 (WordArray a) acc

wordarray_map_no_break :: Wordarray_map_no_break_ArgT a acc obsv -> Wordarray_map_no_break_RetT a acc obsv
wordarray_map_no_break = undefined

type Wordarray_print_ArgT = WordArray Word8

type Wordarray_print_RetT = ()

wordarray_print :: Wordarray_print_ArgT -> Wordarray_print_RetT
wordarray_print = undefined

type Wordarray_modify_ArgT a acc obsv = R3 (WordArray a) Word32 (R6 a acc obsv -> R4 a acc) acc obsv

type Wordarray_modify_RetT a acc obsv = R1 (WordArray a) acc

wordarray_modify :: Wordarray_modify_ArgT a acc obsv -> Wordarray_modify_RetT a acc obsv
wordarray_modify = undefined

type Snd_ArgT a b = R18 a b

type Snd_RetT a b = b

snd :: Snd_ArgT a b -> Snd_RetT a b
snd __ds_var_0
  = let __ds_var_2 = __ds_var_0
        __ds_var_1 = let R18{p1 = __shallow_v23, p2 = __shallow_v24} = __ds_var_0 in __shallow_v23
      in
      let __ds_var_3 = __ds_var_2
          b = let R18{p1 = __shallow_v25, p2 = __shallow_v26} = __ds_var_2 in __shallow_v26
        in let __ds_var_4 = __ds_var_1 in b

type Second_ArgT b b' a = R18 (b -> b') (R18 a b)

type Second_RetT b b' a = R18 a b'

second :: Second_ArgT b b' a -> Second_RetT b b' a
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

type Min_u64_ArgT = R18 Word64 Word64

type Min_u64_RetT = Word64

min_u64 :: Min_u64_ArgT -> Min_u64_RetT
min_u64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R18{p1 = __shallow_v35, p2 = __shallow_v36} = __ds_var_0 in __shallow_v35
      in
      let __ds_var_2 = __ds_var_1
          b = let R18{p1 = __shallow_v37, p2 = __shallow_v38} = __ds_var_1 in __shallow_v38
        in if (a < b) then a else b

type Min_u32_ArgT = R18 Word32 Word32

type Min_u32_RetT = Word32

min_u32 :: Min_u32_ArgT -> Min_u32_RetT
min_u32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R18{p1 = __shallow_v39, p2 = __shallow_v40} = __ds_var_0 in __shallow_v39
      in
      let __ds_var_2 = __ds_var_1
          b = let R18{p1 = __shallow_v41, p2 = __shallow_v42} = __ds_var_1 in __shallow_v42
        in if (a < b) then a else b

type Map_body_g_ArgT = Word8

type Map_body_g_RetT = Word8

map_body_g :: Map_body_g_ArgT -> Map_body_g_RetT
map_body_g __ds_var_0 = let x = __ds_var_0 in (x * (2 :: Word8))

type Map_body_f_ArgT = Word8

type Map_body_f_RetT = Word8

map_body_f :: Map_body_f_ArgT -> Map_body_f_RetT
map_body_f __ds_var_0 = let x = __ds_var_0 in (x + (1 :: Word8))

type In_range_u32_ArgT = R21 Word32 Word32 Word32

type In_range_u32_RetT = Bool

in_range_u32 :: In_range_u32_ArgT -> In_range_u32_RetT
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

type Fst_ArgT a b = R18 a b

type Fst_RetT a b = a

fst :: Fst_ArgT a b -> Fst_RetT a b
fst __ds_var_0
  = let __ds_var_2 = __ds_var_0
        a = let R18{p1 = __shallow_v52, p2 = __shallow_v53} = __ds_var_0 in __shallow_v52
      in
      let __ds_var_3 = __ds_var_2
          __ds_var_1 = let R18{p1 = __shallow_v54, p2 = __shallow_v55} = __ds_var_2 in __shallow_v55
        in let __ds_var_4 = __ds_var_1 in a

type First_ArgT a a' b = R18 (a -> a') (R18 a b)

type First_RetT a a' b = R18 a' b

first :: First_ArgT a a' b -> First_RetT a a' b
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

type Cogent_low_16_bits_ArgT = Word32

type Cogent_low_16_bits_RetT = Word16

cogent_low_16_bits :: Cogent_low_16_bits_ArgT -> Cogent_low_16_bits_RetT
cogent_low_16_bits __ds_var_0 = let x = __ds_var_0 in u32_to_u16 (x .&. (65535 :: Word32))

type Cogent_high_16_bits_ArgT = Word32

type Cogent_high_16_bits_RetT = Word16

cogent_high_16_bits :: Cogent_high_16_bits_ArgT -> Cogent_high_16_bits_RetT
cogent_high_16_bits __ds_var_0 = let x = __ds_var_0 in u32_to_u16 ((x .&. (4294901760 :: Word32)) `shiftR` fromIntegral (16 :: Word32))

type Cogent_debug_u8_ArgT = Word8

type Cogent_debug_u8_RetT = ()

cogent_debug_u8 :: Cogent_debug_u8_ArgT -> Cogent_debug_u8_RetT
cogent_debug_u8 __ds_var_0 = let x = __ds_var_0 in cogent_debug_u32 (fromIntegral x :: Word32)

type Cogent_debug_u16_ArgT = Word16

type Cogent_debug_u16_RetT = ()

cogent_debug_u16 :: Cogent_debug_u16_ArgT -> Cogent_debug_u16_RetT
cogent_debug_u16 __ds_var_0 = let x = __ds_var_0 in cogent_debug_u32 (fromIntegral x :: Word32)

type Cogent_debug_bool_ArgT = Bool

type Cogent_debug_bool_RetT = ()

cogent_debug_bool :: Cogent_debug_bool_ArgT -> Cogent_debug_bool_RetT
cogent_debug_bool __ds_var_0 = let bool = __ds_var_0 in if bool then cogent_debug "true" else cogent_debug "false"

type Align64_ArgT = R18 Word64 Word64

type Align64_RetT = Word64

align64 :: Align64_ArgT -> Align64_RetT
align64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        x = let R18{p1 = __shallow_v64, p2 = __shallow_v65} = __ds_var_0 in __shallow_v64
      in
      let __ds_var_2 = __ds_var_1
          powof2 = let R18{p1 = __shallow_v66, p2 = __shallow_v67} = __ds_var_1 in __shallow_v67
        in ((x + (powof2 - (1 :: Word64))) .&. complement (powof2 - (1 :: Word64)))

type Align32_ArgT = R18 Word32 Word32

type Align32_RetT = Word32

align32 :: Align32_ArgT -> Align32_RetT
align32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        x = let R18{p1 = __shallow_v68, p2 = __shallow_v69} = __ds_var_0 in __shallow_v68
      in
      let __ds_var_2 = __ds_var_1
          powof2 = let R18{p1 = __shallow_v70, p2 = __shallow_v71} = __ds_var_1 in __shallow_v71
        in ((x + (powof2 - (1 :: Word32))) .&. complement (powof2 - (1 :: Word32)))

type Wordarray_copy_u8_ArgT = R22 (WordArray Word8) (WordArray Word8) Word32 Word32 Word32

type Wordarray_copy_u8_RetT = WordArray Word8

wordarray_copy_u8 :: Wordarray_copy_u8_ArgT -> Wordarray_copy_u8_RetT
wordarray_copy_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_copy arg

type Wordarray_length_u8_ArgT = WordArray Word8

type Wordarray_length_u8_RetT = Word32

wordarray_length_u8 :: Wordarray_length_u8_ArgT -> Wordarray_length_u8_RetT
wordarray_length_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_length arg

type Wordarray_map_u8_ArgT = R18 (WordArray Word8) (Word8 -> Word8)

type Wordarray_map_u8_RetT = WordArray Word8

wordarray_map_u8 :: Wordarray_map_u8_ArgT -> Wordarray_map_u8_RetT
wordarray_map_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_map_ arg

type Wordarray_free'_ArgT a = R0 SysState (WordArray a)

type Wordarray_free'_RetT a = SysState

wordarray_free' :: Wordarray_free'_ArgT a -> Wordarray_free'_RetT a
wordarray_free' __ds_var_0
  = let __ds_var_2 = __ds_var_0
        ex = let R0{ex = __shallow_v72, obj = __shallow_v73} = __ds_var_0 in __shallow_v72
      in
      let __ds_var_1 = __ds_var_2
          obj = let R0{ex = __shallow_v74, obj = __shallow_v75} = __ds_var_2 in __shallow_v75
        in wordarray_free R18{p1 = ex, p2 = obj}

type Wordarray_free_u8_ArgT = R18 SysState (WordArray Word8)

type Wordarray_free_u8_RetT = SysState

wordarray_free_u8 :: Wordarray_free_u8_ArgT -> Wordarray_free_u8_RetT
wordarray_free_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_free arg

type Error_ArgT b a = b

type Error_RetT b a = V15 b a

error :: Error_ArgT b a -> Error_RetT b a
error __ds_var_0 = let b = __ds_var_0 in V15_Error b

type Safe_add32_ArgT = R18 Word32 Word32

type Safe_add32_RetT = V15 () Word32

safe_add32 :: Safe_add32_ArgT -> Safe_add32_RetT
safe_add32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R18{p1 = __shallow_v76, p2 = __shallow_v77} = __ds_var_0 in __shallow_v76
      in
      let __ds_var_2 = __ds_var_1
          b = let R18{p1 = __shallow_v78, p2 = __shallow_v79} = __ds_var_1 in __shallow_v79
        in let r = (a + b) in if ((r < a) || (r < b)) then V15_Error () else V15_Success r

type Safe_add64_ArgT = R18 Word64 Word64

type Safe_add64_RetT = V15 () Word64

safe_add64 :: Safe_add64_ArgT -> Safe_add64_RetT
safe_add64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R18{p1 = __shallow_v80, p2 = __shallow_v81} = __ds_var_0 in __shallow_v80
      in
      let __ds_var_2 = __ds_var_1
          b = let R18{p1 = __shallow_v82, p2 = __shallow_v83} = __ds_var_1 in __shallow_v83
        in let r = (a + b) in if ((r < a) || (r < b)) then V15_Error () else V15_Success r

type Safe_sub32_ArgT = R18 Word32 Word32

type Safe_sub32_RetT = V15 () Word32

safe_sub32 :: Safe_sub32_ArgT -> Safe_sub32_RetT
safe_sub32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R18{p1 = __shallow_v84, p2 = __shallow_v85} = __ds_var_0 in __shallow_v84
      in
      let __ds_var_2 = __ds_var_1
          b = let R18{p1 = __shallow_v86, p2 = __shallow_v87} = __ds_var_1 in __shallow_v87
        in let r = (a - b) in if (r > a) then V15_Error () else V15_Success r

type Safe_sub64_ArgT = R18 Word64 Word64

type Safe_sub64_RetT = V15 () Word64

safe_sub64 :: Safe_sub64_ArgT -> Safe_sub64_RetT
safe_sub64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = let R18{p1 = __shallow_v88, p2 = __shallow_v89} = __ds_var_0 in __shallow_v88
      in
      let __ds_var_2 = __ds_var_1
          b = let R18{p1 = __shallow_v90, p2 = __shallow_v91} = __ds_var_1 in __shallow_v91
        in let r = (a - b) in if (r > a) then V15_Error () else V15_Success r

type Success_ArgT a b = a

type Success_RetT a b = V15 b a

success :: Success_ArgT a b -> Success_RetT a b
success __ds_var_0 = let a = __ds_var_0 in V15_Success a

type Wordarray_clone_ArgT a = R18 SysState (WordArray a)

type Wordarray_clone_RetT a = V15 SysState (R18 SysState (WordArray a))

wordarray_clone :: Wordarray_clone_ArgT a -> Wordarray_clone_RetT a
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

type Wordarray_clone_u8_ArgT = R18 SysState (WordArray Word8)

type Wordarray_clone_u8_RetT = V15 SysState (R18 SysState (WordArray Word8))

wordarray_clone_u8 :: Wordarray_clone_u8_ArgT -> Wordarray_clone_u8_RetT
wordarray_clone_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_clone arg

type Wordarray_create_nz_u8_ArgT = R18 SysState Word32

type Wordarray_create_nz_u8_RetT = V15 SysState (R18 SysState (WordArray Word8))

wordarray_create_nz_u8 :: Wordarray_create_nz_u8_ArgT -> Wordarray_create_nz_u8_RetT
wordarray_create_nz_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_create_nz arg

type Wordarray_create_u8_ArgT = R18 SysState Word32

type Wordarray_create_u8_RetT = V15 SysState (R18 SysState (WordArray Word8))

wordarray_create_u8 :: Wordarray_create_u8_ArgT -> Wordarray_create_u8_RetT
wordarray_create_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_create arg

type Wordarray_get_bounded_ArgT a = R18 (WordArray a) Word32

type Wordarray_get_bounded_RetT a = V15 () a

wordarray_get_bounded :: Wordarray_get_bounded_ArgT a -> Wordarray_get_bounded_RetT a
wordarray_get_bounded __ds_var_0
  = let __ds_var_1 = __ds_var_0
        arr = let R18{p1 = __shallow_v103, p2 = __shallow_v104} = __ds_var_0 in __shallow_v103
      in
      let __ds_var_2 = __ds_var_1
          idx = let R18{p1 = __shallow_v105, p2 = __shallow_v106} = __ds_var_1 in __shallow_v106
        in if (idx < wordarray_length arr) then V15_Success (wordarray_get R18{p1 = arr, p2 = idx}) else V15_Error ()

type Wordarray_get_bounded_u8_ArgT = R18 (WordArray Word8) Word32

type Wordarray_get_bounded_u8_RetT = V15 () Word8

wordarray_get_bounded_u8 :: Wordarray_get_bounded_u8_ArgT -> Wordarray_get_bounded_u8_RetT
wordarray_get_bounded_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_get_bounded arg

type Wordarray_put_u8_ArgT = R20 (WordArray Word8) Word32 Word8

type Wordarray_put_u8_RetT = V15 (WordArray Word8) (WordArray Word8)

wordarray_put_u8 :: Wordarray_put_u8_ArgT -> Wordarray_put_u8_RetT
wordarray_put_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_put arg

type OptionToResult_ArgT a = V14 () a

type OptionToResult_RetT a = V15 () a

optionToResult :: OptionToResult_ArgT a -> OptionToResult_RetT a
optionToResult __ds_var_0
  = case __ds_var_0 of
      V14_None __ds_var_1 -> let __ds_var_3 = __ds_var_1 in V15_Error ()
      __ds_var_2 -> let a = (\ (V14_Some __shallow_v107) -> __shallow_v107) __ds_var_2 in V15_Success a

type ResultToOption_ArgT e a = V15 e a

type ResultToOption_RetT e a = V14 () a

resultToOption :: ResultToOption_ArgT e a -> ResultToOption_RetT e a
resultToOption __ds_var_0
  = case __ds_var_0 of
      V15_Error __ds_var_1 -> let __ds_var_3 = __ds_var_1 in V14_None ()
      __ds_var_2 -> let a = (\ (V15_Success __shallow_v108) -> __shallow_v108) __ds_var_2 in V14_Some a

type Copy_n_ArgT a = R6 a Word32 (WordArray a)

type Copy_n_RetT a = R18 a Word32

copy_n :: Copy_n_ArgT a -> Copy_n_RetT a
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

type Modify_body_f_ArgT = R6 Word8 Word8 Bool

type Modify_body_f_RetT = R4 Word8 Word8

modify_body_f :: Modify_body_f_ArgT -> Modify_body_f_RetT
modify_body_f __ds_var_0
  = let __ds_var_2 = __ds_var_0
        elem = let R6{elem = __shallow_v118, acc = __shallow_v119, obsv = __shallow_v120} = __ds_var_0 in __shallow_v118
      in
      let __ds_var_3 = __ds_var_2
          acc = let R6{elem = __shallow_v121, acc = __shallow_v122, obsv = __shallow_v123} = __ds_var_2 in __shallow_v122
        in
        let __ds_var_1 = __ds_var_3
            obsv = let R6{elem = __shallow_v124, acc = __shallow_v125, obsv = __shallow_v126} = __ds_var_3 in __shallow_v126
          in if obsv then R4{elem = (elem + acc), acc = (elem + acc)} else R4{elem = elem, acc = acc}

type Wordarray_modify_u8_ArgT = R3 (WordArray Word8) Word32 (R6 Word8 Word8 Bool -> R4 Word8 Word8) Word8 Bool

type Wordarray_modify_u8_RetT = R1 (WordArray Word8) Word8

wordarray_modify_u8 :: Wordarray_modify_u8_ArgT -> Wordarray_modify_u8_RetT
wordarray_modify_u8 __ds_var_0 = let arg = __ds_var_0 in wordarray_modify arg

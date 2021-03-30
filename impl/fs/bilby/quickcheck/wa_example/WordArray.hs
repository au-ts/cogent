{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ImplicitParams #-}
{- LANGUAGE ImplicitPrelude #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PartialTypeSignatures #-}
{- LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -Wno-missing-fields #-}
{- OPTIONS_GHC -F -pgmFderive -optF-F #-}

module WordArray where

import Control.Exception (bracket)
import Control.Lens hiding (elements)
-- import Control.Monad.State
import Control.Monad (void)
import Control.Monad.Trans.Class (lift)
import Data.Array.IArray
import Data.Array.IO hiding (newArray)
import Data.Either.Extra  -- extra-1.6
-- import Data.Function
import Data.Functor.Classes
import Data.Ix
import Data.List (genericDrop, genericTake)
import qualified Data.Set as S
-- import qualified Data.Set.Internal as S
import Enumerate
import Foreign hiding (void)
import Foreign.C.String hiding (CString)
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc
import Foreign.Marshal.Unsafe (unsafeLocalState)
import Foreign.Ptr
import Foreign.Storable
import GHC.Generics
import Prelude as P
-- import QuickCheck.GenT
import Test.QuickCheck hiding (Success)
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Function
import Test.QuickCheck.Gen
import Test.QuickCheck.Monadic

import CogentMonad
import Corres
import Wa_FFI_Types
import Wa_FFI_Types_Abs
import Wa_FFI
import Util

-- import Debug.Trace

{- |
To run the REPL: 
> cabal v1-repl wa-example --ghc-options=" wa_example/build/wa.o"
-}


-- * Haskell specification

-- | The Haskell type for wordarrays
type WordArray e = Array Word32 e

data O = O_mallocFail
       | O_zeroLengthFail
       | O_good
       deriving (Show, Generic, Enumerable)

empty_array :: WordArray e
empty_array = array (0, 0) []

hs_wordarray_create :: (?o :: O, Integral e) => Word32 -> Maybe (WordArray e)
hs_wordarray_create 0
  | O_zeroLengthFail <- ?o = Nothing
  | otherwise              = Just (array (1,0) [])
hs_wordarray_create l
  | O_mallocFail <- ?o = Nothing
  | otherwise          = Just (listArray (0, l-1) (repeat 0))

hs_wordarray_create_nd :: (Integral e) => Word32 -> CogentMonad (Maybe (WordArray e))
hs_wordarray_create_nd 0 = return Nothing <|> return (Just $ array (1,0) [])  -- either nothing or empty array
hs_wordarray_create_nd l = return Nothing <|> return (Just $ listArray (0, l-1) (repeat 0))

hs_wordarray_create_nz :: (Integral e, ?o :: O) => Word32 -> Maybe (WordArray e)
hs_wordarray_create_nz 0
  | O_zeroLengthFail <- ?o = Nothing
  | otherwise              = Just (array (1,0) [])
hs_wordarray_create_nz l
  | O_mallocFail <- ?o = Nothing
  | otherwise          = Just (array (0, l-1) [(i,v) | i <- [0..l-1], v <- [0]])

hs_wordarray_free :: WordArray e -> ()
hs_wordarray_free _ = ()

hs_wordarray_get_bounded :: Integral e => WordArray e -> Word32 -> Maybe e
hs_wordarray_get_bounded xs i = 
  if i `is_inbound` xs then Just $ xs ! i else Nothing

is_inbound :: Word32 -> WordArray e -> Bool
is_inbound i xs = case bounds xs of (l,u) -> l <= i && i <= u

hs_wordarray_modify :: WordArray e
                    -> Word32
                    -> ((e, acc, obsv) -> (e, acc))
                    -> acc
                    -> obsv
                    -> (WordArray e, acc)
hs_wordarray_modify xs i f acc obsv
  | i `is_inbound` xs = 
      let (e',acc') = f (xs ! i, acc, obsv)
       in (xs // [(i, e')], acc')
  | otherwise = (xs, acc)                          

-- | __NOTE__: We also need to specify all inner functions used. As on the Cogent
-- side, due to the way higher-order function calls are made, we cannot generate
-- random functions for testing. The way we test higher-order functions is
-- to show that for all callable inner functions, the outer function behaves
-- correctly. 
--
-- In the case of @wordarray_modify@, @modify_bofy_f@ is the only callable
-- function. This can be seem in the @dispatch@ functions generated in the .h file. / zilinc
hs_modify_body_f :: (Word8, Word8, Bool) -> (Word8, Word8)
hs_modify_body_f (e, acc, obsv) =
  if obsv then (e + acc, e + acc) else (e, acc)

hs_wordarray_put :: WordArray e -> Word32 -> e -> Either (WordArray e) (WordArray e)
hs_wordarray_put xs i _ | not (i `is_inbound` xs) = Left xs
hs_wordarray_put xs i a = Right $ xs // [(i,a)]

hs_wordarray_length :: WordArray e -> Word32
hs_wordarray_length = fromIntegral . length

hs_wordarray_clone :: (?o :: O) => WordArray e -> Maybe (WordArray e)
hs_wordarray_clone xs
  | O_mallocFail <- ?o = Nothing
  | otherwise          = Just xs

hs_wordarray_set :: WordArray a -> Word32 -> Word32 -> a -> WordArray a
hs_wordarray_set arr frm n a = 
  let len = hs_wordarray_length arr
      to  = min (frm + n) len - 1
   in if frm >= len then arr
      else arr // (zip [frm .. to] (repeat a))

hs_wordarray_copy :: WordArray e -> WordArray e -> Word32 -> Word32 -> Word32 -> WordArray e
hs_wordarray_copy dst src dst_offs src_offs n =
  let len_dst = fromIntegral $ length dst
      len_src = fromIntegral $ length src
      dst_avl = len_dst - dst_offs
      src_avl = len_src - src_offs
      n' = minimum [n, dst_avl, src_avl]
      src_cpy = genericTake n' . genericDrop src_offs $ elems src 
   in if dst_offs > len_dst - 1 || src_offs > len_src - 1 then dst 
      else dst // zip [dst_offs .. dst_offs + n' - 1] src_cpy

hs_wordarray_map :: WordArray e
                 -> (e -> e)
                 -> WordArray e
hs_wordarray_map xs f = fmap f xs

hs_map_body_f = (+1)
hs_map_body_g = (*2)

-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @wordarray_create@.

prop_corres_wordarray_create_u8 :: Property
prop_corres_wordarray_create_u8 = 
  forAll (pure O_good) $ \o -> let ?o = o in 
    monadicIO $ forAllM gen_c_wordarray_create_u8_arg $ \ic -> run $ do
      oa <- hs_wordarray_create @ Word8 <$> abs_wordarray_create_u8_arg ic
      bracket (cogent_wordarray_create_u8 ic)
              (\oc -> do Ct8 tag err suc <- peek oc
                         if | fromEnum tag == fromEnum tagEnumError -> return ()
                            | fromEnum tag == fromEnum tagEnumSuccess -> do 
                                psuc <- new suc
                                cogent_wordarray_free_u8 psuc
                                return ()
                            | otherwise -> fail "impossible")
              (\oc -> corresM' rel_wordarray_create_u8_ret oa oc)

prop_corres_wordarray_create_u8_nd :: Property
prop_corres_wordarray_create_u8_nd = monadicIO $ 
  forAllM gen_c_wordarray_create_u8_arg $ \ic -> run $ do
    oa <- hs_wordarray_create_nd @ Word8 <$> abs_wordarray_create_u8_arg ic
    bracket (cogent_wordarray_create_u8 ic)
            (\oc -> do Ct8 tag err suc <- peek oc
                       if | fromEnum tag == fromEnum tagEnumError -> return ()
                          | fromEnum tag == fromEnum tagEnumSuccess -> do 
                              psuc <- new suc
                              cogent_wordarray_free_u8 psuc
                              return ()
                          | otherwise -> fail "impossible")
            (\oc -> corresM rel_wordarray_create_u8_ret oa oc)

prop_equiv_wordarray_create_u8 :: Property
prop_equiv_wordarray_create_u8 =
  forAll (choose (0, 4095) :: Gen Word32) $ \l ->
    let d_os = flip map (enumerated :: [O]) $ \o -> 
                 let ?o = o
                  in hs_wordarray_create @ Word8 l
        nd_os = hs_wordarray_create_nd l
     in liftEq eq (S.fromList d_os) (S.fromList nd_os)
  where eq :: Maybe (WordArray Word8) -> Maybe (WordArray Word8) -> Bool
        eq Nothing Nothing = True
        eq (Just a1) (Just a2) = length a1 == length a2
        eq _ _ = False

gen_c_wordarray_create_u8_arg :: Gen (Ptr Ct7)
gen_c_wordarray_create_u8_arg = do
  let p1 = unsafeLocalState pDummyCSysState
  ct6 <- Ct7 p1 <$> choose (0, 4095)
  return $ unsafeLocalState $ new ct6

abs_wordarray_create_u8_arg :: Ptr Ct7 -> IO Word32
abs_wordarray_create_u8_arg ia = do
  Ct7 _ p2 <- peek ia
  return $ fromIntegral p2

rel_wordarray_create_u8_ret :: Maybe (WordArray Word8) -> Ptr Ct8 -> IO Bool
rel_wordarray_create_u8_ret oa oc = do
  Ct8 tag err suc <- peek oc
  if | fromEnum tag == fromEnum tagEnumError  , Nothing <- oa -> return True
     | fromEnum tag == fromEnum tagEnumSuccess, Just _  <- oa -> return True  -- nothing that we can check about the values of the wordarrays
     | otherwise -> return False


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @wordarray_create_nz@

prop_corres_wordarray_create_nz_u8 :: Property
prop_corres_wordarray_create_nz_u8 = 
  forAll (pure O_good) $ \o -> let ?o = o in
    monadicIO $ forAllM gen_c_wordarray_create_nz_u8_arg $ \ic -> run $ do
      oa <- hs_wordarray_create_nz @ Word8 <$> abs_wordarray_create_nz_u8_arg ic
      bracket (cogent_wordarray_create_nz_u8 ic)
              (\oc -> do Ct8 tag err suc <- peek oc
                         if | fromEnum tag == fromEnum tagEnumError -> return ()
                            | fromEnum tag == fromEnum tagEnumSuccess -> do 
                                psuc <- new suc
                                cogent_wordarray_free_u8 psuc
                                return ()
                            | otherwise -> fail "impossible")
              (\oc -> corresM' rel_wordarray_create_nz_u8_ret oa oc)

gen_c_wordarray_create_nz_u8_arg :: Gen (Ptr Ct7)
gen_c_wordarray_create_nz_u8_arg = gen_c_wordarray_create_u8_arg

abs_wordarray_create_nz_u8_arg :: Ptr Ct7 -> IO Word32
abs_wordarray_create_nz_u8_arg = abs_wordarray_create_u8_arg

rel_wordarray_create_nz_u8_ret :: Maybe (WordArray Word8) -> Ptr Ct8 -> IO Bool
rel_wordarray_create_nz_u8_ret oa oc = do
  Ct8 tag err suc <- peek oc
  if | fromEnum tag == fromEnum tagEnumError  , Nothing     <- oa -> return True
     | fromEnum tag == fromEnum tagEnumSuccess, Just hs_arr <- oa -> do
         let Ct6 _ parr = suc
         rel_wordarray_u8 hs_arr parr
     | otherwise -> return False

rel_wordarray_u8 :: WordArray Word8 -> Ptr (CWordArray_u8) -> IO Bool
rel_wordarray_u8 hs_arr c_arr = do
  CWordArray_u8 len pvalues <- peek c_arr
  arr <- peekArray (fromIntegral len) pvalues
  return $ map fromIntegral (elems hs_arr) == arr


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @wordarray_get_bounded@

prop_corres_wordarray_get_bounded_u8 :: Property
prop_corres_wordarray_get_bounded_u8 = monadicIO $
  forAllM gen_c_wordarray_get_bounded_u8_arg $ \ic -> run $ do
    (arr, idx) <- abs_wordarray_get_bounded_u8_arg ic
    let oa = hs_wordarray_get_bounded @ Word8 arr idx
    oc <- cogent_wordarray_get_bounded_u8 ic
    bracket (return ic)
            (\ic -> do Ct2 parr _ <- peek ic
                       CWordArray_u8 _ pvalues <- peek parr
                       free pvalues
                       free parr)
            (\_ -> corresM' rel_wordarray_get_bounded_u8_ret oa oc)

prop_corres_wordarray_get_bounded_u8' :: Property
prop_corres_wordarray_get_bounded_u8' = monadicIO $
  forAllM gen_c_wordarray_get_bounded_u8_arg' $ \(elems,idx) -> run $ do
    let (arr,idx') = mk_hs_wordarray_get_bounded_u8_arg (elems,idx)
        oa = hs_wordarray_get_bounded @ Word8 arr idx'
    bracket (mk_c_wordarray_get_bounded_u8_arg (elems,idx))
            (\ic -> do Ct2 parr _ <- peek ic
                       free_CWordArray_u8 parr)
            (\ic -> do oc <- cogent_wordarray_get_bounded_u8 ic
                       corresM' rel_wordarray_get_bounded_u8_ret oa oc)

-- NOTE: length can't be 0. Otherwise segfault. / zilinc
gen_c_wordarray_get_bounded_u8_arg :: Gen (Ptr Ct2)
gen_c_wordarray_get_bounded_u8_arg = do
  l <- choose (1, 200) :: Gen CInt
  arr <- gen_CWordArray_u8 (fromIntegral l)
  let parr = unsafeLocalState $ new arr
  idx <- frequency [(1, fmap (+l) $ getPositive <$> (arbitrary :: Gen (Positive CInt))), (3, choose (0, l))]
  return $ unsafeLocalState $ new (Ct2 parr (fromIntegral idx))

gen_CWordArray_u8 :: Int -> Gen CWordArray_u8
gen_CWordArray_u8 l = do
  let parr = unsafeLocalState (mallocArray l) :: Ptr Cu8
  elems <- vector l :: Gen [Cu8]
  unit <- return . unsafeLocalState $ pokeArray parr elems
  return $ unit `seq` CWordArray_u8 (fromIntegral l) parr

gen_c_wordarray_get_bounded_u8_arg' :: Gen ([Word8], Word32)
gen_c_wordarray_get_bounded_u8_arg' = do
  l <- choose (1, 200) :: Gen Int
  elems <- vector l :: Gen [Word8]
  idx <- frequency [(1, fmap (+l) $ getNonNegative <$> arbitrary), (3, choose (0, l-1))]
  return (elems, fromIntegral idx)

mk_c_wordarray_u8 :: [Word8] -> IO (Ptr CWordArray_u8)
mk_c_wordarray_u8 elems = do
  let l = length elems
  pvalues <- newArray (map fromIntegral elems :: [Cu8])
  new $ CWordArray_u8 (fromIntegral l) pvalues

mk_c_wordarray_get_bounded_u8_arg :: ([Word8], Word32) -> IO (Ptr Ct2)
mk_c_wordarray_get_bounded_u8_arg (elems, idx) = do
  parr <- mk_c_wordarray_u8 elems
  new $ Ct2 parr (fromIntegral idx)

mk_hs_wordarray_get_bounded_u8_arg :: ([Word8], Word32) -> (WordArray Word8, Word32)
mk_hs_wordarray_get_bounded_u8_arg (elems, idx) =
  let arr = listWordArray elems
   in (arr, idx)

abs_wordarray_get_bounded_u8_arg :: Ptr Ct2 -> IO (WordArray Word8, Word32)
abs_wordarray_get_bounded_u8_arg ia = do
  Ct2 carr cidx <- peek ia
  arr <- abs_CWordArray_u8 =<< peek carr
  let idx = fromIntegral cidx
  return (arr, idx)

abs_CWordArray_u8 :: CWordArray_u8 -> IO (WordArray Word8)
abs_CWordArray_u8 (CWordArray_u8 len values) = do
  elems <- peekArray (fromIntegral len) values
  return $ listArray (0, fromIntegral len - 1) (map fromIntegral elems)

rel_wordarray_get_bounded_u8_ret :: Maybe Word8 -> Ptr Ct16 -> IO Bool
rel_wordarray_get_bounded_u8_ret oa oc = do
  Ct16 tag err suc <- peek oc
  if | fromEnum tag == fromEnum tagEnumError  , Nothing <- oa -> return True
     | fromEnum tag == fromEnum tagEnumSuccess, Just a  <- oa -> do
         return $ fromIntegral a == suc
     | otherwise -> return False

free_CWordArray_u8 :: Ptr CWordArray_u8 -> IO ()
free_CWordArray_u8 parr = do
  CWordArray_u8 _ pvalues <- peek parr
  free pvalues
  free parr


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @wordarray_put@

prop_corres_wordarray_put_u8 :: Property
prop_corres_wordarray_put_u8 = monadicIO $
  forAllM gen_wordarray_put_u8_arg' $ \args -> run $ do
    let ia = mk_hs_wordarray_put_u8_arg args
        oa = uncurry3 hs_wordarray_put ia
    bracket (mk_c_wordarray_put_u8_arg args)
            (\ic -> do Ct9 parr _ _ <- peek ic
                       free_CWordArray_u8 parr)
            (\ic -> do oc <- cogent_wordarray_put_u8 ic
                       corresM' rel_wordarray_put_u8_ret oa oc)

gen_wordarray_put_u8_arg' :: Gen ([Word8], Word32, Word8)
gen_wordarray_put_u8_arg' = do
  l <- choose (1, 200) :: Gen Word32
  arr <- vector $ fromIntegral l
  idx <- frequency [(1, fmap (+l) $ getNonNegative <$> arbitrary), (3, choose (0, l-1))]
  a <- arbitrary :: Gen Word8
  return (arr, idx, a)

mk_hs_wordarray_put_u8_arg :: ([Word8], Word32, Word8) -> (WordArray Word8, Word32, Word8)
mk_hs_wordarray_put_u8_arg (elems, idx, a) =
  let arr = listWordArray elems
   in (arr, idx, a)

mk_c_wordarray_put_u8_arg :: ([Word8], Word32, Word8) -> IO (Ptr Ct9)
mk_c_wordarray_put_u8_arg (elems, idx, a) = do
  parr <- mk_c_wordarray_u8 elems
  new $ Ct9 parr (fromIntegral idx) (fromIntegral a)

rel_wordarray_put_u8_ret :: Either (WordArray Word8) (WordArray Word8) -> Ptr Ct10 -> IO Bool
rel_wordarray_put_u8_ret oa oc = do
  Ct10 tag err suc <- peek oc
  if | Left  arr <- oa, fromEnum tag == fromEnum tagEnumError   -> rel_wordarray_u8 arr err
     | Right arr <- oa, fromEnum tag == fromEnum tagEnumSuccess -> rel_wordarray_u8 arr suc
     | otherwise -> return False


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @wordarray_set@

prop_corres_wordarray_set_u8 :: Property
prop_corres_wordarray_set_u8 = monadicIO $
  forAllM gen_wordarray_set_u8_arg' $ \args -> run $ do
    let ia = mk_hs_wordarray_set_u8_arg args
        oa = uncurry4 hs_wordarray_set ia
    bracket (mk_c_wordarray_set_u8_arg args)
            (\ic -> do Ct5 parr _ _ _ <- peek ic
                       free_CWordArray_u8 parr)
            (\ic -> do oc <- cogent_wordarray_set_u8 ic
                       corresM' rel_wordarray_u8 oa oc)

gen_wordarray_set_u8_arg' :: Gen ([Word8], Word32, Word32, Word8)
gen_wordarray_set_u8_arg' = do
  l <- choose (1, 200) :: Gen Word32
  arr <- vector $ fromIntegral l
  frm <- choose (0, 250)
  n <- choose (0, 150)
  a <- arbitrary :: Gen Word8
  return (arr, frm, n, a)

mk_hs_wordarray_set_u8_arg :: ([Word8], Word32, Word32, Word8)
                            -> (WordArray Word8, Word32, Word32, Word8)
mk_hs_wordarray_set_u8_arg (arr, frm, n, a) =
  let arr' = listWordArray arr
   in (arr', frm, n, a)

mk_c_wordarray_set_u8_arg :: ([Word8], Word32, Word32, Word8) -> IO (Ptr Ct5)
mk_c_wordarray_set_u8_arg (arr, frm, n, a) = do
  p_arr <- mk_c_wordarray_u8 arr
  new $ Ct5 p_arr (fromIntegral frm) (fromIntegral n) (fromIntegral a)


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @wordarray_copy@

prop_corres_wordarray_copy_u8 :: Property
prop_corres_wordarray_copy_u8 = monadicIO $
  forAllM gen_wordarray_copy_u8_arg' $ \args -> run $ do
    let ia = mk_hs_wordarray_copy_u8_arg args
        oa = uncurry5 hs_wordarray_copy ia
    bracket (mk_c_wordarray_copy_u8_arg args)
            (\ic -> do Ct1 pdst psrc _ _ _ <- peek ic
                       free_CWordArray_u8 pdst
                       free_CWordArray_u8 psrc)
            (\ic -> do oc <- cogent_wordarray_copy_u8 ic
                       corresM' rel_wordarray_u8 oa oc)

gen_wordarray_copy_u8_arg' :: Gen ([Word8], [Word8], Word32, Word32, Word32)
gen_wordarray_copy_u8_arg' = do
  l_dst <- choose (1, 200) :: Gen Word32
  l_src <- choose (1, 200) :: Gen Word32
  dst <- vector $ fromIntegral l_dst
  src <- vector $ fromIntegral l_src
  idx_dst <- choose (0, 199)
  idx_src <- choose (0, 199)
  len <- choose (0, 99)
  return (dst, src, idx_dst, idx_src, len)

mk_hs_wordarray_copy_u8_arg :: ([Word8], [Word8], Word32, Word32, Word32)
                            -> (WordArray Word8, WordArray Word8, Word32, Word32, Word32)
mk_hs_wordarray_copy_u8_arg (dst, src, idx_dst, idx_src, len) =
  let arr_dst = listWordArray dst
      arr_src = listWordArray src
   in (arr_dst, arr_src, idx_dst, idx_src, len)

mk_c_wordarray_copy_u8_arg :: ([Word8], [Word8], Word32, Word32, Word32) -> IO (Ptr Ct1)
mk_c_wordarray_copy_u8_arg (dst, src, idx_dst, idx_src, len) = do
  p_dst <- mk_c_wordarray_u8 dst
  p_src <- mk_c_wordarray_u8 src
  new $ Ct1 p_dst p_src (fromIntegral idx_dst) (fromIntegral idx_src) (fromIntegral len)


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @wordarray_modify@

prop_corres_wordarray_modify_u8 :: Property
prop_corres_wordarray_modify_u8 = monadicIO $
  forAllM gen_wordarray_modify_u8_arg' $ \args -> run $ do
    let ia = mk_hs_wordarray_modify_u8_arg args
        oa = uncurry5 hs_wordarray_modify ia
    bracket (mk_c_wordarray_modify_u8_arg args)
            (\ic -> do Ct14 parr _ _ _ _ <- peek ic
                       free_CWordArray_u8 parr)
            (\ic -> do oc <- cogent_wordarray_modify_u8 ic
                       corresM' rel_wordarray_modify_u8_ret oa oc)

gen_wordarray_modify_u8_arg' :: Gen ([Word8], Word32, Int, Word8, Bool)
gen_wordarray_modify_u8_arg' = do
  l <- choose (1, 200) :: Gen Word32
  arr <- vector $ fromIntegral l
  idx <- frequency [(1, fmap (+l) $ getNonNegative <$> arbitrary), (3, choose (0, l-1))]
  f <- elements [1]  -- funcEnum
  acc <- arbitrary
  obsv <- arbitrary
  return (arr, idx, f, acc, obsv)

mk_hs_wordarray_modify_u8_arg :: ([Word8], Word32, Int, Word8, Bool)
                              -> (WordArray Word8, Word32, (Word8, Word8, Bool) -> (Word8, Word8), Word8, Bool) 
mk_hs_wordarray_modify_u8_arg (elems, idx, f, acc, obsv) =
  let arr = listWordArray elems
      f' = case f of 1 -> hs_modify_body_f
   in (arr, idx, f', acc, obsv)

mk_c_wordarray_modify_u8_arg :: ([Word8], Word32, Int, Word8, Bool)
                             -> IO (Ptr Ct14)
mk_c_wordarray_modify_u8_arg (elems, idx, f, acc, obsv) = do
  parr <- mk_c_wordarray_u8 elems
  new $ Ct14 parr (fromIntegral idx) (toEnum f) (fromIntegral acc) (mk_c_bool obsv)

mk_c_bool :: Bool -> Cbool_t
mk_c_bool b = Cbool_t $ fromIntegral $ if b then 1 else 0

rel_wordarray_modify_u8_ret :: (WordArray Word8, Word8) -> Ptr Ct15 -> IO Bool
rel_wordarray_modify_u8_ret (hs_arr, hs_acc) oc = do
  Ct15 c_arr c_acc <- peek oc
  barr <- rel_wordarray_u8 hs_arr c_arr
  return $ barr && (fromIntegral hs_acc == c_acc)


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @wordarray_map@

prop_corres_wordarray_map_u8 :: Property
prop_corres_wordarray_map_u8 = monadicIO $
  forAllM gen_wordarray_map_u8_arg' $ \args -> run $ do
    let ia = mk_hs_wordarray_map_u8_arg args
        oa = uncurry hs_wordarray_map ia
    bracket (mk_c_wordarray_map_u8_arg args)
            (\ic -> do Ct4 parr _ <- peek ic
                       free_CWordArray_u8 parr)
            (\ic -> do oc <- cogent_wordarray_map_u8 ic
                       corresM' rel_wordarray_u8 oa oc)

gen_wordarray_map_u8_arg' :: Gen ([Word8], Int)
gen_wordarray_map_u8_arg' = do
  l <- choose (1, 200) :: Gen Word32
  arr <- vector $ fromIntegral l
  f <- elements [0, 1]  -- funcEnum
  return (arr, f)

mk_hs_wordarray_map_u8_arg :: ([Word8], Int) -> (WordArray Word8, Word8 -> Word8)
mk_hs_wordarray_map_u8_arg (elems, f) =
  let arr = listWordArray elems
      f' = case f of 0 -> hs_map_body_f
                     1 -> hs_map_body_g
   in (arr, f')

mk_c_wordarray_map_u8_arg :: ([Word8], Int) -> IO (Ptr Ct4)
mk_c_wordarray_map_u8_arg (elems, f) = do
  parr <- mk_c_wordarray_u8 elems
  new $ Ct4 parr (toEnum f)



-- /////////////////////////////////////////////////////////////////////////////
--
-- * Properties atop the Haskell spec.

prop_wordarray_get_put = 
  forAll (choose (1, 200)) $ \len ->
  forAll (vector len :: Gen [Word8]) $ \elems ->
  forAll (choose (0, 2 * fromIntegral len)) $ \idx ->
  forAll (arbitrary :: Gen Word8) $ \val ->
    let arr = listWordArray elems
        r = hs_wordarray_put arr idx val
     in if | idx < fromIntegral len, Right arr' <- r ->
               let Just val' = hs_wordarray_get_bounded arr' idx
                in val == val'
           | idx >= fromIntegral len, Left arr' <- r -> 
               arr' == arr
           | otherwise -> False


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Helper functions

listWordArray :: [a] -> WordArray a
listWordArray arr = listArray (0, fromIntegral (length arr - 1)) arr


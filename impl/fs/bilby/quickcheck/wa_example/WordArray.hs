{- LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PartialTypeSignatures #-}
{- LANGUAGE RebindableSyntax #-}
{- LANGUAGE ImplicitPrelude #-}
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
-- import Control.Monad.State
import Control.Monad (void)
import Control.Monad.Trans.Class (lift)
import Data.Array.IArray
import Data.Array.IO hiding (newArray)
import Data.Either.Extra  -- extra-1.6
-- import Data.Function
import Data.Ix
-- import Data.Set as S
import Foreign hiding (void)
import Foreign.C.String hiding (CString)
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc
import Foreign.Marshal.Unsafe (unsafeLocalState)
import Foreign.Ptr
import Foreign.Storable
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
-- import qualified FFI as FFI
-- import Wa_Shallow_Desugar 
-- import WordArray
import Util

import Debug.Trace

{- |
To run the REPL: 
> cabal v1-repl wa-example --ghc-options=" wa_example/build/wa.o"
-}


-- * Haskell specification

-- | The Haskell type for wordarrays
type WordArray e = Array Word32 e

hs_wordarray_create :: Word32 -> CogentMonad (Maybe (WordArray e))
hs_wordarray_create 0 = (return $ Nothing)
hs_wordarray_create l = (return $ Just (array (0, l-1) []))  -- elements will be undefined
                          <|>
                        (return $ Nothing)

hs_wordarray_create_nz :: (Integral e) => Word32 -> CogentMonad (Maybe (WordArray e))
hs_wordarray_create_nz 0 = (return $ Nothing)
hs_wordarray_create_nz l = (return $ Just (array (0, l-1) [(i,v) | i <- [0..l-1], v <- [0]]))
                             <|> 
                           (return $ Nothing)

hs_wordarray_free :: WordArray e -> CogentMonad ()
hs_wordarray_free _ = return ()

hs_wordarray_get_bounded :: Integral e => WordArray e -> Word32 -> CogentMonad (Maybe e)
hs_wordarray_get_bounded xs i = return $
    if i `is_inbound` xs then Just $ xs ! i
                         else Nothing

is_inbound :: Word32 -> WordArray e -> Bool
is_inbound i xs = case bounds xs of (l,u) -> l <= i && i <= u

hs_wordarray_modify :: WordArray e
                    -> Word32
                    -> ((e, acc, obsv) -> (e, acc))
                    -> acc
                    -> obsv
                    -> CogentMonad (WordArray e, acc)
hs_wordarray_modify xs i f acc obsv
  | i `is_inbound` xs = 
      let (e',acc') = f (xs ! i, acc, obsv)
       in return (xs // [(i, e')], acc')
  | otherwise = return (xs, acc)                          

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

hs_wordarray_put :: WordArray e -> Word32 -> e -> CogentMonad (Either (WordArray e) (WordArray e))
hs_wordarray_put xs i _ | not (i `is_inbound` xs) = return $ Left xs
hs_wordarray_put xs i a = return $ Right $ xs // [(i,a)]

hs_wordarray_length :: WordArray e -> CogentMonad Word32
hs_wordarray_length = return . fromIntegral . length

hs_wordarray_clone :: WordArray e -> CogentMonad (Maybe (WordArray e))
hs_wordarray_clone xs = (return $ Just xs) <|> (return Nothing)

hs_wordarray_map :: WordArray e
                 -> (e -> e)
                 -> CogentMonad (WordArray e)
hs_wordarray_map xs f = return $ fmap f xs

hs_map_body_f = (+1)
hs_map_body_g = (*2)

-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @wordarray_create@.

prop_corres_wordarray_create_u8 :: Property
prop_corres_wordarray_create_u8 = monadicIO $
  forAllM gen_c_wordarray_create_u8_arg $ \ic -> run $ do
    oa <- hs_wordarray_create @ Word8 <$> abs_wordarray_create_u8_arg ic
    bracket (cogent_wordarray_create_u8 ic)
            (\oc -> do Ct7 tag err suc <- peek oc
                       if | fromEnum tag == fromEnum tagEnumError -> return ()
                          | fromEnum tag == fromEnum tagEnumSuccess -> do 
                              psuc <- new suc
                              cogent_wordarray_free_u8 psuc
                              return ()
                          | otherwise -> fail "impossible")
            (\oc -> corresM rel_wordarray_create_u8_ret oa oc)

gen_c_wordarray_create_u8_arg :: Gen (Ptr Ct6)
gen_c_wordarray_create_u8_arg = do
  let p1 = unsafeLocalState pDummyCSysState
  ct6 <- Ct6 p1 <$> choose (0, 4095)
  return $ unsafeLocalState $ new ct6

abs_wordarray_create_u8_arg :: Ptr Ct6 -> IO Word32
abs_wordarray_create_u8_arg ia = do
  Ct6 _ p2 <- peek ia
  return $ fromIntegral p2

rel_wordarray_create_u8_ret :: Maybe (WordArray Word8) -> Ptr Ct7 -> IO Bool
rel_wordarray_create_u8_ret oa oc = do
  Ct7 tag err suc <- peek oc
  if | fromEnum tag == fromEnum tagEnumError  , Nothing <- oa -> return True
     | fromEnum tag == fromEnum tagEnumSuccess, Just _  <- oa -> return True  -- nothing that we can check about the values of the wordarrays
     | otherwise -> return False


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @wordarray_create_nz@

prop_corres_wordarray_create_nz_u8 :: Property
prop_corres_wordarray_create_nz_u8 = monadicIO $
  forAllM gen_c_wordarray_create_nz_u8_arg $ \ic -> run $ do
    oa <- hs_wordarray_create_nz @ Word8 <$> abs_wordarray_create_nz_u8_arg ic
    bracket (cogent_wordarray_create_nz_u8 ic)
            (\oc -> do Ct7 tag err suc <- peek oc
                       if | fromEnum tag == fromEnum tagEnumError -> return ()
                          | fromEnum tag == fromEnum tagEnumSuccess -> do 
                              psuc <- new suc
                              cogent_wordarray_free_u8 psuc
                              return ()
                          | otherwise -> fail "impossible")
            (\oc -> corresM rel_wordarray_create_nz_u8_ret oa oc)

gen_c_wordarray_create_nz_u8_arg :: Gen (Ptr Ct6)
gen_c_wordarray_create_nz_u8_arg = gen_c_wordarray_create_u8_arg

abs_wordarray_create_nz_u8_arg :: Ptr Ct6 -> IO Word32
abs_wordarray_create_nz_u8_arg = abs_wordarray_create_u8_arg

rel_wordarray_create_nz_u8_ret :: Maybe (WordArray Word8) -> Ptr Ct7 -> IO Bool
rel_wordarray_create_nz_u8_ret oa oc = do
  Ct7 tag err suc <- peek oc
  if | fromEnum tag == fromEnum tagEnumError  , Nothing     <- oa -> return True
     | fromEnum tag == fromEnum tagEnumSuccess, Just hs_arr <- oa -> do
         let Ct5 _ parr = suc
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
            (\_ -> corresM rel_wordarray_get_bounded_u8_ret oa oc)

prop_corres_wordarray_get_bounded_u8' :: Property
prop_corres_wordarray_get_bounded_u8' = monadicIO $
  forAllM gen_c_wordarray_get_bounded_u8_arg' $ \(elems,idx) -> run $ do
    let (arr,idx') = mk_hs_wordarray_get_bounded_u8_arg (elems,idx)
        oa = hs_wordarray_get_bounded @ Word8 arr idx'
    bracket (mk_c_wordarray_get_bounded_u8_arg (elems,idx))
            (\ic -> do Ct2 parr _ <- peek ic
                       CWordArray_u8 _ pvalues <- peek parr
                       free pvalues
                       free parr)
            (\ic -> do oc <- cogent_wordarray_get_bounded_u8 ic
                       corresM rel_wordarray_get_bounded_u8_ret oa oc)

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
  let arr = listArray (0, fromIntegral (length elems) - 1) elems
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

rel_wordarray_get_bounded_u8_ret :: Maybe Word8 -> Ptr Ct15 -> IO Bool
rel_wordarray_get_bounded_u8_ret oa oc = do
  Ct15 tag err suc <- peek oc
  if | fromEnum tag == fromEnum tagEnumError  , Nothing <- oa -> return True
     | fromEnum tag == fromEnum tagEnumSuccess, Just a  <- oa -> do
         return $ fromIntegral a == suc
     | otherwise -> return False


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @wordarray_put@

prop_corres_wordarray_put_u8 :: Property
prop_corres_wordarray_put_u8 = monadicIO $
  forAllM gen_wordarray_put_u8_arg' $ \args -> run $ do
    let (arr,idx,a) = mk_hs_wordarray_put_u8_arg args
        oa = hs_wordarray_put @ Word8 arr idx a
    bracket (mk_c_wordarray_put_u8_arg args)
            (\ic -> do Ct8 parr _ _ <- peek ic
                       CWordArray_u8 _ pvalues <- peek parr
                       free pvalues
                       free parr)
            (\ic -> do oc <- cogent_wordarray_put_u8 ic
                       corresM rel_wordarray_put_u8_ret oa oc)

gen_wordarray_put_u8_arg' :: Gen ([Word8], Word32, Word8)
gen_wordarray_put_u8_arg' = do
  l <- choose (1, 200) :: Gen Word32
  arr <- vector $ fromIntegral l
  idx <- frequency [(1, fmap (+l) $ getNonNegative <$> arbitrary), (3, choose (0, l-1))]
  a <- arbitrary :: Gen Word8
  return (arr, idx, a)

mk_hs_wordarray_put_u8_arg :: ([Word8], Word32, Word8) -> (WordArray Word8, Word32, Word8)
mk_hs_wordarray_put_u8_arg (elems, idx, a) =
  let arr = listArray (0, fromIntegral (length elems) - 1) elems
   in (arr, idx, a)

mk_c_wordarray_put_u8_arg :: ([Word8], Word32, Word8) -> IO (Ptr Ct8)
mk_c_wordarray_put_u8_arg (elems, idx, a) = do
  parr <- mk_c_wordarray_u8 elems
  new $ Ct8 parr (fromIntegral idx) (fromIntegral a)

rel_wordarray_put_u8_ret :: Either (WordArray Word8) (WordArray Word8) -> Ptr Ct9 -> IO Bool
rel_wordarray_put_u8_ret oa oc = do
  Ct9 tag err suc <- peek oc
  if | Left  arr <- oa, fromEnum tag == fromEnum tagEnumError   -> rel_wordarray_u8 arr err
     | Right arr <- oa, fromEnum tag == fromEnum tagEnumSuccess -> rel_wordarray_u8 arr suc
     | otherwise -> return False


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @wordarray_modify@

prop_corres_wordarray_modify_u8 :: Property
prop_corres_wordarray_modify_u8 = monadicIO $
  forAllM gen_wordarray_modify_u8_arg' $ \args -> run $ do
    let (arr,idx,f,acc,obsv) = mk_hs_wordarray_modify_u8_arg args
        oa = hs_wordarray_modify arr idx f acc obsv
    bracket (mk_c_wordarray_modify_u8_arg args)
            (\ic -> do Ct13 parr _ _ _ _ <- peek ic
                       CWordArray_u8 _ pvalues <- peek parr
                       free pvalues
                       free parr)
            (\ic -> do oc <- cogent_wordarray_modify_u8 ic
                       corresM rel_wordarray_modify_u8_ret oa oc)

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
  let arr = listArray (0, fromIntegral (length elems) - 1) elems
      f' = case f of 1 -> hs_modify_body_f
   in (arr, idx, f', acc, obsv)

mk_c_wordarray_modify_u8_arg :: ([Word8], Word32, Int, Word8, Bool)
                             -> IO (Ptr Ct13)
mk_c_wordarray_modify_u8_arg (elems, idx, f, acc, obsv) = do
  parr <- mk_c_wordarray_u8 elems
  new $ Ct13 parr (fromIntegral idx) (toEnum f) (fromIntegral acc) (mk_c_bool obsv)

mk_c_bool :: Bool -> Cbool_t
mk_c_bool b = Cbool_t $ fromIntegral $ if b then 1 else 0

rel_wordarray_modify_u8_ret :: (WordArray Word8, Word8) -> Ptr Ct14 -> IO Bool
rel_wordarray_modify_u8_ret (hs_arr, hs_acc) oc = do
  Ct14 c_arr c_acc <- peek oc
  barr <- rel_wordarray_u8 hs_arr c_arr
  return $ barr && (fromIntegral hs_acc == c_acc)

-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @wordarray_map@

prop_corres_wordarray_map_u8 :: Property
prop_corres_wordarray_map_u8 = monadicIO $
  forAllM gen_wordarray_map_u8_arg' $ \args -> run $ do
    let (arr,f) = mk_hs_wordarray_map_u8_arg args
        oa = hs_wordarray_map arr f
    bracket (mk_c_wordarray_map_u8_arg args)
            (\ic -> do Ct4 parr _ <- peek ic
                       CWordArray_u8 _ pvalues <- peek parr
                       free pvalues
                       free parr)
            (\ic -> do oc <- cogent_wordarray_map_u8 ic
                       corresM rel_wordarray_u8 oa oc)

gen_wordarray_map_u8_arg' :: Gen ([Word8], Int)
gen_wordarray_map_u8_arg' = do
  l <- choose (1, 200) :: Gen Word32
  arr <- vector $ fromIntegral l
  f <- elements [0, 1]  -- funcEnum
  return (arr, f)

mk_hs_wordarray_map_u8_arg :: ([Word8], Int) -> (WordArray Word8, Word8 -> Word8)
mk_hs_wordarray_map_u8_arg (elems, f) =
  let arr = listArray (0, fromIntegral (length elems) - 1) elems
      f' = case f of 0 -> hs_map_body_f
                     1 -> hs_map_body_g
   in (arr, f')

mk_c_wordarray_map_u8_arg :: ([Word8], Int) -> IO (Ptr Ct4)
mk_c_wordarray_map_u8_arg (elems, f) = do
  parr <- mk_c_wordarray_u8 elems
  new $ Ct4 parr (toEnum f)


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Main function

return []
main = $quickCheckAll

-- -- /////////////////////////////////////////////////////////////////////////////

-- prop_wordarray_get_put = 
--   forAll (listOf (arbitrary :: Gen Word8)) $ \arr ->
--     forAll (elements [0 .. 2 * fromIntegral (length arr)]) $ \idx ->
--       forAll (arbitrary :: Gen Word8) $ \val ->
--         if idx < fromIntegral (length arr)
--            then let Right arr' = hs_wordarray_put arr idx val in hs_wordarray_get arr' idx === val
--            else Left arr === hs_wordarray_put arr idx val
-- 
-- -- This is useless, but looks really weird
-- prop_wordarray_get_put_c = monadicIO $
--   forAllM (listOf (arbitrary :: Gen Word8)) $ \arr ->
--     forAllM (elements [0 .. 2 * fromIntegral (length arr)]) $ \idx ->
--       forAllM (arbitrary :: Gen Word8) $ \val -> run $ do
--         p_arr <- new =<< toC_wordarray_u8 arr
--         c_idx <- return $ fromIntegral idx
--         c_val <- return $ fromIntegral val
--         Ct7 tag error success <- cogent_wordarray_put_u8 (Ct6 p_arr c_idx c_val)
--         let p_arr' = if fromEnum tag == fromEnum tagEnumError
--                        then error else success
--         ret <- cogent_wordarray_get_u8 (Ct2 p_arr' idx)
--         if idx < fromIntegral (length arr)
--            then return $ ret === c_val
--            else return $ p_arr' === p_arr
-- 



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
hs_wordarray_create l = (return $ Just (array (0, l-1) []))  -- elements will be undefined
                          <|>
                        (return $ Nothing)

hs_wordarray_create_nz :: (Integral e) => Word32 -> CogentMonad (Maybe (WordArray e))
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

hs_wordarray_put :: WordArray e -> Word32 -> e -> CogentMonad (Either (WordArray e) (WordArray e))
hs_wordarray_put xs i _ | not (i `is_inbound` xs) = return $ Left xs
hs_wordarray_put xs i a = return $ Right $ xs // [(i,a)]

hs_wordarray_length :: WordArray e -> CogentMonad Word32
hs_wordarray_length = return . fromIntegral . length

hs_wordarray_clone :: WordArray e -> CogentMonad (Maybe (WordArray e))
hs_wordarray_clone xs = (return $ Just xs) <|> (return Nothing)

hs_wordarray_map :: WordArray e
                 -> Word32
                 -> Word32
                 -> ((e, acc, obsv) -> (e, acc, Maybe rbrk))
                 -> acc
                 -> obsv
                 -> CogentMonad (WordArray e, acc, Maybe rbrk)
hs_wordarray_map xs frm to f acc obsv = return $
  let (l, u) = bounds xs
      frm' = max l frm
      to'  = min u to
   in foldl (\r i -> case r of (xs',acc',Nothing) -> let (e',acc'',b') = f (xs' ! i, acc', obsv)
                                                      in (xs' // [(i, e')], acc'', b')
                               _ -> r) (xs, acc, Nothing) [frm' .. to']


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @wordarray_create@.

prop_wordarray_create_u8_corres :: Property
prop_wordarray_create_u8_corres = monadicIO $
  forAllM gen_c_wordarray_create_u8_arg $ \ic -> run $ do
    oa <- hs_wordarray_create @ Word8 <$> abs_wordarray_create_u8_arg ic
    bracket (cogent_wordarray_create_u8 ic)
            (\oc -> do Ct5 tag err suc <- peek oc
                       if | fromEnum tag == fromEnum tagEnumError -> return ()
                          | fromEnum tag == fromEnum tagEnumSuccess -> do 
                              psuc <- new suc
                              cogent_wordarray_free_u8 psuc
                              return ()
                          | otherwise -> fail "impossible")
            (\oc -> corresM wordarray_create_u8_ret_corres oa oc)

gen_c_wordarray_create_u8_arg :: Gen (Ptr Ct4)
gen_c_wordarray_create_u8_arg = do
  let p1 = unsafeLocalState pDummyCSysState
  ct4 <- Ct4 p1 <$> choose (0, 4095)
  return $ unsafeLocalState $ new ct4

abs_wordarray_create_u8_arg :: Ptr Ct4 -> IO Word32
abs_wordarray_create_u8_arg ia = do
  Ct4 _ p2 <- peek ia
  return $ fromIntegral p2

wordarray_create_u8_ret_corres :: Maybe (WordArray Word8) -> Ptr Ct5 -> IO Bool
wordarray_create_u8_ret_corres oa oc = do
  Ct5 tag err suc <- peek oc
  if | fromEnum tag == fromEnum tagEnumError, Nothing <- oa -> return True
     | fromEnum tag == fromEnum tagEnumSuccess, Just wa <- oa -> return True  -- nothing that we can check about the values of the wordarrays
     | otherwise -> return False


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @wordarray_create_nz@

prop_wordarray_create_nz_u8_corres :: Property
prop_wordarray_create_nz_u8_corres = monadicIO $
  forAllM gen_c_wordarray_create_nz_u8_arg $ \ic -> run $ do
    oa <- hs_wordarray_create_nz @ Word8 <$> abs_wordarray_create_nz_u8_arg ic
    bracket (cogent_wordarray_create_nz_u8 ic)
            (\oc -> do Ct5 tag err suc <- peek oc
                       if | fromEnum tag == fromEnum tagEnumError -> return ()
                          | fromEnum tag == fromEnum tagEnumSuccess -> do 
                              psuc <- new suc
                              cogent_wordarray_free_u8 psuc
                              return ()
                          | otherwise -> fail "impossible")
            (\oc -> corresM wordarray_create_nz_u8_ret_corres oa oc)

gen_c_wordarray_create_nz_u8_arg :: Gen (Ptr Ct4)
gen_c_wordarray_create_nz_u8_arg = gen_c_wordarray_create_u8_arg

abs_wordarray_create_nz_u8_arg :: Ptr Ct4 -> IO Word32
abs_wordarray_create_nz_u8_arg = abs_wordarray_create_u8_arg

wordarray_create_nz_u8_ret_corres :: Maybe (WordArray Word8) -> Ptr Ct5 -> IO Bool
wordarray_create_nz_u8_ret_corres oa oc = do
  Ct5 tag err suc <- peek oc
  if | fromEnum tag == fromEnum tagEnumError  , Nothing <- oa -> return True
     | fromEnum tag == fromEnum tagEnumSuccess, Just wa <- oa -> do
         let Ct3 _ p = suc
         CWordArray_u8 l v <- peek p
         arr <- peekArray (fromIntegral l) v
         return $ map fromIntegral (elems wa) == arr
     | otherwise -> return False


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @wordarray_get_bounded@

prop_wordarray_get_bounded_u8_corres :: Property
prop_wordarray_get_bounded_u8_corres = monadicIO $
  forAllM gen_c_wordarray_get_bounded_u8_arg $ \ic -> run $ do
    (arr, idx) <- abs_wordarray_get_bounded_u8_arg ic
    let oa = hs_wordarray_get_bounded @ Word8 arr idx
    oc <- cogent_wordarray_get_bounded_u8 ic
    bracket (return ic)
            (\ic -> do Ct2 parr _ <- peek ic
                       free parr)
            (\_ -> corresM wordarray_get_bounded_u8_ret_corres oa oc)

prop_wordarray_get_bounded_u8_corres' :: Property
prop_wordarray_get_bounded_u8_corres' = monadicIO $
  forAllM gen_c_wordarray_get_bounded_u8_arg' $ \(l,elems,idx) -> run $ do
    let (arr,idx') = mk_hs_wordarray_get_bounded_u8_arg (l,elems,idx)
        oa = hs_wordarray_get_bounded @ Word8 arr idx'
    bracket (mk_c_wordarray_get_bounded_u8_arg (l,elems,idx))
            (\ic -> do Ct2 parr _ <- peek ic
                       free parr)
            (\ic -> do oc <- cogent_wordarray_get_bounded_u8 ic
                       corresM wordarray_get_bounded_u8_ret_corres oa oc)

gen_c_wordarray_get_bounded_u8_arg :: Gen (Ptr Ct2)
gen_c_wordarray_get_bounded_u8_arg = do
  l <- choose (0, 200) :: Gen CInt
  arr <- gen_CWordArray_u8 (fromIntegral l)
  let parr = unsafeLocalState $ new arr
  idx <- frequency [(1, fmap (+l) $ getPositive <$> (arbitrary :: Gen (Positive CInt))), (3, choose (0, l))]
  return $ unsafeLocalState $ new (Ct2 parr (fromIntegral idx))

gen_CWordArray_u8 :: Int -> Gen CWordArray_u8
gen_CWordArray_u8 l = do
  let parr = unsafeLocalState (mallocArray l) :: Ptr Cu8
  elems <- vector l :: Gen [Cu8]
  unit <- return . unsafeLocalState $ pokeArray parr elems
  -- let elems' = unsafeLocalState $ peekArray l parr
  -- trace ("gen_elems = " ++ show elems ++ "\ngen_elem' = " ++ ( unit `seq` show elems')) $ 
  return $ unit `seq` CWordArray_u8 (fromIntegral l) parr

gen_c_wordarray_get_bounded_u8_arg' :: Gen (Int, [Word8], Word32)
gen_c_wordarray_get_bounded_u8_arg' = do
  l <- choose (0, 200) :: Gen Int
  elems <- vector l :: Gen [Word8]
  idx <- frequency [(1, fmap (+l) $ getPositive <$> arbitrary), (3, choose (0, l))]
  return (l, elems, fromIntegral idx)

mk_c_wordarray_get_bounded_u8_arg :: (Int, [Word8], Word32) -> IO (Ptr Ct2)
mk_c_wordarray_get_bounded_u8_arg (l, elems, idx) = do
  pvalues <- newArray (map fromIntegral elems)
  let arr = CWordArray_u8 (fromIntegral l) pvalues
  parr <- new arr
  new $ Ct2 parr (fromIntegral idx)

mk_hs_wordarray_get_bounded_u8_arg :: (Int, [Word8], Word32) -> (WordArray Word8, Word32)
mk_hs_wordarray_get_bounded_u8_arg (l, elems, idx) =
  let arr = array (0, fromIntegral l - 1) $ zip [0..] elems
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
  putStrLn $ "elems = " ++ show elems
  return $ array (0, fromIntegral len - 1) $ zip [0..] (map fromIntegral elems)

wordarray_get_bounded_u8_ret_corres :: Maybe Word8 -> Ptr Ct21 -> IO Bool
wordarray_get_bounded_u8_ret_corres oa oc = do
  Ct21 tag err suc <- peek oc
  if | fromEnum tag == fromEnum tagEnumError  , Nothing <- oa -> return True
     | fromEnum tag == fromEnum tagEnumSuccess, Just a  <- oa -> do
         return $ fromIntegral a == suc
     | otherwise -> return False








-- prop_wordarray_get_u8_corres = monadicIO $
--   forAllM gen_wordarray_get_u8_arg $ \arg -> run $ do
--     rc <- cogent_wordarray_get_u8 =<< toC_wordarray_get_u8_arg arg
--     ra <- return $ uncurry hs_wordarray_get (abs_wordarray_get_u8_arg arg)
--     return $ corres' wordarray_get_u8_corres ra rc
-- 
-- gen_wordarray_get_u8_arg :: Gen (R15 (WordArray Word8) Word32)
-- gen_wordarray_get_u8_arg = do
--   arr <- listOf (arbitrary :: Gen Word8)
--   idx <- elements [0 .. 2 * fromIntegral (length arr)]
--   return $ R15 arr idx
-- 
-- toC_wordarray_get_u8_arg :: R15 (WordArray Word8) Word32 -> IO Ct2
-- toC_wordarray_get_u8_arg (R15 p1 p2) = Ct2 <$> (new =<< toC_wordarray_u8 p1) <*> (pure $ fromIntegral p2)
-- 
-- abs_wordarray_get_u8_arg :: R15 (WordArray Word8) Word32 -> (WordArray Word8, Word32)
-- abs_wordarray_get_u8_arg (R15 p1 p2) = (p1, p2)
-- 
-- wordarray_get_u8_corres :: Word8 -> Cu8 -> Bool
-- wordarray_get_u8_corres ra rc = fromIntegral ra == fromIntegral rc
-- 
-- cogent_wordarray_get_u8 :: Ct2 -> IO Cu8
-- cogent_wordarray_get_u8 = (c_wordarray_get_u8 =<<) . new

-- hs_wordarray_get :: Integral a => WordArray a -> Word32 -> a
-- hs_wordarray_get xs i | is_inbound xs i = xs !! (fromIntegral i)
--                       | otherwise = 0

-- /////////////////////////////////////////////////////////////////////////////
-- instantiated with [U8, U8, Bool]

-- prop_wordarray_modify_u8_corres = monadicIO $
--   forAllM gen_wordarray_modify_u8_arg $ \arg -> run $ do
--     rc <- cogent_wordarray_modify_u8 =<< toC_wordarray_modify_u8_arg arg
--     let (arr,idx,f,acc,obsv) = abs_wordarray_modify_u8_arg arg
--     ra <- return $ hs_wordarray_modify arr idx f acc obsv
--     corresM' wordarray_modify_u8_corres ra rc
-- 
-- gen_wordarray_modify_u8_arg :: Gen (R3 (WordArray Word8) Word32 FuncEnum Word8 Bool)
-- gen_wordarray_modify_u8_arg = do
--   arr  <- listOf (arbitrary :: Gen Word8)
--   idx  <- elements [0 .. 2 * fromIntegral (length arr)]
--   f    <- elements [funEnumModifyBodyF]
--   acc  <- arbitrary
--   obsv <- arbitrary
--   return $ R3 arr idx f acc obsv
-- 

-- 
-- toC_wordarray_modify_u8_arg :: R3 (WordArray Word8) Word32 FuncEnum Word8 Bool -> IO Ct19
-- toC_wordarray_modify_u8_arg (R3 {..}) = do
--   c_arr  <- new =<< toC_wordarray_u8 arr
--   c_idx  <- return $ fromIntegral idx
--   c_f    <- return $ toEnum $ fromEnum f
--   c_acc  <- return $ fromIntegral acc
--   c_obsv <- return $ if obsv then const_true else const_false
--   return $ Ct19 c_arr c_idx c_f c_acc c_obsv
-- 
-- abs_wordarray_modify_u8_arg :: R3 (WordArray Word8) Word32 FuncEnum Word8 Bool
--                             -> (WordArray Word8, Word32, (Word8, Word8, Bool) -> (Word8, Word8), Word8, Bool)
-- abs_wordarray_modify_u8_arg (R3 {..}) = 
--   let f' = if | fromEnum f == fromEnum funEnumModifyBodyF -> hs_modify_body_f
--       f'' (a1,a2,a3) = f' a1 a2 a3
--    in (arr, idx, f'', acc, obsv)
-- 
-- wordarray_modify_u8_corres :: (WordArray Word8, Word8) -> Ct20 -> IO Bool
-- wordarray_modify_u8_corres (hs_arr, hs_acc) (Ct20 p_arr acc) = do 
--   b1 <- wordarray_u8_corres hs_arr =<< peek p_arr
--   b2 <- return $ hs_acc == fromIntegral acc
--   return $ b1 && b2
-- 
-- cogent_wordarray_modify_u8 :: Ct19 -> IO Ct20
-- cogent_wordarray_modify_u8 arg = peek =<< c_wordarray_modify_u8 =<< new arg
-- 

-- -- /////////////////////////////////////////////////////////////////////////////
-- 
-- prop_wordarray_put_u8_corres = monadicIO $
--   forAllM gen_wordarray_put_u8_arg $ \arg -> run $ do
--     rc <- cogent_wordarray_put_u8 =<< toC_wordarray_put_u8_arg arg
--     let (arr,idx,val) = abs_wordarray_put_u8_arg arg
--     ra <- return $ hs_wordarray_put arr idx val
--     corresM' wordarray_put_u8_corres ra rc
-- 
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
-- gen_wordarray_put_u8_arg :: Gen (R4 (WordArray Word8) Word32 Word8)
-- gen_wordarray_put_u8_arg = do
--   arr <- listOf (arbitrary :: Gen Word8)
--   idx <- elements [0 .. 2 * fromIntegral (length arr)]
--   val <- arbitrary
--   return $ R4 arr idx val
-- 
-- toC_wordarray_put_u8_arg :: R4 (WordArray Word8) Word32 Word8 -> IO Ct6
-- toC_wordarray_put_u8_arg (R4 {..}) = do
--   p_arr <- new =<< toC_wordarray_u8 arr
--   c_idx <- return $ fromIntegral idx
--   c_val <- return $ fromIntegral val
--   return $ Ct6 p_arr c_idx c_val
-- 
-- abs_wordarray_put_u8_arg :: R4 (WordArray Word8) Word32 Word8 -> (WordArray Word8, Word32, Word8)
-- abs_wordarray_put_u8_arg (R4 {..}) = (arr, idx, val)
-- 
-- wordarray_put_u8_corres :: (Either (WordArray Word8) (WordArray Word8)) -> Ct7 -> IO Bool
-- wordarray_put_u8_corres (Left arr) (Ct7 tag error _) | fromEnum tag == fromEnum tagEnumError = 
--   wordarray_u8_corres arr =<< peek error
-- wordarray_put_u8_corres (Right arr) (Ct7 tag _ success) | fromEnum tag == fromEnum tagEnumSuccess =
--   wordarray_u8_corres arr =<< peek success
-- wordarray_put_u8_corres _ _ = return False
-- 
-- cogent_wordarray_put_u8 :: Ct6 -> IO Ct7
-- cogent_wordarray_put_u8 arg = peek =<< c_wordarray_put_u8 =<< new arg
-- 


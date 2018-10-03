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
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -Wno-missing-fields #-}
{- OPTIONS_GHC -F -pgmFderive -optF-F #-}

module WordArray where

-- import Control.Monad.State
import Data.Array.IArray
import Data.Array.IO
import Data.Either.Extra  -- extra-1.6
-- import Data.Function
import Data.Ix
-- import Data.Set as S
import Foreign
import Foreign.C.String hiding (CString)
import Foreign.C.Types
import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable
import Prelude as P
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


-- \////////////////////////////////////////////////////////////////////////////
--
--

-- wordarray_u8_corres :: WordArray Word8 -> CWordArray Cu8 -> IO Bool
-- wordarray_u8_corres hs_arr c_arr = do
--   arr <- peekArray (fromIntegral $ len c_arr) (values c_arr)
--   return $ arr == P.map fromIntegral hs_arr
-- 
-- toC_wordarray_u8 :: WordArray Word8 -> IO (CWordArray Cu8)
-- toC_wordarray_u8 hs_arr = do
--   p_vals <- newArray $ P.map fromIntegral hs_arr
--   let len = length hs_arr
--   return $ CWordArray (fromIntegral len) p_vals

-- prop_wordarray_create_u8_corres = monadicIO $
--   forAllM gen_wordarray_create_u8_arg $ \arg -> run $ do
--     rc <- cogent_wordarray_create_u8 =<< toC_wordarray_create_u8_arg arg
--     ra <- return $ hs_wordarray_create (abs_wordarray_create_u8_arg arg)
--     corresM wordarray_create_u8_corres ra rc
-- 
-- gen_wordarray_create_u8_arg :: Gen (R15 SysState Word32)
-- gen_wordarray_create_u8_arg = do
--   s <- arbitrary
--   l <- elements [0..100]
--   return $ R15 s l
-- 
-- toC_wordarray_create_u8_arg :: R15 SysState Word32 -> IO Ct4
-- toC_wordarray_create_u8_arg (R15 p1 p2) = do
--   p1' <- pDummyCSysState
--   p2' <- return $ fromIntegral p2
--   return $ Ct4 p1' p2'
-- 
-- abs_wordarray_create_u8_arg :: R15 SysState Word32 -> Word32
-- abs_wordarray_create_u8_arg (R15 _ p2) = p2
-- 
-- wordarray_create_u8_corres :: Maybe (WordArray Word8) -> Ct5 -> IO Bool
-- wordarray_create_u8_corres Nothing    (Ct5 {..}) | fromEnum tag == fromEnum tagEnumError = pure True
-- wordarray_create_u8_corres (Just arr) (Ct5 {..}) | fromEnum tag == fromEnum tagEnumSuccess = do
--   let Ct3 _ p_arr = success
--   wordarray_u8_corres arr =<< peek p_arr
-- wordarray_create_u8_corres _ _ = return False
-- 
-- cogent_wordarray_create_u8 :: Ct4 -> IO Ct5
-- cogent_wordarray_create_u8 arg = peek =<< c_wordarray_create_u8 =<< new arg
-- 
-- hs_wordarray_create :: (Integral a) => Word32 -> Cogent_monad (Maybe (WordArray a))
-- hs_wordarray_create l = (return . Just $ replicate (fromIntegral l) (fromIntegral 0)) `alternative` (return Nothing)
--   where return = CogentMonad.return
--         (>>=)  = (CogentMonad.>>=)
--         (>>)   = (CogentMonad.>>)

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


{- LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RebindableSyntax #-}
{- LANGUAGE ImplicitPrelude #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -Wno-missing-fields #-}
{- OPTIONS_GHC -F -pgmFderive -optF-F #-}

module WordArray where

-- import Control.Monad.State
import Data.Either.Extra  -- extra-1.6
-- import Data.Function
import Data.Set as S
import Foreign
import Foreign.C.String hiding (CString)
import Foreign.C.Types
import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable
import Prelude as P
import Test.QuickCheck hiding (Success)
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import Test.QuickCheck.Monadic

import CogentMonad hiding (return, (>>=), (>>))
import qualified CogentMonad as CogentMonad
import Corres
import FFI
-- import qualified FFI as FFI
import Wa_Shallow_Desugar 
-- import WordArray
import Util


ifThenElse c e1 e2 = case c of True -> e1; False -> e2


-- /////////////////////////////////////////////////////////////////////////////

prop_wordarray_create_u8_corres = monadicIO $
  forAllM gen_wordarray_create_u8_arg $ \arg -> run $ do
    rc <- cogent_wordarray_create_u8 =<< toC_wordarray_create_u8_arg arg
    ra <- return $ hs_wordarray_create (abs_wordarray_create_u8_arg arg)
    corresM wordarray_create_u8_corres ra rc

gen_wordarray_create_u8_arg :: Gen (R15 SysState Word32)
gen_wordarray_create_u8_arg = do
  s <- arbitrary
  l <- elements [0..100]
  return $ R15 s l

toC_wordarray_create_u8_arg :: R15 SysState Word32 -> IO Ct4
toC_wordarray_create_u8_arg (R15 p1 p2) = do
  p1' <- pDummyCSysState
  p2' <- return $ fromIntegral p2
  return $ Ct4 p1' p2'

abs_wordarray_create_u8_arg :: R15 SysState Word32 -> Word32
abs_wordarray_create_u8_arg (R15 _ p2) = p2

wordarray_create_u8_corres :: Maybe (WordArray Word8) -> Ct5 -> IO Bool
wordarray_create_u8_corres Nothing    (Ct5 {..}) | fromEnum tag == fromEnum tagEnumError = pure True
wordarray_create_u8_corres (Just arr) (Ct5 {..}) | fromEnum tag == fromEnum tagEnumSuccess = do
  let Ct3 _ p_arr = success
  c_arr <- peek p_arr
  hs_arr <- peekArray (fromIntegral $ len c_arr) (values c_arr)
  return $ hs_arr == P.map fromIntegral arr
wordarray_create_u8_corres _ _ = return False

foreign import ccall unsafe "ffi_wordarray_create_u8"
  c_wordarray_create_u8 :: Ptr Ct4 -> IO (Ptr Ct5)

cogent_wordarray_create_u8 :: Ct4 -> IO Ct5
cogent_wordarray_create_u8 arg = do
  p_arg <- new arg
  p_ret <- c_wordarray_create_u8 p_arg
  peek p_ret

hs_wordarray_create :: (Integral a) => Word32 -> Cogent_monad (Maybe (WordArray a))
hs_wordarray_create l = (return . Just $ replicate (fromIntegral l) (fromIntegral 0)) `alternative` (return Nothing)
  where return = CogentMonad.return
        (>>=)  = (CogentMonad.>>=)
        (>>)   = (CogentMonad.>>)

-- /////////////////////////////////////////////////////////////////////////////

prop_wordarray_get_u8_corres = monadicIO $
  forAllM gen_wordarray_get_u8_arg $ \arg -> run $ do
    rc <- cogent_wordarray_get_u8 =<< toC_wordarray_get_u8_arg arg
    ra <- return $ uncurry hs_wordarray_get (abs_wordarray_get_u8_arg arg)
    return $ corres' wordarray_get_u8_corres ra rc

gen_wordarray_get_u8_arg :: Gen (R15 (WordArray Word8) Word32)
gen_wordarray_get_u8_arg = do
  arr <- listOf (arbitrary :: Gen Word8)
  let len = length arr
  idx <- elements [0 .. 2 * fromIntegral len]
  return $ R15 arr idx

toC_wordarray_get_u8_arg :: R15 (WordArray Word8) Word32 -> IO Ct2
toC_wordarray_get_u8_arg (R15 p1 p2) = do
  p_vals <- newArray $ P.map fromIntegral p1
  let len = length p1
      cogent_arr = CWordArray (fromIntegral len) p_vals
  p_arr <- new cogent_arr
  return $ Ct2 p_arr (fromIntegral p2)

abs_wordarray_get_u8_arg :: R15 (WordArray Word8) Word32 -> (WordArray Word8, Word32)
abs_wordarray_get_u8_arg (R15 p1 p2) = (p1, p2)

wordarray_get_u8_corres :: Word8 -> Cu8 -> Bool
wordarray_get_u8_corres ra rc = fromIntegral ra == fromIntegral rc

foreign import ccall unsafe "ffi_wordarray_get_0"
  c_wordarray_get_u8 :: Ptr Ct2 -> IO Cu8

cogent_wordarray_get_u8 :: Ct2 -> IO Cu8
cogent_wordarray_get_u8 = (c_wordarray_get_u8 =<<) . new

hs_wordarray_get :: Integral a => WordArray a -> Word32 -> a
hs_wordarray_get xs i | is_inbound xs i = xs !! (fromIntegral i)
                      | otherwise = 0

-- /////////////////////////////////////////////////////////////////////////////

hs_wordarray_free :: WordArray a -> ()
hs_wordarray_free _ = ()

hs_wordarray_get_bounded :: Integral a => WordArray a -> Word32 -> Maybe a
hs_wordarray_get_bounded xs i =
  if is_inbound xs i then Just $ hs_wordarray_get xs i
                     else Nothing

hs_wordarray_modify :: WordArray a -> Word32 -> ((a, acc, obsv) -> (a, acc)) -> acc -> obsv -> (WordArray a, acc)
hs_wordarray_modify xs i f acc obsv = 
  let (xs1,x:xs2) = splitAt (fromIntegral i) xs
      (x',acc') = f (x,acc,obsv)
   in (xs1 ++ x':xs2, acc')

is_inbound :: WordArray a -> Word32 -> Bool
is_inbound xs i = i < (fromIntegral $ length xs)

hs_wordarray_put :: WordArray a -> Word32 -> a -> Either (WordArray a) (WordArray a)
hs_wordarray_put xs i _ | not (is_inbound xs i) = Left xs
hs_wordarray_put xs i a = let (xs1,x:xs2) = splitAt (fromIntegral i) xs
                           in Right (xs1 ++ a:xs2)

hs_wordarray_put2 :: WordArray a -> Word32 -> a -> WordArray a
hs_wordarray_put2 = ((fromEither .) .) . hs_wordarray_put

hs_wordarray_length :: WordArray a -> Word32
hs_wordarray_length = fromIntegral . length



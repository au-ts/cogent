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
import Data.Set as S
import Foreign
import Foreign.C.String hiding (CString)
import Foreign.C.Types
import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable
import Prelude hiding ((>>), (>>=), return)
import qualified Prelude as P
import Test.QuickCheck hiding (Success)
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import Test.QuickCheck.Monadic

import CogentMonad -- hiding (return, (>>=), (>>))
import qualified CogentMonad as CogentMonad
import Corres
-- import FFI (pDummyCSysState, dummyCSysState, const_unit, const_true, const_false)
-- import qualified FFI as FFI
import Wa_Shallow_Desugar 
-- import WordArray
import Util


ifThenElse c e1 e2 = case c of True -> e1; False -> e2

-- infixl 1 >>, >>=
-- (>>=)  = (CogentMonad.>>=)
-- (>>)   = (CogentMonad.>>)
-- return = CogentMonad.return


prop_wordarray_create_corres =
  forAllM (arbitrary :: Gen (Small Word32)) $ \(Small l) -> run $ do
    rc <- cogent_wordarray_create_u8 l
    ra <- return $ hs_wordarray_create l
    return $ corres wordarray_create_corres ra rc
  where (>>=) = (P.>>=)
        (>>)  = (P.>>)
        return = P.return

wordarray_create_corres :: Maybe (WordArray Word8) -> Maybe (WordArray Word8) -> Bool
wordarray_create_corres (Just wa) (Just wc) = wa `wordarray_length_corres` wc
wordarray_create_corres a c = a == c

wordarray_length_corres :: WordArray a -> WordArray a -> Bool
wordarray_length_corres ra rb = length ra == length rb

foreign import ccall unsafe "ffi_wordarray_create_u8"
  c_wordarray_create_u8 :: Ptr Ct2 -> IO (Ptr Ct3)

cogent_wordarray_create_u8 :: Word32 -> IO (Maybe (WordArray Word8))
cogent_wordarray_create_u8 l = undefined

hs_wordarray_create :: (Integral a) => Word32 -> Cogent_monad (Maybe (WordArray a))
hs_wordarray_create l = hs_wordarray_create_nz l

hs_wordarray_free :: WordArray a -> ()
hs_wordarray_free _ = ()

hs_wordarray_create_nz :: (Integral a) => Word32 -> Cogent_monad (Maybe (WordArray a))
hs_wordarray_create_nz l = (return . Just $ replicate (fromIntegral l) (fromIntegral 0)) `alternative` (return Nothing)

hs_wordarray_get :: Integral a => WordArray a -> Word32 -> a
hs_wordarray_get xs i | is_inbound xs i = xs !! (fromIntegral i)
                      | otherwise = 0

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



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

import Control.Monad.State
import Data.Either.Extra  -- extra-1.6
import Data.Set as S
import Foreign
import Foreign.C.String hiding (CString)
import Foreign.C.Types
import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable
import Prelude
import Test.QuickCheck hiding (Success)
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import Test.QuickCheck.Monadic

import CogentMonad hiding (return, (>>=), (>>))
import qualified CogentMonad as CogentMonad
import Corres
-- import FFI (pDummyCSysState, dummyCSysState, const_unit, const_true, const_false)
-- import qualified FFI as FFI
import Fsop_Shallow_Desugar 
-- import WordArray
import Util


type WordArray a = [a]
type CString = WordArray U8

wordarray_create_nz :: U32 -> WordArray a
wordarray_create_nz l = repeat l 0

wordarray_get :: Num a => WordArray a -> Int -> a
wordarray_get xs i | is_inbound xs i = xs !! i
                   | otherwise = 0

wordarray_get_bounded :: Num a => WordArray a -> Int -> Maybe a
wordarray_get_bounded xs i =
  if is_inbound xs i then Just $ wordarray_get xs i
                     else Nothing

wordarray_modify :: WordArray a -> Int -> ((a, acc, obsv) -> (a, acc)) -> acc -> obsv -> (WordArray a, acc)
wordarray_modify xs i f acc obsv = 
  let (xs1,x:xs2) = splitAt i xs
      (x',acc') = f (x,acc,obsv)
   in (xs1 ++ x':xs2, acc')

is_inbound :: WordArray a -> Int -> Bool
is_inbound xs i = i < length xs

wordarray_put :: WordArray a -> Int -> a -> Either (WordArray a) (WordArray a)
wordarray_put xs i _ | not (is_inbound xs i) = Left xs
wordarray_put xs i a = let (xs1,x:xs2) = splitAt i xs
                        in Right (xs1 ++ a:xs2)

wordarray_put2 :: WordArray a -> Int -> a -> WordArray a
wordarray_put2 = ((fromEither .) .) . wordarray_put

wordarray_length :: WordArray a -> Int
wordarray_length = length



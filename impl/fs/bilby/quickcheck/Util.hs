{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}

module Util where

import Foreign
import Foreign.C.Types
import QuickCheck.GenT (GenT(..), runGenT)
import Test.QuickCheck
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import Test.QuickCheck.Monadic

newtype Flip f (a :: a') (b :: b') = Flip { unflip :: f b a }

ffmap :: (Functor (Flip f c)) => (a -> b) -> f a c -> f b c
ffmap f = unflip . fmap f . Flip

ttraverse :: (Traversable (Flip f b), Applicative m) => (a -> m a') -> f a b -> m (f a' b)
ttraverse f = fmap unflip . traverse f . Flip


type Cu8  = CUChar
type Cu16 = CUShort 
type Cu32 = CUInt
type Cu64 = CULLong

newtype CSysState = CSysState { dummy :: CChar } deriving Storable

instance Arbitrary CSysState where
  arbitrary = return dummyCSysState

dummyCSysState :: CSysState
dummyCSysState = CSysState $ CChar 0

pDummyCSysState :: IO (Ptr CSysState)
pDummyCSysState = new dummyCSysState

newtype Tag = Tag Int deriving (Enum)  -- hs type
newtype Ctag_t = Ctag_t CInt deriving (Enum, Show, Storable)  -- c type equiv.

newtype FuncEnum = FuncEnum Int deriving (Enum, Show)
newtype Cuntyped_func_enum = Cuntyped_func_enum CInt deriving (Enum, Show, Storable)

newtype Cunit_t = Cunit_t { dummy :: CInt } deriving (Show, Storable)
newtype Cbool_t = Cbool_t { boolean :: CUChar } deriving (Show, Storable)

instance Arbitrary Cunit_t where
  arbitrary = return const_unit

instance Arbitrary Cbool_t where
  arbitrary = elements [const_true, const_false]

const_unit = Cunit_t $ CInt 0
const_true  = Cbool_t $ CUChar 1
const_false = Cbool_t $ CUChar 0


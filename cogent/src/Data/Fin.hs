--
-- Copyright 2019, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--


{-# LANGUAGE DataKinds #-}
{- LANGUAGE DeriveFoldable #-}
{- LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Fin where

import Cogent.Compiler (__impossible)
#if __GLASGOW_HASKELL__ < 711
import Cogent.Compiler (__ghc_t3927)
#endif
import Cogent.Util

import Data.Ex
import Data.Nat
-- import Data.PropEq

import Control.Applicative
import Data.Binary
#if __GLASGOW_HASKELL__ >= 709
import Data.Foldable (find)
#else
import Data.Foldable
#endif
import Data.Monoid
import Data.Traversable
import GHC.Generics (Generic, Rep, V1)
import Prelude hiding (length, repeat, splitAt, take, unzip, zip, zipWith)
import qualified Text.PrettyPrint.ANSI.Leijen as L

data Fin :: Nat -> * where
  FZero :: Fin ('Suc n)
  FSuc  :: Fin n -> Fin ('Suc n)

deriving instance Eq   (Fin n)
deriving instance Show (Fin n)
deriving instance Ord  (Fin n)

instance Generic (Fin 'Zero) where
  type Rep (Fin 'Zero) = V1
instance Binary (Fin 'Zero) where
  -- These functions don't need to be defined, as 'Fin \'Zero' has no inhabitants.

f0 = FZero
f1 = FSuc f0
f2 = FSuc f1

finInt :: Fin n -> Int
finInt FZero = 0
finInt (FSuc f) = finInt f + 1

finNat :: Fin n -> Nat
finNat FZero = n0
finNat (FSuc f) = Suc $ finNat f

atList :: [t] -> Fin a -> t
atList [] _ = __impossible "atList"
atList (x:xs) FZero = x
atList (x:xs) (FSuc s) = atList xs s

widen :: Fin n -> Fin ('Suc n)
widen FZero = FZero
widen (FSuc n) = FSuc (widen n)

widenN :: Fin n -> SNat m -> Fin (n :+: m)
widenN f (SZero) = f
widenN f (SSuc n) = widen (widenN f n)

upshift :: Fin n -> SNat m -> Fin (n :+: m)
upshift n SZero    = n
upshift n (SSuc m) = FSuc (upshift n m)

-- liftIdx idx var means:
--   if idx <= var, var -> var + 1; otherwise intact
liftIdx :: Fin ('Suc n) -> Fin n -> Fin ('Suc n)
liftIdx FZero v = FSuc v
liftIdx (FSuc i) FZero = FZero
liftIdx (FSuc i) (FSuc v) = FSuc $ liftIdx i v

maxFin :: SNat n -> Fin ('Suc n)
maxFin SZero = FZero
maxFin (SSuc n) = FSuc $ maxFin n


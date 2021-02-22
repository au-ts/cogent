--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE DeriveGeneric #-}

module Data.DList
  ( DList(..)
  , empty
  , singleton
  , cons
  , fromList
  , toList
  ) where

import Control.Arrow (first)
import Data.Binary
import qualified Data.Set as S
import Data.List (find, foldl')
import GHC.Generics (Generic)

{-
 - Distinct list.
 - Used to keep track of definitions, which require an ordering
 - but don't need to be stored multiple times.
 -}
data DList a = DList ![a] deriving (Eq, Ord, Generic)

instance Binary a => Binary (DList a)

-- Just implement functions that we currently use.
empty :: DList a
empty = DList []

singleton :: a -> DList a
singleton a = DList [a]

cons :: Ord a => a -> DList a -> DList a
cons x dl@(DList xs) | x `elem` xs = dl
                     | otherwise = DList (x:xs)

fromList :: Ord a => [a] -> DList a
fromList = foldl' (flip cons) empty . reverse

toList :: DList a -> [a]
toList (DList xs) = xs

instance Show a => Show (DList a) where
  showsPrec n (DList xs) = showsPrec n xs
instance (Ord a, Read a) => Read (DList a) where
  readsPrec n s = map (first DList) $ readsPrec n s

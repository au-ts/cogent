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

module Data.DList (DList(..), empty, cons, fromList, toList) where

import Data.Binary
import qualified Data.Set as S
import Data.List (foldl')
import GHC.Generics (Generic)

{-
 - Distinct list.
 - Used to keep track of definitions, which require an ordering
 - but don't need to be stored multiple times.
 -}
data DList a = DList ![a] !(S.Set a)
             deriving (Generic)

instance Binary a => Binary (DList a)

-- Just implement functions that we currently use.
empty :: DList a
empty = DList [] S.empty

cons :: Ord a => a -> DList a -> DList a
cons x dl@(DList xs xsSet) | S.member x xsSet = dl
                           | otherwise = DList (x:xs) (S.insert x xsSet)

fromList :: Ord a => [a] -> DList a
fromList = foldl' (flip cons) empty . reverse

toList :: DList a -> [a]
toList (DList xs _) = xs

instance Eq a => Eq (DList a) where
  DList xs _ == DList ys _ = xs == ys
instance Ord a => Ord (DList a) where
  DList xs _ `compare` DList ys _ = xs `compare` ys
instance Show a => Show (DList a) where
  showsPrec n (DList xs _) = showsPrec n xs
instance (Ord a, Read a) => Read (DList a) where
  readsPrec n s = map (\(xs, s') -> (DList xs (S.fromList xs), s')) $ readsPrec n s

--
-- Copyright 2020, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Data.OMap
  ( OMap (..)
  , length
  , empty
  , singleton
  , lookup
  , insert
  , delete
  , adjust
  , alter
  , fromList
  , toList
  ) where

import Control.Arrow (first)
import Data.Binary
import qualified Data.List as L (length, lookup)
import Data.List (find, foldl')
import GHC.Generics (Generic)
import Prelude hiding (length, lookup)

-- import Debug.Trace

{-
 - Ordered map.
 -}
data OMap k v = OMap [(k,v)] deriving (Eq, Ord, Generic, Functor)

instance (Binary k, Binary v) => Binary (OMap k v)

length :: OMap k v -> Int
length (OMap ls) = L.length ls

empty :: OMap k v
empty = OMap []

singleton :: k -> v -> OMap k v
singleton k v = OMap [(k,v)]

lookup :: Eq k => k -> OMap k v -> Maybe v
lookup k (OMap ls) = L.lookup k ls

insert :: Eq k => k -> v -> OMap k v -> OMap k v
insert k v m@(OMap ls) =
  case L.lookup k ls of
    Nothing -> OMap $ (k,v):ls
    Just _  -> m

delete :: Eq k => k -> OMap k v -> OMap k v
delete k m@(OMap ls) =
  case L.lookup k ls of
    Nothing -> m
    Just _  -> OMap $ filter ((/= k) . fst) ls

adjust :: Eq k => (v -> v) -> k -> OMap k v -> OMap k v
adjust f k m@(OMap ls) = OMap $ map (\(k',v) -> if k == k' then (k', f v) else (k', v)) ls

alter :: Eq k => (Maybe v -> Maybe v) -> k -> OMap k v -> OMap k v
alter f k m@(OMap ls) =
  case L.lookup k ls of
    Nothing -> case f Nothing of
                 Nothing -> m
                 Just v' -> insert k v' m
    Just v  -> case f (Just v) of
                 Nothing -> delete k m
                 Just v' -> adjust (const v') k m

fromList :: (Eq k, Show k) => [(k,v)] -> OMap k v
fromList = foldl' (flip $ uncurry insert) empty . reverse

toList :: OMap k v -> [(k,v)]
toList (OMap xs) = xs

instance (Show k, Show v) => Show (OMap k v) where
  showsPrec n (OMap xs) = showsPrec n xs
instance (Ord k, Read k, Read v) => Read (OMap k v) where
  readsPrec n s = map (first OMap) $ readsPrec n s


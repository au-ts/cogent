--
-- Copyright 2021, Trustworthy Systems Group (UNSW)
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(UNSW_GPL)
--

{-# LANGUAGE DeriveFunctor #-}
module Data.Bwd where

import Data.List
import Data.Monoid

-- | Backward list
data Bwd a = BEmp | Bwd a :< a
  deriving (Eq, Ord, Read, Show, Functor)

instance Foldable Bwd where
  foldr f z BEmp = z
  foldr f z (sx :< x) = x `f` foldr f z sx
  foldMap f sx = foldr (<>) mempty $ fmap f sx

fwd :: Bwd a -> [a]
fwd = foldl (flip (:)) []

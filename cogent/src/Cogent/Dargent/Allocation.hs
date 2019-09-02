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

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Cogent.Dargent.Allocation where

import Cogent.Common.Syntax
import Cogent.Dargent.Util

{- * Bit range -}

-- | A range of bit indices into a data type.
--
--   Should satisfy
--
--  prop> bitSizeBR >= 1
--  prop> bitOffsetBR >= 0
--
--   Represents the set
--
--  @
--  {bitOffset, bitOffset + 1, ..., bitOffset + bitSize - 1}
--  @
data BitRange = BitRange { bitSizeBR :: Size, bitOffsetBR :: Size }
              deriving (Eq, Show, Ord)

instance Offsettable BitRange where
  offset n range@(BitRange { bitOffsetBR }) = range { bitOffsetBR = bitOffsetBR + n}

-- | A predicate to determine if the bit-range is zero sized.
isZeroSizedBR :: BitRange -> Bool
isZeroSizedBR BitRange { bitSizeBR, bitOffsetBR } = (bitSizeBR == 0)


{- * Allocations -}

-- | A set of bit indices into a data type.
--
-- Represents the set which is the union of the sets represented by the 'BitRange's in the list.
type Allocation = [(BitRange, DataLayoutPath)]

instance Offsettable Allocation where
  offset n = fmap $ \(range, path) -> (offset n range, path)

isZeroSizedAllocation :: Allocation -> Bool
isZeroSizedAllocation = all (isZeroSizedBR . fst)


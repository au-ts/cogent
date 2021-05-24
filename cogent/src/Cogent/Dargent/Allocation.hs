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

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- This module sets up Allocation as an abstract object so we can establish
-- internal invariants

module Cogent.Dargent.Allocation
  ( BitRange (..)
  , newBitRangeFromTo
  , newBitRangeBaseSize
  , emptyBitRange
  , primBitRange
  , pointerBitRange
  , isZeroSizedBR
  , AllocationBlock
  , OverlappingAllocationBlocks (..)
  , Allocation
  , Allocation' (..)
  , emptyAllocation
  , singletonAllocation
  , undeterminedAllocation
  , (\/)
  , (/\)
  , overlaps
  , isZeroSizedAllocation
  , endOfAllocation
  , AlignedBitRange (..)
  , alignSize
  , alignOffsettable
  , rangeToAlignedRanges
  )
where


import Control.Applicative
import Control.Monad.Trans.Writer
import Control.Monad (guard)
import Data.Bifunctor (first)
import Data.Binary
import GHC.Generics (Generic)

import Cogent.Common.Types
import Cogent.Common.Syntax
import Cogent.Compiler
import Cogent.Dargent.Surface
import Cogent.Dargent.Util
import Cogent.Util

{- * Bit range -}

-- | A range of bit indices into a data type.
--
--   Should satisfy
--
--  prop> bitSizeBR >= 1
--  prop> bitOffsetBR >= 0
--
--   Represents the set
--  @
--  {bitOffset, bitOffset + 1, ..., bitOffset + bitSize - 1}
--  @
--
--  We keep an internal invariant that @bitSizeBR >= 0@ and @bitOffsetBR >= 0@
data BitRange = BitRange { bitSizeBR :: Size, bitOffsetBR :: Size }
  deriving (Eq, Show, Ord, Generic)

instance Offsettable BitRange where
  offset n range@(BitRange { bitOffsetBR }) | n >= 0    = range { bitOffsetBR = bitOffsetBR + n }
                                            | otherwise = error "offset from Offsettable called with n<0"

instance Binary BitRange

{- basic checked constructors for BitRange -}

newBitRangeFromTo :: Size -> Size -> Maybe BitRange
newBitRangeFromTo from to = if 0 <= from && from <= to
                            then pure $ BitRange { bitSizeBR = to - from, bitOffsetBR = from }
                            else Nothing

newBitRangeBaseSize :: Size -> Size -> Maybe BitRange
newBitRangeBaseSize bitOffsetBR bitSizeBR = if 0 <= bitSizeBR && 0 <= bitOffsetBR
                                then pure $ BitRange { bitSizeBR, bitOffsetBR }
                                else Nothing

{- basic layout constructors for BitRange -}

emptyBitRange :: BitRange
emptyBitRange = BitRange { bitSizeBR = 0, bitOffsetBR = 0 }

primBitRange :: PrimInt -> BitRange
primBitRange primInt = BitRange { bitSizeBR = primIntSizeBits primInt, bitOffsetBR = 0 }

pointerBitRange :: BitRange
pointerBitRange = BitRange { bitSizeBR = pointerSizeBits, bitOffsetBR = 0 }

-- | A predicate to determine if the bit-range is zero sized.
isZeroSizedBR :: BitRange -> Bool
isZeroSizedBR BitRange { bitSizeBR, bitOffsetBR } = bitSizeBR == 0

{- * Allocations -}

-- | The smallest piece of an allocation
type AllocationBlock p = (BitRange, p)

newtype OverlappingAllocationBlocks p =
  OverlappingAllocationBlocks { unOverlappingAllocationBlocks :: (AllocationBlock p, AllocationBlock p) }
  deriving (Eq, Show, Ord, Functor)

-- | A set of bit indices into a data type.
--
-- Represents the set which is the union of the sets represented by the 'BitRange's in the list.
--
-- We keep an internal invariant that the list is sorted.
newtype Allocation' p = Allocation { unAllocation :: [AllocationBlock p] }
  deriving (Eq, Show, Ord, Functor)

instance Offsettable (Allocation' p) where
  offset n = Allocation . fmap (first (offset n)) . unAllocation

emptyAllocation :: Allocation' p
emptyAllocation = Allocation []

singletonAllocation :: AllocationBlock p -> Allocation' p
singletonAllocation b = Allocation [b]

undeterminedAllocation :: Allocation' p
undeterminedAllocation = emptyAllocation

-- | Disjunction of allocations
(\/) :: forall p. Ord p => Allocation' p -> Allocation' p -> Allocation' p
(Allocation a1) \/ (Allocation a2) = Allocation (a1 ++ a2)


-- | Conjunction of allocations
--
-- Used when the two allocations could be used simultaneously, and so they must not overlap.
-- For example, if they are allocations for two fields of the same record.
-- It will either succeed, with an allocation, or return overlapping allocation blocks
-- if the two allocations overlap.
(/\) :: forall p. Ord p => Allocation' p -> Allocation' p -> Either [OverlappingAllocationBlocks p] (Allocation' p)
(Allocation a1) /\ (Allocation a2) =
  case allOverlappingBlocks a1 a2 of
    overlappingBlocks@(_ : _) -> Left overlappingBlocks
    []                        -> return $ Allocation (a1 ++ a2)
  where
    allOverlappingBlocks :: [AllocationBlock p] -> [AllocationBlock p] -> [OverlappingAllocationBlocks p]
    allOverlappingBlocks xbs ybs =
      do
        xb <- xbs
        yb <- ybs
        guard $ overlaps (fst xb) (fst yb) -- if they overlap, continue
        return $ OverlappingAllocationBlocks (xb,yb)


{- [Isabelle/HOL] / v.jackson
lemma
  "{o1::int..<o1+s1} ∩ {o2..<o2+s2} ≠ {} ⟷ o1 < o2 + s2 ∧ o2 < o1 + s1 ∧ 0 < s1 ∧ 0 < s2"
  by clarsimp
-}
overlaps :: BitRange -> BitRange -> Bool
overlaps (BitRange s1 o1) (BitRange s2 o2) =
  o1 < o2 + s2 && o2 < o1 + s1 && s1 > 0 && s2 > 0

isZeroSizedAllocation :: Allocation' p -> Bool
isZeroSizedAllocation = all (isZeroSizedBR . fst) . unAllocation

endOfAllocation :: Allocation -> Integer  -- calculates the last bit of an allocation
endOfAllocation (Allocation abs) = maximum $ fmap (\(BitRange s o, _) -> s + o) abs

type Allocation = Allocation' DataLayoutPath



-- | A range of bit indices into a data type.
--
--   Should satisfy the following properties:
--
--  prop> bitSizeABR >= 1
--  prop> bitOffsetABR >= 0
--  prop> wordOffsetABR >= 0
--
--   Should satisfy the alignment property:
--
--  prop> bitSizeABR + bitOffsetABR <= wordSizeBits
--
--   Represents the set

--  @
--  { wordOffset * wordSizeBits + bitOffset
--  , wordOffset * wordSizeBits + bitOffset + 1
--  , ...
--  , wordOffset * wordSizeBits + bitOffset + bitSize - 1
--  }
--  @
--
--   All heap allocated structures are a multiple of a word in size (malloc guarantees this?)
--   and will be word aligned. Hence accesses to an aligned bitrange of a heap-allocated
--   data structure should usually be word aligned.
--
--   While array is the special case here since we use bytearray for dargent arrays i.e. array
--   elements are aligned to bytes instead of words. We still use this structure to represent
--   data layout aligned to bytes and here "word" in "wordOffset" can refer to a single byte.
--
--   Suppose a 2 Word data type is represented using the following array of 'AlignedBitRange's:
--
--  @
--  [ AlignedBitRange { bitSizeABR = 19, ... }  -- Range 0
--  , AlignedBitRange { bitSizeABR = 21, ... }  -- Range 1
--  , AlignedBitRange { bitSizeABR = 24, ... }  -- Range 2
--  ]
--  @
--
--   Then the bits for the 2 word data structure would be obtained as follows
--
--  @
--  HI                                                             LO
--  64                      40                   19                 0
--  +-------+-------+-------+-------+-------+----+--+-------+-------+
--  |HI      Range 2      LO|HI    Range 1     LO|HI    Range 0   LO|
--  +-------+-------+-------+-------+-------+----+--+-------+-------+
--  @
data AlignedBitRange
  = AlignedBitRange { bitSizeABR :: Size, bitOffsetABR :: Size, wordOffsetABR :: Size }
  deriving (Eq, Show, Ord)

{- * Word alignment transformations -}

alignSize :: Size -> Size -> Size
alignSize toMultipleOf size =
    size + ((toMultipleOf - size `mod` toMultipleOf) `mod` toMultipleOf)

-- | Aligns an 'Offsettable' (assumed to initially have offset 0)
--   so that its new offset is the smallest offset which is at least 'minBitOffset'
--   and aligned to a multiple of 'alignBitSize'
--
--   That is:
--
-- @
-- x = 0 -> 0
-- x \in {1, ..., alignBitSize} -> 1
-- x \in {alignBitSize + 1, ..., 2 * alignBitSize} -> 2
-- @
alignOffsettable :: Offsettable a => Size -> Size -> a -> a
alignOffsettable alignBitSize minBitOffset = offset (alignSize alignBitSize minBitOffset)

-- | Splits a 'BitRange' into an equivalent collection of 'AlignedBitRange's
-- satisfying the conditions listed on 'AlignedBitRange'.
rangeToAlignedRanges
  :: Integer
  -> BitRange
    -- Assumes 'bitSizeBR range >= 1'. If 'bitSizeBR range == 0', will return '[]'.
  -> [AlignedBitRange]
rangeToAlignedRanges alignSize (BitRange size offset) =
  let
    offsetWords = offset `div` alignSize
    offsetBits  = offset `mod` alignSize
  in
    rangeToAlignedRanges' offsetWords offsetBits size
  where
    rangeToAlignedRanges' :: Size -> Size -> Size -> [AlignedBitRange]
    rangeToAlignedRanges'           _          _                 0 = []
    rangeToAlignedRanges' offsetWords offsetBits remainingSizeBits =
      let
        currSizeBits = min remainingSizeBits (alignSize - offsetBits)
      in
        AlignedBitRange
        { bitSizeABR    = currSizeBits
        , bitOffsetABR  = offsetBits
        , wordOffsetABR = offsetWords
        } :
        rangeToAlignedRanges' (offsetWords + 1) 0 (remainingSizeBits - currSizeBits)

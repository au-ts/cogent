--
-- Copyright 2018, Data61
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
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
module Cogent.Dargent.Core where

import Data.IntMap as IM hiding (foldr)
import Data.Map (Map)

import Text.Parsec.Pos (SourcePos)

import Cogent.Common.Syntax (TagName, FieldName, Size)
import Cogent.Common.Types (PrimInt (..))
import Cogent.Dargent.Allocation
import Cogent.Dargent.Util

{- * Core datalayout types -}

-- | A specification of the bit layout of a Cogent type
--
--   The Cogent core language type for layouts is @DataLayout BitRange@.
--   Will transform to @DataLayout [AlignedBitRange]@ immediately before code generation.
--
--
--   NOTE: We may wish to retain more 'SourcePos' information to enable better error messages
--   when matching @DataLayout BitRange@s with monomorphised cogent core types / mdimeglio
data DataLayout' bits
  = UnitLayout
  | PrimLayout
    { bitsDL          :: bits
    }
  | SumLayout
    { tagDL           :: bits
    , alternativesDL  :: Map TagName (Integer, DataLayout' bits, SourcePos)
      -- ^ The 'Integer' is the tag's value
    }
  | RecordLayout
    { fieldsDL        :: Map FieldName (DataLayout' bits, SourcePos)
    }
#ifdef BUILTIN_ARRAYS
  | ArrayLayout (DataLayout' bits) SourcePos
#endif
  deriving (Show, Eq, Functor, Foldable)

deriving instance Ord bits => Ord (DataLayout' bits)

instance Offsettable a => Offsettable (DataLayout' a) where
  offset n = fmap (offset n)

-- The DataLayout wrapper type
data DataLayout bits
  = Layout (DataLayout' bits) -- this type has this layout
  | CLayout  -- defer the layout of this type to C
  deriving (Show, Eq, Functor, Foldable)

deriving instance Ord bits => Ord (DataLayout bits)

instance Offsettable a => Offsettable (DataLayout a) where
  offset n = fmap (offset n)


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
--   datastructure will be word aligned.
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

{- * @DataLayout BitRange@ helpers -}

endAllocatedBits' :: DataLayout' BitRange -> Size
endAllocatedBits' = foldr (\range start -> max (bitOffsetBR range + bitSizeBR range) start) 0

endAllocatedBits :: DataLayout BitRange -> Size
endAllocatedBits = foldr (\range start -> max (bitOffsetBR range + bitSizeBR range) start) 0

dataLayoutSizeBytes :: DataLayout BitRange -> Size
dataLayoutSizeBytes = (`div` wordSizeBits) . (alignSize wordSizeBits) . endAllocatedBits


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
  :: BitRange
    -- Assumes 'bitSizeBR range >= 1'. If 'bitSizeBR range == 0', will return '[]'.
  -> [AlignedBitRange]
rangeToAlignedRanges (BitRange size offset) =
  let
    offsetWords = offset `div` wordSizeBits
    offsetBits  = offset `mod` wordSizeBits
  in
    rangeToAlignedRanges' offsetWords offsetBits size
  where
    rangeToAlignedRanges' :: Size -> Size -> Size -> [AlignedBitRange]
    rangeToAlignedRanges'           _          _                 0 = []
    rangeToAlignedRanges' offsetWords offsetBits remainingSizeBits =
      let
        currSizeBits = min remainingSizeBits (wordSizeBits - offsetBits)
      in
        AlignedBitRange
        { bitSizeABR    = currSizeBits
        , bitOffsetABR  = offsetBits
        , wordOffsetABR = offsetWords
        } :
        rangeToAlignedRanges' (offsetWords + 1) 0 (remainingSizeBits - currSizeBits)

alignLayout' :: DataLayout' BitRange -> DataLayout' [AlignedBitRange]
alignLayout' = fmap rangeToAlignedRanges

alignLayout :: DataLayout BitRange -> DataLayout [AlignedBitRange]
alignLayout = fmap rangeToAlignedRanges



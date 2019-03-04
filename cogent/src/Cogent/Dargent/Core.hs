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
  
import Data.Map (Map)

import Text.Parsec.Pos (SourcePos)

import Cogent.Common.Syntax (TagName, FieldName, Size)

import Cogent.Common.Types (PrimInt (..))

{- * Core datalayout types -}

-- | A specification of the bit layout of a Cogent type
--
--   The Cogent core language type for layouts is @DataLayout BitRange@.
--   Will transform to @DataLayout [AlignedBitRange]@ immediately before code generation.
--
--
--   NOTE: We may wish to retain more 'SourcePos' information to enable better error messages
--   when matching @DataLayout BitRange@s with monomorphised cogent core types / mdimeglio
data DataLayout bits
  = UnitLayout
  | PrimLayout
    { bitsDL          :: bits
    }
  | SumLayout
    { tagDL           :: bits
    , alternativesDL  :: Map TagName (Integer, DataLayout bits, SourcePos)
      -- ^ The 'Integer' is the tag's value
    }
  | RecordLayout
    { fieldsDL        :: Map FieldName (DataLayout bits, SourcePos)
    }
  deriving (Show, Eq, Functor, Foldable)

deriving instance Ord bits => Ord (DataLayout bits)

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
data BitRange
  = BitRange { bitSizeBR :: Size, bitOffsetBR :: Size }
  deriving (Eq, Show, Ord)
  
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

endAllocatedBits :: DataLayout BitRange -> Size
endAllocatedBits = foldr (\range start -> max (bitOffsetBR range + bitSizeBR range) start) 0

dataLayoutSizeBytes :: DataLayout BitRange -> Size
dataLayoutSizeBytes = (`div` wordSizeBits) . (alignSize wordSizeBits) . endAllocatedBits

{- * Default bit 'Sizes' and 'BitRanges' -}

wordSizeBits :: Size
wordSizeBits = 32


data Architecture = X86_64 | X86_32

architecture :: Architecture
architecture = X86_64


pointerSizeBits :: Size
pointerSizeBits = case architecture of
  X86_32 -> 32
  X86_64 -> 64

primIntSizeBits :: PrimInt -> Size
primIntSizeBits U8      = 8
primIntSizeBits U16     = 16
primIntSizeBits U32     = 32
primIntSizeBits U64     = 64
primIntSizeBits Boolean = 8

primBitRange :: PrimInt -> BitRange
primBitRange primInt = BitRange { bitSizeBR = primIntSizeBits primInt, bitOffsetBR = 0 }

pointerBitRange :: BitRange
pointerBitRange = BitRange { bitSizeBR = pointerSizeBits, bitOffsetBR = 0 }
  
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

alignLayout :: DataLayout BitRange -> DataLayout [AlignedBitRange]
alignLayout = fmap rangeToAlignedRanges


-- When transforming (Offset repExpr offsetSize),
-- we want to add offset bits to all blocks inside the repExpr,
-- as well as the allocation corresponding to that repExpr.
class Offsettable a where
  offset :: Size -> a -> a
  
instance Offsettable BitRange where
  offset n range@(BitRange { bitOffsetBR }) = range { bitOffsetBR = bitOffsetBR + n}
  
instance Offsettable a => Offsettable (DataLayout a) where
  offset n = fmap (offset n)

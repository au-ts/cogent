{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
module Cogent.DataLayout.Core where
  
import Data.Map (Map)

import Text.Parsec.Pos (SourcePos)

import Cogent.Common.Syntax (TagName, FieldName, Size)

import Cogent.Common.Types (PrimInt (..))

{- * CORE DATALAYOUT TYPES -}

-- | A specification of the bit layout of a Cogent type
--
--   The Cogent core language type for layouts is 'DataLayout BitRange'.
--   Will transform to 'DataLayout [AlignedBitRange]' immediately before code generation.
--
--   NOTE: We may wish to retain more 'SourcePos' information to enable better error messages
--   when matching 'DataLayout BitRange's with monomorphised cogent core types / mdimeglio
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
--   prop> bitSizeBR >= 1
--
--   Represents the set
--   @
--   {bitOffset, bitOffset + 1, ..., bitOffset + bitSize - 1}
--   @
data BitRange
  = BitRange { bitSizeBR :: Size, bitOffsetBR :: Size }
  deriving (Eq, Show, Ord)
  
-- | A range of bit indices into a data type.
--
--   Should satisfy the following properties:
--   prop> bitSizeABR >= 1
--   prop> bitOffsetABR >= 0
--   prop> wordOffsetABR >= 0
--
--   Should satisfy the alignment property:
--   prop> bitSizeABR + bitOffsetABR <= wordSizeBits
--
--   Represents the set
--   @
--   { wordOffset * wordSizeBits + bitOffset
--   , wordOffset * wordSizeBits + bitOffset + 1
--   , ...
--   , wordOffset * wordSizeBits + bitOffset + bitSize - 1
--   }
--   @
--
--   All heap allocated structures are a multiple of a word in size (malloc guarantees this?)
--   and will be word aligned. Hence accesses to an aligned bitrange of a heap-allocated
--   datastructure will be word aligned.
data AlignedBitRange
  = AlignedBitRange { bitSizeABR :: Size, bitOffsetABR :: Size, wordOffsetABR :: Size }
  deriving (Eq, Show, Ord)

{- * DataLayout 'BitRange' HELPERS -}
endAllocatedBits :: DataLayout BitRange -> Size
endAllocatedBits = foldr (\range start -> max (bitOffsetBR range + bitSizeBR range) start) 0

{- * DEFAULT BIT 'Sizes' AND 'BitRanges' -}

wordSizeBits :: Size
wordSizeBits = 32

pointerSizeBits :: Size
pointerSizeBits = 32

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
  
{- * WORD ALIGNMENT TRANSFORMATIONS -}

-- | Aligns an 'Offsettable' (assumed to initially have offset 0)
--   so that its new offset is the smallest offset which is at least 'minBitOffset'
--   and aligned to a multiple of 'alignBitSize'
alignOffsettable :: Offsettable a => Size -> Size -> a -> a
alignOffsettable alignBitSize minBitOffset = offset bitOffset
  where
    bitOffset = (minBitOffset `div` alignBitSize + 1) * alignBitSize

-- Splits a 'BitRange' into an equivalent collection of 'AlignedBitRange's
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
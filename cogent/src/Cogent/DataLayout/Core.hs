{-# LANGUAGE DeriveFunctor #-}
module Cogent.DataLayout.Core where
  
import Data.Map (Map)

import Text.Parsec.Pos (SourcePos)

import Cogent.Common.Syntax (TagName, FieldName, Size)

{- CORE DATALAYOUT TYPES -}

-- A specification of the bit layout of a Cogent type
--
-- The Cogent core language type is `DataLayout BitRange`.
-- Will transform to `DataLayout [AlignedBitRange]` immediately before code generation.
--
-- NOTE: We may wish to retain more SourcePos information to enable better error messages
-- when matching `DataLayout BitRange`s with monomorphised cogent core types / mdimeglio
data DataLayout bits
  = UnitLayout
  | PrimLayout
    { bitsDL          :: bits
    }
  | SumLayout
    { tagDL           :: bits
    , alternativesDL  :: Map TagName (Size, DataLayout bits, SourcePos)
    }
  | RecordLayout
    { fieldsDL        :: Map FieldName (DataLayout bits, SourcePos)
    }
  deriving (Show, Eq, Functor, Ord)

-- A range of bit indices into a data type.
--
-- Should satisfy `bitSizeBR >= 1`.
-- Represents the set {bitOffset, bitOffset + 1, ..., bitOffset + bitSize - 1}
data BitRange
  = BitRange { bitSizeBR :: Size, bitOffsetBR :: Size }
  deriving (Eq, Show, Ord)
  
-- A range of bit indices into a data type.
--
-- Should satisfy `bitSizeABR >= 1`, `bitOffsetABR >= 0` and `wordOffsetABR >= 0`.
-- Should be aligned in the sense that `bitSizeABR + bitOffsetABR <= wordSizeBits`.
--
-- Represents the set
-- { wordOffset * wordSizeBits + bitOffset
-- , wordOffset * wordSizeBits + bitOffset + 1
-- , ...
-- , wordOffset * wordSizeBits + bitOffset + bitSize - 1
-- }
--
-- All heap allocated structures are a multiple of a word in size (malloc guarantees this?)
-- and will be word aligned. Hence accesses to an aligned bitrange of a heap-allocated
-- datastructure will be word aligned.
data AlignedBitRange
  = AlignedBitRange { bitSizeABR :: Size, bitOffsetABR :: Size, wordOffsetABR :: Size }
  deriving (Eq, Show, Ord)
  
{- WORD ALIGNMENT TRANSFORMATION -}
wordSizeBits :: Size
wordSizeBits = 32
  
-- Splits a BitRange into an equivalent collection of AlignedBitRanges
-- where each AlignedBitRange
rangeToAlignedRanges
  :: BitRange
    -- Assumes `bitSizeBR range >= 1`. If `bitSizeBR range == 0`, will return [].
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
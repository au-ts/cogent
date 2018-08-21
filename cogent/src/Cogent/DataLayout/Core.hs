{-# LANGUAGE DeriveFunctor #-}
module Cogent.DataLayout.Core where
  
import Data.Map (Map)

import Cogent.Common.Syntax (TagName, FieldName, SourcePos)

{- CORE DATALAYOUT TYPES -}

-- A range of bit indices into a data type.
--
-- Should satisfy `bitSizeBR >= 1` and `bitOffset >= 0`.
-- Represents the set {bitOffset, bitOffset + 1, ..., bitOffset + bitSize - 1}
data BitRange
  = BitRange { bitSizeBR :: Integer, bitOffsetBR :: Integer }
  deriving (Eq, Show, Ord)
  
-- A range of bit indices into a data type.
--
-- Should satisfy `bitSizeABR >= 1`, `bitOffsetABR >= 0` and `wordOffsetABR >= 0`.
-- Should be aligned in the sense that `bitSizeABR + bitOffsetABR <= wordSizeBits`.
-- Represents the set
-- { wordOffset * wordSizeBits + bitOffset
-- , wordOffset * wordSizeBits + bitOffset + 1
-- , ...
-- , wordOffset * wordSizeBits + bitOffset + bitSize - 1
-- }
data AlignedBitRange
  = AlignedBitRange { bitSizeABR :: Integer, bitOffsetABR :: Integer, wordOffsetABR :: Integer }
  deriving (Eq, Show, Ord)

-- A specification of how to get/set the bits for part of a primitive type
--
-- Size 0 surface language blocks go to core language UnitLayout rather than PrimLayout.
-- After splitting, the BitRange of DataBlocks cannot contain a multiple of the wordSize.
-- This ensures that each block is fully contained within an aligned word.
-- All heap allocated structures must be a multiple of a word in size. Malloc guarantees this by default???
data Block
  = DataBlock     BitRange
  | PaddingBlock  Integer
  deriving (Show, Eq)

data DataLayout bits
  = UnitLayout
  | PrimLayout
    { bitsDL          :: bits
    }
  | SumLayout
    { tagDL           :: bits
    , alternativesDL  :: Map TagName (Integer, DataLayout bits, SourcePos)
    }
  | RecordLayout
    { fieldsDL        :: Map FieldName (DataLayout bits, SourcePos)
    }
  deriving (Show, Eq, Functor)
  
{- WORD ALIGNMENT TRANSFORMATION -}
wordSizeBits :: Integer
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
    rangeToAlignedRanges' :: Integer -> Integer -> Integer -> [AlignedBitRange]
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
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

{- * @DataLayout BitRange@ helpers -}

endAllocatedBits' :: DataLayout' BitRange -> Size
endAllocatedBits' = foldr (\range start -> max (bitOffsetBR range + bitSizeBR range) start) 0

endAllocatedBits :: DataLayout BitRange -> Size
endAllocatedBits = foldr (\range start -> max (bitOffsetBR range + bitSizeBR range) start) 0

dataLayoutSizeBytes :: DataLayout BitRange -> Size
dataLayoutSizeBytes = (`div` wordSizeBits) . (alignSize wordSizeBits) . endAllocatedBits


alignLayout' :: DataLayout' BitRange -> DataLayout' [AlignedBitRange]
alignLayout' = fmap rangeToAlignedRanges

alignLayout :: DataLayout BitRange -> DataLayout [AlignedBitRange]
alignLayout = fmap rangeToAlignedRanges

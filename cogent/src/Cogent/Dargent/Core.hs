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
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
module Cogent.Dargent.Core where

import Data.Binary
import Data.IntMap as IM hiding (foldr)
import Data.Map (Map)
import GHC.Generics (Generic)
import Text.Parsec.Pos (SourcePos)

import Cogent.Common.Syntax (TagName, FieldName, Size, DLVarName)
import Cogent.Common.Types (PrimInt (..))
import Cogent.Dargent.Allocation
import Cogent.Dargent.Util
import Cogent.Util

import Data.Nat

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
    , alternativesDL  :: Map TagName (Integer, DataLayout' bits)
      -- ^ The 'Integer' is the tag's value
    }
  | RecordLayout
    { fieldsDL        :: Map FieldName (DataLayout' bits)
    }
#ifdef BUILTIN_ARRAYS
  | ArrayLayout (DataLayout' bits)
#endif
  | VarLayout Nat Size  -- the second argument remembers the pending offset (always in bits)
  deriving (Show, Eq, Functor, Foldable, Generic)

deriving instance Ord bits => Ord (DataLayout' bits)

instance Offsettable a => Offsettable (DataLayout' a) where
  offset n (VarLayout x s) = VarLayout x $ s + n
  offset n l = fmap (offset n) l

instance Binary a => Binary (DataLayout' a)

-- The DataLayout wrapper type
data DataLayout bits
  = Layout (DataLayout' bits) -- this type has this layout
  | CLayout  -- defer the layout of this type to C
  deriving (Show, Eq, Functor, Foldable, Generic)

deriving instance Ord bits => Ord (DataLayout bits)

instance Offsettable a => Offsettable (DataLayout a) where
  offset n = fmap (offset n)

instance Binary a => Binary (DataLayout a)

{- * @DataLayout BitRange@ helpers -}

endAllocatedBits' :: DataLayout' BitRange -> Size
endAllocatedBits' = foldr (\range start -> max (bitOffsetBR range + bitSizeBR range) start) 0

endAllocatedBits :: DataLayout BitRange -> Size
endAllocatedBits = foldr (\range start -> max (bitOffsetBR range + bitSizeBR range) start) 0

dataLayoutSizeInWords :: DataLayout BitRange -> Size
dataLayoutSizeInWords = (`div` wordSizeBits) . (alignSize wordSizeBits) . endAllocatedBits

dataLayoutSizeInBytes' :: DataLayout' BitRange -> Size
dataLayoutSizeInBytes' = (`div` byteSizeBits) . (alignSize byteSizeBits) . endAllocatedBits'

alignLayout' :: DataLayout' BitRange -> DataLayout' [AlignedBitRange]
alignLayout' = fmap (rangeToAlignedRanges wordSizeBits)

alignLayout :: DataLayout BitRange -> DataLayout [AlignedBitRange]
alignLayout = fmap (rangeToAlignedRanges wordSizeBits)

alignLayoutToBytes' :: DataLayout' BitRange -> DataLayout' [AlignedBitRange]
alignLayoutToBytes' = fmap (rangeToAlignedRanges byteSizeBits)

alignLayoutToBytes :: DataLayout BitRange -> DataLayout [AlignedBitRange]
alignLayoutToBytes = fmap (rangeToAlignedRanges byteSizeBits)

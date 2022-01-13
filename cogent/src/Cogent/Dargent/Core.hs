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
{-# LANGUAGE ViewPatterns #-}

module Cogent.Dargent.Core where

import Data.Binary
import Data.IntMap as IM hiding (foldr)
import Data.Map as M (Map, toList)
import GHC.Generics (Generic)
import Text.Parsec.Pos (SourcePos)

import Cogent.Common.Syntax (TagName, FieldName, Size, DLVarName)
import Cogent.Common.Types (PrimInt (..))
import Cogent.Compiler (__impossible)
import Cogent.Dargent.Allocation
import Cogent.Dargent.Surface (Endianness)
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
    , endianness      :: Endianness
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
  | ArrayLayout (DataLayout' bits) Integer
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

loBitRange :: BitRange -> Size
loBitRange (BitRange sz off) = off

hiBitRange :: BitRange -> Size
hiBitRange (BitRange sz off) = sz + off

loDataLayout' :: DataLayout' BitRange -> Size
loDataLayout' UnitLayout = 0
loDataLayout' (PrimLayout b _) = loBitRange b
loDataLayout' (SumLayout tag alts) = foldr (\(_,b) m -> min (loDataLayout' b) m) (loBitRange tag) alts
loDataLayout' (RecordLayout (M.toList -> (f:fs))) = foldr (\(_,b) m -> min (loDataLayout' b) m) (loDataLayout' (snd f)) fs
#ifdef BUILTIN_ARRAYS
loDataLayout' (ArrayLayout d l) = loDataLayout' d
#endif
loDataLayout' (VarLayout v off) = __impossible "loDataLayout': don't know the last bit of a variable"

hiDataLayout' :: DataLayout' BitRange -> Size
hiDataLayout' UnitLayout = 0
hiDataLayout' (PrimLayout b _) = hiBitRange b
hiDataLayout' (SumLayout tag alts) = foldr (\(_,b) m -> max (hiDataLayout' b) m) (hiBitRange tag) alts
hiDataLayout' (RecordLayout fs) = foldr (\b m -> max (hiDataLayout' b) m) 0 fs
#ifdef BUILTIN_ARRAYS
hiDataLayout' (ArrayLayout d l) = let low = loDataLayout' d
                                      sz = dataLayoutSizeInBytes' d
                                   in low + l * sz * 8
#endif
hiDataLayout' (VarLayout v off) = __impossible "hiDataLayout': don't know the last bit of a variable"

loDataLayout :: DataLayout BitRange -> Size
loDataLayout (Layout d) = loDataLayout' d
loDataLayout CLayout = __impossible "loDataLayout: CLayout"

hiDataLayout :: DataLayout BitRange -> Size
hiDataLayout (Layout d) = hiDataLayout' d
hiDataLayout CLayout = __impossible "hiDataLayout: CLayout"

dataLayoutSizeInWords :: DataLayout BitRange -> Size
dataLayoutSizeInWords d = (`div` wordSizeBits) . alignSize wordSizeBits $ hiDataLayout d - loDataLayout d

dataLayoutSizeInBytes' :: DataLayout' BitRange -> Size
dataLayoutSizeInBytes' d = (`div` byteSizeBits) . alignSize byteSizeBits $ hiDataLayout' d - loDataLayout' d

alignLayout' :: DataLayout' BitRange -> DataLayout' [AlignedBitRange]
alignLayout' = fmap (rangeToAlignedRanges wordSizeBits)

alignLayout :: DataLayout BitRange -> DataLayout [AlignedBitRange]
alignLayout = fmap (rangeToAlignedRanges wordSizeBits)

alignLayoutToBytes' :: DataLayout' BitRange -> DataLayout' [AlignedBitRange]
alignLayoutToBytes' = fmap (rangeToAlignedRanges byteSizeBits)

alignLayoutToBytes :: DataLayout BitRange -> DataLayout [AlignedBitRange]
alignLayoutToBytes = fmap (rangeToAlignedRanges byteSizeBits)

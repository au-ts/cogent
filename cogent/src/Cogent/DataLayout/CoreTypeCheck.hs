{-# LANGUAGE NamedFieldPuns #-}
module Cogent.DataLayout.CoreTypeCheck where

import Data.Map (Map)
import Data.Map as M

import Cogent.Compiler              ( __fixme
                                    , __impossible
                                    )
import Cogent.Common.Syntax         ( DataLayoutName
                                    , Size
                                    , TagName
                                    , FieldName
                                    )
import Cogent.Common.Types          ( Sigil (..))
import Cogent.DataLayout.Core
import Cogent.Core                  ( Type (..)
                                    )


-- Checks that all boxed records in the type at any depth
-- have a valid datalayout which matches the associated record
checkType :: Type t -> Bool

checkType (TRecord fields (Boxed _ layout)) =
  let unboxed = TRecord fields Unboxed
  in  checkType unboxed && checkDataLayout layout && unboxed `matchesDataLayout` layout

checkType (TRecord fields _)   = all checkType $ fmap (fst . snd) fields
checkType (TSum alts)          = all checkType $ fmap (fst . snd) alts
checkType (TCon _ ts _)        = all checkType ts
checkType (TFun t1 t2)         = all checkType [t1, t2]
checkType (TProduct t1 t2)     = all checkType [t1, t2]
checkType (TArray t _)         = checkType t
checkType _                    = True


checkDataLayout :: DataLayout BitRange -> Bool
checkDataLayout _ = __fixme (True)
  -- ^ Need to check
  --   1. Blocks for different fields of a record don't overlap
  --   2. Block for tag of an alternative doesn't overlap with blocks for
  --      any of the alternatives.
  --   3. Tag values for an alternative are positive and would fit in its tag block
  --   4. All blocks have size at least 1 and offset at least 0

matchesDataLayout :: Type t -> DataLayout BitRange -> Bool
matchesDataLayout (TCon _ _       (Boxed _ _))  (PrimLayout (BitRange { bitSizeBR })) = bitSizeBR == pointerSizeBits
matchesDataLayout (TRecord _      (Boxed _ _))  (PrimLayout (BitRange { bitSizeBR })) = bitSizeBR == pointerSizeBits
matchesDataLayout (TPrim primInt)               (PrimLayout (BitRange { bitSizeBR })) = bitSizeBR == primIntSizeBits primInt 
matchesDataLayout (TSum alts)                   (SumLayout tagLayout altLayouts)      = __fixme (True)
  -- ^ Need to check the alternative names match,
  --   and that each alternative's type matches the corresponding layout.
matchesDataLayout (TRecord fields Unboxed)      (RecordLayout fieldLayouts)           = __fixme (True)
  -- ^ Need to check the field names match,
  --   and that each field's type matches the corresponding layout.
matchesDataLayout (TUnit)                       (UnitLayout)                          = True
matchesDataLayout _                             _                                     = False


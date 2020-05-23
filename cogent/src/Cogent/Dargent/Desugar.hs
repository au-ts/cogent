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

{-# LANGUAGE ScopedTypeVariables #-}
{- OPTIONS_GHC -Wall -Werror -}

module Cogent.Dargent.Desugar
 ( desugarAbstractTypeSigil
 , desugarSize
 -- Remaining exports for testing only
 , constructDataLayout
 ) where

import Data.Map (Map)
import Data.Map as M
import Data.Maybe (fromJust)
import Data.Traversable (mapAccumL)

import Text.Parsec.Pos (SourcePos, newPos)

import Cogent.Compiler              ( __fixme
                                    , __impossible
                                    , __todo
                                    )
import Cogent.Common.Syntax         ( DataLayoutName
                                    , Size
                                    , TagName
                                    , FieldName
                                    )
import Cogent.Common.Types          ( Sigil(Unboxed, Boxed), PrimInt(..))
import Cogent.Core                  ( Type(..) )
import Cogent.Dargent.Allocation
import Cogent.Dargent.Core
import Cogent.Dargent.Surface       ( DataLayoutSize(Bytes, Bits, Add)
                                    , DataLayoutExpr(..)
                                    , DataLayoutExpr'(..)
                                    , evalSize
                                    )
import Cogent.Dargent.TypeCheck     ( TCDataLayout )
import Cogent.Dargent.Util

{- * Helper functions used in Core.Desugar -}

-- | After WH-normalisation, @TCon _ _ _@ values only represent primitive and abstract types.
--   Primitive types have no sigil, and abstract types may be boxed or unboxed but have no layout.
--   'desugarAbstractTypeSigil' should only be used when desugaring the sigils of abstract types, to eliminate the @Maybe DataLayoutExpr@.
desugarAbstractTypeSigil
  :: Sigil (Maybe TCDataLayout)
  -> Sigil ()
desugarAbstractTypeSigil = fmap desugarMaybeLayout
  where
    desugarMaybeLayout Nothing = ()
    desugarMaybeLayout _       = __impossible "desugarAbstractTypeSigil (Called on TCon after normalisation, only for case when it is an abstract type)"

desugarSize :: DataLayoutSize -> Size
desugarSize = evalSize


{- * CONSTRUCTING 'DataLayout's -}

constructDataLayout' :: Show a => Type t a -> DataLayout' BitRange
constructDataLayout' (TUnit        ) = UnitLayout
constructDataLayout' (TPrim primInt) = PrimLayout $ primBitRange primInt
constructDataLayout' (TSum alternatives)
  | length alternatives > 2 ^ wordSizeBits = __impossible $ "constructDataLayout' (Type check should prevent more alternatives than can fit in a word for sum types embedded in a boxed type with default layout)"
  | otherwise                              = SumLayout tagLayout alternativesLayout
      where
        tagLayout          = fromJust $ newBitRangeBaseSize 0 wordSizeBits {- 0 <= wordSizeBits -}
        alternativesLayout = fromList . snd $ mapAccumL constructAlternativeLayout (wordSizeBits, 0) alternatives

        constructAlternativeLayout
          :: Show a 
          => (Size, Integer) -- ^ Offset and tag value for this alternative.
          -> (TagName, (Type t a, Bool))
          -> ((Size, Integer) -- Offset and tag value for next alternative.
            ,(TagName, (Integer, DataLayout' BitRange)))

        constructAlternativeLayout (minBitOffset, tagValue) (name, (coreType, _)) =
          let layout :: DataLayout' BitRange
              layout = alignOffsettable wordSizeBits minBitOffset $ constructDataLayout' coreType
          in  ((endAllocatedBits' layout, tagValue + 1), (name, (tagValue, layout)))

constructDataLayout' (TRecord rp _ (Boxed {})) = PrimLayout pointerBitRange
constructDataLayout' (TRecord rp fields Unboxed) = RecordLayout . fromList . snd $ mapAccumL go 0 fields
  where
    go :: Show a => Size -> (FieldName, (Type t a, Bool)) -> (Size, (FieldName, DataLayout' BitRange))
    go minBitOffset (name, (coreType, _)) =
      let layout = alignOffsettable wordSizeBits minBitOffset $ go' coreType
      in (endAllocatedBits' layout, (name, layout))

    -- Equations for boxed embedded types
    go' :: Show a => Type t a -> DataLayout' BitRange
    go' (TRecord _ _ (Boxed _ _)) = PrimLayout pointerBitRange
    go' (TCon    _ _ (Boxed _ _)) = PrimLayout pointerBitRange

    -- Equations for as yet unsupported embedded types
    go' (TCon n _ Unboxed) = __impossible $ "go' (Type check should fail on boxed types containing embedded unboxed abstract types)\n Failed on TCon type: " ++ n
    go' (TVar         _  ) = __impossible $ "go' (Type check should fail on boxed types containing type variables)"
    go' (TVarBang     _  ) = __impossible $ "go' (Type check should fail on boxed types containing type variables)"
    go' (TFun         _ _) = __impossible $ "go' (Type check should fail on boxed types containing functions)"
    go' (TString         ) = __impossible $ "go' (Type check should fail on boxed types containing strings)"
#if BUILTIN_ARRAYS
    go' (TArray   _ _ _ _) = __impossible $ "go' (Type check should fail on boxed types containing arrays)"
#endif
    go' (TProduct     _ _) = __impossible $ "go' (Type check should fail on boxed types containing pairs)"
      -- TODO(dargent): implement matching data layouts with types so that the above mentioned type check fails actually occur /mdimeglio
      -- TODO(dargent): implement layout polymorphism to handle boxed types containing type variables /mdimeglio
      -- TODO(dargent): implement layouts for TProduct and TArray types /mdimeglio
      -- TODO(dargent): maybe implement layouts for function types like other boxed (pointer) layouts /mdimeglio
    go' t = __impossible $ "go': type not handled " ++ show t

constructDataLayout' (TCon _  _ (Boxed {})) = PrimLayout pointerBitRange
constructDataLayout' (TCon tn _ Unboxed) = __impossible "constructDataLayout': unboxed TCon not yet supported"
constructDataLayout' _ = __impossible "constructDataLayout': unhandled type"

-- constructs a default layout
constructDataLayout :: Show a => Type t a -> DataLayout BitRange
constructDataLayout = Layout . constructDataLayout'

dummyPos = __fixme $ newPos "Dummy Pos" 0 0 -- FIXME: Not sure what SourcePos to give for layouts generated automatically.





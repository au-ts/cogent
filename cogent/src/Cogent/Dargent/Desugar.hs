
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

module Cogent.Dargent.Desugar
 ( desugarAbstractTypeSigil
 , desugarSigil
 -- Remaining exports for testing only
 , desugarDataLayout
 ) where

import Data.Map (Map)
import Data.Map as M
import Data.Traversable (mapAccumL)

import Text.Parsec.Pos (SourcePos, newPos)

import Cogent.Compiler              ( __fixme
                                    , __impossible
                                    )
import Cogent.Common.Syntax         ( DataLayoutName
                                    , Size
                                    , TagName
                                    , FieldName
                                    )
import Cogent.Common.Types          ( Sigil, PtrSigil(..), PrimInt(..))
import Cogent.Dargent.Surface       ( DataLayoutSize(Bytes, Bits, Add)
                                    , DataLayoutExpr(..)
                                    , DataLayoutExpr'(..)
                                    )
import Cogent.Dargent.TypeCheck     ( desugarSize )
import Cogent.Dargent.Core
import Cogent.Core                  ( Type (..) )
{- * Desugaring 'Sigil's -}

-- | After WH-normalisation, @TCon _ _ _@ values only represent primitive and abstract types.
--   Primitive types have no sigil, and abstract types may be boxed or unboxed but have no layout.
--   'desugarAbstractTypeSigil' should only be used when desugaring the sigils of abstract types, to eliminate the @Maybe DataLayoutExpr@.
desugarAbstractTypeSigil
  :: Sigil (Maybe DataLayoutExpr)
  -> Sigil ()
desugarAbstractTypeSigil = fmap desugarMaybeLayout
  where
    desugarMaybeLayout Nothing = ()
    desugarMaybeLayout _       = __impossible $ "desugarAbstractTypeSigil (Called on TCon after normalisation, only for case when it is an abstract type)"


-- | If a 'DataLayoutExpr' was provided, desugars the 'DataLayoutExpr' to a @DataLayout BitRange@
--   Otherwise, constructs a @DataLayout BitRange@ which matches the type.
--   TODO: Layout polymorphism and layout inference will require changing the second behavior /mdimeglio
--
--   Should not be used to desugar sigils associated with @TCon _ _ _@ types, ie. abstract types.
desugarSigil
  :: Sigil (Maybe DataLayoutExpr)
      -- ^ Since desugarSigil is only called for normalising boxed records (and later, boxed variants),
      --   the @Maybe DataLayoutExpr@ should always be in the @Just layout@ alternative.

  -> Sigil (DataLayout BitRange)

desugarSigil = fmap desugarMaybeLayout
  where
    desugarMaybeLayout Nothing  = CLayout -- default to a CLayout
    desugarMaybeLayout (Just l) = desugarDataLayout l


{- * Desugaring 'DataLayout's -}

desugarDataLayout :: DataLayoutExpr -> DataLayout BitRange
desugarDataLayout l = Layout $ desugarDataLayout' l
  where
    desugarDataLayout' :: DataLayoutExpr -> DataLayout' BitRange
    desugarDataLayout' (DLRepRef _) = __impossible "desugarDataLayout (Called after normalisation)"
    desugarDataLayout' (DLPrim size)
      | bitSize <- desugarSize size
      , bitSize > 0
        = PrimLayout (BitRange bitSize 0)
      | otherwise = UnitLayout
    
    desugarDataLayout' (DLOffset dataLayoutExpr offsetSize) =
      offset (desugarSize offsetSize) (desugarDataLayout' (DL dataLayoutExpr))
    
    desugarDataLayout' (DLRecord fields) =
      RecordLayout $ M.fromList fields'
      where fields' = fmap (\(fname, pos, layout) -> (fname, (desugarDataLayout' layout, pos))) fields
    
    desugarDataLayout' (DLVariant tagExpr alts) =
      SumLayout tagBitRange $ M.fromList alts'
      where
        tagBitRange = case desugarDataLayout' (DL tagExpr) of
          PrimLayout range -> range
          _                -> __impossible $ "desugarDataLayout (Called after typecheck, tag layouts known to be single range)"
    
        alts' = fmap (\(aname, pos, size, layout) -> (aname, (size, desugarDataLayout' layout, pos))) alts

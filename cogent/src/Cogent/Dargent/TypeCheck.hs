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

{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}

module Cogent.Dargent.TypeCheck where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust)

import Control.Monad (guard, foldM)
import Control.Monad.Trans.Except

import Cogent.Common.Syntax (FieldName, TagName, DataLayoutName, Size, DLVarName)
import Cogent.Common.Types (Sigil)
import Cogent.Compiler (__fixme, __impossible)
import Cogent.Dargent.Allocation
import Cogent.Dargent.Surface
import Cogent.Dargent.Util
import Cogent.Util (WriterMaybe, tellEmpty, mapTells)
import Cogent.Surface (Type(..))

import Data.Bifunctor (bimap, first, second)
import Text.Parsec.Pos (SourcePos)

import Debug.Trace

{- * Important exported functions -}

-- | Checks that the layout structure is valid
--
-- This includes that relevant blocks of bits don't overlap
-- And tag values are in the right ranges
tcDataLayoutExpr :: NamedDataLayouts -> [DLVarName] -> DataLayoutExpr -> Except [DataLayoutTcError] Allocation
tcDataLayoutExpr env _ (DLRepRef n) =
  case M.lookup n env of
    Just (_, Just allocation) -> mapPaths (InDecl n) $ return allocation
    Just (_, Nothing)         -> throwE [BadDataLayout n PathEnd]
    Nothing                   -> throwE [UnknownDataLayout n PathEnd]

tcDataLayoutExpr _ _ (DLPrim size) = return $ singletonAllocation (bitRange, PathEnd)
  where
    bitSize  = evalSize size
    bitRange = fromJust $ newBitRangeBaseSize 0 bitSize {- 0 <= bitSize -}

tcDataLayoutExpr env vs (DLOffset dataLayoutExpr offsetSize) =
  offset (evalSize offsetSize) <$> tcDataLayoutExpr env vs (DL dataLayoutExpr)

tcDataLayoutExpr env vs (DLRecord fields) = foldM tcField emptyAllocation fields
  where
    tcField
      :: Allocation -- The accumulated allocation from previous alternatives
      -> (FieldName, SourcePos, DataLayoutExpr)
      -> Except [DataLayoutTcError] Allocation

    tcField accumAlloc (fieldName, pos, dataLayoutExpr) = do
      fieldsAlloc <- mapPaths (InField fieldName pos) (tcDataLayoutExpr env vs dataLayoutExpr)
      except $ first (fmap OverlappingBlocks) $ accumAlloc /\ fieldsAlloc

tcDataLayoutExpr env vs (DLVariant tagExpr alternatives) =
  case primitiveBitRange (DL tagExpr) of
    Just tagBits | isZeroSizedBR tagBits -> throwE [ZeroSizedBitRange (InTag PathEnd)]
                 | otherwise ->
      do
        altsAlloc <- fst <$> foldM (tcAlternative tagBits) (emptyAllocation, M.empty) alternatives
        except $ first (fmap OverlappingBlocks) $ singletonAllocation (tagBits, InTag PathEnd) /\ altsAlloc
    Nothing      -> throwE [TagNotSingleBlock (InTag PathEnd)]
  where
    tcAlternative
      :: BitRange -- Of the variant's tag
      -> (Allocation, Map Size TagName)  -- The accumulated (allocation, set of used tag values) from already evaluated alternatives
      -> (TagName, SourcePos, Size, DataLayoutExpr) -- The alternative to evaluate
      -> Except [DataLayoutTcError] (Allocation, Map Size TagName)

    tcAlternative range (accumAlloc, accumTagValues) (tagName, pos, tagValue, dataLayoutExpr) = do
      alloc     <- (\/) accumAlloc <$> mapPaths (InAlt tagName pos) (tcDataLayoutExpr env vs dataLayoutExpr)
      tagValues <- checkedTagValues
      return (alloc, tagValues)
      where
        checkedTagValues :: Except [DataLayoutTcError] (Map Size TagName)
        checkedTagValues
          | tagValue < 0 || tagValue >= 2 ^ bitSizeBR range =
            throwE [OversizedTagValue (InAlt tagName pos PathEnd) range tagName tagValue]
          | Just conflictingTagName <- tagValue `M.lookup` accumTagValues =
            throwE [SameTagValues (InAlt tagName pos PathEnd) conflictingTagName tagName tagValue]
          | otherwise =
            return $ M.insert tagValue tagName accumTagValues

    primitiveBitRange :: DataLayoutExpr -> Maybe BitRange
    primitiveBitRange (DLPrim size)        = newBitRangeBaseSize 0 (evalSize size)
    primitiveBitRange (DLOffset expr size) = offset (evalSize size) <$> primitiveBitRange (DL expr)
    primitiveBitRange _                    = Nothing

#ifdef BUILTIN_ARRAYS
tcDataLayoutExpr env vs (DLArray e p) = mapPaths (InElmt p) $ tcDataLayoutExpr env vs e
#endif
tcDataLayoutExpr _ _ DLPtr = return $ singletonAllocation (pointerBitRange, PathEnd)
tcDataLayoutExpr _ vs (DLVar n) =
  case n `elem` vs of
    True -> return $ emptyAllocation -- FIXME
    False -> throwE [UnknownDataLayoutVar n PathEnd]
tcDataLayoutExpr _ _ l = __impossible $ "tcDataLayoutExpr; tried to typecheck unexpected layout: " ++ show l


-- NOTE: the check for type-layout compatibility is in Cogent.TypeCheck.Base

-- | Normalises the layout remove references to named layouts
normaliseDataLayoutExpr :: NamedDataLayouts -> DataLayoutExpr -> DataLayoutExpr
normaliseDataLayoutExpr env (DLRepRef n) =
  case M.lookup n env of
    Just (expr, _) -> normaliseDataLayoutExpr env expr
    Nothing        -> __impossible $ "normaliseDataLayoutExpr (RepRef " ++ show n ++ " already known to exist)"
normaliseDataLayoutExpr env (DLRecord fields) =
  DLRecord (fmap (\(fn, pos, expr) -> (fn, pos, normaliseDataLayoutExpr env expr)) fields)
normaliseDataLayoutExpr env (DLVariant tag alts) =
  DLVariant tag (fmap (\(tn, pos, size, expr) -> (tn, pos, size, normaliseDataLayoutExpr env expr)) alts)
normaliseDataLayoutExpr env (DLOffset expr size) = DLOffset (unDataLayoutExpr $ normaliseDataLayoutExpr env (DL expr)) size
#ifdef BUILTIN_ARRAYS
normaliseDataLayoutExpr env (DLArray e pos) = DLArray (normaliseDataLayoutExpr env e) pos
#endif
normaliseDataLayoutExpr _ r = r

{- * Types -}
type NamedDataLayouts = Map DataLayoutName (DataLayoutExpr, Maybe Allocation)
type DataLayoutTcError = DataLayoutTcErrorP DataLayoutPath
-- type DataLayoutTypeMatchError = DataLayoutTcErrorP DataLayoutPath -- TODO: needed to implement `tcDataLayoutTypeMatch`


-- | Errors when checking a DataLayout's structure
--
-- The type parameter @p@ is the type of the path to the error (@DataLayoutPath@)
-- We parameterise by @p@ so we can use the functor instance to map changes to the path
data DataLayoutTcErrorP p
  = OverlappingBlocks       (OverlappingAllocationBlocks p)
    -- ^ Have declared two overlapping bit ranges which shouldn't overlap

  | UnknownDataLayout       DataLayoutName p
    -- ^ Have referenced a data layout which hasn't been declared
    -- The path is the path to the use of that Rep in the DataLayoutExpr being checked

  | BadDataLayout           DataLayoutName p
  -- ^ Have referenced a data layout which isn't correct

  | TagNotSingleBlock       p

  | SameTagValues           p TagName TagName Size
    -- ^ Path to two tags in the same variant and their common value

  | OversizedTagValue       p BitRange TagName Size
    -- ^ Used a tag value which is too large to fit in the variant's tag bit range
    -- Path to the variant, bits for its bit range, name of the alternative, it's tag value

  | ZeroSizedBitRange       p
  -- ^ The layout contains a bit range of size zero.
  -- This could generate an array of length 0, which is disallowed by C

  | UnknownDataLayoutVar    DLVarName p
  deriving (Eq, Show, Ord, Functor)


{-
-- The type parameter p is the type of the path to the error (DataLayoutPath)
-- We parameterise by p so we can use the functor instance to map changes to the path
data DataLayoutTypeMatchErrorP p
  = TypeUnsupported p RawType
  -- Path to where we found a non-layoutable type and the type which wasn't layoutable
  | FieldMissing          p FieldName
  -- Path to the record with a missing field, and expected name of the field
  | FieldUnknown          p FieldName
  -- Path to the record with an unknown field and the field name
  | AltMissing            p TagName
  -- Path to the variant with the missing alternative, and expected name of the alternative
  | AltUnknown            p TagName
  -- Path to the variant with the unknown alternative
  | RecordLayoutExpected  p
  -- Path to where we expect to find a record layout
  | SumLayoutExpected     p
  -- Path to where we expect to find a sum layout
  | PrimLayoutExpected    p
  -- Path to where we expect to find a bit layout
  deriving (Eq, Show, Ord)
-}


{- * Other exported functions -}
tcDataLayoutDecl :: NamedDataLayouts -> DataLayoutDecl -> Except [DataLayoutTcError] Allocation
tcDataLayoutDecl env (DataLayoutDecl pos name expr) =
  mapPaths (InDecl name) (tcDataLayoutExpr env [] expr)

normaliseDataLayoutDecl :: NamedDataLayouts -> DataLayoutDecl -> DataLayoutDecl
normaliseDataLayoutDecl env (DataLayoutDecl pos name expr) =
  DataLayoutDecl pos name (normaliseDataLayoutExpr env expr)

-- Normalises the layout in the sigil to remove references to named layouts
normaliseSigil :: NamedDataLayouts -> Sigil (Maybe DataLayoutExpr) -> Sigil (Maybe DataLayoutExpr)
normaliseSigil env = fmap (fmap (normaliseDataLayoutExpr env))

{- * Other functions -}
evalSize :: DataLayoutSize -> Size
evalSize (Bytes b) = b * 8
evalSize (Bits b)  = b
evalSize (Add a b) = evalSize a + evalSize b

mapPaths
  :: (DataLayoutPath -> DataLayoutPath)
  -> Except [DataLayoutTcError] Allocation
  -> Except [DataLayoutTcError] Allocation
mapPaths f = mapExcept (bimap (fmap (fmap f)) (fmap f))

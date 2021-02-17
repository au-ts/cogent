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

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}

module Cogent.Dargent.TypeCheck where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust)

import Control.Monad (guard, when, foldM)
import Control.Monad.Trans.Except

import Cogent.Common.Syntax (FieldName, TagName, DataLayoutName, Size, DLVarName)
import Cogent.Common.Types (Sigil)
import Cogent.Compiler (__fixme, __impossible, __todo)
import Cogent.Dargent.Allocation
import Cogent.Dargent.Surface
import Cogent.Dargent.Util
import Cogent.Util (WriterMaybe, tellEmpty, mapTells, third3, fourth4)
import Cogent.Surface (Type(..))
import qualified Cogent.TypeCheck.LRow as LRow

import Data.Data
import Data.Bifunctor (bimap, first, second)
import Text.Parsec.Pos (SourcePos)

import Debug.Trace

{- * Definition for datalayout representation in typechecker -}

data TCDataLayout   = TL { unTCDataLayout :: DataLayoutExpr' TCDataLayout }
                    | TLU Int
                    deriving (Show, Data, Eq, Ord)

pattern TLPrim s       = TL (Prim s)
pattern TLRecord ps    = TL (Record ps)
pattern TLVariant t ps = TL (Variant t ps)
#ifdef BUILTIN_ARRAYS
pattern TLArray e s    = TL (Array e s)
#endif
pattern TLOffset e s   = TL (Offset e s)
pattern TLRepRef n es  = TL (RepRef n es)
pattern TLVar n        = TL (LVar n)
pattern TLPtr          = TL Ptr

{- * Utility functions -}

toDLExpr :: TCDataLayout -> DataLayoutExpr
toDLExpr (TLPrim n) = DLPrim n
toDLExpr (TLRecord fs) = DLRecord ((\(x,y,z) -> (x,y,toDLExpr z)) <$> fs)
toDLExpr (TLVariant e fs) = DLVariant (toDLExpr e) ((\(x,y,z,v) -> (x,y,z,toDLExpr v)) <$> fs)
#ifdef BUILTIN_ARRAYS
toDLExpr (TLArray e p) = DLArray (toDLExpr e) p
#endif
toDLExpr (TLOffset e s) = DLOffset (toDLExpr e) s
toDLExpr (TLRepRef n s) = DLRepRef n $ toDLExpr <$> s
toDLExpr (TLVar n) = DLVar n
toDLExpr TLPtr = DLPtr
toDLExpr (TLU _) = __impossible "toDLExpr: layout unifiers shouldn't be here"

toTCDL :: DataLayoutExpr -> TCDataLayout
toTCDL (DLPrim n) = TLPrim n
toTCDL (DLRecord fs) = TLRecord ((\(x,y,z) -> (x,y,toTCDL z)) <$> fs)
toTCDL (DLVariant e fs) = TLVariant (toTCDL e) ((\(x,y,z,v) -> (x,y,z,toTCDL v)) <$> fs)
#ifdef BUILTIN_ARRAYS
toTCDL (DLArray e p) = TLArray (toTCDL e) p
#endif
toTCDL (DLOffset e s) = TLOffset (toTCDL e) s
toTCDL (DLRepRef n s) = TLRepRef n $ toTCDL <$> s
toTCDL (DLVar n) = TLVar n
toTCDL DLPtr = TLPtr

{- * Important exported functions -}

-- | Checks that the layout structure is valid
--
-- This includes that relevant blocks of bits don't overlap
-- And tag values are in the right ranges
tcDataLayoutExpr :: NamedDataLayouts -> [DLVarName] -> DataLayoutExpr -> Except [DataLayoutTcError] Allocation
tcDataLayoutExpr env vs (DLRepRef n s) =
  case M.lookup n env of
    Just ([], _, Just allocation) | length s > 0 -> throwE [TooManyDataLayoutArgs n PathEnd]
                                  | otherwise    -> mapPaths (InDecl n) $ return allocation
    Just ([], _, Nothing) -> throwE [BadDataLayout n PathEnd]
    Just (vars, expr, _)  | length s == length vars
                          -> tcDataLayoutExpr env vs (substDataLayoutExpr (zip vars s) expr)
                          | length s <  length vars
                          -> throwE [TooFewDataLayoutArgs n PathEnd]
                          | length s >  length vars
                          -> throwE [TooManyDataLayoutArgs n PathEnd]
    Nothing               -> throwE [UnknownDataLayout n PathEnd]

tcDataLayoutExpr _ _ (DLPrim size) = return $ singletonAllocation (bitRange, PathEnd)
  where
    bitSize  = evalSize size
    bitRange = fromJust $ newBitRangeBaseSize 0 bitSize {- 0 <= bitSize -}

tcDataLayoutExpr env vs (DLOffset dataLayoutExpr offsetSize) =
  offset (evalSize offsetSize) <$> tcDataLayoutExpr env vs dataLayoutExpr

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
  case primitiveBitRange tagExpr of
    Just tagBits | isZeroSizedBR tagBits -> throwE [ZeroSizedBitRange (InTag PathEnd)]
                 | otherwise ->
      do
        when (2 ^ (bitSizeBR tagBits - 1) > maximum_ (fmap (\(_,_,x,_) -> x) alternatives)) $
          throwE [TagSizeTooLarge (InTag PathEnd)]
        altsAlloc <- fst <$> foldM (tcAlternative tagBits) (emptyAllocation, M.empty) alternatives
        except $ first (fmap OverlappingBlocks) $ singletonAllocation (tagBits, InTag PathEnd) /\ altsAlloc
    Nothing      -> throwE [TagNotSingleBlock (InTag PathEnd)]
  where
    maximum_ [] = __fixme 1  -- FIXME: currently allowing 1-bit tag for empty variant
    maximum_ li = maximum li

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
    primitiveBitRange (DLOffset expr size) = offset (evalSize size) <$> primitiveBitRange expr
    primitiveBitRange _                    = Nothing

#ifdef BUILTIN_ARRAYS
tcDataLayoutExpr env vs (DLArray e p) = mapPaths (InElmt p) $ tcDataLayoutExpr env vs e
#endif
tcDataLayoutExpr _ _ DLPtr = return $ singletonAllocation (pointerBitRange, PathEnd)
tcDataLayoutExpr _ vs (DLVar n) = if n `elem` vs then return undeterminedAllocation
                                                 else throwE [UnknownDataLayoutVar n PathEnd]
tcDataLayoutExpr _ _ l = __impossible $ "tcDataLayoutExpr; tried to typecheck unexpected layout: " ++ show l



-- NOTE: the check for type-layout compatibility is in Cogent.TypeCheck.Base

-- | Normalises the layout remove references to named layouts
normaliseDataLayoutExpr :: NamedDataLayouts -> DataLayoutExpr -> DataLayoutExpr
normaliseDataLayoutExpr env (DLRepRef n s) =
  case M.lookup n env of
    Just (vars, expr, _) -> normaliseDataLayoutExpr env (substDataLayoutExpr (zip vars s) expr)
    Nothing -> __impossible $ "normaliseDataLayoutExpr (RepRef " ++ show n ++ " already known to exist)"
normaliseDataLayoutExpr env (DLRecord fields) =
  DLRecord (fmap (\(fn, pos, expr) -> (fn, pos, normaliseDataLayoutExpr env expr)) fields)
normaliseDataLayoutExpr env (DLVariant tag alts) =
  DLVariant (normaliseDataLayoutExpr env tag) $
    fmap (\(tn, pos, size, expr) -> (tn, pos, size, normaliseDataLayoutExpr env expr)) alts
normaliseDataLayoutExpr env (DLOffset expr size) = DLOffset (normaliseDataLayoutExpr env expr) size
#ifdef BUILTIN_ARRAYS
normaliseDataLayoutExpr env (DLArray e pos) = DLArray (normaliseDataLayoutExpr env e) pos
#endif
normaliseDataLayoutExpr _ r = r

normaliseTCDataLayout :: NamedDataLayouts -> TCDataLayout -> TCDataLayout
normaliseTCDataLayout env (TLRepRef n s) =
  case M.lookup n env of
    Just (vars, expr, _) -> let s' = toDLExpr <$> s
                             in toTCDL $ normaliseDataLayoutExpr env (substDataLayoutExpr (zip vars s') expr)
    Nothing -> __impossible $ "normaliseTCDataLayout (RepRef " ++ show n ++ " already known to exist)"
normaliseTCDataLayout env (TLRecord fs) = TLRecord $ (\(n, p, l) -> (n, p, normaliseTCDataLayout env l)) <$> fs
normaliseTCDataLayout env (TLVariant t as) = TLVariant t $ (\(n, p, s, l) -> (n, p, s, normaliseTCDataLayout env l)) <$> as
normaliseTCDataLayout env (TLOffset l n) = TLOffset (normaliseTCDataLayout env l) n
#ifdef BUILTIN_ARRAYS
normaliseTCDataLayout env (TLArray l p) = TLArray (normaliseTCDataLayout env l) p
#endif
normaliseTCDataLayout _ l = l

-- | Substitutes layout variables with concrete layouts
substDataLayoutExpr :: [(DLVarName, DataLayoutExpr)] -> DataLayoutExpr -> DataLayoutExpr
substDataLayoutExpr = f
  where
    f ps (DLRepRef n s) = DLRepRef n $ f ps <$> s
    f ps (DLRecord fs) = DLRecord $ third3 (f ps) <$> fs
    f ps (DLVariant t fs) = DLVariant (f ps t) $ fourth4 (f ps) <$> fs
    f ps (DLOffset e s) = flip DLOffset s $ f ps e
#ifdef BUILTIN_ARRAYS
    f ps (DLArray e p) = flip DLArray p $ f ps e
#endif
    f ps (DLVar n) = case lookup n ps of
                       Just v -> v
                       Nothing -> DLVar n
    f ps e = e

substTCDataLayout :: [(DLVarName, TCDataLayout)] -> TCDataLayout -> TCDataLayout
substTCDataLayout = f
  where
    f ps (TLRepRef n s) = TLRepRef n $ f ps <$> s
    f ps (TLRecord fs) = TLRecord $ third3 (f ps) <$> fs
    f ps (TLVariant t fs) = TLVariant (f ps t) $ fourth4 (f ps) <$> fs
    f ps (TLOffset e s) = flip TLOffset s $ f ps e
#ifdef BUILTIN_ARRAYS
    f ps (TLArray e p) = flip TLArray p $ f ps e
#endif
    f ps (TLVar n) = case lookup n ps of
                       Just v -> v
                       Nothing -> TLVar n
    f ps e = e

{- * Types -}
-- TODO: we may change DataLayoutExpr within NamedDataLayouts
type NamedDataLayouts = Map DataLayoutName ([DLVarName], DataLayoutExpr, Maybe Allocation)
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

  | TagSizeTooLarge         p
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
  | TooFewDataLayoutArgs    DataLayoutName p
  | TooManyDataLayoutArgs   DataLayoutName p
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
tcDataLayoutDecl env (DataLayoutDecl pos name vars expr) =
  mapPaths (InDecl name) (tcDataLayoutExpr env vars expr)

normaliseDataLayoutDecl :: NamedDataLayouts -> DataLayoutDecl -> DataLayoutDecl
normaliseDataLayoutDecl env (DataLayoutDecl pos name vars expr) =
  DataLayoutDecl pos name vars (normaliseDataLayoutExpr env expr)

-- Normalises the layout in the sigil to remove references to named layouts
normaliseSigil :: NamedDataLayouts -> Sigil (Maybe TCDataLayout) -> Sigil (Maybe TCDataLayout)
normaliseSigil env = fmap (fmap (normaliseTCDataLayout env))

mapPaths
  :: (DataLayoutPath -> DataLayoutPath)
  -> Except [DataLayoutTcError] Allocation
  -> Except [DataLayoutTcError] Allocation
mapPaths f = mapExcept (bimap (fmap (fmap f)) (fmap f))

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
import Data.Maybe (fromJust, fromMaybe)

import Control.Monad (guard, foldM)
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
pattern TLAfter e f    = TL (After e f)
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
toDLExpr (TLAfter e f)  = flip DLAfter f $ toDLExpr e
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
toTCDL (DLAfter e s) = TLAfter (toTCDL e) s
toTCDL (DLRepRef n s) = TLRepRef n $ toTCDL <$> s
toTCDL (DLVar n) = TLVar n
toTCDL DLPtr = TLPtr

-- the following code block is for reference only and will be removed later
{-
 - tcTCDataLayout :: NamedDataLayouts -> TCDataLayout -> Except [DataLayoutTcError] Allocation
 - tcTCDataLayout env (TLRepRef n s) =
 -   case M.lookup n env of
 -     Just ([], _, Just allocation) | length s > 0 -> throwE [TooManyDataLayoutArgs n PathEnd]
 -                                   | otherwise    -> mapPaths (InDecl n) $ return allocation
 -     Just ([], _, Nothing) -> throwE [BadDataLayout n PathEnd]
 -     Just (vars, expr, _)  | length vars == length s
 -                           -> tcTCDataLayout env (substTCDataLayout (zip vars s) $ toTCDL expr)
 -                           | length vars >  length s
 -                           -> throwE [TooFewDataLayoutArgs n PathEnd]
 -                           | length vars <  length s
 -                           -> throwE [TooManyDataLayoutArgs n PathEnd]
 -     Nothing               -> throwE [UnknownDataLayout n PathEnd]
 - 
 - tcTCDataLayout _ (TLPrim size) = return $ singletonAllocation (bitRange, PathEnd)
 -   where
 -     bitSize  = evalSize size
 -     bitRange = fromJust $ newBitRangeBaseSize 0 bitSize {- 0 <= bitSize -}
 - 
 - tcTCDataLayout env (TLOffset dataLayout offsetSize) =
 -   offset (evalSize offsetSize) <$> tcTCDataLayout env dataLayout
 - 
 - tcTCDataLayout env (TLRecord fields) = foldM tcField emptyAllocation fields
 -   where
 -     tcField accumAlloc (fn, pos, tcl) = do
 -       fieldsAlloc <- mapPaths (InField fn pos) $ tcTCDataLayout env tcl
 -       except $ first (fmap OverlappingBlocks) $ accumAlloc /\ fieldsAlloc
 - 
 - tcTCDataLayout env (TLVariant tagExpr alternatives) =
 -   case primitiveBitRange tagExpr of
 -     Just tagBits | isZeroSizedBR tagBits -> throwE [ZeroSizedBitRange (InTag PathEnd)]
 -                  | otherwise ->
 -       do
 -         altsAlloc <- fst <$> foldM (tcAlternative tagBits) (emptyAllocation, M.empty) alternatives
 -         except $ first (fmap OverlappingBlocks) $ singletonAllocation (tagBits, InTag PathEnd) /\ altsAlloc
 -     Nothing      -> throwE [TagNotSingleBlock (InTag PathEnd)]
 -   where
 -     tcAlternative range (accumAlloc, accumTagValues) (tagName, pos, tagValue, tcl) = do
 -       alloc     <- (\/) accumAlloc <$> mapPaths (InAlt tagName pos) (tcTCDataLayout env tcl)
 -       tagValues <- checkedTagValues
 -       return (alloc, tagValues)
 -       where
 -         checkedTagValues :: Except [DataLayoutTcError] (Map Size TagName)
 -         checkedTagValues
 -           | tagValue < 0 || tagValue >= 2 ^ bitSizeBR range =
 -             throwE [OversizedTagValue (InAlt tagName pos PathEnd) range tagName tagValue]
 -           | Just conflictingTagName <- tagValue `M.lookup` accumTagValues =
 -             throwE [SameTagValues (InAlt tagName pos PathEnd) conflictingTagName tagName tagValue]
 -           | otherwise =
 -             return $ M.insert tagValue tagName accumTagValues
 -     primitiveBitRange (TLPrim size)        = newBitRangeBaseSize 0 (evalSize size)
 -     primitiveBitRange (TLOffset expr size) = offset (evalSize size) <$> primitiveBitRange expr
 -     primitiveBitRange _                    = Nothing
 - 
 - #ifdef BUILTIN_ARRAYS
 - tcTCDataLayout env (TLArray e p) = mapPaths (InElmt p) $ tcTCDataLayout env e
 - #endif
 - tcTCDataLayout _ TLPtr = return $ singletonAllocation (pointerBitRange, PathEnd)
 - tcTCDataLayout _ (TLU _) = return undeterminedAllocation
 - tcTCDataLayout _ l = __impossible $ "tcTCDataLayout; tried to typecheck unexpected layout: " ++ show l
 -}

-- | Replaces refs with concrete layout expression
normaliseLayout :: NamedDataLayouts -> TCDataLayout -> TCDataLayout
normaliseLayout env (TLRepRef n s) =
  case M.lookup n env of
    Just (vars, expr) -> normaliseLayout env (substTCDataLayout (zip vars s) expr)
    Nothing -> __impossible $ "normaliseLayout (RepRef " ++ show n ++ " already known to exist)"
normaliseLayout env (TLRecord fs) = TLRecord $ (\(n, p, l) -> (n, p, normaliseLayout env l)) <$> fs
normaliseLayout env (TLVariant t as) = TLVariant (normaliseLayout env t) $
  (\(n, p, s, l) -> (n, p, s, normaliseLayout env l)) <$> as
normaliseLayout env (TLOffset l n) = TLOffset (normaliseLayout env l) n
#ifdef BUILTIN_ARRAYS
normaliseLayout env (TLArray l p) = TLArray (normaliseLayout env l) p
#endif
normaliseLayout _ (TLPrim n) = TLPrim n
normaliseLayout _ (TLVar n) = TLVar n
normaliseLayout _ TLPtr = TLPtr
normaliseLayout _ l = __impossible $ "normaliseLayout: unexpeced layout " ++ show l

-- | Substitutes layout variables with concrete layouts
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
    f ps (TLVar n) = fromMaybe (TLVar n) (lookup n ps)
    f ps e = e

{- * Types -}
type DataLayoutEnv e = Map DataLayoutName ([DLVarName], e)
type NamedDataLayouts = DataLayoutEnv TCDataLayout
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
  | DataLayoutArgsNotMatch  DataLayoutName Int Int p
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

-- Normalises the layout in the sigil to remove references to named layouts
normaliseSigil :: NamedDataLayouts -> Sigil (Maybe TCDataLayout) -> Sigil (Maybe TCDataLayout)
normaliseSigil env = fmap (fmap (normaliseLayout env))

unknownDataLayout :: DataLayoutName -> DataLayoutTcError
unknownDataLayout n = UnknownDataLayout n PathEnd

unknownDataLayoutVar :: DLVarName -> DataLayoutTcError
unknownDataLayoutVar n = UnknownDataLayoutVar n PathEnd

dataLayoutArgsNotMatch :: DLVarName -> Int -> Int -> DataLayoutTcError
dataLayoutArgsNotMatch n exp act = DataLayoutArgsNotMatch n exp act PathEnd

mapPaths
  :: (DataLayoutPath -> DataLayoutPath)
  -> Except [DataLayoutTcError] Allocation
  -> Except [DataLayoutTcError] Allocation
mapPaths f = mapExcept (bimap (fmap (fmap f)) (fmap f))

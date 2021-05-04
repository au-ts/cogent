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

import Cogent.Common.Syntax (FieldName, TagName, DataLayoutName, Size, DLVarName, RepName)
import Cogent.Common.Types (Sigil)
import Cogent.Compiler (__fixme, __impossible, __todo)
import Cogent.Dargent.Allocation
import Cogent.Dargent.Surface
import Cogent.Dargent.Util
import Cogent.Surface (Type(..))
import qualified Cogent.TypeCheck.LRow as LRow
import Cogent.Util (WriterMaybe, tellEmpty, mapTells, third3, fourth4, fst3, thd3)

import Control.Monad (guard, foldM, unless, when)
import Control.Monad.Trans.Except
import Data.Bifunctor (bimap, first, second)
import Data.Data
import qualified Data.Map as M
import Data.List ((\\))
import Data.Map (Map)
import Data.Maybe (fromJust, fromMaybe)
import Lens.Micro
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
pattern TLEndian e n   = TL (Endian e n)
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
toDLExpr (TLAfter e f)  = DLAfter (toDLExpr e) f
toDLExpr (TLEndian e n) = DLEndian (toDLExpr e) n
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
toTCDL (DLAfter e s) = TLAfter (toTCDL e) s
toTCDL (DLEndian e n) = TLEndian (toTCDL e) n
toTCDL (DLRepRef n s) = TLRepRef n $ toTCDL <$> s
toTCDL (DLVar n) = TLVar n
toTCDL DLPtr = TLPtr



{- * Checks that the layout structure is valid -}

tcDataLayoutExpr :: NamedDataLayouts -> [DLVarName] -> DataLayoutExpr -> Except DataLayoutTcError (TCDataLayout, Allocation)
tcDataLayoutExpr env vs (DLRepRef n es) =
  case M.lookup n env of
    Just (vars, expr) | length es == length vars
                      -> tcDataLayoutExpr env vs (substDataLayoutExpr (zip vars es) expr)
                      | otherwise
                      -> throwE $ DataLayoutArgsNotMatch n (length vars) (length es) PathEnd
    Nothing           -> throwE $ UnknownDataLayout n PathEnd

tcDataLayoutExpr _ _ (DLPrim size) = return (TLPrim size, singletonAllocation (bitRange, PathEnd))
  where
    bitSize  = evalSize size
    bitRange = fromJust $ newBitRangeBaseSize 0 bitSize {- 0 <= bitSize -}

tcDataLayoutExpr env vs (DLOffset expr off) = do
  (expr', alloc) <- tcDataLayoutExpr env vs expr
  let alloc' = offset (evalSize off) alloc
  return (TLOffset expr' off, alloc')

tcDataLayoutExpr env vs (DLRecord fields) = do
  blob <- foldM tcField [] fields
  let (fields', fieldAllocs) = unzip $ fmap (\(a,b,c,d) -> ((a,b,c),d)) blob
  alloc <- except $ first OverlappingBlocks $ foldM (/\) emptyAllocation fieldAllocs
  return (TLRecord fields', alloc)
  where lookup' :: (Eq a) => a -> [(a,b,c,d)] -> Maybe (c,d)
        lookup' _key []          =  Nothing
        lookup'  key ((x,_,z,w):xyzws)
          | key == x          =  Just (z,w)
          | otherwise         =  lookup' key xyzws
    
        tcField :: [(FieldName, SourcePos, TCDataLayout, Allocation)]  -- accum
                -> (FieldName, SourcePos, DataLayoutExpr)
                -> Except DataLayoutTcError [(FieldName, SourcePos, TCDataLayout, Allocation)]
        tcField fs (fn, pos, expr) = do
          case expr of
            DLAfter e f -> do case lookup' f fs of
                                Nothing -> throwE $ NonExistingField f (InField fn pos PathEnd)
                                Just (ef,af) -> do 
                                  let end = endOfAllocation af
                                  (e',a) <- tcDataLayoutExpr env vs e
                                  let a' = fmap (InField fn pos) $ offset end a
                                  return (fs ++ [(fn, pos, TLOffset e' (Bits end), a')])
            _           -> do (expr',alloc') <- tcDataLayoutExpr env vs expr
                              return (fs ++ [(fn, pos, expr', fmap (InField fn pos) alloc')])
      
tcDataLayoutExpr env vs (DLVariant tagExpr alts) =
  case primitiveBitRange tagExpr of
    Just tagBits | isZeroSizedBR tagBits -> throwE $ ZeroSizedBitRange (InTag PathEnd)
                 | otherwise ->
      do
        (tagExpr', tagAlloc) <- tcDataLayoutExpr env vs tagExpr
        when (2 ^ (bitSizeBR tagBits) - 1 > maximum (alts <&> (^. _3))) $  -- we don't allow a variant without any alternatives
          throwE $ TagSizeTooLarge (InTag PathEnd)
        (altsExprs, altsAlloc, _) <- foldM (tcAlternative tagBits) ([], emptyAllocation, M.empty) alts
        alloc <- except $ first OverlappingBlocks $ singletonAllocation (tagBits, InTag PathEnd) /\ altsAlloc
        let alts' = zipWith (\(t,p,l,_) e -> (t,p,l,e)) alts altsExprs
        return (TLVariant tagExpr' alts', alloc)
    Nothing -> throwE $ TagNotSingleBlock (InTag PathEnd)

  where
    tcAlternative
      :: BitRange -- Of the variant's tag
      -> ([TCDataLayout], Allocation, Map Integer TagName)
      -- ^ The accumulated (list of layouts, allocation, set of used tag values) from already evaluated alternatives
      -> (TagName, SourcePos, Size, DataLayoutExpr) -- The alternative to evaluate
      -> Except DataLayoutTcError ([TCDataLayout], Allocation, Map Integer TagName)

    tcAlternative range (exprs, accumAlloc, accumTagValues) (tagName, pos, tagValue, expr) = do
      (expr', alloc) <- tcDataLayoutExpr env vs expr
      let alloc' = accumAlloc \/ fmap (InAlt tagName pos) alloc
      tagValues <- checkedTagValues
      return (exprs ++ [expr'], alloc', tagValues)
      where
        checkedTagValues :: Except DataLayoutTcError (Map Size TagName)
        checkedTagValues
          | tagValue < 0 || tagValue >= 2 ^ bitSizeBR range =
            throwE $ OversizedTagValue (InAlt tagName pos PathEnd) range tagName tagValue
          | Just conflictingTagName <- tagValue `M.lookup` accumTagValues =
            throwE $ SameTagValues (InAlt tagName pos PathEnd) conflictingTagName tagName tagValue
          | otherwise =
            return $ M.insert tagValue tagName accumTagValues

    primitiveBitRange :: DataLayoutExpr -> Maybe BitRange
    primitiveBitRange (DLPrim size)        = newBitRangeBaseSize 0 (evalSize size)
    primitiveBitRange (DLOffset expr size) = offset (evalSize size) <$> primitiveBitRange expr
    primitiveBitRange _                    = Nothing

#ifdef BUILTIN_ARRAYS
tcDataLayoutExpr env vs (DLArray e pos) = do
  (e', alloc) <- tcDataLayoutExpr env vs e
  let alloc' = fmap (InElmt pos) alloc
  return (TLArray e' pos, alloc')
#endif

tcDataLayoutExpr _ _ DLPtr = return (TLPtr, singletonAllocation (pointerBitRange, PathEnd))
tcDataLayoutExpr _ vs (DLVar n) = if n `elem` vs then return (TLVar n, undeterminedAllocation)
                                                 else throwE $ UnknownDataLayoutVar n PathEnd
tcDataLayoutExpr _ _ (DLAfter _ f) = throwE $ InvalidUseOfAfter f PathEnd
tcDataLayoutExpr env vs (DLEndian expr end) = do
  (expr', alloc) <- tcDataLayoutExpr env vs expr
  return (TLEndian expr' end, alloc)
tcDataLayoutExpr _ _ l = __impossible $ "tcDataLayoutExpr: tried to typecheck unexpected layout: " ++ show l


-- | Substitutes layout variables with concrete layouts
substDataLayoutExpr :: [(DLVarName, DataLayoutExpr)] -> DataLayoutExpr -> DataLayoutExpr
substDataLayoutExpr = f
  where
    f ps (DLRepRef n s)   = DLRepRef n $ f ps <$> s
    f ps (DLRecord fs)    = DLRecord $ third3 (f ps) <$> fs
    f ps (DLVariant t fs) = DLVariant (f ps t) $ fourth4 (f ps) <$> fs
    f ps (DLOffset e s)   = flip DLOffset s $ f ps e
    f ps (DLAfter e n)    = flip DLAfter n $ f ps e
    f ps (DLEndian e n)   = flip DLEndian n $ f ps e
#ifdef BUILTIN_ARRAYS
    f ps (DLArray e p)    = flip DLArray p $ f ps e
#endif
    f ps (DLVar n)        = fromMaybe (DLVar n) (lookup n ps)
    f ps e                = e

{- * Types -}
type NamedDataLayouts = Map DataLayoutName ([DLVarName], DataLayoutExpr)
type DataLayoutTcError = DataLayoutTcErrorP DataLayoutPath
-- type DataLayoutTypeMatchError = DataLayoutTcErrorP DataLayoutPath -- TODO: needed to implement `tcDataLayoutTypeMatch`


-- | Errors when checking a DataLayout's structure
--
-- The type parameter @p@ is the type of the path to the error (@DataLayoutPath@)
-- We parameterise by @p@ so we can use the functor instance to map changes to the path
data DataLayoutTcErrorP p
  = OverlappingBlocks       [OverlappingAllocationBlocks p]
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
  | DataLayoutArgsNotMatch  DataLayoutName Int Int p
  | OverlappingFields       [FieldName] p
  | CyclicFieldDepedency    [FieldName] p
  | NonExistingField        FieldName p
  | InvalidUseOfAfter       FieldName p
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

unknownDataLayout :: DataLayoutName -> DataLayoutTcError
unknownDataLayout n = UnknownDataLayout n PathEnd

unknownDataLayoutVar :: DLVarName -> DataLayoutTcError
unknownDataLayoutVar n = UnknownDataLayoutVar n PathEnd

dataLayoutArgsNotMatch :: DLVarName -> Int -> Int -> DataLayoutTcError
dataLayoutArgsNotMatch n exp act = DataLayoutArgsNotMatch n exp act PathEnd

overlappingFields :: [FieldName] -> DataLayoutTcError
overlappingFields fs = OverlappingFields fs PathEnd


--
-- Copyright 2020, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--
{-# LANGUAGE DisambiguateRecordFields #-}

module Cogent.LLVM.Types where

-- This module mostly deals with converting Cogent types to LLVM types, plus
-- various utilities for types

import Cogent.Common.Syntax (Size, TagName, TypeName, VarName)
import Cogent.Common.Types (PrimInt (..), Sigil (Boxed, Unboxed))
import Cogent.Compiler (__impossible)
import Cogent.Core as Core
import Cogent.Dargent.Util (primIntSizeBits)
import Data.Function (on)
import Data.List (intercalate, maximumBy)
import Data.Maybe (fromJust)
import Data.Set (Set, empty, fromList, union, unions)
import LLVM.AST
import qualified LLVM.AST as AST
import LLVM.AST.Type (i32, i8, ptr)
import LLVM.IRBuilder.Module (MonadModuleBuilder)

-- Given a Cogent type, produce an LLVM type
toLLVMType :: (MonadModuleBuilder m) => Core.Type t b -> m AST.Type
-- Primitive types are just LLVM integers
toLLVMType (TPrim p) = pure $ IntegerType $ fromInteger $ primIntSizeBits p
-- An unboxed record can be represented as an LLVM structure type
toLLVMType (TRecord _ ts Unboxed) = StructureType False <$> mapM toLLVMType (fieldTypes ts)
-- A boxed record is a pointer to whatever the unboxed representation would be
toLLVMType (TRecord r ts (Boxed _ _)) = ptr <$> toLLVMType (TRecord r ts Unboxed)
-- Unit shall be represented as a byte as VoidType is not a first class type
toLLVMType TUnit = pure i8
-- Strings are just byte pointers
toLLVMType TString = pure $ ptr i8
-- We represent variants as an LLVM structure with a 32-bit tag and a field
-- which is of the largest possible variant option, just like a C union
toLLVMType (TSum ts) = toLLVMType (maxMember ts) >>= \f -> pure $ StructureType False [i32, f]
-- Function types are pointers to LLVM function types
toLLVMType (TFun t1 t2) = do
    at <- toLLVMType t1
    rt <- toLLVMType t2
    pure $ ptr $ FunctionType rt [at] False
-- An unboxed abstract type is just a reference to the typedef for it
toLLVMType t@(TCon _ _ Unboxed) = pure $ NamedTypeReference (mkName (nameType t))
-- A boxed abstract type is a pointer to the unboxed representation
toLLVMType (TCon tn ts (Boxed _ _)) = ptr <$> toLLVMType (TCon tn ts Unboxed)
toLLVMType _ = error "unknown type"

-- Convert a Cogent type to a string name for it
-- Abuse the fact that llvm identifiers can be basically any character
nameType :: Core.Type t b -> TypeName
nameType (TPrim p) = case p of
    U8 -> "U8"
    U16 -> "U16"
    U32 -> "U32"
    U64 -> "U64"
    Boolean -> "Bool"
    _ -> "Unknown"
nameType (TRecord _ ts _) =
    "{"
        ++ intercalate
            ","
            ( ( \(n, (t, _)) ->
                    n ++ ":"
                        ++ nameType t
              )
                <$> ts
            )
        ++ "}"
nameType TUnit = "()"
nameType TString = "String"
nameType (TSum ts) =
    "<"
        ++ intercalate
            "|"
            ( ( \(n, (t, _)) ->
                    n
                        ++ ( case t of
                                TUnit -> ""
                                _ -> " " ++ nameType t
                           )
              )
                <$> ts
            )
        ++ ">"
nameType (TFun t1 t2) = nameType t1 ++ "->" ++ nameType t2
nameType (TCon tn ts _) = unwords $ tn : (nameType <$> ts)
nameType _ = error "unknown type"

-- Extract just the record field types, or variant argument types
fieldTypes :: [(s, (Core.Type t b, Bool))] -> [Core.Type t b]
fieldTypes = map (fst . snd)

-- Get the largest field type, preferring earlier fields in the case of a tie
maxMember :: [(s, (Core.Type t b, Bool))] -> Core.Type t b
maxMember ts = maximumBy (compare `on` typeSize) (reverse (fieldTypes ts))

-- Look up a variant constructor's argument type
tagType :: Core.Type t b -> TagName -> Core.Type t b
tagType (TSum ts) tag = fst $ fromJust $ lookup tag ts
tagType _ _ = error "not a variant type"

-- Check if a type is primitive or not
isPrim :: Core.Type t b -> Bool
isPrim TPrim {} = True
isPrim TUnit = True
isPrim _ = False

-- In future we should just import this from Dargent
pointerSizeBits :: Size
pointerSizeBits = 64 -- need to check 32 bit edge cases

-- A C type can be laid out as:
--  - a pointer
--  - an immediate value of some number of bits
--  - a struct aggregating more type layouts
--  - a union aggregating more type layouts
-- Some stuff here currently ignores Dargent for the sake of simplicity
data CLayout t b = Ptr (Core.Type t b) | Im Size | St [CLayout t b] | Un [CLayout t b]

-- Calculate the C-like representation of a Cogent type
typeLayout :: Core.Type t b -> CLayout t b
typeLayout (TPrim p) = Im (primIntSizeBits p)
typeLayout TUnit = Im 8
typeLayout (TRecord _ ts Unboxed) = St (typeLayout <$> fieldTypes ts)
typeLayout (TSum ts) = St [Im 32, Un (typeLayout <$> fieldTypes ts)]
typeLayout t = Ptr t

-- Calculate the minimum bit alignment of a type layout
typeAlignment :: CLayout t b -> Size
typeAlignment (Ptr _) = pointerSizeBits
typeAlignment (Im i) = min i pointerSizeBits
typeAlignment (St ts) = maximum (typeAlignment <$> ts)
typeAlignment (Un ts) = maximum (typeAlignment <$> ts)
typeAlignment _ = __impossible "typeAlignment"

-- Round up k to the next multiple of n, unless k already is a multiple of n
roundUp :: Integer -> Integer -> Integer
roundUp k n
    | k `mod` n == 0 = k
    | otherwise = (k `div` n + 1) * n

-- A section of memory is made up of padding, immediate values, and pointer values
data Field t b = Padding | Value | Pointer (Core.Type t b) | Invalid
type MemLayout t b = [(Field t b, Size)]

-- Convert a C-like layout to a memory layout including padding
flatLayout :: CLayout t b -> (Size, MemLayout t b)
flatLayout (Ptr t) = (pointerSizeBits, [(Pointer t, pointerSizeBits)])
flatLayout (Im i) = (i, [(Value, i)])
flatLayout (Un ts) = maximumBy (compare `on` fst) (reverse (flatLayout <$> ts))
flatLayout (St ts) = foldl flatLayout' (0, []) ts
    where
        flatLayout' :: (Size, MemLayout t b) -> CLayout t b -> (Size, MemLayout t b)
        flatLayout' (offset, layout) t =
            let layout' = flatLayout t
                alignment = typeAlignment t
                offset' = roundUp offset alignment
                padding = offset' - offset
             in ( offset' + fst layout'
                , layout ++ [(Padding, padding) | padding > 0] ++ snd layout'
                )
flatLayout _ = __impossible "flatLayout"

-- Given a Cogent type, return how many bits it should occupy with padding
typeSize :: Core.Type t b -> Size
typeSize = fst . flatLayout . typeLayout

-- Check if the thing at an offset in a layout is a value, pointer, padding or nothing
memLookup :: Size -> MemLayout t b -> Field t b
memLookup _ [] = Invalid
memLookup offset ((m, s) : ms)
    | offset == 0 = m
    | offset < 0 = Invalid
    | otherwise = memLookup (offset - s) ms

-- Collect all the tagnames for a definition or type
collectTags :: Core.Definition TypedExpr VarName VarName -> Set TagName
collectTags (FunDef _ _ _ _ t rt _) = collectTags' t `union` collectTags' rt
collectTags (AbsDecl _ _ _ _ t rt) = collectTags' t `union` collectTags' rt
collectTags (TypeDef _ _ mt) = maybe empty collectTags' mt

collectTags' :: Core.Type t b -> Set TagName
collectTags' (TRecord _ ts _) = unions $ collectTags' <$> fieldTypes ts
collectTags' (TSum ts) = fromList (fst <$> ts) `union` unions (collectTags' <$> fieldTypes ts)
collectTags' (TFun t1 t2) = collectTags' t1 `union` collectTags' t2
collectTags' (TCon _ ts _) = unions $ collectTags' <$> ts
collectTags' _ = empty

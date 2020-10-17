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

module Cogent.LLVM.Types (
    toLLVMType,
    typeSize,
    nameType,
    maxMember,
    tagType,
    isNativePointer,
    pointerSizeBits,
    isPrim,
    fieldTypes,
) where

-- This module mostly deals with converting Cogent types to LLVM types, plus
-- various utilities for types

import Cogent.Common.Syntax (Size, TagName, TypeName)
import Cogent.Common.Types (PrimInt (..), Sigil (Boxed, Unboxed))
import Cogent.Core as Core (Type (TCon, TFun, TPrim, TRecord, TString, TSum, TUnit))
import Cogent.Dargent.Util (primIntSizeBits)
import Data.Function (on)
import Data.List (intercalate, maximumBy)
import Data.Maybe (fromMaybe)
import LLVM.AST
import qualified LLVM.AST as AST
import LLVM.AST.Type (i32, i8, ptr)

-- A type can be laid out as:
--  - a pointer
--  - an immediate value of some number of bits
--  - a struct aggregating more type layouts
--  - a union aggregating more type layouts
-- Some stuff here currently ignores Dargent for the sake of simplicity
data TypeLayout = Ptr | Im Size | St [TypeLayout] | Un [TypeLayout]
    deriving (Show)

-- In future we should just import this from Dargent
pointerSizeBits :: Size
pointerSizeBits = 64 -- need to check 32 bit edge cases

-- Given a Cogent type, produce an LLVM type
toLLVMType :: Core.Type t b -> AST.Type
-- Primitive types are just LLVM integers
toLLVMType (TPrim p) = IntegerType (fromInteger (primIntSizeBits p))
-- An unboxed record can be represented as an LLVM structure type
toLLVMType (TRecord _ ts Unboxed) =
    StructureType
        { isPacked = False
        , elementTypes = toLLVMType <$> fieldTypes ts
        }
-- A boxed record is a pointer to whatever the unboxed representation would be
toLLVMType (TRecord r ts (Boxed _ _)) = ptr $ toLLVMType (TRecord r ts Unboxed)
-- Unit shall be represented as a byte as VoidType is not a first class type
toLLVMType TUnit = i8
-- Strings are just byte pointers
toLLVMType TString = ptr i8
-- We represent variants as an LLVM structure with a 32-bit tag and a field
-- which is of the largest possible variant option, just like a C union
toLLVMType (TSum ts) =
    StructureType
        { isPacked = False
        , elementTypes = [i32, toLLVMType (maxMember ts)]
        }
-- Function types are pointers to LLVM function types
toLLVMType (TFun t1 t2) =
    ptr
        FunctionType
            { resultType = toLLVMType t2
            , argumentTypes = [toLLVMType t1]
            , isVarArg = False
            }
-- An unboxed abstract type is just a reference to the typedef for it
toLLVMType t@(TCon _ _ Unboxed) = NamedTypeReference (mkName (nameType t))
-- A boxed abstract type is a pointer to the unboxed representation
toLLVMType (TCon tn ts (Boxed _ _)) = ptr $ toLLVMType (TCon tn ts Unboxed)
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

-- Get the largest field type
maxMember :: [(s, (Core.Type t b, Bool))] -> Core.Type t b
maxMember ts = maximumBy (compare `on` typeSize) (fieldTypes ts)

-- Look up a variant constructor's argument type
tagType :: Core.Type t b -> TagName -> Core.Type t b
tagType (TSum ts) tag =
    fst $
        fromMaybe
            (error "cant find tag")
            (lookup tag ts)
tagType _ _ = error "non variant type has no tags"

-- Check whether a type would be represented as a native pointer or not
isNativePointer :: Core.Type t b -> Bool
isNativePointer t = case typeLayout t of
    Ptr -> True
    _ -> False

-- Check if a type is primitive or not
isPrim :: Core.Type t b -> Bool
isPrim TPrim {} = True
isPrim TUnit = True
isPrim _ = False

-- Calculate the representation of a Cogent type
typeLayout :: Core.Type t b -> TypeLayout
typeLayout (TPrim p) = Im (primIntSizeBits p)
typeLayout TUnit = Im 8
typeLayout (TRecord _ ts Unboxed) = St (typeLayout <$> fieldTypes ts)
typeLayout (TSum ts) = St [Im 32, Un (typeLayout <$> fieldTypes ts)]
typeLayout _ = Ptr

-- Calculate the minimum bit alignment of a type layout
typeAlignment :: TypeLayout -> Size
typeAlignment Ptr = pointerSizeBits
typeAlignment (Im i) = min i pointerSizeBits
typeAlignment (St ts) = maximum (typeAlignment <$> ts)
typeAlignment (Un ts) = maximum (typeAlignment <$> ts)

-- Round up k to the next multiple of n, unless k already is a multiple of n
roundUp :: Integer -> Integer -> Integer
roundUp k n
    | k `mod` n == 0 = k
    | otherwise = (k `div` n + 1) * n

-- Given a Cogent type, return how many bits it should occupy
typeSize :: Core.Type t b -> Size
typeSize t = typeSize' (typeLayout t)
    where
        -- Calculate the bits required for a type layout
        typeSize' :: TypeLayout -> Size
        typeSize' Ptr = pointerSizeBits
        typeSize' (Im i) = i
        typeSize' t@(St ts) = roundUp (typeSize'' 0 ts) (typeAlignment t)
        typeSize' t@(Un ts) = roundUp (maximum (typeSize' <$> ts)) (typeAlignment t)

        -- The accumulator keeps track of the current offset of the type so far
        typeSize'' :: Size -> [TypeLayout] -> Size
        typeSize'' offset [] = offset
        typeSize'' offset (t : ts) =
            let size = typeSize' t
                alignment = typeAlignment t
             in typeSize'' (size + roundUp offset alignment) ts

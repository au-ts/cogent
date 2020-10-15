{-# LANGUAGE DisambiguateRecordFields #-}

module Cogent.LLVM.Types where

import Cogent.Common.Syntax (Size, TagName, TypeName)
import Cogent.Common.Types (PrimInt (..), Sigil (Boxed, Unboxed))
import Cogent.Core as Core
import Cogent.Dargent.Util (primIntSizeBits)
import Data.Function (on)
import Data.List (intercalate, maximumBy)
import Data.Maybe (fromMaybe)
import LLVM.AST
import qualified LLVM.AST as AST
import LLVM.AST.Constant
import LLVM.AST.Type (i32, i8, ptr)

data TypeLayout = Ptr | Im Size | St [TypeLayout] | Un [TypeLayout]
    deriving (Show)

pointerSizeBits :: Size
pointerSizeBits = 64 -- need to check 32 bit edge cases

toLLVMType :: Core.Type t b -> AST.Type
toLLVMType (TPrim p) = IntegerType (fromInteger (primIntSizeBits p))
toLLVMType (TRecord _ ts Unboxed) =
    StructureType
        { isPacked = False
        , elementTypes = toLLVMType <$> fieldTypes ts
        }
toLLVMType (TRecord r ts (Boxed _ _)) = ptr $ toLLVMType (TRecord r ts Unboxed)
toLLVMType TUnit = i8 -- as VoidType is not a first class type, use byte for ()
toLLVMType TString = ptr i8
toLLVMType (TSum ts) =
    StructureType
        { isPacked = False
        , elementTypes = [i32, toLLVMType (maxMember ts)]
        }
toLLVMType (TFun t1 t2) =
    ptr
        FunctionType
            { resultType = toLLVMType t2
            , argumentTypes = [toLLVMType t1]
            , isVarArg = False
            }
toLLVMType t@(TCon _ _ Unboxed) = NamedTypeReference (mkName (nameType t))
toLLVMType (TCon tn ts (Boxed _ _)) = ptr $ toLLVMType (TCon tn ts Unboxed)
#ifdef BUILTIN_ARRAYS
toLLVMType (TArray t l s mh) =
  ArrayType { nArrayElements = __todo "toLLVMType: we cannot evaluate LExpr to a constant"
            , elementType = toLLVMType t
            }
#endif
toLLVMType _ = error "unknown type"

-- abuse the fact that llvm identifiers can be basically any character
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

fieldTypes :: [(s, (Core.Type t b, Bool))] -> [Core.Type t b]
fieldTypes = map (fst . snd)

maxMember :: [(s, (Core.Type t b, Bool))] -> Core.Type t b
maxMember ts = maximumBy (compare `on` typeSize) (fieldTypes ts)

tagType :: Core.Type t b -> TagName -> Core.Type t b
tagType (TSum ts) tag =
    fst $
        fromMaybe
            (error "cant find tag")
            (lookup tag ts)
tagType _ _ = error "non variant type has no tags"

isNativePointer :: Core.Type t b -> Bool
isNativePointer t = case typeLayout t of
    Ptr -> True
    _ -> False

isPrim :: Core.Type t b -> Bool
isPrim TPrim {} = True
isPrim TUnit = True
isPrim _ = False

typeLayout :: Core.Type t b -> TypeLayout
typeLayout (TPrim p) = Im (primIntSizeBits p)
typeLayout TUnit = Im 8
typeLayout (TRecord _ ts _) = St (typeLayout <$> fieldTypes ts)
typeLayout (TSum ts) = St [Im 32, Un (typeLayout <$> fieldTypes ts)]
typeLayout _ = Ptr

typeAlignment :: TypeLayout -> Size
typeAlignment Ptr = pointerSizeBits
typeAlignment (Im i) = min i pointerSizeBits
typeAlignment (St ts) = maximum (typeAlignment <$> ts)
typeAlignment (Un ts) = maximum (typeAlignment <$> ts)

roundUp :: Integer -> Integer -> Integer
roundUp k n
    | k `mod` n == 0 = k
    | otherwise = (k `div` n + 1) * n

typeSize :: Core.Type t b -> Size
typeSize t = typeSize' (typeLayout t)

typeSize' :: TypeLayout -> Size
typeSize' Ptr = pointerSizeBits
typeSize' (Im i) = i
typeSize' t@(St ts) = roundUp (typeSize'' 0 ts) (typeAlignment t)
typeSize' t@(Un ts) = roundUp (maximum (typeSize' <$> ts)) (typeAlignment t)

typeSize'' :: Size -> [TypeLayout] -> Size
typeSize'' offset [] = offset
typeSize'' offset (t : ts) =
    let size = typeSize' t
        alignment = typeAlignment t
     in typeSize'' (size + roundUp offset alignment) ts

constInt :: Integer -> Integer -> Operand
constInt n i = ConstantOperand Int {integerBits = fromInteger n, integerValue = i}

constUndef :: AST.Type -> Operand
constUndef t = ConstantOperand Undef {constantType = t}

{-# LANGUAGE DisambiguateRecordFields #-}

module Cogent.LLVM.Types where

import Cogent.Common.Syntax (Size, TagName)
import Cogent.Core as Core
import Cogent.Dargent.Util (primIntSizeBits)
import Data.Function (on)
import Data.List (maximumBy)
import Data.Maybe (fromMaybe)
import LLVM.AST
import qualified LLVM.AST as AST
import LLVM.AST.Constant
import LLVM.AST.Type

data TypeLayout = Ptr | Im Size | St [TypeLayout] | Un [TypeLayout]
    deriving (Show)

pointerSizeBits :: Size
pointerSizeBits = 64 -- need to check 32 bit edge cases

toLLVMType :: Core.Type t b -> AST.Type
toLLVMType (TPrim p) = IntegerType (fromInteger (primIntSizeBits p))
toLLVMType (TRecord _ ts _) =
    -- don't know how to deal with sigil
    StructureType
        { isPacked = False
        , elementTypes = map toLLVMType (fieldTypes ts)
        }
toLLVMType TUnit = IntegerType 8 -- as VoidType is not a first class type, use byte for ()
toLLVMType TString = ptr (IntegerType 8)
toLLVMType (TSum ts) =
    StructureType
        { isPacked = False
        , elementTypes = [IntegerType 32, toLLVMType (maxMember ts)]
        }
toLLVMType (TFun t1 t2) =
    ptr
        FunctionType
            { resultType = toLLVMType t2
            , argumentTypes = [toLLVMType t1]
            , isVarArg = False
            }
toLLVMType (TCon name _ _) = NamedTypeReference (mkName name) -- arbitrary pointer
#ifdef BUILTIN_ARRAYS
toLLVMType (TArray t l s mh) =
  ArrayType { nArrayElements = __todo "toLLVMType: we cannot evaluate LExpr to a constant"
            , elementType = toLLVMType t
            }
#endif
toLLVMType _ = error "unknown type"

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
typeLayout (TRecord _ ts _) = St (map typeLayout (fieldTypes ts))
typeLayout (TSum ts) = St [Im 32, Un (map typeLayout (fieldTypes ts))]
typeLayout _ = Ptr

typeAlignment :: TypeLayout -> Size
typeAlignment Ptr = pointerSizeBits
typeAlignment (Im i) = min i pointerSizeBits
typeAlignment (St ts) = maximum (map typeAlignment ts)
typeAlignment (Un ts) = maximum (map typeAlignment ts)

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
typeSize' t@(Un ts) = roundUp (maximum (map typeSize' ts)) (typeAlignment t)

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

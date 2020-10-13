{-# LANGUAGE DisambiguateRecordFields #-}

module Cogent.LLVM.Types where

import Cogent.Common.Types
import Cogent.Core as Core
import Data.Function (on)
import Data.List (maximumBy)
import LLVM.AST
import qualified LLVM.AST as AST
import LLVM.AST.AddrSpace
import LLVM.AST.Constant

data TypeLayout = Im Int | St [TypeLayout] | Un [TypeLayout]
    deriving (Show)

primBits :: PrimInt -> Int
primBits Boolean = 1
primBits U8 = 8
primBits U16 = 16
primBits U32 = 32
primBits U64 = 64

toLLVMType :: Core.Type t b -> AST.Type
toLLVMType (TPrim p) = IntegerType (toEnum (primBits p))
toLLVMType (TRecord _ ts _) =
    -- don't know how to deal with sigil
    StructureType
        { isPacked = False
        , elementTypes = map toLLVMType (fieldTypes ts)
        }
toLLVMType TUnit = IntegerType 8 -- as VoidType is not a first class type, use byte for ()
toLLVMType TString = ptrTo (IntegerType 8)
toLLVMType (TSum ts) = sumTypeLift (toLLVMType (maxMember ts))
toLLVMType (TFun t1 t2) =
    ptrTo
        FunctionType
            { resultType = toLLVMType t2
            , argumentTypes = [toLLVMType t1]
            , isVarArg = False
            }
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

typeLayout :: Core.Type t b -> TypeLayout
typeLayout (TPrim p) = case p of
    Boolean -> Im 8 -- boolean takes up a whole byte
    U8 -> Im 8
    U16 -> Im 16
    U32 -> Im 32
    U64 -> Im 64
typeLayout TUnit = Im 8 -- so does unit
typeLayout (TRecord _ ts _) = St (map typeLayout (fieldTypes ts))
typeLayout (TSum ts) = St [Im 32, Un (map typeLayout (fieldTypes ts))]
typeLayout _ = Im 64

typeAlignment :: TypeLayout -> Int
typeAlignment (Im i) = i -- self-alignment
typeAlignment (St ts) = maximum (map typeAlignment ts)
typeAlignment (Un ts) = maximum (map typeAlignment ts)

roundUp :: Int -> Int -> Int
roundUp k n
    | k `mod` n == 0 = k
    | otherwise = (k `div` n + 1) * n

typeSize :: Core.Type t b -> Int
typeSize t = typeSize' (typeLayout t)

typeSize' :: TypeLayout -> Int
typeSize' (Im i) = i
typeSize' t@(St ts) = roundUp (typeSize'' 0 ts) (typeAlignment t)
typeSize' t@(Un ts) = roundUp (maximum (map typeSize' ts)) (typeAlignment t)

typeSize'' :: Int -> [TypeLayout] -> Int
typeSize'' offset [] = offset
typeSize'' offset (t : ts) =
    let size = typeSize' t
        alignment = typeAlignment t
     in typeSize'' (size + roundUp offset alignment) ts

sumTypeLift :: AST.Type -> AST.Type
sumTypeLift t =
    StructureType
        { isPacked = False
        , elementTypes = [IntegerType 32, t]
        }

ptrTo :: AST.Type -> AST.Type
ptrTo t = PointerType {pointerReferent = t, pointerAddrSpace = AddrSpace 0}

unPtr :: AST.Type -> AST.Type
unPtr (PointerType t _) = t
unPtr t = t

constInt :: Int -> Integer -> Operand
constInt n i = ConstantOperand Int {integerBits = fromIntegral n, integerValue = i}

constUndef :: AST.Type -> Operand
constUndef t = ConstantOperand Undef {constantType = t}

{-# LANGUAGE DisambiguateRecordFields #-}

module Cogent.LLVM.Types where

import Cogent.Common.Syntax (TagName)
import Cogent.Common.Types
import Cogent.Core as Core
import LLVM.AST
import qualified LLVM.AST as AST
import LLVM.AST.AddrSpace
import LLVM.AST.Constant

toLLVMInt :: PrimInt -> AST.Type
toLLVMInt Boolean = IntegerType 1
toLLVMInt U8 = IntegerType 8
toLLVMInt U16 = IntegerType 16
toLLVMInt U32 = IntegerType 32
toLLVMInt U64 = IntegerType 64

toLLVMType :: Core.Type t b -> AST.Type
toLLVMType (TPrim p) = toLLVMInt p
toLLVMType (TRecord _ ts _) =
    -- don't know how to deal with sigil
    ptrTo
        StructureType
            { isPacked = False
            , elementTypes = map toLLVMType (fieldTypes ts)
            }
toLLVMType TUnit = IntegerType 2 -- as VoidType is not a first class type, use i2 for ()
toLLVMType TString = ptrTo (IntegerType 8)
toLLVMType (TSum ts) = sumTypeLift (IntegerType (toEnum (maxTypeSize ts)))
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

maxTypeSize :: [(TagName, (Core.Type t b, Bool))] -> Int
maxTypeSize ts =
    let typeSizes = map typeSize (fieldTypes ts)
     in foldr max 8 typeSizes

typeSize :: Core.Type t b -> Int
typeSize (TPrim p) = case p of
    Boolean -> 1
    U8 -> 8
    U16 -> 16
    U32 -> 32
    U64 -> 64
typeSize TUnit = 0
typeSize _ = 32 -- assuming 32 bit machine

sumTypeLift :: AST.Type -> AST.Type
sumTypeLift t =
    ptrTo
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

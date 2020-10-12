{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}

module Cogent.LLVM.CCompat where

import Cogent.Common.Syntax (VarName)
import Cogent.Common.Types
import Cogent.Core as Core
import Cogent.LLVM.CodeGen
import Cogent.LLVM.Types
import Data.ByteString.Short.Internal (ShortByteString)
import LLVM.AST as AST
import LLVM.AST.CallingConvention as CC
import qualified LLVM.AST.Constant as C
import LLVM.AST.Global (Global (..))
import LLVM.AST.ParameterAttribute
import LLVM.AST.Typed (typeOf)

data RegLayout = One AST.Type | Two AST.Type AST.Type | Ref deriving (Show)

data TypeLayout = Val Int | Agg [TypeLayout] deriving (Show)

typeLayout :: Core.Type t b -> TypeLayout
typeLayout (TPrim p) = case p of
    Boolean -> Val 8 -- boolean takes up a whole byte
    U8 -> Val 8
    U16 -> Val 16
    U32 -> Val 32
    U64 -> Val 64
typeLayout TUnit = Val 8 -- so does unit
typeLayout (TRecord _ ts _) = Agg (map typeLayout (fieldTypes ts))
typeLayout _ = Val 32

typeAlignment :: TypeLayout -> Int
typeAlignment (Val i) = i -- self-alignment
typeAlignment (Agg ts) = maximum (map typeAlignment ts)

sizeof :: TypeLayout -> Int
sizeof (Val i) = i
sizeof t@(Agg ts) = roundUp (sizeof' 0 ts) (typeAlignment t)

sizeof' :: Int -> [TypeLayout] -> Int
sizeof' offset [] = offset
sizeof' offset (t : ts) =
    let size = sizeof t
        alignment = typeAlignment t
     in sizeof' (size + roundUp offset alignment) ts

regLayout :: Core.Type t b -> RegLayout
regLayout t
    | s <= 64 = One (IntegerType (toEnum s))
    | s <= 128 = Two (IntegerType 64) (IntegerType (toEnum (s - 64)))
    | otherwise = Ref
    where
        s = sizeof (typeLayout t)

roundUp :: Int -> Int -> Int
roundUp k n
    | k `mod` n == 0 = k
    | otherwise = (k `div` n + 1) * n

needsWrapper :: Core.Type t b -> Bool
needsWrapper TRecord {} = True
needsWrapper _ = False

auxCFFIDef :: Core.Definition TypedExpr VarName VarName -> Maybe AST.Definition
auxCFFIDef (FunDef _ name _ _ t rt _) =
    let args = case regLayout t of
            One a0 -> [Parameter a0 "a0" []]
            Two a0 a1 ->
                [ Parameter a0 "a0" []
                , Parameter a1 "a1" []
                ]
            Ref -> [Parameter (toLLVMType t) "a0" [ByVal]]
        (returnArgs, returnType) = case regLayout rt of
            One r0 -> ([], r0)
            Two r0 r1 -> ([], StructureType False [r0, r1])
            Ref -> ([Parameter (toLLVMType rt) "r0" [NoAlias, SRet]], VoidType)
     in Just
            ( def
                (toShortBS (name ++ "_ccompat"))
                (returnArgs ++ args)
                returnType
                (typeToWrapper name t rt returnType (regLayout t))
            )
auxCFFIDef _ = Nothing

typeToWrapper ::
    String ->
    Core.Type t b ->
    Core.Type t b ->
    AST.Type ->
    RegLayout ->
    Codegen (Either Operand (Named Terminator))
typeToWrapper name t rt wrapperRT argLayout = do
    -- Wrap arguments
    arg <- case (argLayout, needsWrapper t) of
        (Ref, _) -> return (LocalReference (toLLVMType t) "a0")
        (_, False) -> return (LocalReference (toLLVMType t) "a0")
        _ -> do
            argNative <-
                instr
                    (toLLVMType t)
                    ( Alloca
                        { allocatedType = unPtr (toLLVMType t)
                        , numElements = Nothing
                        , alignment = 8
                        , metadata = []
                        }
                    )
            let wrapperT =
                    ptrTo
                        ( case argLayout of
                            One a0 -> a0
                            Two a0 a1 -> StructureType False [a0, a1]
                        )
            argCast <-
                instr
                    wrapperT
                    ( BitCast
                        { operand0 = argNative
                        , type' = wrapperT
                        , metadata = []
                        }
                    )
            case argLayout of
                One a0 ->
                    unnamedInstr
                        ( Store
                            { volatile = False
                            , address = argCast
                            , value = LocalReference a0 "a0"
                            , maybeAtomicity = Nothing
                            , alignment = 8
                            , metadata = []
                            }
                        )
                Two a0 a1 -> do
                    field0 <-
                        instr
                            (StructureType False [a0, a1])
                            ( GetElementPtr
                                { inBounds = True
                                , address = argCast
                                , indices = [constInt 32 0, constInt 32 0]
                                , metadata = []
                                }
                            )
                    unnamedInstr
                        ( Store
                            { volatile = False
                            , address = field0
                            , value = LocalReference a0 "a0"
                            , maybeAtomicity = Nothing
                            , alignment = 8
                            , metadata = []
                            }
                        )
                    field1 <-
                        instr
                            (StructureType False [a0, a1])
                            ( GetElementPtr
                                { inBounds = True
                                , address = argCast
                                , indices = [constInt 32 0, constInt 32 1]
                                , metadata = []
                                }
                            )
                    unnamedInstr
                        ( Store
                            { volatile = False
                            , address = field1
                            , value = LocalReference a1 "a1"
                            , maybeAtomicity = Nothing
                            , alignment = 8
                            , metadata = []
                            }
                        )
                    return ()
            return argNative
    -- Call inner function
    let fun =
            ConstantOperand
                ( C.GlobalReference
                    (toLLVMType (TFun t rt))
                    (Name (toShortBS name))
                )
    res <-
        instr
            (toLLVMType rt)
            ( Call
                { tailCallKind = Nothing
                , callingConvention = CC.C
                , returnAttributes = []
                , function = Right fun
                , arguments = [(arg, [])]
                , functionAttributes = []
                , metadata = []
                }
            )
    -- Handle return values
    case (wrapperRT, needsWrapper rt) of
        (VoidType, _) -> do
            -- take the return pointer and copy its memory into return argument
            -- because res was stack allocated, this operation is questionable
            -- really should not return alloca'd memory at all
            argCast <-
                instr
                    (ptrTo (IntegerType 8))
                    ( BitCast
                        { operand0 = LocalReference (toLLVMType t) "r0"
                        , type' = ptrTo (IntegerType 8)
                        , metadata = []
                        }
                    )
            retCast <-
                instr
                    (ptrTo (IntegerType 8))
                    ( BitCast
                        { operand0 = res
                        , type' = ptrTo (IntegerType 8)
                        , metadata = []
                        }
                    )
            unnamedInstr
                ( Call
                    { tailCallKind = Nothing
                    , callingConvention = CC.C
                    , returnAttributes = []
                    , function = Right (iFRef memcpy)
                    , arguments =
                        [ (argCast, [Alignment 8])
                        , (retCast, [Alignment 8])
                        , (constInt 64 (toInteger (sizeof (typeLayout rt)) `div` 8), [])
                        , (constInt 1 0, [])
                        ]
                    , functionAttributes = []
                    , metadata = []
                    }
                )
            ret <- terminator (Do (Ret Nothing []))
            return (Right ret)
        (_, False) -> return (Left res)
        _ -> do
            retCast <-
                instr
                    (ptrTo wrapperRT)
                    ( BitCast
                        { operand0 = res
                        , type' = ptrTo wrapperRT
                        , metadata = []
                        }
                    )
            flatRes <-
                instr
                    wrapperRT
                    ( Load
                        { volatile = False
                        , address = retCast
                        , maybeAtomicity = Nothing
                        , alignment = 8
                        , metadata = []
                        }
                    )
            return (Left flatRes)

data IntrinsicFunction = IntrinsicFunction
    { iFDef :: AST.Definition
    , iFRef :: Operand
    }

mkIntrinsic :: ShortByteString -> [Parameter] -> Bool -> AST.Type -> IntrinsicFunction
mkIntrinsic name params va rt =
    IntrinsicFunction
        ( GlobalDefinition
            ( functionDefaults
                { name = Name name
                , parameters = (params, va)
                , returnType = rt
                , basicBlocks = []
                }
            )
        )
        ( ConstantOperand
            ( C.GlobalReference
                ( ptrTo
                    FunctionType
                        { resultType = rt
                        , argumentTypes = map typeOf params
                        , isVarArg = va
                        }
                )
                (Name name)
            )
        )

memcpy :: IntrinsicFunction
memcpy =
    mkIntrinsic
        "llvm.memcpy.p0i8.p0i8.i64"
        [ Parameter (ptrTo (IntegerType 8)) (UnName 0) [NoAlias, NoCapture, WriteOnly]
        , Parameter (ptrTo (IntegerType 8)) (UnName 1) [NoAlias, NoCapture, ReadOnly]
        , Parameter (IntegerType 64) (UnName 2) []
        , Parameter (IntegerType 1) (UnName 3) [ImmArg]
        ]
        False
        VoidType

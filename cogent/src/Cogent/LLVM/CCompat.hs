{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}

module Cogent.LLVM.CCompat where

import Cogent.Common.Syntax (VarName)
import Cogent.Core as Core
import Cogent.LLVM.CodeGen
import Cogent.LLVM.Expr (castVal)
import Cogent.LLVM.Types
import LLVM.AST as AST
import LLVM.AST.CallingConvention as CC
import qualified LLVM.AST.Constant as C
import LLVM.AST.ParameterAttribute

data RegLayout = One AST.Type | Two AST.Type AST.Type | Ref deriving (Show)

regLayout :: Core.Type t b -> RegLayout
regLayout t
    | s <= 64 = One (IntegerType (toEnum s))
    | s <= 128 = Two (IntegerType 64) (IntegerType (toEnum (s - 64)))
    | otherwise = Ref
    where
        s = typeSize t

needsWrapper :: Core.Type t b -> Bool
needsWrapper TRecord {} = True
needsWrapper TSum {} = True
needsWrapper _ = False

auxCFFIDef :: Core.Definition TypedExpr VarName VarName -> Maybe AST.Definition
auxCFFIDef (FunDef _ name _ _ t rt _) =
    let args = case regLayout t of
            One a0 -> [Parameter a0 "a0" []]
            Two a0 a1 ->
                [ Parameter a0 "a0" []
                , Parameter a1 "a1" []
                ]
            Ref -> [Parameter (ptrTo (toLLVMType t)) "a0" [ByVal]]
        (returnArgs, returnType) = case regLayout rt of
            One r0 -> ([], r0)
            Two r0 r1 -> ([], StructureType False [r0, r1])
            Ref -> ([Parameter (ptrTo (toLLVMType rt)) "r0" [NoAlias, SRet]], VoidType)
     in Just
            ( def
                (toShortBS (name ++ "_ccompat"))
                (returnArgs ++ args)
                returnType
                (typeToWrapper name t rt returnType (regLayout t))
            )
auxCFFIDef _ = Nothing

-- k =
--     [
--         ( Name "entry"
--         , BlockState
--             { idx = 1
--             , instrs =
--                 [ UnName 1
--                     := Load
--                         { volatile = False
--                         , address =
--                             LocalReference
--                                 ( StructureType
--                                     { isPacked = False
--                                     , elementTypes =
--                                         [ IntegerType {typeBits = 64}
--                                         , StructureType
--                                             { isPacked = False
--                                             , elementTypes =
--                                                 [ IntegerType {typeBits = 64}
--                                                 , IntegerType {typeBits = 64}
--                                                 ]
--                                             }
--                                         ]
--                                     }
--                                 )
--                                 (Name "a0")
--                         , maybeAtomicity = Nothing
--                         , alignment = 0
--                         , metadata = []
--                         }
--                 , UnName 2
--                     := Call
--                         { tailCallKind = Nothing
--                         , callingConvention = C
--                         , returnAttributes = []
--                         , function =
--                             Right
--                                 ( ConstantOperand
--                                     ( GlobalReference
--                                         ( PointerType
--                                             { pointerReferent =
--                                                 FunctionType
--                                                     { resultType =
--                                                         StructureType
--                                                             { isPacked = False
--                                                             , elementTypes =
--                                                                 [ StructureType
--                                                                     { isPacked = False
--                                                                     , elementTypes =
--                                                                         [ IntegerType {typeBits = 64}
--                                                                         , IntegerType {typeBits = 64}
--                                                                         ]
--                                                                     }
--                                                                 , IntegerType {typeBits = 64}
--                                                                 ]
--                                                             }
--                                                     , argumentTypes =
--                                                         [ StructureType
--                                                             { isPacked = False
--                                                             , elementTypes =
--                                                                 [ IntegerType {typeBits = 64}
--                                                                 , StructureType
--                                                                     { isPacked = False
--                                                                     , elementTypes =
--                                                                         [ IntegerType {typeBits = 64}
--                                                                         , IntegerType {typeBits = 64}
--                                                                         ]
--                                                                     }
--                                                                 ]
--                                                             }
--                                                         ]
--                                                     , isVarArg = False
--                                                     }
--                                             , pointerAddrSpace = AddrSpace 0
--                                             }
--                                         )
--                                         (Name "foo")
--                                     )
--                                 )
--                         , arguments =
--                             [
--                                 ( LocalReference
--                                     ( StructureType
--                                         { isPacked = False
--                                         , elementTypes =
--                                             [ IntegerType {typeBits = 64}
--                                             , StructureType
--                                                 { isPacked = False
--                                                 , elementTypes =
--                                                     [ IntegerType {typeBits = 64}
--                                                     , IntegerType {typeBits = 64}
--                                                     ]
--                                                 }
--                                             ]
--                                         }
--                                     )
--                                     (UnName 1)
--                                 , []
--                                 )
--                             ]
--                         , functionAttributes = []
--                         , metadata = []
--                         }
--                 , Do
--                     ( Store
--                         { volatile = False
--                         , address =
--                             LocalReference
--                                 ( StructureType
--                                     { isPacked = False
--                                     , elementTypes =
--                                         [ IntegerType {typeBits = 64}
--                                         , StructureType
--                                             { isPacked = False
--                                             , elementTypes =
--                                                 [ IntegerType {typeBits = 64}
--                                                 , IntegerType {typeBits = 64}
--                                                 ]
--                                             }
--                                         ]
--                                     }
--                                 )
--                                 (Name "r0")
--                         , value =
--                             LocalReference
--                                 ( StructureType
--                                     { isPacked = False
--                                     , elementTypes =
--                                         [ StructureType
--                                             { isPacked = False
--                                             , elementTypes =
--                                                 [ IntegerType {typeBits = 64}
--                                                 , IntegerType {typeBits = 64}
--                                                 ]
--                                             }
--                                         , IntegerType {typeBits = 64}
--                                         ]
--                                     }
--                                 )
--                                 (UnName 2)
--                         , maybeAtomicity = Nothing
--                         , alignment = 0
--                         , metadata = []
--                         }
--                     )
--                 ]
--             , term =
--                 Just
--                     ( Do
--                         ( Ret
--                             { returnOperand = Nothing
--                             , metadata' = []
--                             }
--                         )
--                     )
--             }
--         )
--     ]

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
        (_, False) -> return (LocalReference (toLLVMType t) "a0")
        (Ref, _) ->
            instr
                (toLLVMType t)
                ( Load
                    { volatile = False
                    , address = LocalReference (ptrTo (toLLVMType t)) "a0"
                    , maybeAtomicity = Nothing
                    , alignment = 0
                    , metadata = []
                    }
                )
        _ -> do
            argNative <- case argLayout of
                One a0 -> return (LocalReference a0 "a0")
                Two a0 a1 ->
                    let aggT = StructureType False [a0, a1]
                     in instr
                            aggT
                            ( InsertValue
                                { aggregate = constUndef aggT
                                , element = LocalReference a0 "a0"
                                , indices' = [0]
                                , metadata = []
                                }
                            )
                            >>= \ref ->
                                instr
                                    aggT
                                    ( InsertValue
                                        { aggregate = ref
                                        , element = LocalReference a1 "a1"
                                        , indices' = [1]
                                        , metadata = []
                                        }
                                    )
            castVal (toLLVMType t) argNative
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
        (_, False) -> return (Left res)
        (VoidType, _) -> do
            unnamedInstr
                ( Store
                    { volatile = False
                    , address = LocalReference (toLLVMType t) "r0"
                    , maybeAtomicity = Nothing
                    , value = res
                    , alignment = 0
                    , metadata = []
                    }
                )
            ret <- terminator (Do (Ret Nothing []))
            return (Right ret)
        _ -> do
            retCast <- castVal wrapperRT res
            return (Left retCast)

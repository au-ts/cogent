{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}

module Cogent.LLVM.CCompat where

import Cogent.Common.Syntax (VarName)
import Cogent.Core as Core
import Cogent.LLVM.Custom (function)
import Cogent.LLVM.Expr (castVal)
import Cogent.LLVM.Types
import LLVM.AST as AST hiding (function)
import LLVM.AST.Attribute (ParameterAttribute (ByVal, NoAlias, SRet))
import qualified LLVM.AST.Constant as C
import LLVM.AST.Type (ptr)
import LLVM.IRBuilder.Instruction (call, insertValue, load, ret, retVoid, store)
import LLVM.IRBuilder.Module (ModuleBuilder, ParameterName (NoParameterName))
import LLVM.IRBuilder.Monad (MonadIRBuilder, block, named)

data RegLayout = One AST.Type | Two AST.Type AST.Type | Ref | NativeRef deriving (Show)

regLayout :: Core.Type t b -> RegLayout
regLayout t
    | isNativePointer t = NativeRef
    | s <= p || isPrim t = One (IntegerType (fromInteger s))
    | s <= 2 * p = Two (IntegerType (fromInteger p)) (IntegerType (fromInteger (s - p)))
    | otherwise = Ref
    where
        p = pointerSizeBits
        s = typeSize t

needsWrapper :: Core.Type t b -> Bool
needsWrapper TSum {} = True
needsWrapper t@TRecord {} = isUnboxed t
needsWrapper _ = False

auxCFFIDef :: Core.Definition TypedExpr VarName VarName -> ModuleBuilder Operand
auxCFFIDef (FunDef _ name _ _ t rt _) =
    let args = case regLayout t of
            NativeRef -> [(toLLVMType t, [], NoParameterName)]
            One a0 -> [(a0, [], NoParameterName)]
            Two a0 a1 ->
                [ (a0, [], NoParameterName)
                , (a1, [], NoParameterName)
                ]
            Ref -> [(ptr (toLLVMType t), [ByVal], NoParameterName)]
        (returnArgs, returnType) = case regLayout rt of
            NativeRef -> ([], toLLVMType rt)
            One r0 -> ([], r0)
            Two r0 r1 -> ([], StructureType False [r0, r1])
            Ref -> ([(ptr (toLLVMType rt), [NoAlias, SRet], NoParameterName)], VoidType)
     in function
            (mkName (name ++ "_ccompat"))
            (returnArgs ++ args)
            returnType
            (typeToWrapper name t rt returnType (regLayout t))

typeToWrapper ::
    MonadIRBuilder m =>
    String ->
    Core.Type t b ->
    Core.Type t b ->
    AST.Type ->
    RegLayout ->
    [Operand] ->
    m ()
typeToWrapper name t rt wrapperRT argLayout (r0 : args) = do
    block `named` "entry"
    -- Wrap arguments
    arg <- case (argLayout, needsWrapper t) of
        (_, False) -> pure a0
        (Ref, _) -> load a0 0
        _ -> do
            argNative <- case argLayout of
                One _ -> pure a0
                Two a0t a1t ->
                    let aggT = StructureType False [a0t, a1t]
                     in insertValue (constUndef aggT) a0 [0]
                            >>= \ref -> insertValue ref a1 [1]
            castVal (toLLVMType t) argNative
    -- Call inner function
    let fun =
            ConstantOperand
                ( C.GlobalReference
                    (toLLVMType (TFun t rt))
                    (mkName name)
                )
    res <- call fun [(arg, [])]
    -- Handle return values
    case (wrapperRT, needsWrapper rt) of
        (_, False) -> ret res
        (VoidType, _) -> do
            store r0 0 res
            retVoid
        _ -> do
            retCast <- castVal wrapperRT res
            ret retCast
    where
        a0 = case wrapperRT of
            VoidType -> head args
            _ -> r0 -- if there is no r0, a0 is actually first arg
        a1 = last args

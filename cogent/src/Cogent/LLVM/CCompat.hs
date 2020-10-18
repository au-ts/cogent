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
{-# LANGUAGE OverloadedStrings #-}

module Cogent.LLVM.CCompat (auxCFFIDef) where

-- This module attempts to create wrapper functions whose signatures should
-- match those of equivalent C functions compiled with clang

import Cogent.Common.Syntax (Size, VarName)
import Cogent.Compiler (__impossible)
import Cogent.Core as Core (Definition (FunDef), Type (..), TypedExpr, isUnboxed)
import Cogent.LLVM.Custom (function)
import Cogent.LLVM.Expr (castVal, constUndef)
import Cogent.LLVM.Types
import LLVM.AST as AST hiding (function)
import LLVM.AST.Attribute (ParameterAttribute (ByVal, NoAlias, SRet))
import qualified LLVM.AST.Constant as C
import LLVM.AST.Type (ptr)
import LLVM.IRBuilder.Instruction (call, insertValue, load, ret, retVoid, store)
import LLVM.IRBuilder.Module (ModuleBuilder, ParameterName (NoParameterName))
import LLVM.IRBuilder.Monad (MonadIRBuilder, block, named)

data RegLayout = One AST.Type | Two AST.Type AST.Type | Ref

-- A function parameter or return type may be coerced to:
--  - a single parameter (if the original parameter can fit into one register)
--  - two parameters (if the original parameter can fit into two registers)
--  - a reference (if the original parameter is too large)
--  - a 'native reference'  (if the original parameter is already a pointer)
regLayout :: Core.Type t b -> RegLayout
regLayout t
    | size <= p || isPrim t = One (toReg 0 layout size)
    | size <= 2 * p = Two (toReg 0 layout p) (toReg p layout (size - p))
    | otherwise = Ref
    where
        p = pointerSizeBits
        (size, layout) = (flatLayout . typeLayout) t

-- Look at offset inside memory layout to convert it to a single register argument
toReg :: Size -> MemLayout -> Integer -> AST.Type
toReg offset layout regSize = case memLookup offset layout of
    Pointer pt -> pt
    _ -> IntegerType (fromInteger regSize)

-- We must create wrappers for functions which accept or return variants or unboxed records
needsWrapper :: Core.Type t b -> Bool
needsWrapper TSum {} = True
needsWrapper t@TRecord {} = isUnboxed t
needsWrapper _ = False

-- Given an original definition, emit a function which wraps it
-- The arguments for the wrapper are the coerced original arguments, and possibly
-- a return argument
-- The return type of the wrapper is either the coerced return type, or void
auxCFFIDef :: Core.Definition TypedExpr VarName VarName -> ModuleBuilder Operand
auxCFFIDef (FunDef _ name _ _ t rt _) =
    let args = case regLayout t of
            -- NativeRef -> [(toLLVMType t, [], NoParameterName)]
            One a0 -> [(a0, [], NoParameterName)]
            Two a0 a1 ->
                [ (a0, [], NoParameterName)
                , (a1, [], NoParameterName)
                ]
            Ref -> [(ptr (toLLVMType t), [ByVal], NoParameterName)]
        (returnArgs, returnType) = case regLayout rt of
            -- NativeRef -> ([], toLLVMType rt)
            One r0 -> ([], r0)
            Two r0 r1 -> ([], StructureType False [r0, r1])
            Ref -> ([(ptr (toLLVMType rt), [NoAlias, SRet], NoParameterName)], VoidType)
     in function
            (mkName name)
            (returnArgs ++ args)
            returnType
            (typeToWrapper name t rt returnType (regLayout t))
auxCFFIDef _ = __impossible "auxCFFIDef"

-- Given the original function name and type, and the wrapper's type, produce a
-- function body which correctly calls the original function and coerces its output
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
    -- Handle arguments
    arg <- case (argLayout, needsWrapper t) of
        -- No need to coerce arguments
        (_, False) -> pure a0
        -- Argument is a reference, so all we do is load it
        (Ref, _) -> load a0 0
        -- Coerce arguments depending on their layout
        _ -> do
            argNative <- case argLayout of
                One _ -> pure a0
                Two a0t a1t ->
                    let aggT = StructureType False [a0t, a1t]
                     in insertValue (constUndef aggT) a0 [0]
                            >>= \ref -> insertValue ref a1 [1]
                _ -> __impossible "argLayout can't be Ref here"
            castVal (toLLVMType t) argNative
    -- Call inner function
    let fun =
            ConstantOperand
                ( C.GlobalReference
                    (toLLVMType (TFun t rt))
                    (mkName (name ++ "."))
                )
    res <- call fun [(arg, [])]
    -- Handle return value
    case (wrapperRT, needsWrapper rt) of
        -- No need to coerce return value
        (_, False) -> ret res
        -- Return value should be void, with the value stored in a return argument
        (VoidType, _) -> do
            store r0 0 res
            retVoid
        -- Coerce the return value
        _ -> do
            retCast <- castVal wrapperRT res
            ret retCast
    where
        -- a0 is the first non-return argument to the wrapper
        a0 = case wrapperRT of
            VoidType -> head args
            _ -> r0 -- if there is no r0, a0 is actually first arg

        -- a1 is the last argument to the wrapper (possibly = a0)
        a1 = last args

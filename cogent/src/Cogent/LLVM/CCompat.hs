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
{-# LANGUAGE TupleSections #-}

module Cogent.LLVM.CCompat (wrapC, wrapLLVM) where

-- This module attempts to create wrapper functions whose signatures should
-- match those of equivalent C functions compiled with clang

import Cogent.Common.Syntax (FunName, Size)
import Cogent.Compiler (__impossible)
import Cogent.Core as Core (Type (..), isUnboxed)
import Cogent.LLVM.Custom (extern, function)
import Cogent.LLVM.Expr (castVal, constUndef)
import Cogent.LLVM.Types
import LLVM.AST as AST hiding (extern, function)
import LLVM.AST.Attribute (ParameterAttribute (ByVal, NoAlias, SRet))
import qualified LLVM.AST.Constant as C
import LLVM.AST.Type (ptr)
import LLVM.AST.Typed (typeOf)
import LLVM.IRBuilder.Instruction
import LLVM.IRBuilder.Module (ModuleBuilder)
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
wrapLLVM :: FunName -> Core.Type t b -> Core.Type t b -> ModuleBuilder Operand
wrapLLVM name t rt =
    function (mkName name) ts rt' (wrapLLVMInner (name ++ ".llvm") t rt rt' (regLayout t))
    where
        (ts, rt') = optimiseFunctionType t rt

optimiseFunctionType ::
    Core.Type t b ->
    Core.Type t b ->
    ([(AST.Type, [ParameterAttribute])], AST.Type)
optimiseFunctionType t rt =
    let args = case regLayout t of
            One a0 -> [(a0, [])]
            Two a0 a1 ->
                [ (a0, [])
                , (a1, [])
                ]
            Ref -> [(ptr (toLLVMType t), [ByVal])]
        (returnArgs, returnType) = case regLayout rt of
            One r0 -> ([], r0)
            Two r0 r1 -> ([], StructureType False [r0, r1])
            Ref -> ([(ptr (toLLVMType rt), [NoAlias, SRet])], VoidType)
     in (returnArgs ++ args, returnType)

wrapC :: FunName -> Core.Type t b -> Core.Type t b -> ModuleBuilder Operand
wrapC name t rt =
    extern (mkName name) ts rt'
        >> function
            (mkName (name ++ ".llvm"))
            [(toLLVMType t, [])]
            (toLLVMType rt)
            (wrapCInner name t rt ts rt' (regLayout t))
    where
        (ts, rt') = optimiseFunctionType t rt

-- Given the original function name and type, and the wrapper's type, produce a
-- function body which correctly calls the original function and coerces its output
wrapLLVMInner ::
    MonadIRBuilder m =>
    String ->
    Core.Type t b ->
    Core.Type t b ->
    AST.Type ->
    RegLayout ->
    [Operand] ->
    m ()
wrapLLVMInner name t rt wrapperRT argLayout (r0 : args) = do
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
            ConstantOperand $
                C.GlobalReference
                    (toLLVMType (TFun t rt))
                    (mkName name)
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

wrapCInner ::
    MonadIRBuilder m =>
    String ->
    Core.Type t b ->
    Core.Type t b ->
    [(AST.Type, [ParameterAttribute])] ->
    AST.Type ->
    RegLayout ->
    [Operand] ->
    m ()
wrapCInner name t rt ts' wrapperRT argLayout [arg] = do
    block `named` "entry"
    -- Handle arguments
    args <- case (argLayout, needsWrapper t) of
        -- No need to coerce arguments
        (_, False) -> pure [arg]
        -- Argument must be a reference, so we should pass a pointer
        (Ref, _) -> do
            tmp <- alloca (typeOf arg) Nothing 4
            store tmp 4 arg
            pure [tmp]
        -- Coerce arguments depending on their layout
        _ -> case argLayout of
            One a0 -> (: []) <$> castVal a0 arg
            Two a0t a1t ->
                let aggT = StructureType False [a0t, a1t]
                 in do
                        casted <- castVal aggT arg
                        arg1 <- extractValue casted [0]
                        arg2 <- extractValue casted [1]
                        pure [arg1, arg2]
            _ -> __impossible "argLayout can't be Ref here"
    retArg <- alloca (toLLVMType rt) Nothing 4
    let args' = case (wrapperRT, needsWrapper rt) of
            (VoidType, True) -> retArg : args
            _ -> args
    -- Call inner function
    let fun =
            ConstantOperand $
                C.GlobalReference
                    (ptr (FunctionType wrapperRT (fst <$> ts') False))
                    (mkName name)
    res <- call fun $ (,[]) <$> args'
    -- Handle return value
    case (wrapperRT, needsWrapper rt) of
        -- No need to coerce return value
        (_, False) -> ret res
        -- Return value was void, with the value stored in a return argument
        (VoidType, _) -> load retArg 4 >>= ret
        -- Coerce the return value
        _ -> do
            retCast <- castVal (toLLVMType rt) res
            ret retCast

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

module Cogent.LLVM.Custom (function, extern) where

-- For any overrides of utility functions originally provided by libraries

import Control.Monad (forM)
import LLVM.AST hiding (function)
import LLVM.AST.Attribute (ParameterAttribute)
import qualified LLVM.AST.Constant as C
import LLVM.AST.Global (Global (basicBlocks, name, parameters, returnType), linkage)
import LLVM.AST.Linkage (Linkage (External))
import LLVM.AST.Type (ptr)
import LLVM.IRBuilder hiding (extern, function)
import LLVM.IRBuilder.Module (MonadModuleBuilder)

-- Modified version of https://hackage.haskell.org/package/llvm-hs-pure-9.0.0/docs/src/LLVM.IRBuilder.Module.html#function
-- The change is to allow parameter attributes to be provided
-- Copyright (c) 2013, Benjamin S. Scarlet and Google Inc.
-- All rights reserved.
function ::
    MonadModuleBuilder m =>
    Name ->
    [(Type, [ParameterAttribute])] ->
    Type ->
    ([Operand] -> IRBuilderT m ()) ->
    m Operand
function label argtys retty body = do
    let tys = fst <$> argtys
    (paramNames, blocks) <- runIRBuilderT emptyIRBuilder $ do
        paramNames <- forM argtys $ const fresh
        body $ zipWith LocalReference tys paramNames
        return paramNames
    let def =
            GlobalDefinition
                functionDefaults
                    { name = label
                    , parameters = (zipWith (\(ty, a) nm -> Parameter ty nm a) argtys paramNames, False)
                    , returnType = retty
                    , basicBlocks = blocks
                    }
        funty = ptr $ FunctionType retty tys False
    emitDefn def
    pure $ ConstantOperand $ C.GlobalReference funty label

-- As above
extern ::
    MonadModuleBuilder m =>
    Name ->
    [(Type, [ParameterAttribute])] ->
    Type ->
    m Operand
extern nm argtys retty = do
    emitDefn $
        GlobalDefinition
            functionDefaults
                { name = nm
                , linkage = External
                , parameters = ([Parameter ty (mkName "") pas | (ty, pas) <- argtys], False)
                , returnType = retty
                }
    let funty = ptr $ FunctionType retty (fst <$> argtys) False
    pure $ ConstantOperand $ C.GlobalReference funty nm
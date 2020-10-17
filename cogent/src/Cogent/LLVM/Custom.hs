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

module Cogent.LLVM.Custom (function) where

-- For any overrides of utility functions originally provided by libraries

import Control.Monad (forM)
import LLVM.AST hiding (function)
import LLVM.AST.Attribute (ParameterAttribute)
import qualified LLVM.AST.Constant as C
import LLVM.AST.Global (Global (basicBlocks, name, parameters, returnType))
import LLVM.AST.Type (ptr)
import LLVM.IRBuilder hiding (function)
import LLVM.IRBuilder.Module (MonadModuleBuilder)

-- Modified version ofhttps://hackage.haskell.org/package/llvm-hs-pure-9.0.0/docs/src/LLVM.IRBuilder.Module.html#function
-- The change is to allow parameter attributes to be provided
-- Copyright (c) 2013, Benjamin S. Scarlet and Google Inc.
-- All rights reserved.
function ::
    MonadModuleBuilder m =>
    Name ->
    [(Type, [ParameterAttribute], ParameterName)] ->
    Type ->
    ([Operand] -> IRBuilderT m ()) ->
    m Operand
function label argtys retty body = do
    let tys = (\(ty, _, _) -> ty) <$> argtys
    (paramNames, blocks) <- runIRBuilderT emptyIRBuilder $ do
        paramNames <- forM argtys $ \(_, _, paramName) -> case paramName of
            NoParameterName -> fresh
            ParameterName p -> fresh `named` p
        body $ zipWith LocalReference tys paramNames
        return paramNames
    let def =
            GlobalDefinition
                functionDefaults
                    { name = label
                    , parameters = (zipWith (\(ty, a, _) nm -> Parameter ty nm a) argtys paramNames, False)
                    , returnType = retty
                    , basicBlocks = blocks
                    }
        funty = ptr $ FunctionType retty ((\(ty, _, _) -> ty) <$> argtys) False
    emitDefn def
    pure $ ConstantOperand $ C.GlobalReference funty label

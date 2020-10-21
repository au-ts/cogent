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
{-# LANGUAGE FlexibleContexts #-}

module Cogent.LLVM.CodeGen (LLVM, Codegen, Env (Env), bind, var) where

import Control.Monad.State (MonadState, State, gets, modify)
import Data.Fin (Fin, finInt)
import LLVM.AST (Operand)
import LLVM.IRBuilder (IRBuilderT)
import LLVM.IRBuilder.Module (ModuleBuilderT)

data Env = Env {vars :: [Operand]}

type LLVM = ModuleBuilderT (State Env)
type Codegen = IRBuilderT LLVM

bind :: MonadState Env m => Operand -> m a -> m a
bind var action = do
    vars <- gets vars
    modify $ \s -> s {vars = var : vars}
    res <- action
    modify $ \s -> s {vars = vars}
    pure res

var :: MonadState Env m => Fin v -> m Operand
var idx = gets $ (!! finInt idx) . vars

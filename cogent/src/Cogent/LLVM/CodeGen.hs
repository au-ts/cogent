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

module Cogent.LLVM.CodeGen (LLVM, Codegen, Env (Env), bind, var, tagIndex) where

import Cogent.Common.Syntax (TagName)
import Control.Monad.State (MonadState, State, gets, modify)
import Data.Fin (Fin, finInt)
import Data.List (elemIndex)
import Data.Maybe (fromJust)
import LLVM.AST (Operand)
import LLVM.IRBuilder (IRBuilderT, int32)
import LLVM.IRBuilder.Module (ModuleBuilderT)

data Env = Env {vars :: [Operand], tags :: [TagName]}

type LLVM = ModuleBuilderT (State Env)
type Codegen = IRBuilderT LLVM

-- Perform an action with a new bound variable
bind :: MonadState Env m => Operand -> m a -> m a
bind var action = do
    vars <- gets vars
    modify $ \s -> s {vars = var : vars}
    res <- action
    modify $ \s -> s {vars = vars}
    pure res

-- Retrieve a bound variable by index
var :: MonadState Env m => Fin v -> m Operand
var idx = gets $ (!! finInt idx) . vars

-- Convert a tag name to a global tag index
tagIndex :: MonadState Env m => TagName -> m Operand
tagIndex tag = gets (int32 . toInteger . fromJust . elemIndex tag . tags)

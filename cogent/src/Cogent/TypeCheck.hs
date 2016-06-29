--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE TupleSections #-}

module Cogent.TypeCheck where

import COGENT.TypeCheck.Generator
import COGENT.TypeCheck.Base
import COGENT.TypeCheck.Solver
import COGENT.TypeCheck.Subst (applyE)
import COGENT.Surface
import COGENT.Compiler
import COGENT.Common.Syntax
import Text.Parsec.Pos
import Control.Monad.Except
import Control.Lens

import qualified COGENT.Context as C
import qualified Data.Map as M
typecheck :: [(SourcePos, TopLevel LocType VarName LocExpr)]
          -> ExceptT [ContextualisedError] TC [TopLevel RawType TypedName TypedExpr]
typecheck = mapM (uncurry checkOne)

-- TODO: Check for prior definition
checkOne :: SourcePos -> TopLevel LocType VarName LocExpr
         -> ExceptT [ContextualisedError] TC (TopLevel RawType TypedName TypedExpr)
checkOne loc (Include _) = __impossible "checkOne"
checkOne loc d = case d of
  (TypeDec n ps t) -> do
    t' <- validateType' ps (stripLocT t)
    knownTypes <>= [(n,(ps, Just t'))]
    return (TypeDec n ps (toRawType t'))
  (AbsTypeDec n ps) -> do
    knownTypes <>= [(n,(ps, Nothing))]
    return (AbsTypeDec n ps)
  (AbsDec n (PT ps t)) -> do
    t' <- validateType' (map fst ps) (stripLocT t)
    return (AbsDec n (PT ps (toRawType t')))
  (ConstDef n t e) -> do
    base <- use knownConsts
    t' <- validateType' [] (stripLocT t)
    let ctx = C.addScope (fmap (\(t,p) -> (t,p, Just p)) base) C.empty
    ((c, e'), f) <- lift (runCG ctx [] (cg e t'))
    (errs, subst) <- lift (runSolver (solve c) f)
    if null errs then do
      knownConsts %= M.insert n (t', loc)
      let e'' = toTypedExpr $ applyE subst e'
      return (ConstDef n (toRawType t') e'')
    else
      throwError (map (_1 %~ (InDefinition loc d:)) errs)
  where
    validateType' x = withExceptT (pure . ([InDefinition loc d],)) . validateType x
-- tc :: [(SourcePos, TopLevel LocType VarName LocExpr)]
--    -> ((Either (TypeError, [ErrorContext]) [TopLevel RawType TypedName TypedExpr], WarningErrorLog), TCState)
-- tc defs = undefined

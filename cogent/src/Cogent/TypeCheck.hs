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
{-# LANGUAGE ImplicitParams #-}
module Cogent.TypeCheck where

import Cogent.TypeCheck.Generator
import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Solver
import Cogent.TypeCheck.Subst (applyE, applyAlts)
import Cogent.Surface
import Cogent.Compiler
import Cogent.Common.Syntax
import Text.Parsec.Pos
import Control.Monad.Except
import Control.Monad.State
import Control.Lens
import qualified Cogent.Context as C
import qualified Data.Map as M
-- import Debug.Trace
-- import Cogent.PrettyPrint()
-- import Text.PrettyPrint.ANSI.Leijen
tc :: [(SourcePos, TopLevel LocType VarName LocExpr)]
      -> (Either [ContextualisedError] [TopLevel RawType TypedName TypedExpr ], TCState)
tc i = runState (runExceptT (typecheck i)) (TCS M.empty knownTypes M.empty)
  where
    knownTypes = map (, ([] , Nothing)) $ words "U8 U16 U32 U64 String Bool"

typecheck :: [(SourcePos, TopLevel LocType VarName LocExpr)]
          -> ExceptT [ContextualisedError] TC [TopLevel RawType TypedName TypedExpr]
typecheck = mapM (uncurry checkOne)

-- TODO: Check for prior definition
checkOne :: SourcePos -> TopLevel LocType VarName LocExpr
         -> ExceptT [ContextualisedError] TC (TopLevel RawType TypedName TypedExpr)
checkOne loc d = case d of
  (Include _) -> __impossible "checkOne"
  (TypeDec n ps t) -> do
    t' <- validateType' ps (stripLocT t)
    knownTypes <>= [(n,(ps, Just t'))]
    return (TypeDec n ps (toRawType t'))
  (AbsTypeDec n ps) -> do
    knownTypes <>= [(n,(ps, Nothing))]
    return (AbsTypeDec n ps)
  (AbsDec n (PT ps t)) -> do
    t' <- validateType' (map fst ps) (stripLocT t)
    knownFuns %= M.insert n (PT ps t')
    return (AbsDec n (PT ps (toRawType t')))
  (ConstDef n t e) -> do
    base <- use knownConsts
    t' <- validateType' [] (stripLocT t)
    let ctx = C.addScope (fmap (\(t,p) -> (t,p, Just p)) base) C.empty
    ((c, e'), f) <- lift (runCG ctx [] (cg e t'))
    (errs, subst) <- lift (runSolver (solve c) f [])
    if null errs then do
      knownConsts %= M.insert n (t', loc)
      let e'' = toTypedExpr $ applyE subst e'
      return (ConstDef n (toRawType t') e'')
    else
      throwError (map (_1 %~ (InDefinition loc d:)) errs)
  (FunDef f (PT vs t) alts) -> do
    base <- use knownConsts
    t' <- validateType' (map fst vs) (stripLocT t)
    (i,o) <- asFunType t'
    let ctx = C.addScope (fmap (\(t,p) -> (t,p, Just p)) base) C.empty
    let ?loc = loc
    ((c, alts'), flx) <- lift (runCG ctx (map fst vs) (cgAlts alts o i))
    (errs, subst) <- lift (runSolver (solve c) flx vs)
    -- let alts'' = applyAlts subst alts'
    -- traceShowM ("fun!", pretty c, pretty alts'')
    if null errs then do
      knownFuns %= M.insert f (PT vs t')
      let alts'' = toTypedAlts $ applyAlts subst alts'
      return (FunDef f (PT vs (toRawType t')) alts'')
    else
      throwError (map (_1 %~ (InDefinition loc d:)) errs)

  where
    validateType' x = withExceptT (pure . ([InDefinition loc d],)) . validateType x

    asFunType (T (TFun a b)) = return (a, b)
    asFunType x              = throwError [([InDefinition loc d], NotAFunctionType x)]

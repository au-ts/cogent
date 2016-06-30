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

import Cogent.TypeCheck.Generator
import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Solver
import Cogent.TypeCheck.Subst (applyE)
import Cogent.Surface
import Cogent.Compiler
import Cogent.Common.Syntax
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
    (errs, subst) <- lift (runSolver (solve c) f [])
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

-- ----------------------------------------------------------------------------
-- custTyGen

typecheckCustTyGen :: [(LocType, String)] -> TC [(RawType, String)]
typecheckCustTyGen = mapM $ firstM $ \t ->
  if not (isMonoType t)
    then typeError (CustTyGenIsPolymorphic t)
    else isSynonym t >>= \case
           True -> typeError (CustTyGenIsSynonym t)
           _    -> validateType t

isMonoType :: LocType -> Bool
isMonoType (LocType _ (TVar {})) = False
isMonoType (LocType _ t) = getAll $ foldMap (All . isMonoType) t
isMonoType _ = __impossible "isMonoType: not a type at all"

isSynonym :: LocType -> TC Bool
isSynonym (LocType _ (TCon c _ _)) = lookup c <$> use knownTypes >>= \case
  Nothing -> __impossible "isSynonym: type not in scope"
  Just (vs,Just _ ) -> return True
  Just (vs,Nothing) -> return False
isSynonym (LocType _ t) = foldM (\b a -> (b ||) <$> isSynonym a) False t
isSynonym _ = __impossible "isSynonym: not a type at all"



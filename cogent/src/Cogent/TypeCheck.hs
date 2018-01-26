--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Cogent.TypeCheck (
  tc, isWarnAsError
) where

import Cogent.Compiler
import qualified Cogent.Context as C
import Cogent.PrettyPrint (prettyC)
import Cogent.Surface
import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Generator
import Cogent.TypeCheck.Post (postT, postE, postA)
import Cogent.TypeCheck.Solver
import Cogent.TypeCheck.Subst (applyE, applyAlts)
import Cogent.TypeCheck.Util
-- import Cogent.Util (firstM)

import Control.Arrow (first, second)
import Control.Lens
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer hiding (censor)
import Data.Either (lefts)
import Data.List (nub, (\\))
import qualified Data.Map as M
import qualified Data.Sequence as Seq
import Text.Parsec.Pos
import qualified Text.PrettyPrint.ANSI.Leijen as L
import Text.PrettyPrint.ANSI.Leijen hiding ((<>), (<$>))

-- import Debug.Trace

tc :: [(SourcePos, TopLevel LocType LocPatn LocExpr)]
   -> [(LocType, String)]
   -> IO ((Either () [TopLevel RawType TypedPatn TypedExpr], [ContextualisedEW]), TCState)
tc ds cts = ((first . second) adjustErrors <$>) . flip runStateT (TCS M.empty knownTypes M.empty) . (failError <$>) . runWriterT . runExceptT $ typecheck ds  -- FIXME
  where
    knownTypes = map (, ([], Nothing)) $ words "U8 U16 U32 U64 String Bool"
    adjustErrors = (if __cogent_freverse_tc_errors then reverse else id) . adjustContexts
    adjustContexts = map (first noConstraints)
    noConstraints = if __cogent_ftc_ctx_constraints then id else filter (not . isCtxConstraint)
    failError (Right _, ews) | or (map isWarnAsError ews), Flag_Werror <- __cogent_warning_switch = (Left (), ews)
    failError x = x

typecheck :: [(SourcePos, TopLevel LocType LocPatn LocExpr)]
          -> ExceptT () (WriterT [ContextualisedEW] TC) [TopLevel RawType TypedPatn TypedExpr]
typecheck = censor warnsToErrors . mapM (uncurry checkOne)
  where
    warnsToErrors = case __cogent_warning_switch of
                      Flag_w -> filter (not . isWarn)
                      Flag_Wwarn -> id
                      Flag_Werror -> map warnToError
    warnToError (c,Right w) = (c, Left $ TypeWarningAsError w)
    warnToError ew = ew

-- TODO: Check for prior definition
checkOne :: SourcePos -> TopLevel LocType LocPatn LocExpr
         -> ExceptT () (WriterT [ContextualisedEW] TC) (TopLevel RawType TypedPatn TypedExpr)
checkOne loc d = case d of
  (Include _) -> __impossible "checkOne"
  (IncludeStd _) -> __impossible "checkOne"
  (DocBlock s) -> return $ DocBlock s
  (TypeDec n ps t) -> do
    traceTc "tc" $ bold (text $ replicate 80 '=')
    traceTc "tc" (text "typecheck type definition" <+> pretty n)
    let xs = ps \\ nub ps
    unless (null xs) $ tell [([InDefinition loc d], Left $ DuplicateTypeVariable xs)] >> throwError ()
    t' <- validateType' ps [InDefinition loc d] (stripLocT t)
    knownTypes <>= [(n,(ps, Just t'))]
    t'' <- postT [InDefinition loc d] t'
    return $ TypeDec n ps t''

  (AbsTypeDec n ps) -> do
    traceTc "tc" $ bold (text $ replicate 80 '=')
    traceTc "tc" (text "typecheck abstract type definition" <+> pretty n)
    let xs = ps \\ nub ps
    unless (null xs) $ tell [([InDefinition loc d], Left $ DuplicateTypeVariable xs)] >> throwError ()
    knownTypes <>= [(n,(ps, Nothing))]
    return $ AbsTypeDec n ps

  (AbsDec n (PT ps t)) -> do
    traceTc "tc" $ bold (text $ replicate 80 '=')
    traceTc "tc" (text "typecheck abstract function" <+> pretty n)
    let vs' = map fst ps
        xs = vs' \\ nub vs'
    unless (null xs) $ tell [([InDefinition loc d], Left $ DuplicateTypeVariable xs)] >> throwError ()
    t' <- validateType' (map fst ps) [InDefinition loc d] (stripLocT t)
    knownFuns %= M.insert n (PT ps t')
    t'' <- postT [InDefinition loc d] t'
    return $ AbsDec n (PT ps t'')

  (ConstDef n t e) -> do
    traceTc "tc" $ bold (text $ replicate 80 '=')
    traceTc "tc" (text "typecheck const definition" <+> pretty n)
    base <- use knownConsts
    t' <- validateType' [] [InDefinition loc d] (stripLocT t)
    let ctx = C.addScope (fmap (\(t,p) -> (t,p, Seq.singleton p)) base) C.empty  -- for consts, the definition is the first use.
    ((c, e'), flx, os) <- lift $ lift (runCG ctx [] (cg e t'))
    let c' = c <> Share t' (Constant n)
    (ews, subst, _) <- lift $ lift (runSolver (solve c') flx os [])
    tell $ map addCtx ews
    traceTc "tc" (text "subst for const definition" <+> pretty n <+> text "is"
                  L.<$> pretty subst)
    if null (lefts $ map snd ews) then do
      knownConsts %= M.insert n (t', loc)
      e'' <- postE [InDefinition loc d] $ applyE subst e'
      t'' <- postT [InDefinition loc d] t'
      return (ConstDef n t'' e'')
    else
      throwError ()

  (FunDef f (PT vs t) alts) -> do
    traceTc "tc" $ bold (text $ replicate 80 '=')
    traceTc "tc" (text "typecheck fun definition" <+> pretty f)
    let vs' = map fst vs
        xs = vs' \\ nub vs'
    unless (null xs) $ tell [([InDefinition loc d], Left $ DuplicateTypeVariable xs)] >> throwError ()
    base <- use knownConsts
    t' <- validateType' (map fst vs) [InDefinition loc d] (stripLocT t)
    (i,o) <- asFunType t'
    let ctx = C.addScope (fmap (\(t,p) -> (t, p, Seq.singleton p)) base) C.empty
    let ?loc = loc
    ((c, alts'), flx, os) <- lift $ lift (runCG ctx (map fst vs) (cgAlts alts o i))
    traceTc "tc" (text "constraint for fun definition" <+> pretty f <+> text "is"
                  L.<$> prettyC c)
    -- traceTc "tc" (pretty alts')
    (ews, subst, _) <- lift $ lift (runSolver (solve c) flx os vs)
    tell $ map addCtx ews
    traceTc "tc" (text "subst for fun definition" <+> pretty f <+> text "is"
                  L.<$> pretty subst)
    if null (lefts $ map snd ews) then do
      knownFuns %= M.insert f (PT vs t')
      alts'' <- postA [InDefinition loc d] $ applyAlts subst alts'
      t''    <- postT [InDefinition loc d] t'
      return (FunDef f (PT vs t'') alts'')
    else
      throwError ()

  where
    asFunType (T (TFun a b)) = return (a, b)
    asFunType x@(T (TCon c as _)) = lookup c <$> use knownTypes >>= \case
                                      Just (vs, Just t) -> asFunType (substType (zip vs as) t)
                                      _ -> tell [([InDefinition loc d], Left $ NotAFunctionType x)] >> throwError ()
    asFunType x = tell [([InDefinition loc d], Left $ NotAFunctionType x)] >> throwError ()

    addCtx :: forall x. ([ErrorContext], x) -> ([ErrorContext], x)
    addCtx = (_1 %~ (++ [InDefinition loc d]))


-- ----------------------------------------------------------------------------
-- custTyGen

-- typecheckCustTyGen :: [(LocType, String)] -> TC [(RawType, String)]
-- typecheckCustTyGen = mapM $ firstM $ \t ->
--   if not (isMonoType t)
--     then typeError (CustTyGenIsPolymorphic t)
--     else isSynonym t >>= \case
--            True -> typeError (CustTyGenIsSynonym t)
--            _    -> validateType t
-- 
-- isMonoType :: LocType -> Bool
-- isMonoType (LocType _ (TVar {})) = False
-- isMonoType (LocType _ t) = getAll $ foldMap (All . isMonoType) t
-- isMonoType _ = __impossible "isMonoType: not a type at all"
-- 
-- isSynonym :: LocType -> TC Bool
-- isSynonym (LocType _ (TCon c _ _)) = lookup c <$> use knownTypes >>= \case
--   Nothing -> __impossible "isSynonym: type not in scope"
--   Just (vs,Just _ ) -> return True
--   Just (vs,Nothing) -> return False
-- isSynonym (LocType _ t) = foldM (\b a -> (b ||) <$> isSynonym a) False t
-- isSynonym _ = __impossible "isSynonym: not a type at all"


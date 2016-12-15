--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
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

import Control.Arrow (first, second)
import Control.Lens
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Data.Either (lefts)
import Data.List (nub, (\\))
import qualified Data.Map as M
import Text.Parsec.Pos
import qualified Text.PrettyPrint.ANSI.Leijen as L
import Text.PrettyPrint.ANSI.Leijen hiding ((<>), (<$>))

-- import Debug.Trace

tc :: [(SourcePos, TopLevel LocType LocPatn LocExpr)]
   -> IO ((Either () [TopLevel RawType TypedPatn TypedExpr], [ContextualisedEW]), TCState)
tc = ((first . second) adjustErrors <$>) . flip runStateT (TCS M.empty knownTypes M.empty) . runWriterT . runExceptT . typecheck
  where
    knownTypes = map (, ([] , Nothing)) $ words "U8 U16 U32 U64 String Bool"
    adjustErrors = (if __cogent_freverse_tc_errors then reverse else id) . adjustContexts
    adjustContexts = map (first noConstraints)
    noConstraints = if __cogent_ftc_ctx_constraints then id else filter (not . isCtxConstraint)

typecheck :: [(SourcePos, TopLevel LocType LocPatn LocExpr)]
          -> ExceptT () (WriterT [ContextualisedEW] TC) [TopLevel RawType TypedPatn TypedExpr]
typecheck = mapM (uncurry checkOne)

-- TODO: Check for prior definition
checkOne :: SourcePos -> TopLevel LocType LocPatn LocExpr
         -> ExceptT () (WriterT [ContextualisedEW] TC) (TopLevel RawType TypedPatn TypedExpr)
checkOne loc d = case d of
  (Include _) -> __impossible "checkOne"
  (IncludeStd _) -> __impossible "checkOne"
  (DocBlock s) -> return $ DocBlock s
  (TypeDec n ps t) -> do
    let xs = ps \\ nub ps
    unless (null xs) $ tell [([InDefinition loc d], Left $ DuplicateTypeVariable xs)] >> throwError ()
    t' <- validateType' ps (stripLocT t)
    knownTypes <>= [(n,(ps, Just t'))]
    t'' <- liftErr $ postT [InDefinition loc d] t'
    return $ TypeDec n ps t''

  (AbsTypeDec n ps) -> do
    let xs = ps \\ nub ps
    unless (null xs) $ tell [([InDefinition loc d], Left $ DuplicateTypeVariable xs)] >> throwError ()
    knownTypes <>= [(n,(ps, Nothing))]
    return $ AbsTypeDec n ps

  (AbsDec n (PT ps t)) -> do
    let vs' = map fst ps
        xs = vs' \\ nub vs'
    unless (null xs) $ tell [([InDefinition loc d], Left $ DuplicateTypeVariable xs)] >> throwError ()
    t' <- validateType' (map fst ps) (stripLocT t)
    knownFuns %= M.insert n (PT ps t')
    t'' <- liftErr $ postT [InDefinition loc d] t'
    return $ AbsDec n (PT ps t'')

  (ConstDef n t e) -> do
    traceTC "tc" (text "typecheck const definition" <+> pretty n
                  L.<$$> bold (text $ replicate 80 '='))
    base <- use knownConsts
    t' <- validateType' [] (stripLocT t)
    let ctx = C.addScope (fmap (\(t,p) -> (t,p, Just p)) base) C.empty
    ((c, e'), f, os) <- lift $ lift (runCG ctx [] (cg e t'))
    let c' = c <> Share t' (Constant n)
    (ews, subst, _) <- lift $ lift (runSolver (solve c') f os [])
    tell $ map addCtx ews
    traceTC "tc" (text "subst for const definition" <+> pretty n <+> text "is"
                  L.<$> pretty subst)
    if null (lefts $ map snd ews) then do
      knownConsts %= M.insert n (t', loc)
      e'' <- liftErr $ postE [InDefinition loc d] $ applyE subst e'
      t'' <- liftErr $ postT [InDefinition loc d] t'
      return (ConstDef n t'' e'')
    else
      throwError ()

  (FunDef f (PT vs t) alts) -> do
    traceTC "tc" (text "typecheck fun definition" <+> pretty f
                  L.<$$> bold (text $ replicate 80 '='))
    let vs' = map fst vs
        xs = vs' \\ nub vs'
    unless (null xs) $ tell [([InDefinition loc d], Left $ DuplicateTypeVariable xs)] >> throwError ()
    base <- use knownConsts
    t' <- validateType' (map fst vs) (stripLocT t)
    (i,o) <- asFunType t'
    let ctx = C.addScope (fmap (\(t,p) -> (t, p, Just p)) base) C.empty
    let ?loc = loc
    ((c, alts'), flx, os) <- lift $ lift (runCG ctx (map fst vs) (cgAlts alts o i))
    traceTC "tc" (text "constraint for fun definition" <+> pretty f <+> text "is"
                  L.<$> prettyC c)
    -- traceTC "tc" (pretty alts')
    (ews, subst, _) <- lift $ lift (runSolver (solve c) flx os vs)
    tell $ map addCtx ews
    traceTC "tc" (text "subst for fun definition" <+> pretty f <+> text "is"
                  L.<$> pretty subst)
    if null (lefts $ map snd ews) then do
      knownFuns %= M.insert f (PT vs t')
      alts'' <- liftErr $ postA [InDefinition loc d] $ applyAlts subst alts'
      t''    <- liftErr $ postT [InDefinition loc d] t'
      return (FunDef f (PT vs t'') alts'')
    else
      throwError ()

  where
    validateType' vs = (liftErr . withExceptT (pure . ([InDefinition loc d],) . Left)) . validateType vs

    asFunType (T (TFun a b)) = return (a, b)
    asFunType x@(T (TCon c as _)) = lookup c <$> use knownTypes >>= \case
                                      Just (vs, Just t) -> asFunType (substType (zip vs as) t)
                                      _ -> tell [([InDefinition loc d], Left $ NotAFunctionType x)] >> throwError ()
    asFunType x = tell [([InDefinition loc d], Left $ NotAFunctionType x)] >> throwError ()

    addCtx :: forall x. ([ErrorContext], x) -> ([ErrorContext], x)
    addCtx = (_1 %~ (++ [InDefinition loc d]))

    liftErr :: ExceptT [e] TC a -> ExceptT () (WriterT [e] TC) a
    liftErr ex = mapExceptT f ex
      where f :: TC (Either [e] a) -> WriterT [e] TC (Either () a)
            f tc = WriterT ((,[]) <$> tc) >>= \case
                           Left  e -> tell e >> return (Left ())
                           Right a -> return $ Right a


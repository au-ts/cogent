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
{-# LANGUAGE ViewPatterns #-}

module Cogent.TypeCheck (
  tc
, typecheck
) where

import Cogent.Common.Types (k2)
import Cogent.Compiler
import qualified Cogent.Context as C
import Cogent.Dargent.TypeCheck
import Cogent.PrettyPrint (prettyC)
import Cogent.Surface
import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Errors
import Cogent.TypeCheck.Generator
import Cogent.TypeCheck.Post (postT, postE, postA)
import Cogent.TypeCheck.Solver
import Cogent.TypeCheck.Subst (apply, applyE, applyL, applyAlts)
import Cogent.TypeCheck.Util
import Cogent.Util (firstM, secondM)

import Control.Arrow (first, second)
import Control.Monad.State
import Control.Monad.Trans.Except
-- import Control.Monad.Writer hiding (censor)
-- import Data.Either (lefts)
-- import qualified Data.IntMap as IM
import Data.List (nub, (\\))
import qualified Data.Map as M
import Data.Monoid ((<>))
import qualified Data.Sequence as Seq
import Text.Parsec.Pos
import qualified Text.PrettyPrint.ANSI.Leijen as L
import Text.PrettyPrint.ANSI.Leijen hiding ((<>), (<$>))
import Lens.Micro
import Lens.Micro.Mtl

import Debug.Trace

tc :: [(SourcePos, TopLevel LocType LocPatn LocExpr)]
   -> [(LocType, String)]
   -> IO ((Maybe ([(SourcePos, TopLevel DepType TypedPatn TypedExpr)], [(DepType, String)]), TcLogState), TcState)
tc ds cts = runTc (TcState M.empty knownTypes M.empty M.empty) ((,) <$> typecheck ds <*> typecheckCustTyGen cts)
  where
    knownTypes = map (, ([], Nothing)) $ words "U8 U16 U32 U64 String Bool"

typecheck :: [(SourcePos, TopLevel LocType LocPatn LocExpr)]
          -> TcM [(SourcePos, TopLevel DepType TypedPatn TypedExpr)]
typecheck = mapM (uncurry checkOne)

-- TODO: Check for prior definition
-- NOTE: we may make a choice between VariableNotDeclared and UnknownVariable
checkOne :: SourcePos -> TopLevel LocType LocPatn LocExpr
         -> TcM (SourcePos, TopLevel DepType TypedPatn TypedExpr)
checkOne loc d = lift (errCtx .= [InDefinition loc d]) >> case d of
  (Include _) -> __impossible "checkOne"
  (IncludeStd _) -> __impossible "checkOne"
  (DocBlock s) -> return (loc, DocBlock s)
  (TypeDec n vs (stripLocT -> t)) -> do
    traceTc "tc" $ bold (text $ replicate 80 '=')
    traceTc "tc" (text "typecheck type definition" <+> pretty n)
    let xs = vs \\ nub vs
    unless (null xs) $ logErrExit $ DuplicateTypeVariable xs
    base <- lift . lift $ use knownConsts
    let ctx = C.addScope (fmap (\(t,e,p) -> (t, p, Seq.singleton p)) base) C.empty
    let ?loc = loc
    ((ct,t'), flx, os) <- runCG ctx vs [] $ validateType t
    traceTc "tc" (text "constraint for type decl" <+> pretty n <+> text "is"
                  L.<$> prettyC ct)
    let ps = zip vs (repeat k2)
    (gs, subst) <- runSolver (solve ps [] ct) flx
    traceTc "tc" (text "substs for type decl" <+> pretty n <+> text "is"
                  L.<$> pretty subst)
    exitOnErr $ toErrors os gs
    let t'' = apply subst t'
    lift . lift $ knownTypes %= ( <> [(n, (vs, Just t''))])
    t''' <- postT t''
    return (loc, TypeDec n vs t''')

  (AbsTypeDec n vs (map stripLocT -> ts)) -> do
    traceTc "tc" $ bold (text $ replicate 80 '=')
    traceTc "tc" (text "typecheck abstract type definition" <+> pretty n)
    let xs = vs \\ nub vs
    unless (null xs) $ logErrExit $ DuplicateTypeVariable xs
    base <- lift . lift $ use knownConsts
    let ctx = C.addScope (fmap (\(t,e,p) -> (t, p, Seq.singleton p)) base) C.empty
    let ?loc = loc
    (blob, flx, os) <- runCG ctx vs [] $ mapM validateType ts
    let (cts,ts') = unzip blob
    traceTc "tc" (text "constraint for abstract type decl" <+> pretty n <+> text "is"
                  L.<$> prettyC (mconcat cts))
    let ps = zip vs (repeat k2)
    (gs, subst) <- runSolver (solve ps [] $ mconcat cts) flx
    traceTc "tc" (text "substs for abstract type decl" <+> pretty n <+> text "is"
                  L.<$> pretty subst)
    exitOnErr $ toErrors os gs
    let ts'' = fmap (apply subst) ts'
    ts''' <- mapM postT ts''
    lift . lift $ knownTypes %= (<> [(n, (vs, Nothing))])
    return (loc, AbsTypeDec n vs ts''')

  (AbsDec n (PT ps ls (stripLocT -> t))) -> do
    traceTc "tc" $ bold (text $ replicate 80 '=')
    traceTc "tc" (text "typecheck abstract function" <+> pretty n)
    let vs = map fst ps
        xs = vs \\ nub vs
    unless (null xs) $ logErrExit $ DuplicateTypeVariable xs
    let tvs = nub (tvT t)  -- type variables appearing to `t'
        ys = vs \\ tvs     -- we know `vs' has no duplicates
    unless (null ys) $ logErrExit $ SuperfluousTypeVariable ys
    let vs' = map fst ls
        xs' = vs' \\ nub vs'
    unless (null xs') $ logErrExit $ DuplicateLayoutVariable xs'
    let lvs = nub (lvT t)  -- layout variables in 't'
        ys' = vs' \\ lvs
    unless (null ys') $ logErrExit $ SuperfluousLayoutVariable ys'
    let ltvs = nub . concat $ tvT <$> (stripLocT <$> (snd <$> ls))
        stvs = ltvs \\ vs
    unless (null stvs) $ logErrExit $ TypeVariableNotDeclared stvs
    base <- lift . lift $ use knownConsts
    let ctx = C.addScope (fmap (\(t,e,p) -> (t, p, Seq.singleton p)) base) C.empty
    let ?loc = loc
    (((clt,lts),(ct,t')), flx, os) <- runCG ctx vs vs'
                                        (do x <- validateTypes (stripLocT . snd <$> ls)
                                            y <- validateType t
                                            pure (x,y))
    traceTc "tc" (text "constraint for abstract function" <+> pretty n <+> text "is"
                  L.<$> prettyC ct)
    let ls' = zip (fst <$> ls) lts
    (gs, subst) <- runSolver (solve ps ls' $ clt <> ct) flx
    traceTc "tc" (text "substs for abstract function" <+> pretty n <+> text "is"
                  L.<$> pretty subst)
    exitOnErr $ toErrors os gs
    let t'' = apply subst t'
    lift . lift $ knownFuns %= M.insert n (PT ps ls' t'')
    t''' <- postT t''
    lts' <- mapM postT (snd <$> ls')
    let ls'' = zip (fst <$> ls') lts'
    return (loc, AbsDec n (PT ps ls'' t'''))

  (RepDef decl@(DataLayoutDecl pos name vars expr)) -> do
    traceTc "tc" (text "typecheck rep decl" <+> pretty name)
    let xs = vars \\ nub vars
    unless (null xs) $ logErrExit $ DuplicateLayoutVariable xs
    let elvs = nub (lvL expr)
        ys = vars \\ elvs
    unless (null ys) $ logErrExit $ SuperfluousLayoutVariable ys
    base <- lift . lift $ use knownConsts
    let ctx = C.addScope (fmap (\(t,_,p) -> (t, p, Seq.singleton p)) base) C.empty
    let ?loc = loc
    -- currently no recursive data layout
    ((c,l), flx, os) <- runCG ctx [] vars (validateLayout expr)
    traceTc "tc" (text "constraint for rep decl" <+> pretty name <+> text "is"
                  L.<$> prettyC c)
    (gs, subst) <- runSolver (solve [] [] c) flx
    traceTc "tc" (text "substs for rep decl" <+> pretty name <+> text "is"
                  L.<$> pretty subst)
    exitOnErr $ toErrors os gs
    lift . lift $ knownDataLayouts %= M.insert name (vars, expr)
    let l' = toDLExpr $ applyL subst l
    return (loc, RepDef (DataLayoutDecl pos name vars l'))

  (ConstDef n (stripLocT -> t) e) -> do
    traceTc "tc" $ bold (text $ replicate 80 '=')
    traceTc "tc" (text "typecheck const definition" <+> pretty n)
    base <- lift . lift $ use knownConsts
    let ctx = C.addScope (fmap (\(t,_,p) -> (t,p, Seq.singleton p)) base) C.empty  -- for consts, the definition is the first use
    let ?loc = loc
    (((ct,t'),(c,e')), flx, os) <- runCG ctx [] []
                                     (do x@(ct,t') <- validateType t
                                         y <- cg e t'
                                         pure (x,y))
    let c' = ct <> c <> Share t' (Constant n)
    traceTc "tc" (text "constraint for const definition" <+> pretty n <+> text "is"
                  L.<$> prettyC c')
    (gs, subst) <- runSolver (solve [] [] c') flx
    exitOnErr $ toErrors os gs
    -- mapM_ logTc =<< mapM (\(c,l) -> lift (use errCtx >>= \c' -> return (c++c',l))) logs
    traceTc "tc" (text "substs for const definition" <+> pretty n <+> text "is"
                  L.<$> pretty subst)
    let t'' = apply subst t'
    lift . lift $ knownConsts %= M.insert n (t'', e', loc)
    e'' <- postE $ applyE subst e'
    t''' <- postT t''
    return (loc, ConstDef n t''' e'')

  (FunDef f (PT ps ls (stripLocT -> t)) alts) -> do
    traceTc "tc" $ bold (text $ replicate 80 '=')
    traceTc "tc" (text "typecheck fun definition" <+> pretty f)
    let vs = map fst ps
        xs = vs \\ nub vs
    unless (null xs) $ logErrExit $ DuplicateTypeVariable xs
    let tvs = nub (tvT t ++ foldMap tvA (fmap (fmap stripLocE) alts))
    -- \ ^^^ type variables appearing to `t' and in the body of the function definition. see #308.
        ys = vs \\ tvs    -- we know `vs' has no duplicates
    unless (null ys) $ logErrExit $ SuperfluousTypeVariable ys
    let vs' = map fst ls
        xs' = vs' \\ nub vs'
    unless (null xs') $ logErrExit $ DuplicateLayoutVariable xs'
    let lvs = nub (lvT t)  -- layout variables in 't'
        ys' = vs' \\ lvs
    unless (null ys') $ logErrExit $ SuperfluousLayoutVariable ys'
    let ltvs = nub . concat $ tvT <$> (stripLocT <$> (snd <$> ls))
        stvs = ltvs \\ vs
    unless (null stvs) $ logErrExit $ TypeVariableNotDeclared stvs
    base <- lift . lift $ use knownConsts

    let ctx = C.addScope (fmap (\(t,e,p) -> (t, p, Seq.singleton p)) base) C.empty
    let ?loc = loc
    (((clt,lts),(ct,t'),(c,alts')), flx, os) <- runCG ctx vs vs'
                                        (do x <- validateTypes (stripLocT . snd <$> ls)
                                            y@(ct,t') <- validateType t
                                            -- we add our function to the known functions here so they can be recursive
                                            let ls' = zip (map fst ls) (snd x)
                                            lift $ knownFuns %= M.insert f (PT ps ls' t')
                                            z <- cgFunDef alts t'
                                            pure (x,y,z))
    traceTc "tc" (text "constraint for fun definition" <+> pretty f <+> text "is"
                  L.<$> prettyC c)
    let ls' = zip (fst <$> ls) lts
    (gs, subst) <- runSolver (solve ps ls' $ clt <> ct <> c) flx
    --exitOnErr $ mapM_ logTc =<< mapM (\(c,l) -> lift (use errCtx) >>= \c' -> return (c++c',l)) logs
    traceTc "tc" (text "substs for fun definition" <+> pretty f <+> text "is"
                  L.<$> pretty subst)
    exitOnErr $ toErrors os gs
    let t'' = apply subst t'

    -- Replace our previous definition with the typechecker's updated type
    lift . lift $ knownFuns %= M.delete f
    lift . lift $ knownFuns %= M.insert f (PT ps ls' t'')

    alts'' <- postA $ applyAlts subst alts'
    t'''   <- postT t''
    lts' <- mapM postT (snd <$> ls')
    let ls'' = zip (fst <$> ls') lts'
    return (loc, FunDef f (PT ps ls'' t''') alts'')

-- ----------------------------------------------------------------------------
-- custTyGen

typecheckCustTyGen :: [(LocType, String)] -> TcM [(DepType, String)]
typecheckCustTyGen = mapM . firstM $ \t -> do
  let ?loc = posOfT t
  let t' = stripLocT t
  lift $ errCtx .= [CustomisedCodeGen t]
  if not (isMonoType t')
    then logErrExit (CustTyGenIsPolymorphic t)
    else lift (lift $ isSynonym t') >>= \case
           True -> logErrExit (CustTyGenIsSynonym t)
           _    -> do base <- lift . lift $ use knownConsts
                      let ctx = C.addScope (fmap (\(t,e,p) -> (t, p, Seq.singleton p)) base) C.empty
                      ((ct,t''), flx, os) <- runCG ctx [] [] $ validateType t'
                      (gs, subst) <- runSolver (solve [] [] ct) flx
                      exitOnErr $ toErrors os gs
                      postT $ apply subst t''



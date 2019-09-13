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

{-# OPTIONS_GHC -Werror -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cogent.TypeCheck.Solver.SinkFloat ( sinkfloat ) where 

--
-- Sink/Float is a type inference phase which pushes structural information
-- through subtyping constraints (sinking it down or floating it up).
--
-- In particular, this means adding missing fields to record and variant rows
-- and breaking single unification variables unified with a tuple into a tuple
-- of unification variables. Note that type operators do not change the
-- structure of a type, and so this phase propagates this information through
-- these.
--

import Cogent.Common.Types
import Cogent.Surface (Type(..))
import Cogent.TypeCheck.Base 
import Cogent.TypeCheck.Solver.Goal 
import Cogent.TypeCheck.Solver.Monad
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
import qualified Cogent.TypeCheck.Row as Row
import qualified Cogent.TypeCheck.Subst as Subst
import Cogent.Util (firstM, secondM)

import Control.Applicative (empty)
import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import qualified Data.Map as M
import Lens.Micro

sinkfloat :: Rewrite.RewriteT TcSolvM [Goal]
sinkfloat = Rewrite.rewrite' $ \gs -> do {- MaybeT TcSolvM -}
  a <- MaybeT $ do {- TcSolvM -}
    msubsts <- traverse (runMaybeT . genStructSubst . _goal) gs  -- a list of 'Maybe' substitutions.
    return . getFirst . mconcat $ First <$> msubsts  -- only return the first 'Just' substitution.
  tell [a]
  return $ map (goal %~ Subst.applyC a) gs
 where
  genStructSubst :: Constraint -> MaybeT TcSolvM Subst.Subst
  -- remove type operators first
  genStructSubst (T (TBang t)    :<  v          )   = genStructSubst (t :< v)
  genStructSubst (v              :<  T (TBang t))   = genStructSubst (v :< t)
  genStructSubst (T (TBang t)    :=: v          )   = genStructSubst (t :=: v)
  genStructSubst (v              :=: T (TBang t))   = genStructSubst (v :=: t)
  genStructSubst (T (TUnbox t)   :<  v          )   = genStructSubst (t :< v)
  genStructSubst (v              :<  T (TUnbox t))  = genStructSubst (v :< t)
  genStructSubst (T (TUnbox t)   :=: v          )   = genStructSubst (t :=: v)
  genStructSubst (v              :=: T (TUnbox t))  = genStructSubst (v :=: t)

  -- record rows
  genStructSubst (R r s :< U i) = do
    s' <- case s of
            Left Unboxed -> return $ Left Unboxed -- unboxed is preserved by bang and TUnbox, so we may propagate it
            _            ->  Right <$> lift solvFresh
    makeRowUnifSubsts (flip R s') r i
  genStructSubst (U i :< R r s) = do
    s' <- case s of
            Left Unboxed -> return $ Left Unboxed -- unboxed is preserved by bang and TUnbox, so we may propagate it
            _            ->  Right <$> lift solvFresh
    makeRowUnifSubsts (flip R s') r i
  genStructSubst (R r1 s1 :< R r2 s2)
    {-
      The most tricky case.
      For Records, Taken is the bottom of the order, Untaken is the top.
      If taken things are in r2, then we can infer they must be in r1.
      If untaken things are in r1, then we can infer they must be in r2.
    -}
    | r1new <- Row.takenEntries r2 `M.difference` Row.entries r1
    , not $ M.null r1new
    , Just r1var <- Row.var r1
      = makeRowRowVarSubsts r1new r1var
    | r2new <- Row.untakenEntries r1 `M.difference` Row.entries r2
    , not $ M.null r2new
    , Just r2var <- Row.var r2
      = makeRowRowVarSubsts r2new r2var
    | Left Unboxed <- s1 , Right i <- s2 = return $ Subst.ofSigil i Unboxed
    | Right i <- s1 , Left Unboxed <- s2 = return $ Subst.ofSigil i Unboxed

  -- variant rows
  genStructSubst (V r :< U i) = makeRowUnifSubsts V r i
  genStructSubst (U i :< V r) = makeRowUnifSubsts V r i
  genStructSubst (V r1 :< V r2)
    {-
      The most tricky case.
      For variants, Untaken is the bottom of the order, Taken is the top.
      If untaken things are in r2, then we can infer they must be in r1.
      If taken things are in r1, then we can infer they must be in r2.
    -}
    | r2new <- Row.takenEntries r1 `M.difference` Row.entries r2
    , not $ M.null r2new
    , Just r2var <- Row.var r2
      = makeRowRowVarSubsts r2new r2var
    | r1new <- Row.untakenEntries r2 `M.difference` Row.entries r1
    , not $ M.null r1new
    , Just r1var <- Row.var r1
      = makeRowRowVarSubsts r1new r1var

  -- tuples
  genStructSubst (T (TTuple ts) :< U i) = makeTupleUnifSubsts ts i
  genStructSubst (U i :< T (TTuple ts)) = makeTupleUnifSubsts ts i
  genStructSubst (T (TTuple ts) :=: U i) = makeTupleUnifSubsts ts i
  genStructSubst (U i :=: T (TTuple ts)) = makeTupleUnifSubsts ts i

  -- tcon
  genStructSubst (T (TCon n ts s) :< U i) = makeTConUnifSubsts n ts s i
  genStructSubst (U i :< T (TCon n ts s)) = makeTConUnifSubsts n ts s i
  genStructSubst (T (TCon n ts s) :=: U i) = makeTConUnifSubsts n ts s i
  genStructSubst (U i :=: T (TCon n ts s)) = makeTConUnifSubsts n ts s i

  -- tunit
  genStructSubst (t@(T TUnit) :< U i) = return $ Subst.ofType i t
  genStructSubst (U i :< t@(T TUnit)) = return $ Subst.ofType i t
  genStructSubst (t@(T TUnit) :=: U i) = return $ Subst.ofType i t
  genStructSubst (U i :=: t@(T TUnit)) = return $ Subst.ofType i t

  -- default
  genStructSubst _ = empty

  --
  -- Helper Functions
  --
  makeRowUnifSubsts frow r i = do
    es' <- traverse (secondM (firstM (const $ U <$> lift solvFresh))) $ Row.entries r
    rv' <- traverse (const (lift solvFresh)) $ Row.var r
    let r' = Row.Row es' rv'
    return $ Subst.ofType i (frow r')

  makeRowRowVarSubsts rnew rv = do
    rv' <- Just <$> lift solvFresh
    rnew' <- traverse (secondM (firstM (const (U <$> lift solvFresh)))) rnew
    return $ Subst.ofRow rv $ Row.Row rnew' rv'

  makeTupleUnifSubsts ts i = do
    tus <- traverse (const (U <$> lift solvFresh)) ts
    let t = T (TTuple tus)
    return $ Subst.ofType i t

  makeTConUnifSubsts n ts s i = do
    tus <- traverse (const (U <$> lift solvFresh)) ts
    let t = T (TCon n tus s) -- FIXME: n.b. only one type of sigil, so this is fine?
    return $ Subst.ofType i t


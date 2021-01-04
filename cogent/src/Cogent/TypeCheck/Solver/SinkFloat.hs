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

{-# LANGUAGE LambdaCase #-}
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
import Cogent.Surface (Type(..), Expr(..), bool)
import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Solver.Goal
import Cogent.TypeCheck.Solver.Monad
import Cogent.TypeCheck.Solver.Rewrite as Rewrite hiding (lift)
import qualified Cogent.TypeCheck.Row as R
import qualified Cogent.TypeCheck.Subst as Subst
import Cogent.TypeCheck.Util
import Cogent.Util (elemBy, notElemBy, hoistMaybe)

import Control.Applicative (empty)
import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import Data.Foldable (asum)
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.Set as S
import Lens.Micro
import Lens.Micro.Mtl
import Text.PrettyPrint.ANSI.Leijen (text, pretty)
import qualified Text.PrettyPrint.ANSI.Leijen as P

import Debug.Trace

sinkfloat :: Rewrite.RewriteT TcSolvM [Goal]
sinkfloat = Rewrite.rewrite' $ \gs -> do
  let mentions = getMentions gs
      cs = map (strip . _goal) gs
  a <- asum $ map (genStructSubst mentions) cs  -- a list of 'Maybe' substitutions.
                                                -- only return the first 'Just' substitution.
  tell [a]
  traceTc "solver" (text "Sink/Float writes subst:" P.<$>
                    P.indent 2 (pretty a))
  let gs' = map ((goalEnv %~ Subst.applyGoalEnv a) . (goal %~ Subst.applyC a)) gs

#ifdef REFINEMENT_TYPES
  gss <- forM gs' $ onGoal $ \case
    t1@(T (TRefine v b p)) :< U x
      | IS.member x (snd mentions)
      -> hoistMaybe $ Just [t1 :< T (TRefine v (U x) true)]
    U x :< t2@(T (TRefine v b p))
      | IS.member x (snd mentions)
      -> hoistMaybe $ Just [T (TRefine v (U x) true) :< t2]
    c -> hoistMaybe $ Just [c]
  return $ concat gss
#else
  return []
#endif
  where
    strip :: Constraint -> Constraint
    strip (T (TBang t)    :<  v          )   = t :< v
    strip (v              :<  T (TBang t))   = v :< t
    strip (T (TBang t)    :=: v          )   = t :=: v
    strip (v              :=: T (TBang t))   = v :=: t
    strip (T (TUnbox t)  :<  v           )   = t :< v
    strip (v             :<  T (TUnbox t))   = v :< t
    strip (T (TUnbox t)  :=: v          )    = t :=: v
    strip (v             :=: T (TUnbox t))   = v :=: t
    strip c = c

    -- For sinking row information in a subtyping constraint
    canSink :: IM.IntMap (Int,Int,Int) -> Int -> Bool
    canSink mentions v | Just m <- IM.lookup v mentions = m ^. _2 <= 1
                       | otherwise = False

    canFloat :: IM.IntMap (Int,Int,Int) -> Int -> Bool
    canFloat mentions v | Just m <- IM.lookup v mentions = m ^. _3 <= 1
                        | otherwise = False

    genStructSubst :: (IM.IntMap (Int,Int,Int), IS.IntSet) -> Constraint -> MaybeT TcSolvM Subst.Subst
    -- record rows
    genStructSubst _ (R rp r s :< U i) = do
      s' <- case s of
        Left Unboxed -> return $ Left Unboxed -- unboxed is preserved by bang and TUnbox, so we may propagate it
        _            -> Right <$> lift solvFresh
      makeRowUnifSubsts (flip (R rp) s') (filter R.taken (R.entries r)) i
    genStructSubst _ (U i :< R rp r s) = do
      s' <- case s of
        Left Unboxed -> return $ Left Unboxed -- unboxed is preserved by bang and TUnbox, so we may propagate it
        _            ->  Right <$> lift solvFresh
      -- Subst. a record structure for the unifier with only present entries of
      -- the record r (respecting the lattice order for records).
      makeRowUnifSubsts (flip (R rp) s') (filter R.present (R.entries r)) i
    genStructSubst (mentions,_) (R _ r1 s1 :< R _ r2 s2)
      {- The most tricky case.
         For Records, present is the bottom of the order, taken is the top.
         If present things are in r2, then we can infer they must be in r1.
         If taken things are in r1, then we can infer they must be in r2.
      -}
      | es <- filter (\e -> R.present e && notElemBy R.compatEntry e (R.entries r1))
                     (R.entries r2)
      , not $ null es
      , Just rv <- R.var r1
         = makeRowVarSubsts rv es
      | es <- filter (\e -> R.taken e && notElemBy R.compatEntry e (R.entries r2))
                     (R.entries r1)
      , not $ null es
      , Just rv <- R.var r2
         = makeRowVarSubsts rv es

      | R.isComplete r2 && all (\e -> elemBy R.compatEntry e (R.entries r2)) (R.entries r1)
      , Just rv <- R.var r1
      , es <- filter (\e -> R.taken e && notElemBy R.compatEntry e (R.entries r1))
                     (R.entries r2)
      , canSink mentions rv && not (null es)
         = makeRowVarSubsts rv es

      | R.isComplete r1 && all (\e -> elemBy R.compatEntry e (R.entries r1)) (R.entries r2)
      , Just rv <- R.var r2
      , es <- filter (\e -> R.present e && notElemBy R.compatEntry e (R.entries r2))
                     (R.entries r1)
      , canFloat mentions rv && not (null es)
         = makeRowVarSubsts rv es

      | R.isComplete r1
      , null (R.diff r1 r2)
      , Just rv <- R.var r2
         = makeRowShapeSubsts rv r1

      | R.isComplete r2
      , null (R.diff r2 r1)
      , Just rv <- R.var r1
         = makeRowShapeSubsts rv r2
  
      | Left Unboxed <- s1 , Right i <- s2 = return $ Subst.ofSigil i Unboxed
      | Right i <- s1 , Left Unboxed <- s2 = return $ Subst.ofSigil i Unboxed

    genStructSubst _ (R rp r s :~~ U i) = do
      s' <- case s of
              Left Unboxed -> return $ Left Unboxed
              _            -> Right <$> lift solvFresh
      makeRowUnifSubsts (flip (R rp) s') (filter R.taken (R.entries r)) i
    genStructSubst _ (U i :~~ R rp r s) = do
      s' <- case s of
              Left Unboxed -> return $ Left Unboxed
              _            -> Right <$> lift solvFresh
      makeRowUnifSubsts (flip (R rp) s') (filter R.taken (R.entries r)) i

    -- variant rows
    genStructSubst _ (V r :< U i) =
      makeRowUnifSubsts V (filter R.present (R.entries r)) i
    genStructSubst _ (U i :< V r) =
      makeRowUnifSubsts V (filter R.taken (R.entries r)) i
    genStructSubst (mentions,_) (V r1 :< V r2)
      -- \ | trace ("#### r1 = " ++ show r1 ++ "\n#### r2 = " ++ show r2) False = undefined
      {- The most tricky case.
         For variants, taken is the bottom of the order.
         If taken things are in r2, then we can infer they must be in r1.
         If present things are in r1, then we can infer they must be in r2.
       -}
      | es <- filter (\e -> R.taken e && notElemBy R.compatEntry e (R.entries r1))
                     (R.entries r2)
      , not $ null es
      , Just rv <- R.var r1
         = makeRowVarSubsts rv es
      | es <- filter (\e -> R.present e && notElemBy R.compatEntry e (R.entries r2))
                     (R.entries r1)
      , not $ null es
      , Just rv <- R.var r2
         = makeRowVarSubsts rv es

      | R.isComplete r2 && all (\e -> elemBy R.compatEntry e (R.entries r2)) (R.entries r1)
      , Just rv <- R.var r1
      , es <- filter (\e -> R.present e && notElemBy R.compatEntry e (R.entries r1))
                     (R.entries r2)
      , canSink mentions rv && not (null es)
         = makeRowVarSubsts rv es

      | R.isComplete r1 && all (\e -> elemBy R.compatEntry e (R.entries r1)) (R.entries r2)
      , Just rv <- R.var r2
      , es <- filter (\e -> R.taken e && notElemBy R.compatEntry e (R.entries r2))
                     (R.entries r1)
      , canFloat mentions rv && not (null es)
         = makeRowVarSubsts rv es

      | R.isComplete r1
      , null (R.diff r1 r2)
      , Just rv <- R.var r2
         = makeRowShapeSubsts rv r1

      | R.isComplete r2
      , null (R.diff r2 r1)
      , Just rv <- R.var r1
         = makeRowShapeSubsts rv r2

    genStructSubst _ (V r :~~ U i) = makeRowUnifSubsts V (filter R.present (R.entries r)) i
    genStructSubst _ (U i :~~ V r) = makeRowUnifSubsts V (filter R.present (R.entries r)) i

    -- tuples
    genStructSubst _ (T (TTuple ts) :< U i) = makeTupleUnifSubsts ts i
    genStructSubst _ (U i :< T (TTuple ts)) = makeTupleUnifSubsts ts i
    genStructSubst _ (T (TTuple ts) :=: U i) = makeTupleUnifSubsts ts i
    genStructSubst _ (U i :=: T (TTuple ts)) = makeTupleUnifSubsts ts i

    -- tcon
    genStructSubst _ (T (TCon n ts s) :< U i) = makeTConUnifSubsts n ts s i
    genStructSubst _ (U i :< T (TCon n ts s)) = makeTConUnifSubsts n ts s i
    genStructSubst _ (T (TCon n ts s) :=: U i) = makeTConUnifSubsts n ts s i
    genStructSubst _ (U i :=: T (TCon n ts s)) = makeTConUnifSubsts n ts s i

    -- tfun
    genStructSubst _ (T (TFun mv _ _) :< U i)  = makeFunUnifSubsts mv i
    genStructSubst _ (U i :< T (TFun mv _ _))  = makeFunUnifSubsts mv i
    genStructSubst _ (T (TFun mv _ _) :=: U i) = makeFunUnifSubsts mv i
    genStructSubst _ (U i :=: T (TFun mv _ _)) = makeFunUnifSubsts mv i

    -- tunit
    genStructSubst _ (t@(T TUnit) :< U i) = return $ Subst.ofType i t
    genStructSubst _ (U i :< t@(T TUnit)) = return $ Subst.ofType i t
    genStructSubst _ (t@(T TUnit) :=: U i) = return $ Subst.ofType i t
    genStructSubst _ (U i :=: t@(T TUnit)) = return $ Subst.ofType i t

#ifdef REFINEMENT_TYPES
    -- refinement types
    genStructSubst (_,basetypes) (T (TRefine v b p) :< U x)
      | IS.notMember x basetypes
      = do q <- lift solvFresh
           u <- freshRefVarName _2
           return $ Subst.ofType x (T (TRefine u b (HApp q u [])))
    genStructSubst (_,basetypes) (U x :< T (TRefine v b p))
      | IS.notMember x basetypes
      = do q <- lift solvFresh
           u <- freshRefVarName _2
           return $ Subst.ofType x (T (TRefine u b (HApp q u [])))
#endif

    -- default
    genStructSubst _ _ = empty

    --
    -- Helper Functions
    --

    makeEntryUnif e = R.mkEntry <$>
                      pure (R.fname e) <*>
                      (U <$> lift solvFresh) <*> pure (R.taken e)

    -- Substitute a record structure for the unifier with only the specified
    -- entries, hence an incomplete record.
    makeRowUnifSubsts frow es u =
      do rv <- lift solvFresh
         es' <- traverse makeEntryUnif es
         return $ Subst.ofType u (frow (R.incomplete es' rv))

    -- Expand rows containing row variable rv with the specified entries.
    makeRowVarSubsts rv es =
      do rv' <- lift solvFresh
         es' <- traverse makeEntryUnif es
         return $ Subst.ofRow rv $ R.incomplete es' rv'

    -- Create a shape substitution for the row variable.
    makeRowShapeSubsts rv row =
      return $ Subst.ofShape rv (R.shape row)

    makeTupleUnifSubsts ts i = do
      tus <- traverse (const (U <$> lift solvFresh)) ts
      let t = T (TTuple tus)
      return $ Subst.ofType i t

    makeFunUnifSubsts mv i = do
      t' <- U <$> lift solvFresh
      u' <- U <$> lift solvFresh
      return . Subst.ofType i . T $ TFun mv t' u'

    makeTConUnifSubsts n ts s i = do
      tus <- traverse (const (U <$> lift solvFresh)) ts
      let t = T (TCon n tus s)  -- FIXME: A[R] :< (?0)! will break if ?0 ~> A[W] is needed somewhere else
      return $ Subst.ofType i t


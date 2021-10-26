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

{-# LANGUAGE RecursiveDo #-}
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
import qualified Cogent.TypeCheck.Row as R
import qualified Cogent.TypeCheck.Subst as Subst
import Cogent.TypeCheck.Util
import Cogent.Util (elemBy, notElemBy)

import Control.Applicative (empty)
import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import Data.Foldable (asum)
import qualified Data.IntMap as IM
import Lens.Micro
import Text.PrettyPrint.ANSI.Leijen (text, pretty)
import qualified Text.PrettyPrint.ANSI.Leijen as P

import Debug.Trace


sinkfloat :: Rewrite.RewriteT TcSolvM [Goal]
sinkfloat = Rewrite.rewrite' $ \gs -> do
  let mentions = getMentions gs
      cs = map (strip . _goal) gs
  a <- asum $ map (genStructSubst mentions) cs -- a list of 'Maybe' substitutions.
                                               -- only return the first 'Just' substitution.
  tell [a]
  traceTc "solver" (text "Sink/Float writes subst:" P.<$>
                    P.indent 2 (pretty a))
  return $ map (goal %~ Subst.applyC a) gs
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
    canSink :: IM.IntMap (Int,Int) -> Int -> Bool
    canSink mentions v | Just m <- IM.lookup v mentions = fst m <= 1
                       | otherwise = False

    canFloat :: IM.IntMap (Int,Int) -> Int -> Bool
    canFloat mentions v | Just m <- IM.lookup v mentions = snd m <= 1
                        | otherwise = False

    genStructSubst :: IM.IntMap (Int,Int) -> Constraint -> MaybeT TcSolvM Subst.Subst
    -- record rows
    genStructSubst _ (t@(R rp r s) :< U i) = do
      s' <- case s of
        Left Unboxed -> return $ Left Unboxed -- unboxed is preserved by bang and TUnbox, so we may propagate it
        _            -> Right <$> lift (solvFresh $ SinkFloatSigil (U i) t)
      makeRowUnifSubsts i (flip (R rp) s') (filter R.taken (R.entries r)) t
    genStructSubst _ (U i :< t@(R rp r s)) = do
      s' <- case s of
        Left Unboxed -> return $ Left Unboxed -- unboxed is preserved by bang and TUnbox, so we may propagate it
        _            -> Right <$> lift (solvFresh $ SinkFloatSigil (U i) t)
      -- Subst. a record structure for the unifier with only present entries of
      -- the record r (respecting the lattice order for records).
      makeRowUnifSubsts i (flip (R rp) s') (filter R.present (R.entries r)) t
    genStructSubst mentions (t1@(R _ r1 s1) :< t2@(R _ r2 s2))
      {- The most tricky case.
         For Records, present is the bottom of the order, taken is the top.
         If present things are in r2, then we can infer they must be in r1.
         If taken things are in r1, then we can infer they must be in r2.
      -}
      | es <- filter (\e -> R.present e && notElemBy R.compatEntry e (R.entries r1))
                     (R.entries r2)
      , not $ null es
      , Just rv <- R.var r1
         = makeRowVarSubsts rv es t1 t2

      | es <- filter (\e -> R.taken e && notElemBy R.compatEntry e (R.entries r2))
                     (R.entries r1)
      , not $ null es
      , Just rv <- R.var r2
         = makeRowVarSubsts rv es t1 t2

      | R.isComplete r2 && all (\e -> elemBy R.compatEntry e (R.entries r2)) (R.entries r1)
      , Just rv <- R.var r1
      , es <- filter (\e -> R.taken e && notElemBy R.compatEntry e (R.entries r1))
                     (R.entries r2)
      , canSink mentions rv && not (null es)
         = makeRowVarSubsts rv es t1 t2

      | R.isComplete r1 && all (\e -> elemBy R.compatEntry e (R.entries r1)) (R.entries r2)
      , Just rv <- R.var r2
      , es <- filter (\e -> R.present e && notElemBy R.compatEntry e (R.entries r2))
                     (R.entries r1)
      , canFloat mentions rv && not (null es)
         = makeRowVarSubsts rv es t1 t2

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

    genStructSubst _ (t@(R rp r s) :~~ U i) = do
      s' <- case s of
              Left Unboxed -> return $ Left Unboxed
              _            -> Right <$> lift (solvFresh $ SinkFloatSigil (U i) t)
      makeRowUnifSubsts i (flip (R rp) s') (filter R.taken (R.entries r)) t
    genStructSubst _ (U i :~~ t@(R rp r s)) = do
      s' <- case s of
              Left Unboxed -> return $ Left Unboxed
              _            -> Right <$> lift (solvFresh $ SinkFloatSigil (U i) t)
      makeRowUnifSubsts i (flip (R rp) s') (filter R.taken (R.entries r)) t

    -- variant rows
    genStructSubst _ (t@(V r) :< U i) =
      makeRowUnifSubsts i V (filter R.present (R.entries r)) t
    genStructSubst _ (U i :< t@(V r)) =
      makeRowUnifSubsts i V (filter R.taken (R.entries r)) t
    genStructSubst mentions (t1@(V r1) :< t2@(V r2))
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
         = makeRowVarSubsts rv es t1 t2

      | es <- filter (\e -> R.present e && notElemBy R.compatEntry e (R.entries r2))
                     (R.entries r1)
      , not $ null es
      , Just rv <- R.var r2
         = makeRowVarSubsts rv es t1 t2

      | R.isComplete r2 && all (\e -> elemBy R.compatEntry e (R.entries r2)) (R.entries r1)
      , Just rv <- R.var r1
      , es <- filter (\e -> R.present e && notElemBy R.compatEntry e (R.entries r1))
                     (R.entries r2)
      , canSink mentions rv && not (null es)
         = makeRowVarSubsts rv es t1 t2

      | R.isComplete r1 && all (\e -> elemBy R.compatEntry e (R.entries r1)) (R.entries r2)
      , Just rv <- R.var r2
      , es <- filter (\e -> R.taken e && notElemBy R.compatEntry e (R.entries r2))
                     (R.entries r1)
      , canFloat mentions rv && not (null es)
         = makeRowVarSubsts rv es t1 t2

      | R.isComplete r1
      , null (R.diff r1 r2)
      , Just rv <- R.var r2
         = makeRowShapeSubsts rv r1

      | R.isComplete r2
      , null (R.diff r2 r1)
      , Just rv <- R.var r1
         = makeRowShapeSubsts rv r2

    genStructSubst _ (t@(V r) :~~ U i) = makeRowUnifSubsts i V (filter R.present (R.entries r)) t
    genStructSubst _ (U i :~~ t@(V r)) = makeRowUnifSubsts i V (filter R.present (R.entries r)) t

    -- tuples
    genStructSubst _ (T (TTuple ts) :< U i) = makeTupleUnifSubsts i ts
    genStructSubst _ (U i :< T (TTuple ts)) = makeTupleUnifSubsts i ts
    genStructSubst _ (T (TTuple ts) :=: U i) = makeTupleUnifSubsts i ts
    genStructSubst _ (U i :=: T (TTuple ts)) = makeTupleUnifSubsts i ts

    -- tcon
    genStructSubst _ (T (TCon n ts s) :< U i) = makeTConUnifSubsts  i n ts s
    genStructSubst _ (U i :< T (TCon n ts s)) = makeTConUnifSubsts  i n ts s
    genStructSubst _ (T (TCon n ts s) :=: U i) = makeTConUnifSubsts i n ts s
    genStructSubst _ (U i :=: T (TCon n ts s)) = makeTConUnifSubsts i n ts s

    -- tfun
    genStructSubst _ (t@(T (TFun _ _)) :< U i)  = makeFunUnifSubsts i t
    genStructSubst _ (U i :< t@(T (TFun _ _)))  = makeFunUnifSubsts i t
    genStructSubst _ (t@(T (TFun _ _)) :=: U i) = makeFunUnifSubsts i t
    genStructSubst _ (U i :=: t@(T (TFun _ _))) = makeFunUnifSubsts i t

    -- tunit
    genStructSubst _ (t@(T TUnit) :< U i) = return $ Subst.ofType i t
    genStructSubst _ (U i :< t@(T TUnit)) = return $ Subst.ofType i t
    genStructSubst _ (t@(T TUnit) :=: U i) = return $ Subst.ofType i t
    genStructSubst _ (U i :=: t@(T TUnit)) = return $ Subst.ofType i t

    -- default
    genStructSubst _ _ = empty

    --
    -- Helper Functions
    --

    makeEntryUnif e t1 t2 = R.mkEntry <$>
                            pure (R.fname e) <*>
                            (U <$> lift (solvFresh $ SinkFloatEntry e t1 t2)) <*> pure (R.taken e)

    -- Substitute a record structure for the unifier with only the specified
    -- entries, hence an incomplete record.
    makeRowUnifSubsts :: Int -> (R.Row TCType -> TCType) -> [R.Entry TCType] -> TCType -> MaybeT TcSolvM Subst.Subst
    makeRowUnifSubsts i frow es t = mdo
      rv <- lift (solvFresh $ SinkFloat (U i) s t)
      es' <- traverse (\e -> makeEntryUnif e (U i) t) es
      let s = frow (R.incomplete es' rv)
      return $ Subst.ofType i s

    -- Expand rows containing row variable rv with the specified entries.
    makeRowVarSubsts rv es t1 t2 = mdo
      rv' <- lift (solvFresh $ SinkFloatRow rv s t1 t2)
      es' <- traverse (\e -> makeEntryUnif e t1 t2) es
      let s = R.incomplete es' rv'
      return $ Subst.ofRow rv s

    -- Create a shape substitution for the row variable.
    makeRowShapeSubsts rv row =
      return $ Subst.ofShape rv (R.shape row)

    makeTupleUnifSubsts i ts = mdo
      tus <- traverse (const (U <$> lift (solvFresh $ SinkFloat (U i) s (T $ TTuple ts)))) ts
      let s = T (TTuple tus)
      return $ Subst.ofType i s

    makeFunUnifSubsts i t = mdo
      t' <- U <$> lift (solvFresh $ SinkFloat (U i) s t)
      u' <- U <$> lift (solvFresh $ SinkFloat (U i) s t)
      let s = T $ TFun t' u'
      return $ Subst.ofType i s

    makeTConUnifSubsts i n ts s = mdo
      tus <- traverse (const (U <$> lift (solvFresh $ SinkFloat (U i) t (T $ TCon n ts s)))) ts
      let t = T (TCon n tus s)  -- FIXME: A[R] :< (?0)! will break if ?0 ~> A[W] is needed somewhere else
      return $ Subst.ofType i t


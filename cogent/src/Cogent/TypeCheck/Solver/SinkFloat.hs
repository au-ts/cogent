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

import Cogent.Surface (Type(..))
import Cogent.TypeCheck.Base 
import Cogent.TypeCheck.Solver.Goal 
import Cogent.TypeCheck.Solver.Monad
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
import qualified Cogent.TypeCheck.Row as Row
import qualified Cogent.TypeCheck.Subst as Subst

import Control.Applicative (empty)
import Control.Monad.Writer
import Control.Monad.Trans.Maybe

import qualified Data.Map as M

import Lens.Micro

sinkfloat :: Rewrite.Rewrite' TcSolvM [Goal]
sinkfloat = Rewrite.rewrite' $ \gs -> do {- MaybeT TcSolvM -}
  a <- MaybeT (do {- TcSolvM -}
    let genGoalSubst = uncurry genStructSubst <=< splitConstraint . _goal
    (msigmas :: [Maybe Subst.Subst]) <- traverse (runMaybeT . genGoalSubst) gs
    let msigma = getFirst . mconcat $ First <$> msigmas
    return msigma)
  tell [a]
  return $ map (goal %~ Subst.applyC a) gs
 where
  splitConstraint :: Constraint -> MaybeT TcSolvM (TCType, TCType)
  splitConstraint (ta :<  tb) = return (ta, tb)
  splitConstraint (ta :=: tb) = return (ta, tb)
  splitConstraint _           = empty

  genStructSubst :: TCType -> TCType -> MaybeT TcSolvM Subst.Subst
  -- remove type operators first
  genStructSubst (T (TBang t))   v               = genStructSubst t v
  genStructSubst v               (T (TBang t))   = genStructSubst t v
  genStructSubst (T (TUnbox t))  v               = genStructSubst t v
  genStructSubst v               (T (TUnbox t))  = genStructSubst t v
  genStructSubst (T (TTake _ t)) v               = genStructSubst t v
  genStructSubst v               (T (TTake _ t)) = genStructSubst t v
  genStructSubst (T (TPut _ t))  v               = genStructSubst t v
  genStructSubst v               (T (TPut _ t))  = genStructSubst t v

  -- record rows
  genStructSubst (R r _) v
    | fs <- discard_common v $ get_taken r
    , not $ M.null fs
    = do
      sigilI <- lift solvFresh
      makeRowStructureSubsts (flip R (Right sigilI)) fs v
  genStructSubst v (R r _)
    | fs <- discard_common v $ get_taken r
    , not $ M.null fs
    = do
      sigilI <- lift solvFresh
      makeRowStructureSubsts (flip R (Right sigilI)) fs v

  -- variant rows
  genStructSubst (V r) v
    | fs <- discard_common v $ get_present r
    , not $ M.null fs
    = makeRowStructureSubsts V fs v
  genStructSubst v (V r)
    | fs <- discard_common v $ get_present r
    , not $ M.null fs
    = makeRowStructureSubsts V fs v

  -- tuples
  genStructSubst (T (TTuple ts)) v = genStructSubstTuple ts v
  genStructSubst v (T (TTuple ts)) = genStructSubstTuple ts v

  -- tcon
  genStructSubst (T (TCon n ts s)) v = genStructSubstTCon n ts s v
  genStructSubst v (T (TCon n ts s)) = genStructSubstTCon n ts s v

  -- default
  genStructSubst _ _ = empty


  makeRowStructureSubsts frow fs v = do
    v' <- lift solvFresh
    ts <- traverse (secondFirstF (const (U <$> lift solvFresh))) fs
    let r' = Row.Row ts (Just v')
    substOf_row frow v r'
    where
      secondFirstF :: forall f a b c b'. Functor f => (b -> f b') -> (a,(b,c)) -> f (a,(b',c))
      secondFirstF f (a,(b,c)) = (\b' -> (a,(b',c))) <$> f b

  substOf_row frow (U v') t
    = return (Subst.ofType v' (frow t))
  substOf_row _ (R r _) t
    | Just v' <- Row.var r
    = return (Subst.ofRow v' t)
  substOf_row _ (V r) t
    | Just v' <- Row.var r
    = return (Subst.ofRow v' t)
  substOf_row _ _ _
    = empty

  genStructSubstTuple ts v = do
    tus <- traverse (const (U <$> lift solvFresh)) ts
    let t = T (TTuple tus)
    case v of
      U v' -> return $ Subst.ofType v' t
      _    -> empty

  genStructSubstTCon n ts s v = do
    tus <- traverse (const (U <$> lift solvFresh)) ts
    let t = T (TCon n tus s) -- FIXME: n.b. only one type of sigil, so this is fine?
    case v of
      U v' -> return $ Subst.ofType v' t
      _    -> empty

  get_taken    = get_fields True
  get_present  = get_fields False
  get_fields t = M.filter (\(_,(_,t')) -> t == t') . Row.entries

  discard_common (U _) fs   = fs
  discard_common (R r _) fs = M.difference fs $ Row.entries r
  discard_common (V r)   fs = M.difference fs $ Row.entries r
  discard_common _ _        = M.empty


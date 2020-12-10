--
-- Copyright 2020, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE FlexibleContexts #-}

module Cogent.TypeCheck.Solver.JoinMeet (joinMeet, reShape) where

import Cogent.Surface
import Cogent.TypeCheck.Base
import Cogent.Common.Types
import Cogent.Common.Syntax
import Cogent.TypeCheck.Solver.Goal
import Cogent.TypeCheck.Solver.Monad
import Cogent.TypeCheck.Solver.Rewrite hiding (lift)
import qualified Cogent.TypeCheck.Subst as Subst
import qualified Cogent.TypeCheck.Row as Row
import Cogent.TypeCheck.Util
import Cogent.Util (hoistMaybe)

import Control.Applicative
import Control.Monad
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe
import Control.Monad.Writer (tell)
import Data.Foldable (asum, fold)
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.List (partition)
import qualified Data.Map as M
import qualified Data.Set as S
import Lens.Micro
import Lens.Micro.Mtl
import qualified Text.PrettyPrint.ANSI.Leijen as P hiding (bool, empty)

import Debug.Trace

data Candidate = Meet [ErrorContext] [ErrorContext] TCType TCType TCType
               | Join [ErrorContext] [ErrorContext] TCType TCType TCType



reShape :: RewriteT TcSolvM [Goal]
reShape = rewrite' $ \gs -> do
            let baseTypes = getBaseTypes gs
            a <- asum (map (expand baseTypes . view goal) gs)
            tell [a]
            traceTc "solver" (P.text "ReShape writes subst:" P.<$> 
                              P.indent 2 (P.pretty a))
            return $ map ((goalEnv %~ Subst.applyGoalEnv a) . (goal %~ Subst.applyC a)) gs

  where
    expand :: IS.IntSet -> Constraint -> MaybeT TcSolvM Subst.Subst
    expand mentions (T (TRefine v b p) :< U x)
      | IS.notMember x mentions
      = do q <- lift $ solvFresh
           u <- freshRefVarName _2
           return $ Subst.ofType x (T (TRefine u b (SU (T bool) q)))
    expand mentions (U x :< T (TRefine v b p))
      | IS.notMember x mentions
      = do q <- lift $ solvFresh
           u <- freshRefVarName _2
           return $ Subst.ofType x (T (TRefine u b (SU (T bool) q)))
    expand mentions c
      = empty

compBase :: RewriteT TcSolvM [Goal]
compBase = rewrite $ \gs ->
  let mentions = getBaseTypes gs
   in each (onGoal $ simp mentions) gs

  where
    each :: (Goal -> Maybe [Goal]) -> [Goal] -> Maybe [Goal]
    each f [] = empty
    each f (c:cs) =
      case f c of
        Nothing  -> (c:) <$> each f cs
        Just cs' -> Just $ cs' ++ cs

    onGoal :: (Constraint -> Maybe [Constraint]) -> Goal -> Maybe [Goal]
    onGoal f g = fmap (map (derivedGoal g)) (f (g ^. goal))

    true = SE (T bool) (BoolLit True)

    simp :: IS.IntSet -> Constraint -> Maybe [Constraint]
    simp mentions (t1@(T (TRefine v b p)) :< U x)
      | IS.member x mentions = Just [t1 :< T (TRefine v (U x) true)]
    simp mentions (U x :< t2@(T (TRefine v b p)))
      | IS.member x mentions = Just [T (TRefine v (U x) true) :< t2]
    simp _ c = Nothing

getBaseTypes :: [Goal] -> IS.IntSet
getBaseTypes = foldl go IS.empty
  where
    go :: IS.IntSet -> Goal -> IS.IntSet
    go acc (Goal _ _ (BaseType (U x))) = IS.insert x acc
    -- \ ^^^ We know that when generating constraints, the @BaseType@ is always on a unifier. / zilinc
    go acc _ = acc


-- | Find pairs of subtyping constraints that involve the same unification variable
--   on the right or left hand side, and compute the join/meet to simplify the
--   constraint graph.
joinMeet :: RewriteT TcSolvM [Goal]
joinMeet = reShape <> compBase

{-
joinMeet = Rewrite.withTransform find $ \c -> case c of
  Meet c1 c2 v t1@(T (TRefine v1 b1 p1)) t2@(T (TRefine v2 b2 p2)) | b1 == b2 -> do
    let p1' = substExpr [(v1, SE b1 (Var refVarName))] p1
        p2' = substExpr [(v2, SE b2 (Var refVarName))] p2
        t = T (TRefine refVarName b1 ((SE (T bool) (PrimOp "||" [p1', p2']))))
    pure [ Goal c1 (v :< t)
         , Goal c1 (t :< t1)
         , Goal c2 (t :< t2)
         ]
  Join c1 c2 v t1@(T (TRefine v1 b1 p1)) t2@(T (TRefine v2 b2 p2)) | b1 == b2 -> do
    let p1' = substExpr [(v1, SE b1 (Var refVarName))] p1
        p2' = substExpr [(v2, SE b2 (Var refVarName))] p2
        t = T (TRefine refVarName b1 ((SE (T bool) (PrimOp "||" [p1', p2']))))
    pure [ Goal c1 (t :< v)
         , Goal c1 (t1 :< t)
         , Goal c2 (t2 :< t)
         ]
  -- XXX | Meet c1 c2 v (T (TFun t1 t2)) (T (TFun r1 r2)) -> do
  -- XXX |   b1 <- U <$> lift solvFresh
  -- XXX |   b2 <- U <$> lift solvFresh
  -- XXX |   pure [ Goal c1 (v :< T (TFun b1 b2))
  -- XXX |        , Goal c2 (b2 :< r2), Goal c1 (b2 :< t2)
  -- XXX |        , Goal c1 (t1 :< b1), Goal c2 (r1 :< b1)
  -- XXX |        ]
  -- XXX | Join c1 c2 v (T (TFun t1 t2)) (T (TFun r1 r2)) -> do
  -- XXX |   b1 <- U <$> lift solvFresh
  -- XXX |   b2 <- U <$> lift solvFresh
  -- XXX |   pure [ Goal c1 (v >: T (TFun b1 b2))
  -- XXX |        , Goal c2 (b2 >: r2), Goal c1 (b2 >: t2)
  -- XXX |        , Goal c1 (t1 >: b1), Goal c2 (r1 >: b1)
  -- XXX |        ]
  -- XXX | Meet c1 c2 v (T (TTuple ts)) (T (TTuple us)) -> do
  -- XXX |   bs <- fmap U <$> lift (solvFreshes (length ts))
  -- XXX |   pure [ Goal c1 (v :< T (TTuple bs))
  -- XXX |        , Goal c1 (T (TTuple bs) :< T (TTuple ts) )
  -- XXX |        , Goal c2 (T (TTuple bs) :< T (TTuple us) )
  -- XXX |        ]
  -- XXX | Join c1 c2 v (T (TTuple ts)) (T (TTuple us)) -> do
  -- XXX |   bs <- fmap U <$> lift (solvFreshes (length ts))
  -- XXX |   pure [ Goal c1 (v >: T (TTuple bs))
  -- XXX |        , Goal c1 (T (TTuple bs) >: T (TTuple ts) )
  -- XXX |        , Goal c2 (T (TTuple bs) >: T (TTuple us) )
  -- XXX |        ]

  _ -> empty


find :: [Goal] -> Maybe (Candidate, [Goal])
find [] = Nothing
find (c:cs) = case c ^. goal of
  U v :< tau
    | rigid tau -> case partition (flexRigidSub v) cs of
           ([], rs ) -> fmap (c:) <$> find cs
           (Goal ctx (_ :< rho):rs, rs')
             -> pure (Meet (c ^. goalContext) ctx (U v) tau rho , rs ++ rs')
  tau :< U v
    | rigid tau -> case partition (flexRigidSup v) cs of
           ([], rs ) -> fmap (c:) <$> find cs
           (Goal ctx (rho :< _):rs, rs')
             -> pure (Join (c ^. goalContext) ctx (U v) tau rho , rs ++ rs')

  where
    flexRigidSub v (Goal _ env (U v' :< rho)) = rigid rho && v == v'
    flexRigidSub v _ = False

    flexRigidSup v (Goal _ env (rho :< U v')) = rigid rho && v == v'
    flexRigidSup v _= False

-}

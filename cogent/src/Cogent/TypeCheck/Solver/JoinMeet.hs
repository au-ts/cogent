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

module Cogent.TypeCheck.Solver.JoinMeet (joinMeet) where

import Cogent.Common.Types
import Cogent.Common.Syntax
import Cogent.PrettyPrint
import Cogent.Surface
import Cogent.TypeCheck.Base
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
import Data.List (partition)
import qualified Data.Map as M
import Lens.Micro
import qualified Text.PrettyPrint.ANSI.Leijen as P hiding (bool, empty)

import Debug.Trace

data Candidate = Meet [ErrorContext] [ErrorContext] ConstraintEnv ConstraintEnv TCType TCType TCType
               | Join [ErrorContext] [ErrorContext] ConstraintEnv ConstraintEnv TCType TCType TCType


-- | Find pairs of subtyping constraints that involve the same unification variable
--   on the right or left hand side, and compute the join/meet to simplify the
--   constraint graph.
joinMeet :: RewriteT TcSolvM [Goal]
joinMeet = withTransform find $ \c -> case c of
  Meet c1 c2 (γ1,ρ1) (γ2,ρ2) τ τ1@(T (TRefine v1 b1 p1)) τ2@(T (TRefine v2 b2 p2)) | b1 == b2 -> do
    let p2' = substVarExpr [(v2, v1)] p2
        τ' = T (TRefine v1 b1 ((SE (T bool) (PrimOp "&&" [p1, p2']))))
    pure [ Goal c1 (γ1 `M.union` γ2, ρ1 ++ ρ2) (τ :< τ')  -- FIXME: subst env, and merge properly.
         , Goal c1 (γ1 `M.union` γ2, []) (τ' :< τ1)
         , Goal c2 (γ1 `M.union` γ2, []) (τ' :< τ2)
         ]
  Join c1 c2 (γ1,ρ1) (γ2,ρ2) τ τ1@(T (TRefine v1 b1 p1)) τ2@(T (TRefine v2 b2 p2)) | b1 == b2 -> do
    let p2' = substVarExpr [(v2, v1)] p2
        τ' = T (TRefine v1 b1 ((SE (T bool) (PrimOp "||" [p1, p2']))))
    pure [ Goal c1 (γ1 `M.union` γ2, ρ1 ++ ρ2) (τ  >: τ')  -- FIXME: ditto
         , Goal c1 (γ1 `M.union` γ2, []) (τ' >: τ1)
         , Goal c2 (γ1 `M.union` γ2, []) (τ' >: τ2)
         ]
  _ -> empty


find :: [Goal] -> Maybe (Candidate, [Goal])
find [] = Nothing
find (c:cs) = case c ^. goal of
  τ1@(T (TRefine v1 b1 (HApp x _ _))) :< τ2@(T (TRefine v2 b2 ϕ))
    | isKnown ϕ -> case partition (flexRigidSub τ1 b2) cs of
           ([], rs ) -> fmap (c:) <$> find cs
           (Goal ctx env (_ :< ρ):rs, rs')
             -> pure (Meet (c ^. goalContext) ctx (c ^. goalEnv) env τ1 τ2 ρ , rs ++ rs')
  τ1@(T (TRefine v1 b1 ϕ)) :< τ2@(T (TRefine v2 b2 (HApp x _ _)))
    | isKnown ϕ -> case partition (flexRigidSup τ2 b1) cs of
           ([], rs ) -> fmap (c:) <$> find cs
           (Goal ctx env (ρ :< _):rs, rs')
             -> pure (Join (c ^. goalContext) ctx (c ^. goalEnv) env τ2 τ1 ρ , rs ++ rs')
  _ -> fmap (c:) <$> find cs

  where
    flexRigidSub τ1 b2 (Goal _ env (τ :< T (TRefine v2 b2' ϕ)))
      = τ == τ1 && b2 == b2' && isKnown ϕ  -- FIXME: the type equality is wrong. need to be α-equiv.
    flexRigidSub _ _ _ = False

    flexRigidSup τ2 b1 (Goal _ env (T (TRefine v1 b1' ϕ) :< τ))
      = τ == τ2 && b1 == b1' && isKnown ϕ
    flexRigidSup _ _ _ = False


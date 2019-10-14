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

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Cogent.TypeCheck.Solver (runSolver, solve) where

import           Cogent.Common.Syntax
import           Cogent.Common.Types
import           Cogent.Compiler
import           Cogent.PrettyPrint (prettyC)
import           Cogent.Surface
import           Cogent.TypeCheck.Base
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
import           Cogent.TypeCheck.Solver.Monad
import           Cogent.TypeCheck.Solver.Normalise
import           Cogent.TypeCheck.Solver.Simplify
import           Cogent.TypeCheck.Solver.Unify
import           Cogent.TypeCheck.Solver.JoinMeet
import           Cogent.TypeCheck.Solver.Equate
import           Cogent.TypeCheck.Solver.Default
import           Cogent.TypeCheck.Solver.SinkFloat
import qualified Cogent.TypeCheck.Subst as Subst
import           Cogent.TypeCheck.Subst (Subst(..))
import           Cogent.TypeCheck.Util
import           Cogent.TypeCheck.Solver.Goal
import           Cogent.Util (fst3, u32MAX, Bound(..))

import           Control.Applicative
import           Control.Arrow (first, second)
import           Control.Monad.State hiding (modify)
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.State (modify)
import           Data.Either (either)
import qualified Data.Foldable as F
import           Data.Function (on)
import           Data.Functor.Compose (Compose(..))
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
--import qualified Data.List as L
import           Data.List (elemIndex)
import qualified Data.Map as M
import           Data.Maybe (fromMaybe, mapMaybe)
import           Data.Monoid
#ifdef BUILTIN_ARRAYS
-- import Z3 stuff...
#endif
import qualified Data.Set as S
import qualified Text.PrettyPrint.ANSI.Leijen as P
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))
import           Lens.Micro
import           Lens.Micro.TH
import           Lens.Micro.Mtl


solve :: [(TyVarName, Kind)] -> Constraint -> TcSolvM [Goal]
solve ks c = let gs     = makeGoals [] c
                          -- Simplify does a lot of very small steps so it's slightly nicer for tracing to run it in a nested fixpoint
                 stages = (Rewrite.untilFixedPoint $ debugL "Simplify" $ simplify ks) <>
                          debug  "Unify"      unify <>
                          debugL "Equate"     equate <>
                          debug  "Sink/Float" sinkfloat <>
                          debug  "JoinMeet"   joinMeet <>
                          debugL "Defaults"   defaults
  -- [amos] Type-solver changes I made:
  -- - Simplify rule for `t :=: t` to `Solved t` (see Solver/Simplify.hs)
  --    A constraint like "?a :=: ?a" is almost trivial, except that you need the `Solved` constraint to make sure ?a is given a concrete assignment eventually
  -- - Add Sink/float stage (see Solver/SinkFloat.hs)
  --    When the upper bound of a record subtyping constraint has some field as present, we know the lower bound must also have that field present.
  -- - Add Defaults stage (see Solver/Defaults.hs)
  --    Choosing the smallest size for integer literals, when there are multiple upcast constraints on same unification variable
  -- - Reorder Equate stage before JoinMeet:
  --    The new Sink/float stage can apply when Equate does, but Sink/float introduces potentially many new constraints, while Equate is simpler and just replaces a subtyping constraint with equality.
                 rw     = debugF "Initial constraints" <>
                          Rewrite.untilFixedPoint (debug "Normalise types" $ Rewrite.pre normaliseTypes $ stages)
              in fmap (fromMaybe gs) (runMaybeT (Rewrite.runRewrite rw gs))
 where
  debug  nm rw = rw `Rewrite.andThen` Rewrite.debugPass ("After " ++ nm ++ " the constraints are:") printC
  debugL nm rw = debug nm (Rewrite.lift rw)
  debugF nm = Rewrite.debugFail ("=== " ++ nm ++ " ===") printC

  printC gs =
   let gs' = map (P.nest 2 . pretty . _goal) gs
   in show (P.line <> P.indent 2 (P.list gs'))


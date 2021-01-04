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
import qualified Cogent.Context as C
import           Cogent.PrettyPrint (prettyC)
import           Cogent.Surface
import           Cogent.TypeCheck.Base
import           Cogent.TypeCheck.Solver.Default
import           Cogent.TypeCheck.Solver.Equate
#ifdef REFINEMENT_TYPES
import           Cogent.TypeCheck.Solver.JoinMeet
#endif
import           Cogent.TypeCheck.Solver.Monad
import           Cogent.TypeCheck.Solver.Normalise
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
import           Cogent.TypeCheck.Solver.Simplify
import           Cogent.TypeCheck.Solver.SinkFloat
#ifdef REFINEMENT_TYPES
import           Cogent.TypeCheck.Solver.SMT (smt)
#endif
import           Cogent.TypeCheck.Solver.Unify
import           Cogent.TypeCheck.Solver.Util
import           Cogent.TypeCheck.Util
import           Cogent.TypeCheck.Solver.Goal

import           Control.Monad.Trans.Maybe
import qualified Data.Map as M
import           Data.Maybe (fromMaybe)


-- [amos] Type-solver changes I made:
-- - Simplify rule for `t :=: t` to `Solved t` (see Solver/Simplify.hs)
--    A constraint like "?a :=: ?a" is almost trivial, except that you need the `Solved` constraint to make sure ?a is given a concrete assignment eventually
-- - Add Sink/float stage (see Solver/SinkFloat.hs)
--    When the upper bound of a record subtyping constraint has some field as present, we know the lower bound must also have that field present.
-- - Add Defaults stage (see Solver/Defaults.hs)
--    Choosing the smallest size for integer literals, when there are multiple upcast constraints on same unification variable
-- - Reorder Equate stage before JoinMeet:
--    The new Sink/float stage can apply when Equate does, but Sink/float introduces potentially many new constraints, while Equate is simpler and just replaces a subtyping constraint with equality.
-- [vjackson] Type-solver changes I have made:
-- * expand sink/float to all types, and map under all type-operators
-- * remove join/meet


solve :: [(TyVarName, Kind)] -> [(DLVarName, TCType)] -> Constraint -> TcSolvM [Goal]
solve ks ms c = let gs     = makeGoals [] (M.empty, []) c
                            -- Simplify does a lot of very small steps so it's slightly nicer for tracing to run it in a nested fixpoint
                    stages = Rewrite.untilFixedPoint (debug "Simplify" printC $ simplify ks ms)
                             <> debug  "Unify"      printC unify
                             <> debugL "Equate"     printC equate
                             <> debug  "Sink/Float" printC sinkfloat
#ifdef REFINEMENT_TYPES
                             <> debug  "Join/Meet"  printC joinMeet
#endif
                             <> debugL "Defaults"   printC defaults
#ifdef REFINEMENT_TYPES
                             <> debug  "SMT"        printC smt
#endif
  -- [amos] Type-solver changes I made:
  -- - Simplify rule for `t :=: t` to `Solved t` (see Solver/Simplify.hs)
  --    A constraint like "?a :=: ?a" is almost trivial, except that you need the `Solved` constraint to make sure ?a is given a concrete assignment eventually
  -- - Add Sink/float stage (see Solver/SinkFloat.hs)
  --    When the upper bound of a record subtyping constraint has some field as present, we know the lower bound must also have that field present.
  -- - Add Defaults stage (see Solver/Defaults.hs)
  --    Choosing the smallest size for integer literals, when there are multiple upcast constraints on same unification variable
  -- - Reorder Equate stage before JoinMeet:
  --    The new Sink/float stage can apply when Equate does, but Sink/float introduces potentially many new constraints, while Equate is simpler and just replaces a subtyping constraint with equality.
                    rw     = debugF "Initial constraints" printC <>
                             Rewrite.untilFixedPoint (Rewrite.pre normalise stages)
                 in fmap (fromMaybe gs) (runMaybeT (Rewrite.runRewriteT rw gs))


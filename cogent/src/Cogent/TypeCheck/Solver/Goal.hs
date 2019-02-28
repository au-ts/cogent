--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Cogent.TypeCheck.Solver.Goal where

import qualified Data.Map as M
import           Cogent.TypeCheck.Base
import           Cogent.PrettyPrint
import qualified Text.PrettyPrint.ANSI.Leijen as P
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))
import qualified Data.Foldable as F
import           Lens.Micro
import           Lens.Micro.TH

-- A more efficient implementation would be a term net

data Goal = Goal { _goalContext :: [ErrorContext]
                 , _goal :: Constraint
                 }  -- high-level context at the end of _goalContext

instance Show Goal where
  show (Goal c g) = show big
    where big = (small P.<$> (P.vcat $ map (`prettyCtx` True) c))
          small = pretty g

makeLenses ''Goal

makeGoals :: [ErrorContext] -> Constraint -> [Goal]
makeGoals ctx (constraint :@ c) = makeGoals (c:ctx) constraint
makeGoals ctx (c1 :& c2) = makeGoals ctx c1 ++ makeGoals ctx c2
makeGoals ctx g = pure $ Goal ctx g

makeGoal :: [ErrorContext] -> Constraint -> Goal 
makeGoal ctx (constraint :@ c) = makeGoal (c:ctx) constraint
makeGoal ctx g = Goal ctx g 
derivedGoal :: Goal -> Constraint -> Goal
derivedGoal (Goal c g) g' = makeGoal (SolvingConstraint g:c) g'

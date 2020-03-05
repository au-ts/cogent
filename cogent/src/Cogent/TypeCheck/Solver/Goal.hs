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

<<<<<<< HEAD
import qualified Data.IntMap as IM
=======
import qualified Cogent.Context as C
>>>>>>> compiler.reftypes: more constraint gen and solve
import           Cogent.TypeCheck.Base
import           Cogent.PrettyPrint

import qualified Data.Map as M
import qualified Data.Foldable as F
import           Lens.Micro
import           Lens.Micro.TH
import qualified Text.PrettyPrint.ANSI.Leijen as P
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))

-- A more efficient implementation would be a term net


data Goal = Goal { _goalContext :: [ErrorContext]
                 , _goalEnv     :: ConstraintEnv
                 , _goal        :: Constraint
                 }  -- high-level context at the end of _goalContext

instance Show Goal where
  show (Goal c (ctx,es) g) = show big
    where big   = pretty ctx P.<> P.comma P.<+>
                  commaList (map pretty es) P.<+> warn "⊢" P.<+> 
                  small P.<$> (P.vcat $ map (`prettyCtx` True) c)
          small = pretty g

makeLenses ''Goal

makeGoals :: [ErrorContext] -> ConstraintEnv -> Constraint -> [Goal]
makeGoals ctx env (constraint :@ c) = makeGoals (c:ctx) env constraint
makeGoals ctx env (g :|- c) = makeGoals ctx (g `mergeConstraintEnvs` env) c
makeGoals ctx env (c1 :& c2) = makeGoals ctx env c1 ++ makeGoals ctx env c2
makeGoals ctx env g = pure $ Goal ctx env g

makeGoal :: [ErrorContext] -> ConstraintEnv -> Constraint -> Goal
makeGoal ctx env (constraint :@ c) = makeGoal (c:ctx) env constraint
makeGoal ctx env (g :|- c) = makeGoal ctx (g `mergeConstraintEnvs` env) c
makeGoal ctx env g = Goal ctx env g

derivedGoal :: Goal -> Constraint -> Goal
derivedGoal (Goal c env g) g' = makeGoal (SolvingConstraint g:c) env g'

getMentions :: [Goal] -> IM.IntMap (Int,Int)
getMentions gs =
  foldl (IM.unionWith adds) IM.empty $ fmap mentionsOfGoal gs
  where
    adds (a,b) (c,d) = (a + c, b + d)

    mentionsOfGoal g = case g ^. goal of
      r :< s -> IM.fromListWith adds (mentionL r ++ mentionR s)
      _      -> IM.empty

    mentionL = fmap (\v -> (v, (1,0))) . unifVars
    mentionR = fmap (\v -> (v, (0,1))) . unifVars

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

import           Cogent.Compiler (__impossible)
import qualified Cogent.Context as C
import           Cogent.TypeCheck.Base
import           Cogent.PrettyPrint

import           Control.Monad.Trans.Maybe (MaybeT)
import qualified Data.Foldable as F
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as M
import           Lens.Micro
import           Lens.Micro.TH
import qualified Text.PrettyPrint.ANSI.Leijen as P
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))

import Debug.Trace

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
#ifdef REFINEMENT_TYPES
makeGoals ctx env (g :|- c) = makeGoals ctx (g `mergeConstraintEnvs` env) c
#endif
makeGoals ctx env (c1 :& c2) = makeGoals ctx env c1 ++ makeGoals ctx env c2
makeGoals ctx env g = pure $ Goal ctx env g

makeGoal :: [ErrorContext] -> ConstraintEnv -> Constraint -> Goal
makeGoal ctx env (constraint :@ c) = makeGoal (c:ctx) env constraint
#ifdef REFINEMENT_TYPES
makeGoal ctx env (g :|- c) = makeGoal ctx (g `mergeConstraintEnvs` env) c
#endif
makeGoal ctx env g = Goal ctx env g

derivedGoal :: Goal -> Constraint -> Goal
derivedGoal (Goal c env g) g' = makeGoal (SolvingConstraint g:c) env g'

onGoal :: (Monad m) => (Constraint -> MaybeT m [Constraint]) -> Goal -> MaybeT m [Goal]
onGoal f g = fmap (map (derivedGoal g)) (f (g ^. goal))


-- This function should actually be defined in a separate module,
-- as this Goal.hs is more like a library independent of bussiness
-- logic (i.e. the constraints). We put it here for now, because it
-- is shared by a few phases in the solver.
-- It collects global informatioon about unifiers. Within the 4-tuple,
-- it respectively means the number of occurrences in the (1) environment,
-- the LHS of a :<, the RHS, and whether if its a base type.
-- NOTE: This may not be correct, as suspected by Vincent, because it
-- doesn't take contravariants in the function argument position into
-- account. Craig claims that that won't happen, as Simplify should
-- have already broken down function types. Vincent worries that if a
-- function type appears within a record, it might block Simplify.
-- / zilinc (06-08-2020)
getMentions :: [Goal] -> (IM.IntMap (Int,Int,Int), IS.IntSet)
getMentions gs =
  foldl (\(ms,ss) (m,s) -> (IM.unionWith adds ms m, IS.union ss s)) (IM.empty, IS.empty) $ fmap mentionsOfGoal gs
 where
  adds (env1,a,b) (env2,c,d) = (env1 + env2, a + c, b + d)

  mentionsOfGoal :: Goal -> (IM.IntMap (Int,Int,Int), IS.IntSet)
  mentionsOfGoal g = case g ^. goal of
   r :< s      -> (IM.fromListWith adds (mentionEnv (g ^. goalEnv) (r :< s) ++ mentionL r ++ mentionR s), IS.empty)
#ifdef REFINEMENT_TYPES
   Arith e     -> (IM.fromListWith adds (mentionEnv (g ^. goalEnv) (Arith e)), IS.empty)
   BaseType t  -> (IM.fromListWith adds (mentionEnv (g ^. goalEnv) (BaseType t)), basetype t)
   Self x t t' -> (IM.fromListWith adds (mentionEnv (g ^. goalEnv) (Self x t t') ++ mentionL t ++ mentionR t'), IS.empty)
#endif
   _           -> (IM.empty, IS.empty)

  mentionEnv (gamma, es) c = -- fmap (\v -> (v, (1,0,0))) $ unifVarsEnv env
#ifdef REFINEMENT_TYPES
    -- NOTE: we only register a unifvar in the environment when the variable is used in the RHS. / zilinc
    let pvs = progVarsC c
        ms  = fmap (\(t,_) -> unifVars t ++ unknowns t) gamma  -- a map from progvars to the unifvars appearing in that entry.
     in fmap (\v -> (v, (1,0,0))) $ concat $ M.elems $ M.restrictKeys ms pvs
        -- trace ("##### gamma = " ++ show (prettyGoalEnv (gamma,es)) ++ "\n" ++
        --        "      c = " ++ show (prettyC c) ++ "\n" ++
        --        "      pvs = " ++ show pvs ++ "\n" ++
        --        "      ms = " ++ show ms ++ "\n" ++
        --        "      ms' = " ++ show ms' ++ "\n") ms'
  mentionL t = fmap (\v -> (v, (0,1,0))) $ unifVars t ++ unknowns t
  mentionR t = fmap (\v -> (v, (0,0,1))) $ unifVars t ++ unknowns t
#else
    mempty
  mentionL t = fmap (\v -> (v, (0,1,0))) $ unifVars t
  mentionR t = fmap (\v -> (v, (0,0,1))) $ unifVars t
#endif

  basetype (U x) = IS.singleton x
  basetype _  = IS.empty

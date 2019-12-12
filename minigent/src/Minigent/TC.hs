-- |
-- Module      : Minigent.TC
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- The top level type checking/inference module.
--
-- May be used qualified or unqualified.
module Minigent.TC where

import Minigent.Fresh

import Minigent.TC.ConstraintGen
import Minigent.TC.Solver

import Minigent.Syntax
import Minigent.Syntax.Utils
import Minigent.Syntax.Utils.Rewrite(untilFixedPoint)
import Minigent.Environment
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as M
import Debug.Trace

import Minigent.Syntax.PrettyPrint

-- | Run type checking/inference on the given definitions under the given 'GlobalEnvironments'.
--
--   Returns either a list of unsolved constraints (if inference fails) or a new definition
--   with type signatures added to each subexpression and type applications expanded explicitly.
tc :: GlobalEnvironments
   -> [(FunName, (VarName, Expr))]
   -> Fresh VarName [Either (FunName, [Constraint]) (FunName,(VarName,Expr))]
tc envs = mapM check
  where
    check (f, (x, e)) = do
      (axs, e', c) <- runCG (cgFunction f x e) mempty envs

      (cs',ss) <- runSolver (solve axs [c])
      let subst = normaliseType (untilFixedPoint (foldMap substAssign ss))
      if null cs'
        then return $ Right (f, (x, exprTypes subst e'))
        else return $ Left (f, cs')

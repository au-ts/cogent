--
-- Copyright 2019, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

module Cogent.TypeCheck.Solver.Monad where

import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Subst
 
import qualified Control.Monad.State as S (get)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.RWS

type TcSolvM = RWST TcState [Subst] Int IO

solvFresh :: TcSolvM Int
solvFresh = do
  x <- get
  modify (+1)
  return x

solvFreshes :: Int -> TcSolvM [Int]
solvFreshes 0 = pure []
solvFreshes n = (:) <$> solvFresh <*> solvFreshes (n-1)

runSolver :: TcSolvM a -> Int -> TcM (a, Subst)
runSolver act i = do st <- lift (lift S.get)
                     fmap mconcat <$> (lift . lift . lift $ evalRWST act st i)

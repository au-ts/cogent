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

import Data.IntMap
import Lens.Micro
import Lens.Micro.Mtl (use, (%=))

type TcSolvM = RWST TcState [Subst] (Int, IntMap VarOrigin) IO

solvFresh :: VarOrigin -> TcSolvM Int
solvFresh o = do
  x <- use _1
  _1 %= (+1)
  _2 %= insert x o
  return x

runSolver :: TcSolvM a -> (Int, IntMap VarOrigin) -> TcM (a, Subst, IntMap VarOrigin)
runSolver act s = do st <- lift (lift S.get)
                     (a, s', w) <- lift . lift . lift $ runRWST act st s
                     return (a, mconcat w, snd s')

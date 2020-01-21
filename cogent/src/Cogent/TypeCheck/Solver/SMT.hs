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

module Cogent.TypeCheck.Solver.SMT where

import Cogent.TypeCheck.Base
import Cogent.TypeCheck.SMT
import Cogent.TypeCheck.Util (traceTc)
import Cogent.PrettyPrint (indent')
import Cogent.Surface

import Data.SBV (SatResult (..), SMTResult (..), z3)
import Data.SBV.Dynamic (satWith)
import Text.PrettyPrint.ANSI.Leijen as L

smtSat :: TCSExpr -> IO Bool
smtSat e = do
  SatResult s <- satWith z3 (sexprToSmt e)
  traceTc "sol/smt" (text "Running SMT on expression"
                     L.<$> indent' (pretty e)
                     L.<$> text "gives result"
                     L.<$> indent' (text . show $ SatResult s))
  case s of
    Satisfiable {} -> return True
    _              -> return False

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

import Cogent.Common.Syntax
import Cogent.TypeCheck.Base
import Cogent.TypeCheck.SMT
import Cogent.TypeCheck.Solver.Goal
import Cogent.TypeCheck.Solver.Monad (TcSolvM)
import Cogent.TypeCheck.Solver.Rewrite as Rewrite hiding (lift)
import Cogent.TypeCheck.Util (traceTc)
import Cogent.PrettyPrint (indent')
import Cogent.Surface
import Cogent.Util (hoistMaybe)

import Control.Monad.IO.Class
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.RWS (RWST (..))
import Data.SBV (SatResult (..), SMTResult (..), z3)
import Data.SBV.Dynamic (satWith)
import Lens.Micro
import qualified Text.PrettyPrint.ANSI.Leijen as L

data SmtState = SmtState { constraints :: [TCSExpr] }

type SmtM = StateT SmtState IO

trans :: RewriteT SmtM [Goal] -> RewriteT TcSolvM [Goal]
trans (RewriteT m) =
  RewriteT $ \a ->
    case m a of
      MaybeT (StateT m') ->
        MaybeT $ RWST (\r s -> m' (SmtState []) >>= \(a',_) -> return (a',s,[]))

smt :: RewriteT TcSolvM [Goal]
smt = trans $ smtSolve []

smtSolve :: [(VarName, TCExpr)] -> RewriteT SmtM [Goal]
smtSolve axs = 
  collLogic `andThen`
  (rewrite' $ \gs -> do
    -- TODO: currently we don't use the axiom set / zilinc
    SmtState c <- get
    b <- liftIO $ smtSat $ andTCSExprs c
    case b of True  -> hoistMaybe $ Just gs
              False -> hoistMaybe $ Nothing
   )
    
   
collLogic :: RewriteT SmtM [Goal]
collLogic = pickOne' $ \g -> do
  let c = g ^. goal
      (es,c') = splitArithConstraints c
  if null es then
    hoistMaybe $ Nothing
  else do
    modify (\(SmtState c) -> SmtState (c++es))
    hoistMaybe $ Just [g & goal .~ c']

smtSat :: TCSExpr -> IO Bool
smtSat e = do
  SatResult s <- satWith z3 (sexprToSmt e)
  traceTc "sol/smt" (L.text "Running SMT on expression"
                     L.<$> indent' (L.pretty e)
                     L.<$> L.text "gives result"
                     L.<$> indent' (L.text . show $ SatResult s))
  case s of
    Satisfiable {} -> return True
    _              -> return False

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
import Cogent.TypeCheck.Base as Tc
import Cogent.TypeCheck.SMT
import Cogent.TypeCheck.Solver.Goal
import Cogent.TypeCheck.Solver.Monad (TcSolvM)
import Cogent.TypeCheck.Solver.Rewrite as Rewrite hiding (lift)
import Cogent.TypeCheck.Util (traceTc)
import Cogent.PrettyPrint (indent')
import Cogent.Surface
import Cogent.Util (hoistMaybe, (.>))

import Control.Monad.IO.Class
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.RWS (RWST (..))
import qualified Data.IntMap as IM (empty)
import qualified Data.Map as M (Map, empty, map, toList)
import Data.SBV (SatResult (..), ThmResult (..), SMTResult (..), z3)
import Data.SBV.Dynamic (satWith, proveWith, SMTConfig (..))
import Lens.Micro
import Lens.Micro.Mtl (view)
import qualified Text.PrettyPrint.ANSI.Leijen as L

import Debug.Trace

data SmtState = SmtState { constraints :: [TCSExpr]
                         , knownConsts :: M.Map VarName (TCType, TCExpr)
                         }

type SmtM = StateT SmtState IO

trans :: RewriteT SmtM a -> RewriteT TcSolvM a
trans (RewriteT m) =
  RewriteT $ \a ->
    case m a of
      MaybeT (StateT m') ->
        MaybeT $ RWST (\r s -> m' (SmtState [] (r ^. Tc.knownConsts & M.map (\(a,b,c) -> (a,b)))) >>= \(a',_) -> return (a',s,[]))

smt :: RewriteT TcSolvM [Goal]
smt = trans $ smtSolve

smtSolve :: RewriteT SmtM [Goal]
smtSolve = 
  collLogic `andThen`
  (rewrite' $ \gs -> do
    SmtState c ks <- get
    let ks' = constEquations ks
    traceTc "sol/smt" (L.text "Constants" L.<> L.colon L.<$> L.prettyList ks')
    b <- liftIO $ smtSat $ implTCSExpr (andTCSExprs ks') (andTCSExprs c)
    case b of True  -> hoistMaybe $ Just gs
              False -> hoistMaybe $ Nothing
   )
    
constEquations :: M.Map VarName (TCType, TCExpr) -> [TCSExpr]
constEquations = M.toList .>
                 filter simpleExpr .>
                 map (\(v,(t,e)) -> SE (T bool) (PrimOp "==" [SE t (Var v), toTCSExpr e]))
  where simpleExpr (_, (_, e)) = simpleTE e

collLogic :: RewriteT SmtM [Goal]
collLogic = pickOne' $ \g -> do
  let c = g ^. goal
      (es,c') = splitArithConstraints c
  if null es then
    hoistMaybe $ Nothing
  else do
    modify (\(SmtState c ks) -> SmtState (c++es) ks)
    hoistMaybe $ Just [g & goal .~ c']

smtSat :: TCSExpr -> IO Bool
smtSat e = do
  SatResult s <- satWith (z3 { verbose = True }) (evalStateT (sexprToSmt e) (SmtTransState IM.empty M.empty))
  traceTc "sol/smt" (L.text "Running SMT on expression"
                     L.<$> indent' (L.pretty e)
                     L.<$> L.text "gives result"
                     L.<$> indent' (L.text . show $ SatResult s))
  case s of
    Satisfiable {} -> return True
    _              -> return False

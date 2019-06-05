{-# OPTIONS_GHC -Werror -Wall #-}
module Cogent.TypeCheck.Solver.Bubble ( bubble ) where 

-- import Cogent.Surface
-- import Cogent.Util
import Cogent.TypeCheck.Base 
-- import Cogent.Common.Types
import Cogent.TypeCheck.Solver.Goal 
import Cogent.TypeCheck.Solver.Monad
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
-- import qualified Cogent.TypeCheck.Solver.Simplify as Simplify
import qualified Cogent.TypeCheck.Row as Row
-- import qualified Cogent.TypeCheck.Subst as Subst
import Control.Monad.Writer
import Control.Monad.Trans.Maybe

import qualified Data.Map as M

bubble :: Rewrite.Rewrite' TcSolvM [Goal]
bubble = Rewrite.pickOne' go
 where
  go g = case _goal g of
    R r s :< v
     | fs <- discard_common v $ get_taken r
     , not $ M.null fs
     -> make_constraints (flip R s) (:<) fs g v
    v :< R r s
     | fs <- discard_common v $ get_present r
     , not $ M.null fs
     -> make_constraints (flip R s) (flip (:<)) fs g v

    V r :< v
     | fs <- discard_common v $ get_present r
     , not $ M.null fs
     -> make_constraints V (flip (:<)) fs g v
    v :< V r
     | fs <- discard_common v $ get_taken r
     , not $ M.null fs
     -> make_constraints V (:<) fs g v

    _ -> MaybeT $ pure Nothing

  make_constraints frow fsub fs g v = do
    v' <- lift solvFresh
    ts <- mapM (\t -> (,) t <$> lift solvFresh) fs
    let r' = Row.Row (fmap (\((fn,(_,tk)),u) -> (fn, (U u, tk))) ts) (Just v')
    let cv = v :=: frow r'
    let cs = fmap (\(_,((_,(t,_)),u)) -> fsub t (U u)) $ M.toList ts
    pure (g : fmap (derivedGoal g) (cv : cs))

  get_taken    = get_fields True
  get_present  = get_fields False
  get_fields t = M.filter (\(_,(_,t')) -> t == t') . Row.entries

  discard_common (U _) fs   = fs
  discard_common (R r _) fs = M.difference fs $ Row.entries r
  discard_common (V r)   fs = M.difference fs $ Row.entries r
  discard_common _ _        = M.empty


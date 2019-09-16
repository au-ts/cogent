module Cogent.TypeCheck.Errors where 

import Cogent.TypeCheck.Solver.Goal
import Cogent.TypeCheck.Base
import Control.Monad
import Lens.Micro.Mtl
import qualified Data.IntMap as IM

toErrors :: IM.IntMap VarOrigin -> [Goal] -> TcM ()
toErrors os = mapM_ $ \(Goal ctx c) -> case c of
    Sat -> return ()
    Unsat e -> logErr e
    c -> logErr (UnsolvedConstraint c os)
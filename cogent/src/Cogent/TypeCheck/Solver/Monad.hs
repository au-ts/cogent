module Cogent.TypeCheck.Solver.Monad where
import Cogent.TypeCheck.Base 
import Cogent.TypeCheck.Subst

import Control.Monad.State 
import Control.Monad.Writer 
import Control.Monad.Reader 
import Control.Monad.Trans
type TcSolvM = WriterT [Subst] (StateT Int (ReaderT TcState IO))
solvFresh :: TcSolvM Int 
solvFresh = do
  x <- get 
  modify (+1)
  return x

solvFreshes :: Int -> TcSolvM [Int]
solvFreshes 0 = pure []
solvFreshes n = (:) <$> solvFresh <*> solvFreshes (n-1)

runSolver :: TcSolvM a -> Int 
          -> TcM (a, Subst)
runSolver act i = do st <- lift (lift get) 
                     fmap mconcat . fst <$> lift (lift (lift (runReaderT (runStateT (runWriterT act) i) st)))

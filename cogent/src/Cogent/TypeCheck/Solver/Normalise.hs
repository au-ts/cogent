--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--
{-# LANGUAGE CPP #-}
module Cogent.TypeCheck.Solver.Normalise where
import Cogent.Common.Types
import Cogent.Surface
import Cogent.TypeCheck.Base
import Cogent.Compiler
import Cogent.TypeCheck.Solver.Goal
import Cogent.TypeCheck.Solver.Monad
import Cogent.TypeCheck.Solver.Rewrite
import qualified Cogent.TypeCheck.Row as Row

import Control.Applicative
import Data.Maybe
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Lens.Micro.Mtl
import Lens.Micro

normaliseRW :: Rewrite' TcSolvM TCType
normaliseRW = rewrite' $ \t -> case t of
    T (TBang (T (TCon t ts s))) -> pure (T (TCon t ts (bangSigil s)))
    T (TBang (T (TVar v b))) -> pure (T (TVar v True))
    T (TBang (T (TFun x y))) -> pure (T (TFun x y))
    T (TBang (R row (Left s))) 
      | isNothing (Row.var row) -> pure (R (fmap (T . TBang) row) (Left (bangSigil s)))
    T (TBang (V row)) 
      | isNothing (Row.var row) -> pure (V (fmap (T . TBang) row))
    T (TBang (T (TTuple ts))) -> pure (T (TTuple (map (T . TBang) ts)))
    T (TBang (T TUnit)) -> pure (T TUnit)

    T (TUnbox (T (TCon t ts s))) -> pure (T (TCon t ts Unboxed))
    T (TUnbox (R row _)) -> pure (R row (Left Unboxed))

    Synonym n as -> do 
        table <- view knownTypes
        case lookup n table of 
            Just (as', Just b) -> pure (substType (zip as' as) b)
            _ -> __impossible "normaliseRW: missing synonym"

    T (TTake fs (R row s)) 
      | isNothing (Row.var row) -> case fs of 
        Nothing -> pure $ R (Row.takeAll row) s
        Just fs -> pure $ R (Row.takeMany fs row) s 
    T (TTake fs (V row)) 
      | isNothing (Row.var row) -> case fs of 
        Nothing -> pure $ V (Row.takeAll row)
        Just fs -> pure $ V (Row.takeMany fs row)
    T (TPut fs (R row s)) 
      | isNothing (Row.var row) -> case fs of 
        Nothing -> pure $ R (Row.putAll row) s
        Just fs -> pure $ R (Row.putMany fs row) s 
    T (TPut fs (V row)) 
      | isNothing (Row.var row) -> case fs of 
        Nothing -> pure $ V (Row.putAll row)
        Just fs -> pure $ V (Row.putMany fs row)
    _ -> empty 

#ifdef BUILTIN_ARRAYS
    T (TBang (T (TArray t e))) -> pure (T (TArray (T (TBang t)) e))
#endif
  where
    bangSigil (Boxed _ r) = Boxed True r
    bangSigil x           = x

whnf :: TCType -> TcSolvM TCType
whnf input = do 
    step <- case input of 
        T (TTake fs t') -> T . TTake fs <$> whnf t' 
        T (TPut  fs t') -> T . TPut  fs <$> whnf t' 
        T (TBang    t') -> T . TBang    <$> whnf t' 
        T (TUnbox   t') -> T . TUnbox   <$> whnf t' 
        _               -> pure input
    fromMaybe step <$> runMaybeT (run' (untilFixedPoint normaliseRW) step)

-- | Normalise all types within a set of constraints
normaliseTypes :: [Goal] -> TcSolvM [Goal]
normaliseTypes = mapM $ \g -> do
   c' <- traverse whnf (g ^. goal)
   pure $ set goal c' g


-- | Fully unfold and deeply normalise a type (as opposed to previous functions, which normalise to whnf)
fullnormal :: TCType -> TcSolvM TCType
fullnormal t0 = case t0 of
  T t -> do
    t' <- traverse fullnormal t
    whnf $ T t'
  U i   -> pure $ U i
  R r s -> R <$> traverse fullnormal r <*> pure s
  V r   -> V <$> traverse fullnormal r
  Synonym{} -> do
    s' <- whnf t0
    fullnormal s'


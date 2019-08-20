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
import Cogent.Compiler
import Cogent.Dargent.Common (DargentLayout(..))
import Cogent.Surface
import Cogent.TypeCheck.Base
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
    T (TBang (T (TCon t ts s))) -> pure (T (TCon t (fmap (T . TBang) ts) (bangSigil s)))
    T (TBang (T (TVar v b u))) -> pure (T (TVar v True u))
    T (TBang (T (TFun x y))) -> pure (T (TFun x y))
    T (TBang (R r (Left s))) | Row.isComplete r ->
      pure (R (fmap (T . TBang) r) (Left (bangSigil s)))
    T (TBang (V r)) | Row.isComplete r ->
      pure (V (fmap (T . TBang) r))
    T (TBang (T (TTuple ts))) -> pure (T (TTuple (map (T . TBang) ts)))
    T (TBang (T TUnit)) -> pure (T TUnit)

    T (TUnbox (T (TVar v b u))) -> pure (T (TVar v b True))
    T (TUnbox (T (TCon t ts s))) -> pure (T (TCon t ts Unboxed))
    T (TUnbox (R r _)) -> pure (R r (Left Unboxed))

    Synonym n as -> do
        table <- view knownTypes
        case lookup n table of
            Just (as', Just b) ->
              MaybeT $ Just <$> whnf (substType (zip as' as) b)
            _ -> __impossible "normaliseRW: missing synonym"

    T (TTake fs (R r s)) | Row.isComplete r ->
      case fs of
        Nothing -> pure $ R (Row.takeAll r) s
        Just fs -> pure $ R (Row.takeMany fs r) s
    T (TTake fs (V r)) | Row.isComplete r ->
      case fs of 
        Nothing -> pure $ V (Row.takeAll r)
        Just fs -> pure $ V (Row.takeMany fs r)
    T (TTake fs t) | __cogent_flax_take_put -> return t
    T (TPut fs (R r s)) | Row.isComplete r ->
      case fs of 
        Nothing -> pure $ R (Row.putAll r) s
        Just fs -> pure $ R (Row.putMany fs r) s 
    T (TPut fs (V r)) | Row.isComplete r ->
      case fs of 
        Nothing -> pure $ V (Row.putAll r)
        Just fs -> pure $ V (Row.putMany fs r)
    T (TPut fs t) | __cogent_flax_take_put -> return t
    T (TLayout l (R row (Left (Boxed p _)))) ->
      pure $ R row $ Left $ Boxed p (Just (Layout l))
    T (TLayout l (R row (Right i))) ->
      __impossible "normaliseRW: TLayout over a sigil variable"
    T (TLayout l _) -> -- TODO(dargent): maybe handle this later
      empty
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
        T (TLayout l t') -> T . TLayout l <$> whnf t'
        _               -> pure input
    fromMaybe step <$> runMaybeT (run' (untilFixedPoint normaliseRW) step)

-- | Normalise all types within a set of constraints
normaliseTypes :: [Goal] -> TcSolvM [Goal]
normaliseTypes = mapM $ \g -> do
   c' <- traverse whnf (g ^. goal)
   pure $ set goal c' g


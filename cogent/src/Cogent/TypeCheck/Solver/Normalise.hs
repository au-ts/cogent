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

{-# LANGUAGE TupleSections #-}

module Cogent.TypeCheck.Solver.Normalise where

import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Surface
import Cogent.TypeCheck.ARow as AR (ARow(..))
import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Solver.Goal
import Cogent.TypeCheck.Solver.Monad
import Cogent.TypeCheck.Solver.Rewrite
import Cogent.TypeCheck.Solver.Util
import qualified Cogent.TypeCheck.Row as Row

import Control.Applicative
import Data.Maybe
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Lens.Micro.Mtl
import Lens.Micro

normaliseRW :: RewriteT TcSolvM TCType
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
#ifdef BUILTIN_ARRAYS
    T (TBang (A t l (Left s) tkns)) -> pure (A (T . TBang $ t) l (Left (bangSigil s)) tkns)  -- FIXME
#endif

    T (TUnbox (T (TVar v b u))) -> pure (T (TVar v b True))
    T (TUnbox (T (TCon t ts s))) -> pure (T (TCon t ts Unboxed))
    T (TUnbox (R r _)) -> pure (R r (Left Unboxed))
#ifdef BUILTIN_ARRAYS
    T (TUnbox (A t l _ tkns)) -> pure (A t l (Left Unboxed) tkns)  -- FIXME
#endif

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
#ifdef BUILTIN_ARRAYS
    -- Don't normliase ARows. That's done in Cogent.TypeCheck.Solver.Simplify
    T (TATake idxs (A t l s (ARow knowns unevals mall mv))) -> 
      let unevals' = unevals ++ map (,True) idxs   -- NOTE: it may contain conflicting entries in 'unevals', but they
                                                   -- should get resolved when evaluated. / zilinc
       in pure $ A t l s (ARow knowns unevals' mall mv)
    T (TAPut idxs (A t l s (ARow knowns unevals mall mv))) -> 
      let unevals' = unevals ++ map (,False) idxs
       in pure $ A t l s (ARow knowns unevals' mall mv)
#endif

    T (TLayout l (R row (Left (Boxed p _)))) ->
      pure $ R row $ Left $ Boxed p (Just l)
    T (TLayout l (R row (Right i))) ->
      __impossible "normaliseRW: TLayout over a sigil variable (R)"
#ifdef BUILTIN_ARRAYS
    T (TLayout l (A t n (Left (Boxed p _)) tkns)) ->
      pure $ A t n (Left (Boxed p (Just l))) tkns
    T (TLayout l (A t n (Right i) tkns)) ->
      __impossible "normaliseRW: TLayout over a sigil variable (A)"
#endif
    T (TLayout l _) -> -- TODO(dargent): maybe handle this later
      empty
    _ -> empty

  where
    bangSigil (Boxed _ r) = Boxed True r
    bangSigil x           = x

whnf :: TCType -> TcSolvM TCType
whnf input = do
    step <- case input of
        T (TTake  fs t') -> T . TTake fs  <$> whnf t'
        T (TPut   fs t') -> T . TPut  fs  <$> whnf t'
#ifdef BUILTIN_ARRAYS
        T (TATake fs t') -> T . TATake fs <$> whnf t'
        T (TAPut  fs t') -> T . TAPut  fs <$> whnf t'
#endif
        T (TBang     t') -> T . TBang     <$> whnf t'
        T (TUnbox    t') -> T . TUnbox    <$> whnf t'
        T (TLayout l t') -> T . TLayout l <$> whnf t'
        _                -> pure input
    fromMaybe step <$> runMaybeT (runRewrite (untilFixedPoint $ debug "Normalise Type" printPretty normaliseRW) step)

-- | Normalise all types within a set of constraints
normaliseTypes :: [Goal] -> TcSolvM [Goal]
normaliseTypes = mapM $ \g -> do
   c' <- traverse whnf (g ^. goal)
   pure $ set goal c' g


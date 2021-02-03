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

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Cogent.TypeCheck.Solver.Normalise where

import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Surface
import Cogent.Dargent.TypeCheck
import qualified Cogent.TypeCheck.ARow as ARow
import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Solver.Goal
import Cogent.TypeCheck.Solver.Monad
import Cogent.TypeCheck.Solver.Rewrite
import Cogent.TypeCheck.Solver.Util
import qualified Cogent.TypeCheck.Row as Row
import Cogent.Util

import Control.Applicative
import Data.Bitraversable
import qualified Data.IntMap as IM
import Data.Maybe
import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Lens.Micro.Mtl
import Lens.Micro

-- import Debug.Trace

normaliseRWT :: RewriteT TcSolvM TCType
normaliseRWT = rewrite' $ \case
    T (TBang (T (TCon t ts s))) -> pure (T (TCon t (fmap (T . TBang) ts) (bangSigil s)))
    T (TBang (T (TVar v b u))) -> pure (T (TVar v True u))
    T (TBang (T (TFun mv x y))) -> pure (T (TFun mv x y))
    T (TBang (R rp r (Left s))) | Row.isComplete r ->
      pure (R rp (fmap (T . TBang) r) (Left (bangSigil s)))
    T (TBang (V r)) | Row.isComplete r ->
      pure (V (fmap (T . TBang) r))
    T (TBang (T (TTuple ts))) -> pure (T (TTuple (map (T . TBang) ts)))
    T (TBang (T TUnit)) -> pure (T TUnit)
    T (TBang (T (TRPar v _ m))) -> pure (T (TRPar v True m))
#ifdef REFINEMENT_TYPES
    T (TBang (A t l (Left s) tkns)) -> pure (A (T . TBang $ t) l (Left (bangSigil s)) tkns)  -- FIXME
    T (TBang (T (TRefine x t p))) -> pure (T (TRefine x (T $ TBang t) p))  -- FIXME: bang x in p
#endif

    T (TUnbox (T (TVar v b u))) -> pure (T (TVar v b True))
    T (TUnbox (T (TCon t ts s))) -> pure (T (TCon t ts Unboxed))
    T (TUnbox (R rp r _)) -> pure (R rp r (Left Unboxed))
#ifdef REFINEMENT_TYPES
    T (TUnbox (A t l _ tkns)) -> pure (A t l (Left Unboxed) tkns)  -- FIXME
#endif

    Synonym n as -> do
        table <- view knownTypes
        case lookup n table of
            Just (as', Just b) ->
              MaybeT $ Just <$> whnf (substType (zip as' as) b)
            _ -> __impossible "normaliseRWT: missing type synonym"

    T (TTake fs (R rp r s)) | Row.isComplete r ->
      case fs of
        Nothing -> pure $ R rp (Row.takeAll r) s
        Just fs -> pure $ R rp (Row.takeMany fs r) s
    T (TTake fs (V r)) | Row.isComplete r ->
      case fs of
        Nothing -> pure $ V (Row.takeAll r)
        Just fs -> pure $ V (Row.takeMany fs r)
    T (TTake fs t) | __cogent_flax_take_put -> return t
    T (TPut fs (R rp r s)) | Row.isComplete r ->
      case fs of
        Nothing -> pure $ R rp (Row.putAll r) s
        Just fs -> pure $ R rp (Row.putMany fs r) s
    T (TPut fs (V r)) | Row.isComplete r ->
      case fs of
        Nothing -> pure $ V (Row.putAll r)
        Just fs -> pure $ V (Row.putMany fs r)
    T (TPut fs t) | __cogent_flax_take_put -> return t

#ifdef REFINEMENT_TYPES
    T (TATake [idx] (A t l s (Right _))) ->
      __impossible "normaliseRW: TATake over a hole variable"
    T (TATake [idx] (A t l s (Left Nothing))) ->
      let l' = normaliseSExpr l
       in pure $ A t l s (Left $ Just idx)
    T (TAPut [idx] (A t l s (Right _))) ->
      __impossible "normaliseRW: TAPut over a hole variable"
    T (TAPut [idx] (A t l s (Left (Just idx')))) | idx == idx' -> 
      let l' = normaliseSExpr l
       in pure $ A t l s (Left Nothing)
#endif

    T (TLayout l (R rp row (Left (Boxed p _)))) ->
      pure $ R rp row $ Left $ Boxed p (Just l)
    T (TLayout l (R _ row (Right i))) ->
      __impossible "normaliseRW: TLayout over a sigil variable (R)"
#ifdef REFINEMENT_TYPES
    T (TLayout l (A t n (Left (Boxed p _)) tkns)) ->
      pure $ A t n (Left (Boxed p (Just l))) tkns
    T (TLayout l (A t n (Right i) tkns)) ->
      __impossible "normaliseRWT: TLayout over a sigil variable (A)"
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
#ifdef REFINEMENT_TYPES
        T (TATake fs t') -> T . TATake fs <$> whnf t'
        T (TAPut  fs t') -> T . TAPut  fs <$> whnf t'
#endif
        T (TBang     t') -> T . TBang     <$> whnf t'
        T (TUnbox    t') -> T . TUnbox    <$> whnf t'
        T (TLayout l t') -> T . TLayout l <$> whnf t'
        _                -> pure input
    fromMaybe step <$> runMaybeT (runRewriteT (untilFixedPoint $ debug "Normalise Type" printPretty normaliseRWT) step)

normaliseRWL :: RewriteT TcSolvM TCDataLayout
normaliseRWL = rewrite' $ \case
  TLRepRef n s -> do
    ls <- view knownDataLayouts
    case M.lookup n ls of
      Just (vars, expr, _) -> pure $ normaliseTCDataLayout ls (substTCDataLayout (zip vars s) (toTCDL expr))
      _ -> __impossible "normaliseRWL: missing layout synonym"
  _ -> empty

normL :: TCDataLayout -> TcSolvM TCDataLayout
normL l = do
  step <- case l of
#ifdef REFINEMENT_TYPES
    TLArray e p -> TLArray <$> normL e <*> pure p
#endif
    TLRecord fs -> TLRecord <$> mapM (third3M normL) fs
    TLVariant l fs -> TLVariant <$> normL l <*> mapM (fourth4M normL) fs
    TLOffset l n -> TLOffset <$> normL l <*> pure n
    _ -> pure l
  fromMaybe step <$> runMaybeT (runRewriteT (untilFixedPoint $ debug "Normalise Layout" printPretty normaliseRWL) step)

-- | Normalise both types and layouts within a set of constraints
normalise :: [Goal] -> TcSolvM [Goal]
normalise = mapM $ \g -> do
  c' <- bimapM whnf normL (g ^. goal)
  pure $ set goal c' g

normaliseSExpr :: TCSExpr -> Int
normaliseSExpr (SE _ (IntLit n)) = fromIntegral n
normaliseSExpr _ = __todo "normaliseSExpr"

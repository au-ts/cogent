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
{-# OPTIONS_GHC -Wall #-}

module Cogent.TypeCheck.Solver.Default ( defaults ) where

import Cogent.Common.Types
import Cogent.Compiler
import qualified Cogent.Context as C
import Cogent.Surface
import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Solver.Goal hiding (getMentions)
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
import Cogent.Util

import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import qualified Data.IntMap as IM
import Data.List (elemIndex)
import qualified Data.Map as M
import Data.Maybe (catMaybes)
import Lens.Micro ((^.))

-- import Debug.Trace

-- | Default upcast constraints to the max of all mentioned sizes:
--
-- U8 ~> ?a
-- U16 ~> ?a
-- U8 ~> ?a
--
-- ==>
--
-- U16 :=: ?a
--

defaults :: Rewrite.Rewrite [Goal]
defaults = Rewrite.withTransform findUpcasts (pure . catMaybes . map toEquality . IM.toList)

toEquality :: (Int, [TCType]) -> Maybe Goal
toEquality (x, []) = __impossible "defaults: toEquality"
toEquality (x, bot:bots) = do
  bot' <- foldM (primGuess LUB) bot bots
  return $ Goal [] (M.empty, []) (bot' :=: U x)

getMentions :: [Goal] -> IM.IntMap Int
getMentions gs = foldl (IM.unionWith (+)) IM.empty $ fmap (\g -> occ (g ^. goal)) gs
  where
    occ :: Constraint -> IM.IntMap Int 
    occ (a :<  b) = IM.unionsWith (+) $ fmap (flip IM.singleton 1) $ unifVars a ++ unifVars b
    occ (a :=: b) = IM.unionsWith (+) $ fmap (flip IM.singleton 1) $ unifVars a ++ unifVars b
    -- occ (a :-> b) = IM.unionWith (+) (occ a) (occ b)
#ifdef REFINEMENT_TYPES
    occ (g :|- c) = occ c
    occ (Self x t t') = IM.unionsWith (+) $ fmap (flip IM.singleton 1) $ unifVars t' ++ unifVars t
#endif
    occ c         = IM.empty

-- | It returns a pair:
--   * The first component is an IntMap, from unification variables to
--     a list of @bot@ types from goals of the form @bot :~> U top@, where
--     the @top@s are not "mentioned" by other goals.
--   * The second component is the rest goals, that are not @Upcastable@.
findUpcasts :: [Goal] -> Maybe (IM.IntMap [TCType], [Goal])
findUpcasts gs = do
    let (ms, gs') = foldl go (IM.empty, []) gs
    guard (not $ IM.null ms)
    pure (ms, gs')
  where
    mentions = getMentions gs
    -- \ ^^^ FIXME: How do we ensure that all the Upcastable constraints are solved
    -- only if the involved unifier cannot be furthre processed by other constraints? / zilinc

    go (m,gs) g@(Goal _ _ (Upcastable t (U x))) = 
      case x `IM.lookup` mentions of
        Nothing -> (IM.insertWith (++) x [t] m, gs)
        Just n  -> (m, g : gs)  -- @n@ cannot be 0
    go (m,gs) g = (m, g : gs)

primGuess :: Bound -> TCType -> TCType -> Maybe TCType
primGuess d (T (TCon n [] Unboxed)) (T (TCon m [] Unboxed))
  | Just n' <- elemIndex n primTypeCons
  , Just m' <- elemIndex m primTypeCons
  = let f = case d of GLB -> min; LUB -> max
    in Just (T (TCon (primTypeCons !! f n' m') [] Unboxed))
primGuess _ _ _ = Nothing


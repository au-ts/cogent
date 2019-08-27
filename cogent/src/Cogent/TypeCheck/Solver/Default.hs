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

{-# OPTIONS_GHC -Werror -Wall #-}

module Cogent.TypeCheck.Solver.Default ( defaults ) where 

import Cogent.Common.Types
import Cogent.Surface
import Cogent.TypeCheck.Base 
import Cogent.TypeCheck.Solver.Goal 
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
import Cogent.Util

import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import Data.List (elemIndex)


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
defaults ::  Rewrite.Rewrite [Goal]
defaults = Rewrite.rewrite' go
 where
  go gs = do
    (bots,top) <- maybeT $ findUpcasts gs
    case bots of
     [] -> maybeT Nothing
     (b:bots') -> do
      bot <- maybeT $ foldM (primGuess LUB) b bots'
      return (Goal [] (bot :=: U top) : gs)


findUpcasts :: [Goal] -> Maybe ([TCType],Int)
findUpcasts gs = get $ map _goal gs
 where
  get [] = Nothing
  get (Upcastable b (U t) : gs') = collect [b] t gs'
  get (_ : gs') = get gs'

  collect bots top [] = Just (bots, top)
  collect bots top (g:gs')
   | Upcastable b (U t) <- g
   , t == top
   = collect (b : bots) top gs'
   | otherwise
   = collect bots top gs'


maybeT :: Monad m => Maybe a -> MaybeT m a
maybeT = MaybeT . return

primGuess :: Bound -> TCType -> TCType -> Maybe TCType
primGuess d (T (TCon n [] (Unboxed, l1))) (T (TCon m [] (Unboxed, l2)))
  | Just n' <- elemIndex n primTypeCons
  , Just m' <- elemIndex m primTypeCons
  , l1 == l2
  = let f = case d of GLB -> min; LUB -> max
    in Just (T (TCon (primTypeCons !! f n' m') [] (Unboxed, l1)))
primGuess _ _ _ = Nothing


{-# OPTIONS_GHC -Werror -Wall #-}
module Cogent.TypeCheck.Solver.Default ( defaults ) where 

import Cogent.Surface
import Cogent.Util
import Cogent.TypeCheck.Base 
import Cogent.Common.Types
import Cogent.TypeCheck.Solver.Goal 
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
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
primGuess d (T (TCon n [] Unboxed)) (T (TCon m [] Unboxed))
  | Just n' <- elemIndex n primTypeCons
  , Just m' <- elemIndex m primTypeCons
  = let f = case d of GLB -> min; LUB -> max
    in Just (T (TCon (primTypeCons !! f n' m') [] Unboxed))
primGuess _ _ _ = Nothing


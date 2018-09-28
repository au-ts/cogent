
module Corres where

import Control.Monad.Extra
import Data.Set (toList)

import CogentMonad

corres :: (a -> c -> Bool) -> Cogent_monad a -> c -> Bool
corres rrel ma c = any (`rrel` c) $ toList ma

corresM :: (Monad m) => (a -> c -> m Bool) -> Cogent_monad a -> c -> m Bool
corresM rrel ma c = anyM (`rrel` c) $ toList ma

corres' :: (a -> c -> Bool) -> a -> c -> Bool
corres' rrel a c = a `rrel` c

corresM' :: (Monad m) => (a -> c -> m Bool) -> a -> c -> m Bool
corresM' rrel a c = a `rrel` c

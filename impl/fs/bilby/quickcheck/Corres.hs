
module Corres where

import Control.Monad.Extra
import CogentMonad

corres :: (a -> c -> Bool) -> CogentMonad a -> c -> Bool
corres rrel ma c = any (`rrel` c) ma

corresM :: (Monad m) => (a -> c -> m Bool) -> CogentMonad a -> c -> m Bool
corresM rrel ma c = anyM (`rrel` c) ma

corres' :: (a -> c -> Bool) -> a -> c -> Bool
corres' rrel a c = a `rrel` c

corresM' :: (Monad m) => (a -> c -> m Bool) -> a -> c -> m Bool
corresM' rrel a c = a `rrel` c

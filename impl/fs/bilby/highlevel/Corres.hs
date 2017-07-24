
module Corres where

import Data.Set (toList)

import CogentMonad

corres :: (a -> c -> Bool) -> Cogent_monad a -> c -> Bool
corres rrel ma c = any (`rrel` c) $ toList ma

corres' :: (a -> c -> Bool) -> a -> c -> Bool
corres' rrel a c = a `rrel` c

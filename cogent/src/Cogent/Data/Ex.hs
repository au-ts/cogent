
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
module Cogent.Data.Ex where

data Exists :: (k -> *) -> * where
    ExI :: l v -> Exists l
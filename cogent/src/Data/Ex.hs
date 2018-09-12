
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
module Data.Ex where

data Exists :: (k -> *) -> * where
    ExI :: l v -> Exists l
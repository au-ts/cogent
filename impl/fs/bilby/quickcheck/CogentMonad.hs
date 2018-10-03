{-# LANGUAGE InstanceSigs #-}
{- LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes #-}

module CogentMonad (
  CogentMonad
, flatten
, image
, select
, alternative, (<|>) 
) where

import Control.Applicative
import Data.List as L

type CogentMonad a = [a]

flatten :: [[a]] -> [a]
flatten = concat

image :: (a -> b) -> [a] -> [b]
image = fmap

select :: [a] -> CogentMonad a
select = id

alternative :: CogentMonad a -> CogentMonad a -> CogentMonad a
alternative = (<|>)


{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}

module Util where


newtype Flip f (a :: a') (b :: b') = Flip { unflip :: f b a }

ffmap :: (Functor (Flip f c)) => (a -> b) -> f a c -> f b c
ffmap f = unflip . fmap f . Flip

ttraverse :: (Traversable (Flip f b), Applicative m) => (a -> m a') -> f a b -> m (f a' b)
ttraverse f = fmap unflip . traverse f . Flip



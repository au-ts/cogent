--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--


{-# LANGUAGE DataKinds #-}
{- LANGUAGE DeriveFoldable #-}
{- LANGUAGE DeriveFunctor #-}
{- LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Vec where

import Cogent.Compiler (__impossible)
#if __GLASGOW_HASKELL__ < 711
import Cogent.Compiler (__ghc_t3927)
#endif
import Cogent.Util

import Data.Ex
import Data.Fin
import Data.Nat
import Data.PropEq

import Control.Applicative
#if __GLASGOW_HASKELL__ >= 709
import Data.Binary (Binary(..))
import Data.Foldable (find)
#else
import Data.Foldable
#endif
import Data.Monoid
import Data.Traversable
-- import GHC.Generics (Generic)
import Prelude hiding (length, repeat, splitAt, take, unzip, zip, zipWith)
import qualified Text.PrettyPrint.ANSI.Leijen as L

data Vec :: Nat -> * -> * where
  Nil :: Vec 'Zero a
  Cons :: a -> Vec n a -> Vec ('Suc n) a

deriving instance Show a => Show (Vec n a)
deriving instance Eq a => Eq (Vec n a)

instance Functor (Vec n) where
  fmap f Nil = Nil
  fmap f (Cons x y) = Cons (f x) (fmap f y)

instance Applicative (Vec 'Zero) where
  pure _ = Nil
  _ <*> _ = Nil

instance (Applicative (Vec n)) => Applicative (Vec (Suc n)) where
  pure x = Cons x $ pure x
  fs <*> xs = zipWith id fs xs

instance Foldable (Vec n) where
  foldMap f Nil = mempty
  foldMap f (Cons x y) = f x <> foldMap f y

instance Traversable (Vec n) where
  traverse f Nil = pure Nil
  traverse f (Cons x y) = Cons <$> f x <*> traverse f y

-- v1 <++> v2 == v2 ++ v1
(<++>) :: Vec a t -> Vec b t -> Vec (a :+: b) t
v <++> Nil = v
v <++> Cons x xs = Cons x (v <++> xs)

length :: Vec a t -> SNat a
length Nil = SZero
length (Cons x xs) = SSuc (length xs)

fromList :: [a] -> Exists (Flip Vec a)
fromList [] = ExI $ Flip Nil
fromList (x:xs) | ExI (Flip xs') <- fromList xs = ExI $ Flip $ Cons x xs'

takeFromList :: SNat n -> [a] -> Maybe (Vec n a)
takeFromList SZero _ = Just Nil
takeFromList (SSuc n) (x:xs) = Cons x <$> takeFromList n xs
takeFromList (SSuc n) []     = Nothing

cvtFromList :: SNat n -> [a] -> Maybe (Vec n a)
cvtFromList SZero [] = Just Nil
cvtFromList SZero _  = Nothing
cvtFromList (SSuc n) [] = Nothing
cvtFromList (SSuc n) (x:xs) = Cons x <$> cvtFromList n xs

cvtToList :: Vec n a -> [a]
cvtToList Nil = []
cvtToList (Cons a v) = a:cvtToList v

head :: Vec ('Suc a) t -> t
head (Cons x xs) = x

tail :: Vec ('Suc a) t -> Vec a t
tail (Cons x xs) = xs

repeat :: SNat v -> a -> Vec v a
repeat SZero x = Nil
repeat (SSuc v) x = Cons x $ repeat v x

splitAt :: SNat n -> Vec (v :+: n) a -> (Vec n a, Vec v a)
splitAt SZero x = (Nil, x)
splitAt (SSuc n) (Cons x xs) = let (a, b) = splitAt n xs in (Cons x a, b)
#if __GLASGOW_HASKELL__ < 711
splitAt _ _ = __ghc_t3927 "splitAt"
#endif

at :: Vec a t -> Fin a -> t
at Nil _ = __impossible "`at' called with empty Vector"  -- See https://ghc.haskell.org/trac/ghc/ticket/3927#comment:6
at (Cons x xs) FZero    = x
at (Cons x xs) (FSuc s) = at xs s
#if __GLASGOW_HASKELL__ < 711
at _ _ = __ghc_t3927 "at"
#endif

update :: Vec a t -> Fin a -> t -> Vec a t
update Nil _ x = Nil
update (Cons _ xs) FZero    x' = Cons x' xs
update (Cons x xs) (FSuc s) x' = Cons x (update xs s x')
#if __GLASGOW_HASKELL__ < 711
update _ _ _ = __ghc_t3927 "update"
#endif

modifyAt :: Fin a -> (t -> t) -> Vec a t -> Vec a t
modifyAt l f v = update v l (f (v `at` l))

findIx :: (Eq t) => t -> Vec a t -> Maybe (Fin a)
findIx x ls = fmap snd . find (\(y,_) -> x == y) . zip ls $ allFins $ length ls

findBy :: (Eq t) => (t -> Bool) -> Vec a t -> Maybe (Fin a)
findBy pred ls = fmap snd . find (pred . fst) . zip ls $ allFins $ length ls

allFins :: SNat n -> Vec n (Fin n)
allFins SZero = Nil
allFins (SSuc n) = FZero `Cons` (FSuc <$> allFins n)

zipWith :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith f Nil Nil = Nil
zipWith f (Cons x xs) (Cons y ys) = Cons (f x y) (zipWith f xs ys)
#if __GLASGOW_HASKELL__ < 711
zipWith _ _ _ = __ghc_t3927 "zipWith"
#endif

zip :: Vec n a -> Vec n b -> Vec n (a,b)
zip = zipWith (,)

unzip :: Vec n (a,b) -> (Vec n a, Vec n b)
unzip Nil = (Nil, Nil)
unzip (Cons (x,y) (unzip -> (xs, ys))) = (Cons x xs, Cons y ys)


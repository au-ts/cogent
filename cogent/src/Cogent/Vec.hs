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
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Cogent.Vec where

import Cogent.Compiler (__impossible)
#if __GLASGOW_HASKELL__ < 711
import Cogent.Compiler (__ghc_t4139)
#endif
import Cogent.Util

import Control.Applicative
#if __GLASGOW_HASKELL__ >= 709
import Data.Foldable (find)
#else
import Data.Foldable
#endif
import Data.Monoid
import Data.Traversable
import Prelude hiding (length, repeat, splitAt, take, unzip, zip, zipWith)
import qualified Text.PrettyPrint.ANSI.Leijen as L

data Nat = Zero | Suc Nat

data Exists :: (k -> *) -> * where
  ExI :: l v -> Exists l

type family (:+:) (a :: Nat) (b :: Nat) :: Nat where
   x :+: 'Zero = x
   x :+: ('Suc n) = 'Suc (x :+: n)

data (:=:) :: k -> k -> * where
  Refl :: a :=: a

zeroPlusNEqualsN :: SNat n -> ('Zero :+: n) :=: n
zeroPlusNEqualsN SZero = Refl
zeroPlusNEqualsN (SSuc n) | Refl <- zeroPlusNEqualsN n = Refl

addSucLeft :: SNat v -> SNat n -> ('Suc (v :+: n)) :=: ('Suc v :+: n)
addSucLeft v SZero = Refl
addSucLeft v (SSuc n) | Refl <- addSucLeft v n = Refl

addSucLeft' :: SNat v -> SNat n -> ('Suc (v :+: n)) :=: ('Suc n :+: v)
addSucLeft' SZero n | Refl <- zeroPlusNEqualsN n = Refl
addSucLeft' (SSuc v) n | Refl <- addSucLeft v n, Refl <- addSucLeft' v n = Refl

sucZeroIsSuc :: SNat n -> ('Suc 'Zero :+: n) :=: ('Suc n)
sucZeroIsSuc n | Refl <- sym (addSucLeft SZero n), Refl <- zeroPlusNEqualsN n = Refl

sym :: a :=: b -> b :=: a
sym Refl = Refl

assoc :: SNat a -> SNat b -> SNat c -> (a :+: (b :+: c)) :=: ((a :+: b) :+: c)
assoc a b SZero                          = Refl
assoc a b (SSuc n) | Refl <- assoc a b n = Refl

annoying :: SNat v -> SNat n -> SNat n1 -> 'Suc (v :+: n) :+: n1 :=: 'Suc (v :+: (n :+: n1))
annoying v n n1 | Refl <- assoc v n n1
                , Refl <- addSucLeft (sadd v n) n1
                = Refl

annoying' :: SNat v -> SNat n -> SNat n1 -> ('Suc ('Suc (v :+: n)) :+: n1) :=: (v :+: ('Suc ('Suc (n :+: n1))))
annoying' v n n1 | Refl <- assoc v n n1
                 , Refl <- addSucLeft (sadd v n) n1
                 , Refl <- addSucLeft (SSuc (sadd v n)) n1
                 = Refl

withAssocSS :: SNat v -> SNat n -> SNat n1 -> (('Suc ('Suc (v :+: n)) :+: n1) :=: (v :+: ('Suc ('Suc (n :+: n1)))) -> p) -> p
withAssocSS a b c = ($ annoying' a b c)

withAssocS :: SNat v -> SNat n -> SNat n1 -> ('Suc (v :+: n) :+: n1 :=: 'Suc (v :+: (n :+: n1)) -> p) -> p
withAssocS v n n1 = ($ annoying v n n1)

withAssoc :: SNat v -> SNat n -> SNat n1 -> ((v :+: n) :+: n1 :=: (v :+: (n :+: n1)) -> p) -> p
withAssoc v n n1 = ($ sym $ assoc v n n1)


(=?)  :: SNat a -> SNat b -> Maybe (a :=: b)
SZero  =? SZero  = Just Refl
SSuc n =? SSuc m | Just Refl <- n =? m = Just Refl
_ =? _ = Nothing

data SNat :: Nat -> * where
  SZero :: SNat 'Zero
  SSuc :: SNat n -> SNat ('Suc n)

deriving instance Show (SNat n)

s0 = SZero
s1 = SSuc s0
s2 = SSuc s1

instance L.Pretty (SNat n) where
  pretty = L.dullred . L.string . ('S':) . show . toInt

data Fin :: Nat -> * where
  FZero :: Fin ('Suc n)
  FSuc  :: Fin n -> Fin ('Suc n)

deriving instance Eq   (Fin n)
deriving instance Show (Fin n)
deriving instance Ord  (Fin n)

f0 = FZero
f1 = FSuc f0
f2 = FSuc f1

finInt :: Fin n -> Int
finInt FZero = 0
finInt (FSuc f) = finInt f + 1

data Vec :: Nat -> * -> * where
  Nil :: Vec 'Zero a
  Cons :: a -> Vec n a -> Vec ('Suc n) a

deriving instance Show a => Show (Vec n a)
deriving instance Eq a => Eq (Vec n a)

instance Functor (Vec n) where
  fmap f Nil = Nil
  fmap f (Cons x y) = Cons (f x) (fmap f y)

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

sadd :: SNat v -> SNat n -> SNat (v :+: n)
sadd m SZero = m
sadd m (SSuc n) = SSuc (m `sadd` n)

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
splitAt _ _ = __ghc_t4139 "splitAt"
#endif

at :: Vec a t -> Fin a -> t
at (Cons x xs) FZero    = x
at (Cons x xs) (FSuc s) = at xs s
#if __GLASGOW_HASKELL__ < 711
at _ _ = __ghc_t4139 "at"
#endif

atList :: [t] -> Fin a -> t
atList [] _ = __impossible "atList"
atList (x:xs) FZero = x
atList (x:xs) (FSuc s) = atList xs s

update :: Vec a t -> Fin a -> t -> Vec  a t
update (Cons _ xs) FZero    x' = Cons x' xs
update (Cons x xs) (FSuc s) x' = Cons x (update xs s x')
#if __GLASGOW_HASKELL__ < 711
update _ _ _ = __ghc_t4139 "update"
#endif

modifyAt :: Fin a -> (t -> t) -> Vec a t -> Vec a t
modifyAt l f v = update v l (f (v `at` l))

findIx :: (Eq t) => t -> Vec a t -> Maybe (Fin a)
findIx x ls = fmap snd . find (\(y,_) -> x == y) . zip ls $ allFins $ length ls

allFins :: SNat n -> Vec n (Fin n)
allFins SZero = Nil
allFins (SSuc n) = FZero `Cons` (FSuc <$> allFins n)

zipWith :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith f Nil Nil = Nil
zipWith f (Cons x xs) (Cons y ys) = Cons (f x y) (zipWith f xs ys)
#if __GLASGOW_HASKELL__ < 711
zipWith _ _ _ = __ghc_t4139 "zipWith"
#endif

zip :: Vec n a -> Vec n b -> Vec n (a,b)
zip = zipWith (,)

unzip :: Vec n (a,b) -> (Vec n a, Vec n b)
unzip Nil = (Nil, Nil)
unzip (Cons (x,y) (unzip -> (xs, ys))) = (Cons x xs, Cons y ys)

toInt :: SNat v -> Int
toInt SZero = 0
toInt (SSuc n) = 1 + toInt n

widen :: Fin n -> Fin ('Suc n)
widen FZero = FZero
widen (FSuc n) = FSuc (widen n)

widenN :: Fin n -> SNat m -> Fin (n :+: m)
widenN f (SZero) = f
widenN f (SSuc n) = widen (widenN f n)

upshift :: Fin n -> SNat m -> Fin (n :+: m)
upshift n SZero    = n
upshift n (SSuc m) = FSuc (upshift n m)

-- liftIdx idx var means:
--   if idx <= var, var -> var + 1; otherwise intact
liftIdx :: Fin ('Suc n) -> Fin n -> Fin ('Suc n)
liftIdx FZero v = FSuc v
liftIdx (FSuc i) FZero = FZero
liftIdx (FSuc i) (FSuc v) = FSuc $ liftIdx i v

maxFin :: SNat n -> Fin ('Suc n)
maxFin SZero = FZero
maxFin (SSuc n) = FSuc $ maxFin n


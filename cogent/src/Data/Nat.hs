
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NPlusKPatterns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Nat where

import Data.Binary
import Data.PropEq
import GHC.Generics (Generic)

import qualified Text.PrettyPrint.ANSI.Leijen as L

data Nat = Zero | Suc Nat
  deriving (Show, Eq, Ord, Generic)

instance Enum Nat where
  toEnum 0 = Zero
  toEnum (n + 1) = Suc $ toEnum n
  fromEnum = natToInt

instance Binary Nat

n0 = Zero
n1 = Suc n0
n2 = Suc n1

type family (:+:) (a :: Nat) (b :: Nat) :: Nat where
  x :+: 'Zero  = x
  x :+: 'Suc n = 'Suc (x :+: n)

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

--
-- Functions
--

toInt :: SNat v -> Int
toInt SZero = 0
toInt (SSuc n) = 1 + toInt n

sadd :: SNat v -> SNat n -> SNat (v :+: n)
sadd m SZero = m
sadd m (SSuc n) = SSuc (m `sadd` n)

natToInt :: Nat -> Int
natToInt Zero = 0
natToInt (Suc n) = natToInt n + 1


--
-- Properties
--

zeroPlusNEqualsN :: SNat n -> ('Zero :+: n) :=: n
zeroPlusNEqualsN SZero = Refl
zeroPlusNEqualsN (SSuc n) | Refl <- zeroPlusNEqualsN n = Refl

addSucLeft :: SNat v -> SNat n -> 'Suc (v :+: n) :=: ('Suc v :+: n)
addSucLeft v SZero = Refl
addSucLeft v (SSuc n) | Refl <- addSucLeft v n = Refl

addSucLeft' :: SNat v -> SNat n -> 'Suc (v :+: n) :=: ('Suc n :+: v)
addSucLeft' SZero n | Refl <- zeroPlusNEqualsN n = Refl
addSucLeft' (SSuc v) n | Refl <- addSucLeft v n, Refl <- addSucLeft' v n = Refl

sucZeroIsSuc :: SNat n -> ('Suc 'Zero :+: n) :=: 'Suc n
sucZeroIsSuc n | Refl <- sym (addSucLeft SZero n), Refl <- zeroPlusNEqualsN n = Refl

assoc :: SNat a -> SNat b -> SNat c -> (a :+: (b :+: c)) :=: ((a :+: b) :+: c)
assoc a b SZero                          = Refl
assoc a b (SSuc n) | Refl <- assoc a b n = Refl

annoying :: SNat v -> SNat n -> SNat n1 -> 'Suc (v :+: n) :+: n1 :=: 'Suc (v :+: (n :+: n1))
annoying v n n1 | Refl <- assoc v n n1
                , Refl <- addSucLeft (sadd v n) n1
                = Refl

annoying' :: SNat v -> SNat n -> SNat n1 -> ('Suc ('Suc (v :+: n)) :+: n1) :=: (v :+: 'Suc ('Suc (n :+: n1)))
annoying' v n n1 | Refl <- assoc v n n1
                 , Refl <- addSucLeft (sadd v n) n1
                 , Refl <- addSucLeft (SSuc (sadd v n)) n1
                 = Refl

annoying'' :: SNat v -> SNat n -> SNat n1 -> ('Suc ('Suc v) :+: (n :+: n1)) :=: 'Suc ('Suc ((v :+: n) :+: n1))
annoying'' v n n1 | Refl <- sym (addSucLeft (SSuc v) (sadd n n1))
                  , Refl <- sym (addSucLeft v (sadd n n1))
                  , Refl <- assoc v n n1 = Refl

withAssocSS :: SNat v -> SNat n -> SNat n1 -> (('Suc ('Suc (v :+: n)) :+: n1) :=: (v :+: 'Suc ('Suc (n :+: n1))) -> p) -> p
withAssocSS a b c = ($ annoying' a b c)

withAssocS :: SNat v -> SNat n -> SNat n1 -> ('Suc (v :+: n) :+: n1 :=: 'Suc (v :+: (n :+: n1)) -> p) -> p
withAssocS v n n1 = ($ annoying v n n1)

withAssoc :: SNat v -> SNat n -> SNat n1 -> ((v :+: n) :+: n1 :=: (v :+: (n :+: n1)) -> p) -> p
withAssoc v n n1 = ($ sym $ assoc v n n1)

withSSAssoc :: SNat v -> SNat n -> SNat n1 -> (('Suc ('Suc v) :+: (n :+: n1)) :=: 'Suc ('Suc ((v :+: n) :+: n1)) -> p) -> p
withSSAssoc v n n1 = ($ annoying'' v n n1)

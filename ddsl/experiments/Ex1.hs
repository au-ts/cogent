--
-- Copyright 2017, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--
{-# LANGUAGE LambdaCase, MultiWayIf, GADTs, DataKinds, KindSignatures, PolyKinds, TypeFamilies #-}
{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, ExistentialQuantification #-}
{-# LANGUAGE OverlappingInstances, DeriveFunctor #-}

import Prelude hiding (length)
import Control.Applicative ((<$>))
import Control.Monad.Cont hiding (guard)
import Unsafe.Coerce 
-- import Vec as V


data Nat = Zero | Succ Nat

type family (:+:) (a :: Nat) (b :: Nat) :: Nat
type instance x :+: Zero = x
type instance x :+: (Succ n) = Succ (x :+: n)

data SNat :: Nat -> * where
  SZero :: SNat Zero
  SSucc :: SNat n -> SNat (Succ n)

data Bit :: Nat -> * where
  BNil  :: Bit Zero
  BCons :: Bit n -> Bit (Succ n)

zero   = Zero
one    = Succ zero
two    = Succ one
three  = Succ two
four   = Succ three

s0 = SZero
s1 = SSucc s0
s2 = SSucc s1
s3 = SSucc s2
s4 = SSucc s3

type One   = Succ Zero
type Two   = Succ One
type Three = Succ Two
type Four  = Succ Three
type Five  = Succ Four
type Ten   = Five :+: Five
type Twenty = Ten :+: Ten
type Fifty = Twenty :+: Twenty :+: Ten

type Eight = Four :+: Four
type Sixteen = Eight :+: Eight
type ThirtyTwo = Sixteen :+: Sixteen
type SixtyFour = ThirtyTwo :+: ThirtyTwo


type U8  = Bit Eight
type U16 = Bit Sixteen
type U32 = Bit ThirtyTwo
type U64 = Bit SixtyFour

class IntT t where
  toInt :: t -> Integer

instance IntT (Bit n) where
  toInt = undefined

instance IntT Integer where
  toInt = id


u8  = undefined :: U8 
u16 = undefined :: U16
u32 = undefined :: U32
u64 = undefined :: U64

toU16 :: IntT a => a -> U16
toU16 = \_ -> u16

toU32 :: IntT a => a -> U32
toU32 = \_ -> u32

length :: a -> Integer
length = \_ -> undefined


data DDSL t

instance Functor DDSL where
  fmap = undefined

instance Monad DDSL where
  return = undefined
  (>>=)  = undefined

pu8 :: DDSL U8
pu8 = return u8

ple16 :: DDSL U16
ple16 = return u16

pbe32 :: DDSL U32
pbe32 = return u32

bit :: SNat (n :: Nat) -> DDSL (Bit n)
bit SZero = return $ BNil
bit (SSucc n) = BCons <$> bit n

array :: DDSL a -> U32 -> DDSL [a]
array = undefined

guard :: DDSL a -> (a -> Bool) -> DDSL a
guard fa g = fa >>= \a -> if g a then fa else undefined

check :: (a -> Bool) -> DDSL a
check = undefined


infixr |+|
data (t1 |+| t2) where
  InjL :: t1 -> (t1 |+| t2)
  InjR :: t2 -> (t1 |+| t2)

infix :<:
class (sub :<: sup) where
  inj :: sub -> sup

instance f :<: f where
  inj = id

instance f :<: (f |+| g) where
  inj = InjL

instance (f :<: g) => f :<: (h |+| g) where
  inj = InjR . inj

type family Tag (n :: Nat) :: Nat
type instance Tag s = s


tag :: Bit (n :: Nat) -> DDSL (Bit (Tag n))
tag = undefined

cat :: Bit n1 -> Bit n2 -> Bit (n1 :+: n2)
cat = undefined

-- data D { x :: U8 } =
-- { a :: Ple16 
-- , b :: Pbe32 where b > a
-- , c :: Array Pbe32 b
-- } instance t where length t < x

-- ser_D (val : *D!, buf : .Buf, idx : #Idx, x : #U8) : (.Buf, #Idx) + .Buf = 
-- { check (length (val) < x)
--   handle (err) fail (err, buf)
-- ; buf, idx <- ser_Ple16 (val.a, buf, idx)
--               handle (err, buf) fail (err, buf)
-- ; check (val.b > val.a)
--   handle (err) fail (err, buf)
-- ; buf, idx <- ser_Pbe32 (val.b, buf, idx)
--               handle (err, buf) fail (err, buf)
-- ; buf, idx <- ser_Array_Pbe32 (val.c, buf, idx, val.b)
--               handle (err, buf) fail (err, buf)
-- ; return (buf, idx)
-- }

-- des_D (buf : *Buf, idx : #Idx, x : #U8) : (.D, #Idx) + () = 
-- { a, idx <- des_Ple16 (buf, idx)
--             handle (err) fail (err)
-- ; b, idx <- des_Pbe32 (buf, idx)
--             handle (err) fail (err)
-- ; check (b > a)
--   handle (err) fail (err)
-- ; c, idx <- des_Array_Pbe32 (buf, idx, b)
--             handle (err) fail (err)
-- ; val <- malloc_D ()
--          handle (err) { free_Array_Pbe32 (c); fail (err) }
-- ; val <- put val {a = a, b = b, c = c}
-- ; check (length(val) < x)
--   handle (err) { free_D (val); fail (err) }
-- ; return (val, idx)
-- }

data Ser t
data Des t

data D = D { a :: U16, b :: U32, c :: [U32] }

lengthD :: D -> U32
lengthD = undefined

serPle16 :: U16 -> IO ()
serPle16 = undefined

serPbe32 :: U32 -> IO ()
serPbe32 = undefined

serArrayPbe32 :: [U32] -> IO ()
serArrayPbe32 = undefined

instance MonadCont IO where
  callCC = undefined

serD :: U8 -> D -> IO ()
serD x = \val -> (`runCont` id) $ return $ do
  callCC $ \fail -> do when (not $ toInt (lengthD val) < toInt x) (fail ())
                       serPle16 $ a val
                       serPbe32 $ b val
                       when (not $ toInt (b val) > toInt (a val)) (fail ())
                       serArrayPbe32 $ c val
                       return ()

typeS :: Integer -> DDSL (U16, U32, [U32])
typeS x = do a <- ple16
             b <- pbe32 `guard` (\b -> toInt b > toInt a)
             c <- array pbe32 b
             return (a, b, c)
          `guard` (\t -> length t < x)

-- Bad! Not sequenced.
typeS' :: Integer -> DDSL (U32, U16, [U32])
typeS' x = do a <- ple16
              b <- pbe32 `guard` (\b -> toInt b > toInt a)
              c <- array pbe32 b
              return (b, a, c)
           `guard` (\t -> length t < x)

typeBF :: Integer -> DDSL (Bit (Three :+: One :+: Tag Four))
typeBF x = do a <- bit s3 
              b <- bit s1 `guard` (\b -> toInt b < toInt a)
              c <- tag =<< bit s4
              return $ a `cat` b `cat` c

typeBF1 :: DDSL (Bit (Two :+: One :+: Tag Two :+: Three))
typeBF1 = undefined

typeBF2 :: DDSL (Bit (Three :+: Tag Two :+: Two :+: One))
typeBF2 = undefined

typeBF3 :: DDSL (Bit (Three :+: Tag Two :+: Three))
typeBF3 = undefined

bits :: (SNat p, SNat s) -> Bit w -> DDSL (Bit (Tag s))
bits = undefined

typeBU :: DDSL (Bit (Three :+: Tag Two :+: Three))
typeBU = do tag <- bits (s3, s2) =<< pu8
            it <- if | (toInt tag == (15::Integer)) -> typeBF1
                     | (toInt tag == (16::Integer)) -> typeBF2
                     | (toInt tag == (17::Integer)) -> typeBF3
            return it

typeU :: Integer -> DDSL (U16, (U16 |+| U32 |+| U8))
typeU x = do tag <- ple16
             it <- if | (toInt tag == (15::Integer)) -> ple16                                   >>= return . inj
                      | (toInt tag == (16::Integer)) -> pbe32 `guard` (\b -> toInt b < toInt x) >>= return . inj
                      | (toInt tag == (17::Integer)) -> pu8                                     >>= return . inj
             return (tag, it)


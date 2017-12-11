{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE DataKinds #-}
{- LANGUAGE DatatypeContexts #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{- LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{- LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Shallow where


import Control.Applicative
import Control.Monad.Except hiding (forM_, replicateM)
import Control.Monad.State hiding (forM_, replicateM)
import qualified Data.Bits as B
import Data.Data
-- import Data.Foldable (forM_)
import Data.Function
import Data.Kind 
import Data.Proxy
-- import Data.Traversable (forM)
import GHC.TypeLits hiding (Nat, KnownNat, natVal, type (<=), type (+))
import Prelude hiding (read)

-- auxiliary
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

data Nat = Zero | Succ Nat deriving (Eq, Show)

data SNat :: Nat -> Type where
  SZero :: SNat Zero
  SSucc :: SNat n -> SNat (Succ n)

type family (<=) (n :: Nat) (m :: Nat) :: Bool where
  Zero <= m = True
  (Succ n) <= Zero = False
  (Succ n) <= (Succ m) = n <= m

type family (+) (n :: Nat) (m :: Nat) :: Nat where
  Zero + m = m
  (Succ n) + m = Succ (n + m)

class KnownNat (n :: Nat) where
  natVal :: f n -> Int

instance KnownNat N0 where
  natVal _ = 0

instance KnownNat n => KnownNat (Succ n) where
  natVal f = natVal (undefined :: Proxy n) + 1


type N0 = Zero
type N1 = Succ N0
type N2 = Succ N1
type N3 = Succ N2
type N4 = Succ N3
type N5 = Succ N4
type N6 = Succ N5
type N7 = Succ N6
type N8 = Succ N7
type N9 = Succ N8
type N10 = Succ N9
type N11 = Succ N10
type N12 = Succ N11
type N13 = Succ N12
type N14 = Succ N13
type N15 = Succ N14
type N16 = Succ N15

s0 = SZero
s1 = SSucc s0
s2 = SSucc s1
s3 = SSucc s2
s4 = SSucc s3
s5 = SSucc s4
s6 = SSucc s5
s7 = SSucc s6
s8 = SSucc s7

newtype Flip f b a = Flip { unflip :: f a b }

-- meta.
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

data Sigil = Boxed | Unboxed deriving (Eq, Show)

data IntTy (w :: Nat) where
  IntTy :: Int -> IntTy w

deriving instance Eq (IntTy w)
deriving instance Show (IntTy w)

data IntKind  -- kind of integral types

-- data Bit :: Nat -> * where
--   BNil  :: Bit Zero
--   BCons :: Bit n -> Bit (Succ n)


class Datatype t where
  s :: S t
  d :: D t
  v :: V t
  v = d
-- accessors declared by users will be generated on demand

class Bitfieldtype t where
  bitfield_chk :: BITFIELD t => ()
  bitfield_chk = ()

type family BITFIELD (t :: Type) :: Constraint


-- primitives
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- XXX | NOTE: M doesn't sat Moand laws. e.g. return a >>= k === k a

-- data (Sizeable t) => M t = M { runM :: (Buf, Idx) -> Either (Buf, Idx, Err) (Buf, Idx, t) }
-- type M = IO

type M t = ExceptT Err (StateT Idx Buf) t


type S t = t -> M ()
type D t = M t

-- deriving instance Monad S
-- deriving instance Monad D

-- type V t = M t
type V t = D t

type Buf = IO
type Idx = Int
type Err = String

write :: S t
write = undefined

read :: D t
read = undefined

idxi :: Int -> M Int
idxi delta = get >>= \i -> put (i + delta) >> return (i + delta)

type U8  = IntTy N8
type U16 = IntTy N16

instance Datatype U8 where
  s = pu8_s
  d = pu8_d

instance Datatype U16 where
  s = pu16_s
  d = pu16_d


pu8_s :: S U8
pu8_s n = write n >> idxi 1 >> return ()

pu8_d :: D U8
pu8_d = read >>= \n -> idxi 1 >> return n

pu16_s :: S U16
pu16_s n = write n >> idxi 2 >> return ()

pu16_d :: D U16
pu16_d = read >>= \n -> idxi 2 >> return n

padding :: Int -> M ()
padding n = idxi n >> return ()


-- examples
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

const1, const2, const3 :: IntTy N16
const1 = IntTy 1
const2 = IntTy 3
const3 = IntTy 7

const4, const5 :: IntTy N8
const4 = IntTy 2
const5 = IntTy 6

data T1 deriving Datatype
data T2 deriving Datatype
data T3 deriving Datatype

t1_s :: S T1
t2_s :: S T2
t3_s :: S T3
t1_d :: D T1
t2_d :: D T2
t3_d :: D T3
t1_s = undefined
t2_s = undefined
t3_s = undefined
t1_d = undefined
t2_d = undefined
t3_d = undefined

-- instance Datatype T1 where
-- instance Datatype T2 where
-- instance Datatype T3 where


-- records
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

{- {f1 : T1, f2 : T2, f3 : T3} -}
data P (t :: Sigil) where 
  P :: { f1 :: T1, f2 :: T2, f3 :: T3 } -> P Boxed

instance Datatype (P Boxed) where
  s = \obj -> s (obj & (f1 :: P Boxed -> T1)) >>
              s (obj & (f2 :: P Boxed -> T2)) >>
              s (obj & (f3 :: P Boxed -> T3))
  d = d >>= \f1 -> 
      d >>= \f2 -> 
      d >>= \f3 ->
      return (P {f1,f2,f3})

p_s :: S (P Boxed)
p_s obj = t1_s (obj & (f1 :: P Boxed -> T1)) >>
          t2_s (obj & (f2 :: P Boxed -> T2)) >>
          t3_s (obj & (f3 :: P Boxed -> T3))

p_d :: D (P Boxed)
p_d = t1_d >>= \f1 ->
      t2_d >>= \f2 ->
      t3_d >>= \f3 ->
      return (P {f1,f2,f3})


-- FIXME: they are wrong! should take an argument P (or actually index to P), in some monad.
-- the type of p.f1 is P -> T1, but it doesn't embrace the env.

p_f1 :: M T1
p_f1 = t1_d

p_f2 :: M T2
p_f2 = t1_d >> t2_d

-- NOTE: this is wrong! because after unfolding p_d, the offset has been moved too far away
-- it does NOT equal to p_f1
p_f1' :: M T1
p_f1' = p_d >>= \p -> return (p & (f1 :: P Boxed -> T1))


-- Q :: the same in-mem type, but with padding between f2 and f3 in buffer
data Q (t :: Sigil) where
  Q :: { q1 :: T1, q2 :: T2, q3 :: T3 } -> Q Boxed

instance Datatype (Q Boxed) where
  s = \q -> s (q&q1) >>
            s (q&q2) >>
            padding 2  >>
            s (q&q3)
  d = d >>= \q1 ->
      d >>= \q2 ->
      padding 2 >>
      d >>= \q3 ->
      return (Q {q1,q2,q3})

q_s :: S (Q Boxed)
q_s obj = t1_s (obj&q1) >>
          t2_s (obj&q2) >>
          padding 2 >>
          t3_s (obj&q3)

q_d :: D (Q Boxed)
q_d = t1_d >>= \q1 ->
      t2_d >>= \q2 ->
      padding 2 >>
      t3_d >>= \q3 ->
      return (Q {q1,q2,q3})

q_g3 :: D T3
q_g3 = t1_d >> t2_d >> padding 2 >> t3_d

-- Q: can we consider deser functions lazy so that when we ignore the binder, it means
-- not to deser but simply jump over the chunk of buffer
-- Q: all deser functions can be thought as view. when we want to copy, we do something
-- specific to indicate so, because this case should be rare compared to view


{- #{f1 : T1, f2 : T2, f3 : T3} -}
data R (t :: Sigil) where
  R :: { f1 :: T1, f2 :: T2, f3 :: T3 } -> R Unboxed


-- tagged unions
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

{- <F1 T1 | F2 T2 | F3 T3> -}
data T = F1 T1 | F2 T2 | F3 T3

instance Datatype (U16, T) where
  s = \(tag,v) -> s tag >> if | tag == const1 -> case v of F1 v' -> s v'
                              | tag == const2 -> case v of F2 v' -> s v'
                              | tag == const3 -> case v of F3 v' -> s v'
  d = d >>= \tag -> (if | tag == const1 -> F1 <$> d
                        | tag == const2 -> F2 <$> d
                        | tag == const3 -> F3 <$> d) >>= \v ->
      return (tag,v)
 
r_s :: S (U16, T)
r_s = \(tag,v) -> pu16_s tag >> if | tag == const1 -> case v of F1 v' -> t1_s v'
                                   | tag == const2 -> case v of F2 v' -> t2_s v'
                                   | tag == const3 -> case v of F3 v' -> t3_s v'

r_d :: D (U16, T)
r_d = pu16_d >>= \tag -> (if | tag == const1 -> F1 <$> t1_d
                             | tag == const2 -> F2 <$> t2_d
                             | tag == const3 -> F3 <$> t3_d) >>= \v ->
      return (tag,v)

-- unions?

u_s :: U16 -> S T
u_s tag = \v -> if | tag == const1 -> case v of F1 v' -> t1_s v'
                   | otherwise     -> case v of F2 v' -> t2_s v'

-- another way of doing tagged unions
-- ------------------------------------

data G = G1 U8
       | G2 {g1 :: U8, g2 :: T1}
       | G3 (Array U16 N3)

-- then the compiler needs to create an encoding for tags Gi, and 
-- serialise them to the buffer accordingly. this requires a bit more
-- back-end support


-- bitfields
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

data X' (fs :: [(Nat, Nat)]) t where
  X' :: {f1 :: Bits N0 N3 U8, f2 :: Bits N3 N2 U8, f3 :: Bits N5 N3 U8}
     -> X' '[ '(N0,N3),'(N3,N2),'(N5,N3) ] (Bitfield U8)

-- x_good' = x_good

x_s'' :: S (X' '[ '(N0,N3),'(N3,N2),'(N5,N3) ] (Bitfield U8))
x_s'' obj = (bitfield_s' pu8_s (obj&(f1 :: X' _ _ -> Bits N0 N3 U8)) >>
             bitfield_s' pu8_s (obj&(f2 :: X' _ _ -> Bits N3 N2 U8)) >>
             bitfield_s' pu8_s (obj&(f3 :: X' _ _ -> Bits N5 N3 U8))) & bitfield_complete

x_d'' :: D (X' '[ '(N0,N3),'(N3,N2),'(N5,N3) ] (Bitfield U8))
x_d'' = (bitfield_d' pu8_d >>= \f1 ->
         bitfield_d' pu8_d >>= \f2 ->
         bitfield_d' pu8_d >>= \f3 ->
         return (X' {f1, f2, f3})) & bitfield_complete

instance Datatype (X' '[ '(N0,N3),'(N3,N2),'(N5,N3) ] (Bitfield U8)) where
  s obj = (bfms s (obj&(f1 :: X' _ _ -> Bits N0 N3 U8))) >>
          (bfms s (obj&(f2 :: X' _ _ -> Bits N3 N2 U8))) >>
          (bfms s (obj&(f3 :: X' _ _ -> Bits N5 N3 U8))) & bitfield_complete
  d = (bfm d >>= \f1 ->
       bfm d >>= \f2 ->
       bfm d >>= \f3 ->
       return (X' {f1, f2, f3})) & bitfield_complete

bfms :: S (IntTy w) -> S' (Bits p b (IntTy w))
bfms s = unflip $ bfm (Flip s)

-- XXX | -- there's no constructor for this type
-- XXX | xxxx :: X' '("f1",N0,N3) '("f2",N3,N2) '("f3",N5,N3) (Bitfield U8)
-- XXX | xxxx = undefined

-- XXX | xxxx_constr = isNorepType $ dataTypeOf xxxx

data Bits (p :: Nat) (w :: Nat) (c :: Type) where
  Bits :: Int -> Bits p w c
  deriving (Typeable, Data)

data X t where
  X :: {f1 :: Bits N0 N3 U8, f2 :: Bits N3 N2 U8, f3 :: Bits N5 N3 U8} -> X (Bitfield (IntTy (N3 + N2 + N3)))

type instance BITFIELD (X (Bitfield U8)) = (N0 + N3 ~ N3, N3 + N2 ~ N5, N5 + N3 ~ N8)

instance Bitfieldtype (X (Bitfield U8))
-- vvv changed to ^^^
-- this one doesn't need to run -- if the definition is wrong, it won't typecheck
-- x_good :: (N0 + N3 ~ N3, N3 + N2 ~ N5, N5 + N3 ~ N8) => ()
-- x_good = ()

class BFmodifier (a :: Type -> Type) (a' :: Type -> Type) where
  bfm :: a (IntTy w) -> a' (Bits p b (IntTy w))

instance BFmodifier (Flip (->) (M ())) (Flip (->) (M' ())) where
  bfm s = Flip $ \(Bits n) -> WrapMonad . (unflip s) $ IntTy n
instance BFmodifier (ExceptT Err (StateT Idx Buf)) (WrappedMonad (ExceptT Err (StateT Idx Buf))) where
  bfm d = WrapMonad d >>= \(IntTy n) -> return $ Bits n

bitfield_s' :: S (IntTy w) -> S' (Bits p b (IntTy w))
bitfield_s' s (Bits n) = WrapMonad $ s (IntTy n)

bitfield_d' :: D (IntTy w) -> D' (Bits p b (IntTy w))
bitfield_d' d = WrapMonad d >>= \(IntTy n) -> return $ Bits n

x_s' :: S (X (Bitfield U8))
x_s' obj = (bitfield_s' pu8_s (obj&(f1 :: X (Bitfield U8) -> Bits N0 N3 U8)) >>
            bitfield_s' pu8_s (obj&(f2 :: X (Bitfield U8) -> Bits N3 N2 U8)) >>
            bitfield_s' pu8_s (obj&(f3 :: X (Bitfield U8) -> Bits N5 N3 U8))) & bitfield_complete

x_d' :: D (X (Bitfield U8))
x_d' = (bitfield_d' pu8_d >>= \f1 ->
        bitfield_d' pu8_d >>= \f2 ->
        bitfield_d' pu8_d >>= \f3 ->
        return (X {f1, f2, f3})) & bitfield_complete



-- type family RepTy t :: Type
-- type instance RepTy (X (Bitfield U8)) = U8

data B = BX | BO

data BitFM (m :: [B]) (w :: Nat) where
  B8  :: Int -> BitFM '[b0,b1,b2,b3,b4,b5,b6,b7] N8
  B16 :: Int -> BitFM '[b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15] N16

type family SetBit (w :: Nat) (m :: [B]) (b :: Nat) :: [B] where
  SetBit N8 (BO:bs) Zero = BX:bs
  SetBit N8 (lb:bs) (Succ n) = lb:(SetBit N8 bs n)

type family SetRng (w :: Nat) (m :: [B]) (l :: Nat) (u :: Nat) :: [B] where
  SetRng w m n n = SetBit w m n
  SetRng w m l (Succ u) = SetRng w (SetBit w m (Succ u)) l u

data Bitfield w -- = Bitfield { unBitfield :: w }

type M' t = WrappedMonad (ExceptT Err (StateT Idx Buf)) t

type S' t = t -> M' ()
type D' t = M' t

-- untyped ver.
-- ------------------------------------

bitfield_s :: (Succ u <= w ~ True, l <= w ~ True) => S (IntTy w) -> (SNat l, SNat u) -> S' (IntTy w)
bitfield_s s _ = WrapMonad . s

bitfield_d :: (Succ u <= w ~ True, l <= w ~ True) => D (IntTy w) -> (SNat l, SNat u) -> D' (IntTy w)
bitfield_d d _ = WrapMonad d

bitfield_complete_s :: S' (IntTy w) -> S (IntTy w)
bitfield_complete_s = (unwrapMonad .)

bitfield_complete_d :: D' (IntTy w) -> D (IntTy w)
bitfield_complete_d = unwrapMonad

bitfield_complete :: M' t -> M t
bitfield_complete = unwrapMonad

(.&.) :: IntTy t -> IntTy t -> IntTy t
(.&.) (IntTy a) (IntTy b) = IntTy (a B..&. b)

-- can possibly lifted onto type level
x_s :: S U8
x_s obj = (bitfield_s pu8_s (s0,s2) obj >>
           bitfield_s pu8_s (s3,s4) obj >>
           bitfield_s pu8_s (s5,s7) obj) & bitfield_complete

x_d :: D U8
x_d = (bitfield_d pu8_d (s0,s2) >>= \a ->
       bitfield_d pu8_d (s3,s4) >>= \b ->
       bitfield_d pu8_d (s5,s7) >>= \c ->
       return (a .&. b .&. c)) & bitfield_complete

y_s :: S U8
y_s obj = (bitfield_s pu8_s (s0,s1) obj >>
           bitfield_s pu8_s (s2,s2) obj >>
           bitfield_s pu8_s (s3,s4) obj >>
           bitfield_s pu8_s (s5,s7) obj) & bitfield_complete

y_d :: D U8
y_d = (bitfield_d pu8_d (s0,s1) >>= \a  ->
       bitfield_d pu8_d (s2,s2) >>= \a' ->
       bitfield_d pu8_d (s3,s4) >>= \b  ->
       bitfield_d pu8_d (s5,s7) >>= \c  ->
       return (a .&. a' .&. b .&. c)) & bitfield_complete


-- bitfield unions
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- if in x and y, tag is bits 3 and 4


data Y' (fs :: [(Nat, Nat)]) t where
  Y' :: {f1 :: Bits N0 N2 U8, f1' :: Bits N2 N1 U8, f2 :: Bits N3 N2 U8, f3 :: Bits N5 N3 U8}
     -> Y' '[ '(N0,N2),'(N2,N1),'(N3,N2),'(N5,N3) ] (Bitfield U8)


y_good' = y_good

y_s'' :: S (Y' '[ '(N0,N2),'(N2,N1),'(N3,N2),'(N5,N3) ] (Bitfield U8))
y_s'' obj = (bitfield_s' pu8_s (obj&(f1  :: Y' _ _ -> Bits N0 N2 U8)) >>
             bitfield_s' pu8_s (obj&(f1' :: Y' _ _ -> Bits N2 N1 U8)) >>
             bitfield_s' pu8_s (obj&(f2  :: Y' _ _ -> Bits N3 N2 U8)) >>
             bitfield_s' pu8_s (obj&(f3  :: Y' _ _ -> Bits N5 N3 U8))) & bitfield_complete

y_d'' :: D (Y' '[ '(N0,N2),'(N2,N1),'(N3,N2),'(N5,N3) ] (Bitfield U8))
y_d'' = (bitfield_d' pu8_d >>= \f1  ->
         bitfield_d' pu8_d >>= \f1' ->
         bitfield_d' pu8_d >>= \f2  ->
         bitfield_d' pu8_d >>= \f3  ->
         return (Y' {f1, f1', f2, f3})) & bitfield_complete


data BT' (tag :: (Nat, Nat)) t where
  BTX' :: X' '[ '(N0,N3),           '(N3,N2), '(N5,N3) ] (Bitfield U8) -> BT' '(N3,N2) (Bitfield U8)
  BTY' :: Y' '[ '(N0,N2), '(N2,N1), '(N3,N2), '(N5,N3) ] (Bitfield U8) -> BT' '(N3,N2) (Bitfield U8)

-- deriving instance Data (BT' '(N3,N2) (Bitfield U8))

-- it DOES check if the tag is within the fields
data BTBad (tag :: (Nat, Nat)) t where
  BTXBad :: X' '[ '(N0,N2),           '(N2,N3), '(N5,N3) ] (Bitfield U8) 
         -> BTBad (GetField N1 '[ '(N0,N2),           '(N2,N3), '(N5,N3) ]) (Bitfield U8)
  BTYBad :: Y' '[ '(N0,N2), '(N2,N1), '(N3,N2), '(N5,N3) ] (Bitfield U8) 
         -> BTBad (GetField N2 '[ '(N0,N2), '(N2,N1), '(N3,N2), '(N5,N3) ]) (Bitfield U8)

type family GetField (idx :: Nat) (fs :: [(Nat, Nat)]) :: (Nat, Nat) where
  GetField Zero (b ': bs) = b
  GetField (Succ n) (b ': bs) = GetField n bs

-- [Note: how to check tag consistency]
-- This is tricky --- in GHC, if we want to derive Data on GADTs, then all constructors have
-- to return the same phantoms types, otherwise there is no way to write the deriving clause.
-- This is a lack of feature / bug in GHC I believe, but we can make use of it. [HACK]
-- See how we use it for bitfield tagged unions below

-- deriving instance Data (X' '("f1",N0,N2) '("f2",N3,N2) '("f3",N5,N3) (Bitfield U8))  -- wrong!
deriving instance Data (X' '[ '(N0,N3),         '(N3,N2),'(N5,N3) ] (Bitfield U8))  -- triggers GHC bug #12132, fixed in HEAD
deriving instance Data (Y' '[ '(N0,N2),'(N2,N1),'(N3,N2),'(N5,N3) ] (Bitfield U8))

deriving instance Data (BT'   '(N3,N2) (Bitfield U8))
-- it DOES check if the taken fields are identical (see Note: how to check tag consistency)
-- it DOES check if the fields are correct (inhabited)
-- deriving instance Data (BTBad '(N3,N2) (Bitfield U8))  -- rightly reject.

data Y t where
  Y :: {f1 :: Bits N0 N2 U8, f1' :: Bits N2 N1 U8, f2 :: Bits N3 N2 U8, f3 :: Bits N5 N3 U8} -> Y (Bitfield U8)

-- this one doesn't need to run -- if the definition is wrong, it won't typecheck
y_good :: (N0 + N2 ~ N2, N2 + N1 ~ N3, N3 + N2 ~ N5, N5 + N3 ~ N8) => ()
y_good = ()

y_s' :: S (Y (Bitfield U8))
y_s' obj = (bitfield_s' pu8_s (obj&(f1  :: Y (Bitfield U8) -> Bits N0 N2 U8)) >>
            bitfield_s' pu8_s (obj&(f1' :: Y (Bitfield U8) -> Bits N2 N1 U8)) >>
            bitfield_s' pu8_s (obj&(f2  :: Y (Bitfield U8) -> Bits N3 N2 U8)) >>
            bitfield_s' pu8_s (obj&(f3  :: Y (Bitfield U8) -> Bits N5 N3 U8))) & bitfield_complete

y_d' :: D (Y (Bitfield U8))
y_d' = (bitfield_d' pu8_d >>= \f1  ->
        bitfield_d' pu8_d >>= \f1' ->
        bitfield_d' pu8_d >>= \f2  ->
        bitfield_d' pu8_d >>= \f3  ->
        return (Y {f1, f1', f2, f3})) & bitfield_complete

data BT (tp :: Nat) (tw :: Nat) t where
  BTX :: X (Bitfield U8) -> (X (Bitfield U8) -> Bits N3 N2 U8) -> BT N3 N2 (Bitfield U8)
  BTY :: Y (Bitfield U8) -> (Y (Bitfield U8) -> Bits N3 N2 U8) -> BT N3 N2 (Bitfield U8)

-- ------------------------------------

get_bits :: (Succ u <= w ~  True, l <= w ~ True) => IntTy w -> (SNat l, SNat u) -> IntTy w
get_bits (IntTy n) (l,u) = undefined

f_s :: S U8
f_s obj = let tag = get_bits obj (s2,s3)
           in if | tag == const4 -> x_s obj
                 | tag == const5 -> y_s obj
                 | otherwise -> throwError "not matched"

f_d :: D U8
f_d = pu8_d >>= \obj -> 
      let tag = get_bits obj (s2,s5)
       in if | tag == const4 -> x_d
             | tag == const5 -> y_d
             | otherwise -> throwError "not matched"


-- arrays
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

data Array t (n :: Nat) where
  Array0 :: Array t Zero
  ArrayS :: t -> Array t n -> Array t (Succ n)

length :: (KnownNat n) => Array t n -> Int
length = fromIntegral . natVal

class Arrayish f where
  forM_ :: (Monad m) => f t -> (t -> m s) -> m ()

instance Arrayish (Flip Array n) where
  forM_ (unflip -> Array0) f = return ()
  forM_ (unflip -> ArrayS a as) f = f a >> forM_ (Flip as) f

instance Arrayish XArray where
  forM_ (XArray0) f = return ()
  forM_ (XArrayS a as) f = f a >> forM_ as f

replicateM :: (Monad m) => SNat n -> m d -> m (Array d n)
replicateM SZero _ = return Array0
replicateM (SSucc n) f = ArrayS <$> f <*> replicateM n f

repeatM :: (Monad m) => Int -> m d -> m (XArray d)
repeatM 0 _ = return XArray0 
repeatM n f = XArrayS <$> f <*> repeatM (n-1) f

untilM :: (Monad m) => (d -> Bool) -> m d -> m (XArray d)
untilM c f = untilM' c f XArray0
  where untilM' c f as = f >>= \e -> if c e 
            then return as
            else XArrayS e <$> untilM' c f as

data XArray t where
  XArray0 :: XArray t
  XArrayS :: t -> XArray t -> XArray t

-- physical rep: arr
a_s :: S (Array U16 N5)
a_s obj = forM_ (Flip obj) pu16_s

a_d :: D (Array U16 N5)
a_d = replicateM s5 pu16_d

-- physical rep: arr with 0-terminator
b_s :: S (XArray U16)
b_s obj = forM_ obj pu16_s >> pu16_s (IntTy 0)

b_d :: D (XArray U16)
b_d = untilM (== IntTy 0) pu16_d

-- physical rep: len + arr
c_s :: S (U16, XArray U8)
c_s (len, arr) = pu16_s len >> forM_ arr pu8_s

c_d :: D (U16, XArray U8)
c_d = pu16_d >>= \(IntTy len) -> repeatM len pu8_d >>= \arr -> return (IntTy len, arr)




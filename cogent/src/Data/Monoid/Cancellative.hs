{-
    Copyright 2013-2015 Mario Blazevic

    License: BSD3 (see BSD3-LICENSE.txt file)
-}

-- | This module defines the 'Monoid' => 'ReductiveMonoid' => ('CancellativeMonoid', 'GCDMonoid') class hierarchy.
--
-- The 'ReductiveMonoid' class introduces operation '</>' which is the inverse of '<>'. For the 'Sum' monoid, this
-- operation is subtraction; for 'Product' it is division and for 'Set' it's the set difference. A 'ReductiveMonoid' is
-- not a full group because '</>' may return 'Nothing'.
--
-- The 'CancellativeMonoid' subclass does not add any operation but it provides the additional guarantee that '<>' can
-- always be undone with '</>'. Thus 'Sum' is a 'CancellativeMonoid' but 'Product' is not because @(0*n)/0@ is not
-- defined.
--
-- The 'GCDMonoid' subclass adds the 'gcd' operation which takes two monoidal arguments and finds their greatest common
-- divisor, or (more generally) the greatest monoid that can be extracted with the '</>' operation from both.
--
-- All monoid subclasses listed above are for Abelian, /i.e./, commutative or symmetric monoids. Since most practical
-- monoids in Haskell are not Abelian, each of the these classes has two symmetric superclasses:
--
-- * 'LeftReductiveMonoid'
--
-- * 'LeftCancellativeMonoid'
--
-- * 'LeftGCDMonoid'
--
-- * 'RightReductiveMonoid'
--
-- * 'RightCancellativeMonoid'
--
-- * 'RightGCDMonoid'

{-# LANGUAGE Haskell2010, Trustworthy #-}

module Data.Monoid.Cancellative (
   -- * Symmetric, commutative monoid classes
   CommutativeMonoid, ReductiveMonoid(..), CancellativeMonoid, GCDMonoid(..),
   -- * Asymmetric monoid classes
   LeftReductiveMonoid(..), RightReductiveMonoid(..),
   LeftCancellativeMonoid, RightCancellativeMonoid,
   LeftGCDMonoid(..), RightGCDMonoid(..)
   )
where

import qualified Prelude

import Data.Monoid -- (Monoid, Dual(..), Sum(..), Product(..))
import qualified Data.List as List
import Data.Maybe (isJust)
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Unsafe as ByteString
import qualified Data.ByteString.Lazy as LazyByteString
import qualified Data.Text as Text
import qualified Data.Text.Lazy as LazyText
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import qualified Data.Sequence as Sequence
import qualified Data.Set as Set
import Data.Sequence (ViewL((:<)), ViewR((:>)), (<|), (|>))
import qualified Data.Vector as Vector

import Prelude hiding (gcd)

-- | Class of all Abelian ({i.e.}, commutative) monoids that satisfy the commutativity property:
--
-- > a <> b == b <> a
class Monoid m => CommutativeMonoid m

-- | Class of Abelian monoids with a partial inverse for the Monoid '<>' operation. The inverse operation '</>' must
-- satisfy the following laws:
--
-- > maybe a (b <>) (a </> b) == a
-- > maybe a (<> b) (a </> b) == a
class (CommutativeMonoid m, LeftReductiveMonoid m, RightReductiveMonoid m) => ReductiveMonoid m where
   (</>) :: m -> m -> Maybe m

infix 5 </>

-- | Subclass of 'ReductiveMonoid' where '</>' is a complete inverse of the Monoid '<>' operation. The class instances
-- must satisfy the following additional laws:
--
-- > (a <> b) </> a == Just b
-- > (a <> b) </> b == Just a
class (LeftCancellativeMonoid m, RightCancellativeMonoid m, ReductiveMonoid m) => CancellativeMonoid m

-- | Class of Abelian monoids that allow the greatest common denominator to be found for any two given values. The
-- operations must satisfy the following laws:
--
-- > gcd a b == commonPrefix a b == commonSuffix a b
-- > Just a' = a </> p && Just b' = b </> p
-- >    where p = gcd a b
--
-- If a 'GCDMonoid' happens to also be a 'CancellativeMonoid', it should additionally satisfy the following laws:
--
-- > gcd (a <> b) (a <> c) == a <> gcd b c
-- > gcd (a <> c) (b <> c) == gcd a b <> c
class (ReductiveMonoid m, LeftGCDMonoid m, RightGCDMonoid m) => GCDMonoid m where
   gcd :: m -> m -> m

-- | Class of monoids with a left inverse of 'Data.Monoid.mappend', satisfying the following law:
--
-- > isPrefixOf a b == isJust (stripPrefix a b)
-- > maybe b (a <>) (stripPrefix a b) == b
-- > a `isPrefixOf` (a <> b)
--
-- | Every instance definition has to implement at least the 'stripPrefix' method. Its complexity should be no worse
-- than linear in the length of the prefix argument.
class Monoid m => LeftReductiveMonoid m where
   isPrefixOf :: m -> m -> Bool
   stripPrefix :: m -> m -> Maybe m

   isPrefixOf a b = isJust (stripPrefix a b)
   {-# MINIMAL stripPrefix #-}

-- | Class of monoids with a right inverse of 'Data.Monoid.mappend', satisfying the following law:
--
-- > isSuffixOf a b == isJust (stripSuffix a b)
-- > maybe b (<> a) (stripSuffix a b) == b
-- > b `isSuffixOf` (a <> b)
--
-- | Every instance definition has to implement at least the 'stripSuffix' method. Its complexity should be no worse
-- than linear in the length of the suffix argument.
class Monoid m => RightReductiveMonoid m where
   isSuffixOf :: m -> m -> Bool
   stripSuffix :: m -> m -> Maybe m

   isSuffixOf a b = isJust (stripSuffix a b)
   {-# MINIMAL stripSuffix #-}

-- | Subclass of 'LeftReductiveMonoid' where 'stripPrefix' is a complete inverse of '<>', satisfying the following
-- additional law:
--
-- > stripPrefix a (a <> b) == Just b
class LeftReductiveMonoid m => LeftCancellativeMonoid m

-- | Subclass of 'LeftReductiveMonoid' where 'stripPrefix' is a complete inverse of '<>', satisfying the following
-- additional law:
--
-- > stripSuffix b (a <> b) == Just a
class RightReductiveMonoid m => RightCancellativeMonoid m

-- | Class of monoids capable of finding the equivalent of greatest common divisor on the left side of two monoidal
-- values. The methods' complexity should be no worse than linear in the length of the common prefix. The following laws
-- must be respected:
--
-- > stripCommonPrefix a b == (p, a', b')
-- >    where p = commonPrefix a b
-- >          Just a' = stripPrefix p a
-- >          Just b' = stripPrefix p b
-- > p == commonPrefix a b && p <> a' == a && p <> b' == b
-- >    where (p, a', b') = stripCommonPrefix a b
class LeftReductiveMonoid m => LeftGCDMonoid m where
   commonPrefix :: m -> m -> m
   stripCommonPrefix :: m -> m -> (m, m, m)

   commonPrefix x y = p
      where (p, _, _) = stripCommonPrefix x y
   stripCommonPrefix x y = (p, x', y')
      where p = commonPrefix x y
            Just x' = stripPrefix p x
            Just y' = stripPrefix p y
   {-# MINIMAL commonPrefix | stripCommonPrefix #-}

-- | Class of monoids capable of finding the equivalent of greatest common divisor on the right side of two monoidal
-- values. The methods' complexity must be no worse than linear in the length of the common suffix. The following laws
-- must be respected:
--
-- > stripCommonSuffix a b == (a', b', s)
-- >    where s = commonSuffix a b
-- >          Just a' = stripSuffix p a
-- >          Just b' = stripSuffix p b
-- > s == commonSuffix a b && a' <> s == a && b' <> s == b
-- >    where (a', b', s) = stripCommonSuffix a b
class RightReductiveMonoid m => RightGCDMonoid m where
   commonSuffix :: m -> m -> m
   stripCommonSuffix :: m -> m -> (m, m, m)

   commonSuffix x y = s
      where (_, _, s) = stripCommonSuffix x y
   stripCommonSuffix x y = (x', y', s)
      where s = commonSuffix x y
            Just x' = stripSuffix s x
            Just y' = stripSuffix s y
   {-# MINIMAL commonSuffix | stripCommonSuffix #-}

-- Unit instances

instance CommutativeMonoid ()

instance ReductiveMonoid () where
   () </> () = Just ()

instance CancellativeMonoid ()

instance GCDMonoid () where
   gcd () () = ()

instance LeftReductiveMonoid () where
   stripPrefix () () = Just ()

instance RightReductiveMonoid () where
   stripSuffix () () = Just ()

instance LeftCancellativeMonoid ()

instance RightCancellativeMonoid ()

instance LeftGCDMonoid () where
   commonPrefix () () = ()

instance RightGCDMonoid () where
   commonSuffix () () = ()

-- Dual instances

instance CommutativeMonoid a => CommutativeMonoid (Dual a)

instance ReductiveMonoid a => ReductiveMonoid (Dual a) where
   Dual a </> Dual b = fmap Dual (a </> b)

instance CancellativeMonoid a => CancellativeMonoid (Dual a)

instance GCDMonoid a => GCDMonoid (Dual a) where
   gcd (Dual a) (Dual b) = Dual (gcd a b)

instance LeftReductiveMonoid a => RightReductiveMonoid (Dual a) where
   stripSuffix (Dual a) (Dual b) = fmap Dual (stripPrefix a b)
   Dual a `isSuffixOf` Dual b = a `isPrefixOf` b

instance RightReductiveMonoid a => LeftReductiveMonoid (Dual a) where
   stripPrefix (Dual a) (Dual b) = fmap Dual (stripSuffix a b)
   Dual a `isPrefixOf` Dual b = a `isSuffixOf` b

instance LeftCancellativeMonoid a => RightCancellativeMonoid (Dual a)

instance RightCancellativeMonoid a => LeftCancellativeMonoid (Dual a)

instance LeftGCDMonoid a => RightGCDMonoid (Dual a) where
   commonSuffix (Dual a) (Dual b) = Dual (commonPrefix a b)

instance RightGCDMonoid a => LeftGCDMonoid (Dual a) where
   commonPrefix (Dual a) (Dual b) = Dual (commonSuffix a b)

-- Sum instances

instance Num a => CommutativeMonoid (Sum a)

instance Integral a => ReductiveMonoid (Sum a) where
   Sum a </> Sum b = Just $ Sum (a - b)

instance Integral a => CancellativeMonoid (Sum a)

instance (Integral a, Ord a) => GCDMonoid (Sum a) where
   gcd (Sum a) (Sum b) = Sum (min a b)

instance Integral a => LeftReductiveMonoid (Sum a) where
   stripPrefix a b = b </> a

instance Integral a => RightReductiveMonoid (Sum a) where
   stripSuffix a b = b </> a

instance Integral a => LeftCancellativeMonoid (Sum a)

instance Integral a => RightCancellativeMonoid (Sum a)

instance (Integral a, Ord a) => LeftGCDMonoid (Sum a) where
   commonPrefix a b = gcd a b

instance (Integral a, Ord a) => RightGCDMonoid (Sum a) where
   commonSuffix a b = gcd a b

-- Product instances

instance Num a => CommutativeMonoid (Product a)

instance Integral a => ReductiveMonoid (Product a) where
   Product 0 </> Product 0 = Just (Product 0)
   Product _ </> Product 0 = Nothing
   Product a </> Product b = if remainder == 0 then Just (Product quotient) else Nothing
      where (quotient, remainder) = quotRem a b

instance Integral a => GCDMonoid (Product a) where
   gcd (Product a) (Product b) = Product (Prelude.gcd a b)

instance Integral a => LeftReductiveMonoid (Product a) where
   stripPrefix a b = b </> a

instance Integral a => RightReductiveMonoid (Product a) where
   stripSuffix a b = b </> a

instance Integral a => LeftGCDMonoid (Product a) where
   commonPrefix a b = gcd a b

instance Integral a => RightGCDMonoid (Product a) where
   commonSuffix a b = gcd a b

-- Pair instances

instance (CommutativeMonoid a, CommutativeMonoid b) => CommutativeMonoid (a, b)

instance (ReductiveMonoid a, ReductiveMonoid b) => ReductiveMonoid (a, b) where
   (a, b) </> (c, d) = case (a </> c, b </> d)
                       of (Just a', Just b') -> Just (a', b')
                          _ -> Nothing

instance (CancellativeMonoid a, CancellativeMonoid b) => CancellativeMonoid (a, b)

instance (GCDMonoid a, GCDMonoid b) => GCDMonoid (a, b) where
   gcd (a, b) (c, d) = (gcd a c, gcd b d)

instance (LeftReductiveMonoid a, LeftReductiveMonoid b) => LeftReductiveMonoid (a, b) where
   stripPrefix (a, b) (c, d) = case (stripPrefix a c, stripPrefix b d)
                               of (Just a', Just b') -> Just (a', b')
                                  _ -> Nothing
   isPrefixOf (a, b) (c, d) = isPrefixOf a c && isPrefixOf b d

instance (RightReductiveMonoid a, RightReductiveMonoid b) => RightReductiveMonoid (a, b) where
   stripSuffix (a, b) (c, d) = case (stripSuffix a c, stripSuffix b d)
                               of (Just a', Just b') -> Just (a', b')
                                  _ -> Nothing
   isSuffixOf (a, b) (c, d) = isSuffixOf a c && isSuffixOf b d

instance (LeftCancellativeMonoid a, LeftCancellativeMonoid b) => LeftCancellativeMonoid (a, b)

instance (RightCancellativeMonoid a, RightCancellativeMonoid b) => RightCancellativeMonoid (a, b)

instance (LeftGCDMonoid a, LeftGCDMonoid b) => LeftGCDMonoid (a, b) where
   commonPrefix (a, b) (c, d) = (commonPrefix a c, commonPrefix b d)

instance (RightGCDMonoid a, RightGCDMonoid b) => RightGCDMonoid (a, b) where
   commonSuffix (a, b) (c, d) = (commonSuffix a c, commonSuffix b d)

-- Maybe instances

instance LeftReductiveMonoid x => LeftReductiveMonoid (Maybe x) where
   stripPrefix Nothing y = Just y
   stripPrefix Just{} Nothing = Nothing
   stripPrefix (Just x) (Just y) = fmap Just $ stripPrefix x y

instance LeftGCDMonoid x => LeftGCDMonoid (Maybe x) where
   commonPrefix (Just x) (Just y) = Just (commonPrefix x y)
   commonPrefix _ _ = Nothing

   stripCommonPrefix (Just x) (Just y) = (Just p, Just x', Just y')
      where (p, x', y') = stripCommonPrefix x y
   stripCommonPrefix x y = (Nothing, x, y)

instance RightReductiveMonoid x => RightReductiveMonoid (Maybe x) where
   stripSuffix Nothing y = Just y
   stripSuffix Just{} Nothing = Nothing
   stripSuffix (Just x) (Just y) = fmap Just $ stripSuffix x y

instance RightGCDMonoid x => RightGCDMonoid (Maybe x) where
   commonSuffix (Just x) (Just y) = Just (commonSuffix x y)
   commonSuffix _ _ = Nothing

   stripCommonSuffix (Just x) (Just y) = (Just x', Just y', Just s)
      where (x', y', s) = stripCommonSuffix x y
   stripCommonSuffix x y = (x, y, Nothing)

-- Set instances

instance Ord a => CommutativeMonoid (Set.Set a)

instance Ord a => LeftReductiveMonoid (Set.Set a) where
   isPrefixOf = Set.isSubsetOf
   stripPrefix a b = b </> a

instance Ord a => RightReductiveMonoid (Set.Set a) where
   isSuffixOf = Set.isSubsetOf
   stripSuffix a b = b </> a

instance Ord a => ReductiveMonoid (Set.Set a) where
   a </> b | Set.isSubsetOf b a = Just (a Set.\\ b)
           | otherwise = Nothing

instance Ord a => LeftGCDMonoid (Set.Set a) where
   commonPrefix = Set.intersection

instance Ord a => RightGCDMonoid (Set.Set a) where
   commonSuffix = Set.intersection

instance Ord a => GCDMonoid (Set.Set a) where
   gcd = Set.intersection

-- IntSet instances

instance CommutativeMonoid IntSet.IntSet

instance LeftReductiveMonoid IntSet.IntSet where
   isPrefixOf = IntSet.isSubsetOf
   stripPrefix a b = b </> a

instance RightReductiveMonoid IntSet.IntSet where
   isSuffixOf = IntSet.isSubsetOf
   stripSuffix a b = b </> a

instance ReductiveMonoid IntSet.IntSet where
   a </> b | IntSet.isSubsetOf b a = Just (a IntSet.\\ b)
           | otherwise = Nothing

instance LeftGCDMonoid IntSet.IntSet where
   commonPrefix = IntSet.intersection

instance RightGCDMonoid IntSet.IntSet where
   commonSuffix = IntSet.intersection

instance GCDMonoid IntSet.IntSet where
   gcd = IntSet.intersection

-- Map instances

instance Ord k => LeftReductiveMonoid (Map.Map k a) where
   isPrefixOf = Map.isSubmapOfBy (\_ _-> True)
   stripPrefix a b | Map.isSubmapOfBy (\_ _-> True) a b = Just (b Map.\\ a)
                   | otherwise = Nothing

instance (Ord k, Eq a) => LeftGCDMonoid (Map.Map k a) where
   commonPrefix = Map.mergeWithKey (\_ a b -> if a == b then Just a else Nothing) (const Map.empty) (const Map.empty)

-- IntMap instances

instance LeftReductiveMonoid (IntMap.IntMap a) where
   isPrefixOf = IntMap.isSubmapOfBy (\_ _-> True)
   stripPrefix a b | IntMap.isSubmapOfBy (\_ _-> True) a b = Just (b IntMap.\\ a)
                   | otherwise = Nothing

instance Eq a => LeftGCDMonoid (IntMap.IntMap a) where
   commonPrefix = IntMap.mergeWithKey (\_ a b -> if a == b then Just a else Nothing)
                                      (const IntMap.empty) (const IntMap.empty)

-- List instances

instance Eq x => LeftReductiveMonoid [x] where
   stripPrefix = List.stripPrefix
   isPrefixOf = List.isPrefixOf

instance Eq x => LeftCancellativeMonoid [x]

instance Eq x => LeftGCDMonoid [x] where
   commonPrefix (x:xs) (y:ys) | x == y = x : commonPrefix xs ys
   commonPrefix _ _ = []

   stripCommonPrefix x0 y0 = strip' id x0 y0
      where strip' f (x:xs) (y:ys) | x == y = strip' (f . (x :)) xs ys
            strip' f x y = (f [], x, y)

-- Seq instances

instance Eq a => LeftReductiveMonoid (Sequence.Seq a) where
   stripPrefix p s | p == s1 = Just s2
                   | otherwise = Nothing
      where (s1, s2) = Sequence.splitAt (Sequence.length p) s

instance Eq a => RightReductiveMonoid (Sequence.Seq a) where
   stripSuffix p s | p == s2 = Just s1
                   | otherwise = Nothing
      where (s1, s2) = Sequence.splitAt (Sequence.length s - Sequence.length p) s

instance Eq a => LeftCancellativeMonoid (Sequence.Seq a)

instance Eq a => RightCancellativeMonoid (Sequence.Seq a)

instance Eq a => LeftGCDMonoid (Sequence.Seq a) where
   stripCommonPrefix = findCommonPrefix Sequence.empty
      where findCommonPrefix prefix a b = case (Sequence.viewl a, Sequence.viewl b)
                                          of (a1:<a', b1:<b') | a1 == b1 -> findCommonPrefix (prefix |> a1) a' b'
                                             _ -> (prefix, a, b)

instance Eq a => RightGCDMonoid (Sequence.Seq a) where
   stripCommonSuffix = findCommonSuffix Sequence.empty
      where findCommonSuffix suffix a b = case (Sequence.viewr a, Sequence.viewr b)
                                          of (a':>a1, b':>b1) | a1 == b1 -> findCommonSuffix (a1 <| suffix) a' b'
                                             _ -> (a, b, suffix)

-- Vector instances

instance Eq a => LeftReductiveMonoid (Vector.Vector a) where
   stripPrefix p l | prefixLength > Vector.length l = Nothing
                    | otherwise = strip 0
      where strip i | i == prefixLength = Just (Vector.drop prefixLength l)
                    | l Vector.! i == p Vector.! i = strip (succ i)
                    | otherwise = Nothing
            prefixLength = Vector.length p
   isPrefixOf p l | prefixLength > Vector.length l = False
                  | otherwise = test 0
      where test i | i == prefixLength = True
                   | l Vector.! i == p Vector.! i = test (succ i)
                   | otherwise = False
            prefixLength = Vector.length p

instance Eq a => RightReductiveMonoid (Vector.Vector a) where
   stripSuffix s l | suffixLength > Vector.length l = Nothing
                   | otherwise = strip (pred suffixLength)
      where strip i | i == -1 = Just (Vector.take lengthDifference l)
                    | l Vector.! (lengthDifference + i) == s Vector.! i = strip (pred i)
                    | otherwise = Nothing
            suffixLength = Vector.length s
            lengthDifference = Vector.length l - suffixLength
   isSuffixOf s l | suffixLength > Vector.length l = False
                  | otherwise = test (pred suffixLength)
      where test i | i == -1 = True
                   | l Vector.! (lengthDifference + i) == s Vector.! i = test (pred i)
                   | otherwise = False
            suffixLength = Vector.length s
            lengthDifference = Vector.length l - suffixLength

instance Eq a => LeftCancellativeMonoid (Vector.Vector a)

instance Eq a => RightCancellativeMonoid (Vector.Vector a)

instance Eq a => LeftGCDMonoid (Vector.Vector a) where
   stripCommonPrefix x y = (xp, xs, Vector.drop maxPrefixLength y)
      where maxPrefixLength = prefixLength 0 (Vector.length x `min` Vector.length y)
            prefixLength n len | n < len && x Vector.! n == y Vector.! n = prefixLength (succ n) len
            prefixLength n _ = n
            (xp, xs) = Vector.splitAt maxPrefixLength x

instance Eq a => RightGCDMonoid (Vector.Vector a) where
   stripCommonSuffix x y = findSuffix (Vector.length x - 1) (Vector.length y - 1)
      where findSuffix m n | m >= 0 && n >= 0 && x Vector.! m == y Vector.! n =
               findSuffix (pred m) (pred n)
            findSuffix m n = (Vector.take (succ m) x, yp, ys)
               where (yp, ys) = Vector.splitAt (succ n) y

-- ByteString instances

instance LeftReductiveMonoid ByteString.ByteString where
   stripPrefix p l = if ByteString.isPrefixOf p l
                     then Just (ByteString.unsafeDrop (ByteString.length p) l)
                     else Nothing
   isPrefixOf = ByteString.isPrefixOf

instance RightReductiveMonoid ByteString.ByteString where
   stripSuffix s l = if ByteString.isSuffixOf s l
                     then Just (ByteString.unsafeTake (ByteString.length l - ByteString.length s) l)
                     else Nothing
   isSuffixOf = ByteString.isSuffixOf

instance LeftCancellativeMonoid ByteString.ByteString

instance RightCancellativeMonoid ByteString.ByteString

instance LeftGCDMonoid ByteString.ByteString where
   stripCommonPrefix x y = (xp, xs, ByteString.unsafeDrop maxPrefixLength y)
      where maxPrefixLength = prefixLength 0 (ByteString.length x `min` ByteString.length y)
            prefixLength n len | n < len,
                                 ByteString.unsafeIndex x n == ByteString.unsafeIndex y n =
                                    prefixLength (succ n) len
                               | otherwise = n
            (xp, xs) = ByteString.splitAt maxPrefixLength x

instance RightGCDMonoid ByteString.ByteString where
   stripCommonSuffix x y = findSuffix (ByteString.length x - 1) (ByteString.length y - 1)
      where findSuffix m n | m >= 0, n >= 0,
                             ByteString.unsafeIndex x m == ByteString.unsafeIndex y n =
                                findSuffix (pred m) (pred n)
                           | otherwise = let (yp, ys) = ByteString.splitAt (succ n) y
                                         in (ByteString.unsafeTake (succ m) x, yp, ys)

-- Lazy ByteString instances

instance LeftReductiveMonoid LazyByteString.ByteString where
   stripPrefix p l = if LazyByteString.isPrefixOf p l
                     then Just (LazyByteString.drop (LazyByteString.length p) l)
                     else Nothing
   isPrefixOf = LazyByteString.isPrefixOf

instance RightReductiveMonoid LazyByteString.ByteString where
   stripSuffix s l = if LazyByteString.isSuffixOf s l
                     then Just (LazyByteString.take (LazyByteString.length l - LazyByteString.length s) l)
                     else Nothing
   isSuffixOf = LazyByteString.isSuffixOf

instance LeftCancellativeMonoid LazyByteString.ByteString

instance RightCancellativeMonoid LazyByteString.ByteString

instance LeftGCDMonoid LazyByteString.ByteString where
   stripCommonPrefix x y = (xp, xs, LazyByteString.drop maxPrefixLength y)
      where maxPrefixLength = prefixLength 0 (LazyByteString.length x `min` LazyByteString.length y)
            prefixLength n len | n < len && LazyByteString.index x n == LazyByteString.index y n =
               prefixLength (succ n) len
            prefixLength n _ = n
            (xp, xs) = LazyByteString.splitAt maxPrefixLength x

instance RightGCDMonoid LazyByteString.ByteString where
   stripCommonSuffix x y = findSuffix (LazyByteString.length x - 1) (LazyByteString.length y - 1)
      where findSuffix m n | m >= 0 && n >= 0 && LazyByteString.index x m == LazyByteString.index y n =
               findSuffix (pred m) (pred n)
            findSuffix m n = (LazyByteString.take (succ m) x, yp, ys)
               where (yp, ys) = LazyByteString.splitAt (succ n) y

-- Text instances

instance LeftReductiveMonoid Text.Text where
   stripPrefix = Text.stripPrefix
   isPrefixOf = Text.isPrefixOf

instance RightReductiveMonoid Text.Text where
   stripSuffix = Text.stripSuffix
   isSuffixOf = Text.isSuffixOf

instance LeftCancellativeMonoid Text.Text

instance RightCancellativeMonoid Text.Text

instance LeftGCDMonoid Text.Text where
   stripCommonPrefix x y = maybe (Text.empty, x, y) id (Text.commonPrefixes x y)

-- Lazy Text instances

instance LeftReductiveMonoid LazyText.Text where
   stripPrefix = LazyText.stripPrefix
   isPrefixOf = LazyText.isPrefixOf

instance RightReductiveMonoid LazyText.Text where
   stripSuffix = LazyText.stripSuffix
   isSuffixOf = LazyText.isSuffixOf

instance LeftCancellativeMonoid LazyText.Text

instance RightCancellativeMonoid LazyText.Text

instance LeftGCDMonoid LazyText.Text where
   stripCommonPrefix x y = maybe (LazyText.empty, x, y) id (LazyText.commonPrefixes x y)

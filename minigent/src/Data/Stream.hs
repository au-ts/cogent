-- |
-- Module      : Data.Stream
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- This module provides a type for /streams/ (infinite lists), along with a handful of "Data.List"
-- style utility functions.
--
-- It expects to be imported qualified, except for operators and type names.
--
-- > import Data.Stream (Stream, (!))
-- > import qualified Data.Stream as S
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Data.Stream
  ( -- * Type and Constructors
    Stream (..)
  , -- * Eliminators
    head
  , tail
  , -- * Indexing
    take
  , drop
  , (!)
    -- * Making Streams
  , fromList
  , naturals
  ) where

import Prelude hiding (take, drop, head, tail)
import Data.Foldable (toList)

import qualified Data.List as L

-- | A stream is an infinite list of values. It is a list without the nil @[]@ constructor.
--   Thus, all values of type @Stream a@ must either cycle or continuously produce new values
--   using laziness.
--
--   Thus a @Stream a@ could be thought of as a corecursive process that eternaly produces
--   @a@ values.
--
--   Because of the 'Functor', 'Foldable', and 'Traversable' instances, many utility
--   functions can be found in those classes also (in particular the useful 'toList').
--
data Stream a = Cons a (Stream a) deriving (Show, Functor, Foldable, Traversable)

-- | Implemented like a zip-list. That is, @pure x@ is
--   an infinite stream of @x@ repeated over and over, and @fs \<*> xs@ consists of
--   each function in @fs@ applied to the corresponding argument in @xs@.
instance Applicative Stream where

  pure x = Cons x (pure x)

  (Cons f fs) <*> (Cons x xs) = Cons (f x) (fs <*> xs)

-- | Analogous to 'Data.List.take' from Data.List, returns a list containing the first @n@ elements
--   of the given stream.
take :: Int -> Stream a -> [a]
take n = L.take n . toList

-- | Analogous to 'Data.List.take' from Data.List, returns the given stream but without the first
--   @n@ elements.
drop :: Int -> Stream a -> Stream a
drop 0 s = s
drop n (Cons _ xs) = drop (n - 1) xs

-- | Returns the first element of the stream.
head :: Stream a -> a
head (Cons x xs) = x

-- | Returns the stream without the first element.
tail :: Stream a -> Stream a
tail (Cons x xs) = xs

-- | A stream starting at zero and incrementing by one from there.
naturals :: Stream Integer
naturals = Cons 0 (fmap succ naturals)

-- | A stream consisting of all the elements of the given list @xs@ in order.
--
--   If @xs@ is finite, then the stream will cycle forever through those elements,
--   i.e. @fromList (cycle xs) == fromList xs@ (where @==@ is a bisimulation equivalence).
fromList :: [a] -> Stream a
fromList xs = go xs
 where
   go []     = go xs
   go (a:as) = Cons a (fromList as)

-- | An operator to return the @n@th element of a stream.
(!) :: Stream a -> Int -> a
s ! x = head (drop x s)

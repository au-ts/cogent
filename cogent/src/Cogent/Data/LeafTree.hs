--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ExplicitForAll #-}

module Cogent.Data.LeafTree where

import Prelude

import Data.Foldable (fold)
import Data.Traversable (sequenceA)

{-
A `LeafTree` as opposed to Data.Tree

Has all the information at the leaves
-}

data LeafTree a
    = Branch [LeafTree a]
    | Leaf a
    deriving (Eq, Read, Show)

instance Functor LeafTree where
    -- note the use of List <$> here!
    fmap f (Branch xs) = Branch $ (f <$>) <$> xs
    fmap f (Leaf a) = Leaf $ f a

instance Applicative LeafTree where
    pure = Leaf

    (Branch fs) <*> t           = Branch (map (<*> t) fs)
    t@(Leaf f)  <*> (Branch xs) = Branch (map (t <*>) xs)
    (Leaf f)    <*> (Leaf x)    = Leaf (f x)

-- easier than bind in this case
join' :: LeafTree (LeafTree a) -> LeafTree a
join' (Branch tts) = Branch $ join' <$> tts
join' (Leaf t) = t

instance Monad LeafTree where
    return = pure

    (>>=) :: forall a b.  LeafTree a -> (a -> LeafTree b) -> LeafTree b
    (>>=) t k = join' $ k <$> t

instance Foldable LeafTree where
    foldMap :: Monoid b => (a -> b) -> LeafTree a -> b
    foldMap f (Branch xs) = fold (map (foldMap f) xs)
    foldMap f (Leaf x)    = f x

-- TODO verify the identity and composition laws
instance Traversable LeafTree where
    sequenceA :: Applicative f => LeafTree (f a) -> f (LeafTree a)
    sequenceA (Branch tfas) = pure Branch <*> traverse sequenceA tfas
    sequenceA (Leaf fa)     = pure Leaf   <*> fa

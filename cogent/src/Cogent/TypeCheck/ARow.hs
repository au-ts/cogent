--
-- Copyright 2019, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE FlexibleContexts, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TupleSections #-}

module Cogent.TypeCheck.ARow where

import Cogent.Compiler
import Cogent.Surface
import Data.IntMap as IM

data ARow e = ARow { entries  :: IntMap Taken
                   , uneval   :: [(e, Taken)]  -- unevaluated taken/put indices
                   , all      :: Maybe Taken
                   , var      :: Maybe Int
                   }
            deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

unevaluated :: [(e, Taken)] -> ARow e
unevaluated cs = ARow IM.empty cs Nothing Nothing

empty :: Int -> ARow e
empty x = ARow IM.empty [] Nothing (Just x)

fromTaken :: Int -> e -> ARow e
fromTaken x i = fromTakens x [i]

fromTakens :: Int -> [e] -> ARow e
fromTakens x is = ARow IM.empty (Prelude.map ((,True)) is) Nothing (Just x)

fromPut :: Int -> e -> ARow e
fromPut x i = ARow IM.empty [(i, False)] Nothing (Just x)

allTaken :: ARow e
allTaken = ARow IM.empty [] (Just True) Nothing

allPut :: ARow e
allPut = ARow IM.empty [] (Just False) Nothing

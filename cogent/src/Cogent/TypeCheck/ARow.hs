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

import Cogent.Common.Syntax
import Cogent.Compiler
import Cogent.Surface
import Cogent.Util (for)

import Data.Either (partitionEithers)
import Data.IntMap as IM hiding (null)
import Data.Maybe (isNothing)

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

-- We assume that there's no duplicate indices in 'es' and in 'us'. They should be
-- checked at other places. / zilinc
eval :: (e -> Maybe Int) -> ARow e -> ARow e
eval f (ARow es us ma mv) =
  let blob = for us $ \(u,b) -> case f u of Nothing -> Left (u,b); Just u' -> Right (u',b)
      (ls,rs) = partitionEithers blob
   in ARow (es `IM.union` IM.fromListWith (flip const) rs) ls ma mv  -- entries later in 'es' will overwrite earlier ones

unfoldAll :: Int -> ARow e -> ARow e
unfoldAll l r
  | ARow es us Nothing mv <- r = r
  | ARow es us (Just a) mv <- r =
      let a' = IM.fromList $ zip [0..l - 1] (repeat a)
       in ARow (es `IM.union` a') us Nothing mv
               --- \ ^^^ Left-biased

reduced :: ARow e -> Bool
reduced (ARow _ [] Nothing _) = True
reduced _ = False

conflicts :: ARow e -> ARow e -> [Int]
conflicts r1 r2 | reduced r1, reduced r2 = 
  let ARow es1 _ _ _ = r1
      ARow es2 _ _ _ = r2
      cs = IM.intersectionWith (\a b -> a /= b) es1 es2
   in IM.keys $ IM.filter id cs

-- common, left, right
clr :: ARow e -> ARow e -> (IntMap Taken, IntMap Taken, IntMap Taken)
clr r1 r2 | reduced r1, reduced r2, null (conflicts r1 r2) = 
  let ARow es1 _ _ _ = r1
      ARow es2 _ _ _ = r2
      cs = IM.intersection es1 es2
      ls = IM.difference es1 es2
      rs = IM.difference es2 es1
   in (cs,ls,rs)

updateEntries :: (IntMap Taken -> IntMap Taken) -> ARow e -> ARow e
updateEntries f (ARow es us ma mv) = ARow (f es) us ma mv


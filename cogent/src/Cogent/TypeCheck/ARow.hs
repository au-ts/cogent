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
{-# LANGUAGE ViewPatterns #-}

module Cogent.TypeCheck.ARow where

import Cogent.Common.Syntax
import Cogent.Compiler
import Cogent.Surface
import Cogent.Util (for)

import Data.Either (partitionEithers)
import Data.IntMap as IM
import Data.IntSet as IS (isSubsetOf)
import Data.Maybe (isNothing)

import Debug.Trace

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
fromTakens x is = ARow IM.empty (Prelude.map (,True) is) Nothing (Just x)

fromPut :: Int -> e -> ARow e
fromPut x i = fromPuts x [i]

fromPuts :: Int -> [e] -> ARow e
fromPuts x is = ARow IM.empty (Prelude.map (,False) is) Nothing (Just x)

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
      es' = es `IM.union` IM.fromListWith const rs  -- FIXME: what if 'es' and 'rs' conflict? / zilinc
                          -- \ ^^^ entries later in 'es' will overwrite earlier ones
                          -- Note that the list is scanned from the back thus the combining function's
                          -- first argument is the entry earlier in the list.
   in ARow es' ls ma mv

unfoldAll :: Int -> ARow e -> ARow e
unfoldAll l a
  | ARow es us Nothing mv <- a = a
  | ARow es us (Just b) mv <- a =
      let a' = IM.fromList $ zip [0..l - 1] (repeat b)
       in ARow (es `IM.union` a') us Nothing mv
               --- \ ^^^ Left-biased

reduced :: ARow e -> Bool
reduced (ARow _ [] Nothing _) = True
reduced _ = False

compatible :: ARow e -> ARow e -> Bool
compatible a1 a2 | reduced a1, reduced a2 = compatible' a1 a2
  where 
    compatible' (ARow es1 _ _ Nothing ) (ARow es2 _ _ Nothing ) = IM.keys es1 == IM.keys es2
    compatible' (ARow es1 _ _ (Just _)) (ARow es2 _ _ Nothing ) = IM.keysSet es1 `IS.isSubsetOf` IM.keysSet es2
    compatible' (ARow es1 _ _ Nothing ) (ARow es2 _ _ (Just _)) = IM.keysSet es2 `IS.isSubsetOf` IM.keysSet es1
    compatible' (ARow es1 _ _ (Just x)) (ARow es2 _ _ (Just y)) = x /= y || IM.keys es1 == IM.keys es2

withoutCommon :: ARow e -> ARow e -> (ARow e, ARow e)
withoutCommon a1@(entries -> es1) a2@(entries -> es2) | reduced a1, reduced a2 = 
  let es1' = es1 `IM.withoutKeys` (IM.keysSet es2)
      es2' = es2 `IM.withoutKeys` (IM.keysSet es1)
   in (updateEntries (const es1') a1, updateEntries (const es2') a2)

common :: ARow e -> ARow e -> IntMap (Taken, Taken)
common a1@(entries -> es1) a2@(entries -> es2) | reduced a1, reduced a2 =
  IM.intersectionWith (,) es1 es2

updateEntries :: (IntMap Taken -> IntMap Taken) -> ARow e -> ARow e
updateEntries f (ARow es us ma mv) = ARow (f es) us ma mv

union :: ARow e -> ARow e -> ARow e
union a1 a2 | IM.null (common a1 a2)
            , reduced a1
            , reduced a2
            = ARow (entries a1 `IM.union` entries a2) [] Nothing (var a2)

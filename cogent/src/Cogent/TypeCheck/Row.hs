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
{-# LANGUAGE FlexibleContexts, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Cogent.TypeCheck.Row
  ( Row (..) 
  , -- * Constructors
    fromList
  , fromMap
  , incomplete
  , -- * Queries
    takenIn
  , toEntryList
  , compatible
  , null
  , justVar
  , untakenTypes
  , untakenLabels
  , untakenLabelsSet
  , typesFor
  , allTypes
  , -- * Manipulating
    mapEntries
  , take
  , put
  , takeMany 
  , putMany
  , takeAll 
  , putAll
  , -- * Row Union and Combination
    -- ** Row Union
 --   union
 -- , UnionMethod
 -- , leastTaken
 -- , mostTaken
   -- ** Common entries
    common
  , withoutCommon
  ) where


import qualified Data.Map as M
import qualified Data.Set as S
import Prelude hiding (take, null)
import Data.Maybe (mapMaybe)
import Cogent.Surface
import Cogent.Common.Syntax
import Control.Monad (guard)
import qualified Data.Foldable as F
data Row t = Row { entries :: M.Map FieldName (Entry t)
                 , var :: Maybe Int
                 }  deriving (Show, Eq, Ord, Functor, Foldable,Traversable)
-- | Given a list of entries, produce a complete row without a unification row variable.
fromList :: [Entry t] -> Row t
fromList es = Row (M.fromList (map (\e@(f, _ )-> (f,e)) es)) Nothing

-- | Every entry in the row in list form.
toEntryList :: Row t -> [Entry t]
toEntryList r = F.toList (entries r)
-- | Given a map of entries, produce a complete row without a unification row variable.
fromMap :: M.Map FieldName (t, Bool) -> Row t
fromMap es = Row (M.mapWithKey (,) es) Nothing
-- | Given a list of entries, produce an incomplete row with a fresh unification row variable.
incomplete :: [Entry t] -> Int -> Row t
incomplete es u = (fromList es) { var = Just u }


-- | Returns those pairs of entries in the input rows that have the same field/constructor
--   name.
common :: Row t -> Row t -> [(Entry t, Entry t)]
common r1 r2 = M.elems (M.intersectionWith (,) (entries r1) (entries r2))

-- | Returns whats left of the two input rows when all common entries are removed.
withoutCommon :: Row t -> Row t -> (Row t, Row t)
withoutCommon (Row e1 v1) (Row e2 v2) = ( Row (e1 `M.withoutKeys` M.keysSet e2) v1
                                        , Row (e2 `M.withoutKeys` M.keysSet e1) v2
                                        )

allTypes :: Row t -> [t]
allTypes (Row m _) = map (\(_, (t, _) ) -> t) (M.elems m)

-- | Given a set of field names, return all the types for those field names in the row.
typesFor :: S.Set FieldName -> Row t -> [t]
typesFor fs (Row m _) = map (\(_, (t, _) ) -> t) (M.elems (M.restrictKeys m fs))


-- | Returns true iff the row has no entries and no unification variable.
null :: Row t -> Bool
null (Row m Nothing) = M.null m
null _ = False

-- | A row with no concrete entries and a unification variable, which is effectively an unconstrained unification variable
justVar :: Row t -> Bool
justVar (Row es (Just _)) = M.null es
justVar _ = False

-- | Returns true iff the two rows could be considered equal after unification.
compatible :: Row t -> Row t -> Bool
compatible (Row m1 Nothing) (Row m2 Nothing) = M.keysSet m1 == M.keysSet m2
compatible (Row m1 Nothing) (Row m2 (Just _)) = M.keysSet m2 `S.isSubsetOf` M.keysSet m1
compatible (Row m1 (Just _)) (Row m2 Nothing) = M.keysSet m1 `S.isSubsetOf` M.keysSet m2
compatible (Row m1 (Just x)) (Row m2 (Just y)) = x /= y || M.keysSet m1 == M.keysSet m2

-- | Returns all types not marked as 'Taken' in the row.
untakenTypes :: Row t -> [t]
untakenTypes = mapMaybe (\(_,(t, x)) -> guard (not x) >> Just t) . M.elems . entries

-- | All labels not marked as 'Taken' in the row.
untakenLabels :: Row t -> [FieldName]
untakenLabels = mapMaybe (\(t,(_, x)) -> guard (not x) >> Just t) . M.elems . entries

-- | All labels not marked as 'Taken' in the row.
untakenLabelsSet :: Row t -> S.Set FieldName
untakenLabelsSet = S.fromList . mapMaybe (\(t,(_, x)) -> guard (not x) >> Just t) . M.elems . entries
-- | Manipulate each entry inside a row. It is assumed that the given function
--   does not change the field or constructor name in the entry. Don't do that.
mapEntries :: (Entry t -> Entry t) -> Row t -> Row t
mapEntries func (Row m e) = Row (fmap func m) e

-- | Given a field name, mark is as taken in the row (if it exists).
take :: FieldName -> Row t -> Row t
take f (Row m e) = Row (M.adjust (\(f, (t, _)) -> (f, (t, True))) f m) e

takeMany :: [FieldName] -> Row t -> Row t 
takeMany fs r = foldr take r fs

takeAll :: Row t -> Row t 
takeAll (Row m e) = Row (fmap (fmap (fmap (const True))) m) e

-- | Given a field name, unmark is as taken in the row (if it exists).
put :: FieldName -> Row t -> Row t
put f (Row m e) = Row (M.adjust (\(f, (t, _)) -> (f, (t, False))) f m) e

putMany :: [FieldName] -> Row t -> Row t 
putMany fs r = foldr put r fs

putAll :: Row t -> Row t 
putAll (Row m e) = Row (fmap (fmap (fmap (const False))) m) e
-- | Returns true iff the field is taken in the given row.
takenIn :: FieldName -> Row t -> Bool
takenIn f (Row m _) = case M.lookup f m of
   Nothing -> False
   Just (_, (_, b)) -> b

{-
-- | A @UnionMethod@ is a function that, given a particular field/constructor name,
--   and the two rows in which it may occur, decides whether or not this field should
--   be marked as taken or not.
type UnionMethod = (FieldName -> Row -> Row -> Taken)

-- | Given a @UnionMethod@ to determine if a field should be marked as taken or not,
--   combine two rows into a new one where each type is a fresh unification variable.
union :: (Monad m, F.MonadFresh VarName m) => UnionMethod -> Row -> Row -> m Row
union method r1@(Row m1 _) r2@(Row m2 _)= do
  let keys = S.toList (M.keysSet m1 `S.union` M.keysSet m2)
  entries <- mapM (\x -> Entry x . UnifVar <$> F.fresh <*> pure (method x r1 r2)) keys
  incomplete entries

-- | If the field or constructor is taken in all the rows in which it appears, then it
--   is taken in the union row.
leastTaken :: UnionMethod
leastTaken x r1@(Row m1 v1) r2@(Row m2 v2)
  | x `S.member` M.keysSet m1 && x `S.member` M.keysSet m2 = x `takenIn` r1 && x `takenIn` r2
  | x `S.member` M.keysSet m1 = x `takenIn` r1
  | x `S.member` M.keysSet m2 = x `takenIn` r2
  | otherwise                 = False

-- | If the field is taken in any of the rows in which it appears, then the field is taken
--   in the union row.
mostTaken :: UnionMethod
mostTaken x r1@(Row m1 v1) r2@(Row m2 v2)
  | x `S.member` M.keysSet m1 && x `S.member` M.keysSet m2 = x `takenIn` r1 || x `takenIn` r2
  | x `S.member` M.keysSet m1 = x `takenIn` r1
  | x `S.member` M.keysSet m2 = x `takenIn` r2
  | otherwise                 = True

-}

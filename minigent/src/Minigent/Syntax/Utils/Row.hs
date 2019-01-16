-- |
-- Module      : Minigent.Syntax.Utils.Row
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- A grab-bag of functions to manipulate rows, and to combine them and create them
-- in various ways.
--
-- It must be imported qualified to prevent prelude clashes.
{-# LANGUAGE FlexibleContexts #-}
module Minigent.Syntax.Utils.Row
  ( -- * Constructors
    fromList
  , incomplete
  , -- * Queries
    entries
  , compatible
  , null
  , untakenTypes
  , typesFor
  , -- * Manipulating
    mapEntries
  , take
  , put
  , -- * Row Union and Combination
    -- ** Row Union
    union
  , UnionMethod
  , leastTaken
  , mostTaken
  , -- ** Common entries
    common
  , withoutCommon
  ) where


import Minigent.Syntax
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Minigent.Fresh as F
import Prelude hiding (take, null)
import Data.Maybe (mapMaybe)
import Control.Monad (guard)

-- | Given a list of entries, produce a complete row without a unification row variable.
fromList :: [Entry] -> Row
fromList es = Row (M.fromList (map (\e@(Entry f _ _ )-> (f,e)) es)) Nothing

-- | Given a list of entries, produce an incomplete row with a fresh unification row variable.
incomplete :: (Monad m, F.MonadFresh VarName m) => [Entry] -> m Row
incomplete es = do
  u <- F.fresh
  pure ((fromList es) { rowVar = Just u })

-- | Returns those pairs of entries in the input rows that have the same field/constructor
--   name.
common :: Row -> Row -> [(Entry, Entry)]
common r1 r2 = M.elems (M.intersectionWith (,) (rowEntries r1) (rowEntries r2))

-- | Returns whats left of the two input rows when all common entries are removed.
withoutCommon :: Row -> Row -> (Row, Row)
withoutCommon (Row e1 v1) (Row e2 v2) = ( Row (e1 `M.withoutKeys` M.keysSet e2) v1
                                        , Row (e2 `M.withoutKeys` M.keysSet e1) v2
                                        )

-- | Given a set of field names, return all the types for those field names in the row.
typesFor :: S.Set FieldName -> Row -> [Type]
typesFor fs (Row m _) = map (\(Entry _ t _ ) -> t) (M.elems (M.restrictKeys m fs))


-- | Returns true iff the row has no entries and no unification variable.
null :: Row -> Bool
null (Row m Nothing) = M.null m
null _ = False

-- | Returns true iff the two rows could be considered equal after unification.
compatible :: Row -> Row -> Bool
compatible (Row m1 Nothing) (Row m2 Nothing) = M.keysSet m1 == M.keysSet m2
compatible (Row m1 Nothing) (Row m2 (Just _)) = M.keysSet m1 `S.isSubsetOf` M.keysSet m2
compatible (Row m1 (Just _)) (Row m2 Nothing) = M.keysSet m2 `S.isSubsetOf` M.keysSet m1
compatible (Row m1 (Just x)) (Row m2 (Just y)) = x /= y || M.keysSet m1 == M.keysSet m2

-- | Returns all types not marked as 'Taken' in the row.
untakenTypes :: Row -> [Type]
untakenTypes = mapMaybe (\(Entry _ t x) -> guard (not x) >> Just t) . M.elems . rowEntries

-- | Returns all known entries inside the row.
entries :: Row -> [Entry]
entries = M.elems . rowEntries

-- | Manipulate each entry inside a row. It is assumed that the given function
--   does not change the field or constructor name in the entry. Don't do that.
mapEntries :: (Entry -> Entry) -> Row -> Row
mapEntries func (Row m e) = Row (fmap func m) e

-- | Given a field name, mark is as taken in the row (if it exists).
take :: FieldName -> Row -> Row
take f (Row m e) = Row (M.adjust (\(Entry f t _) -> Entry f t True) f m) e

-- | Given a field name, unmark is as taken in the row (if it exists).
put :: FieldName -> Row -> Row
put f (Row m e) = Row (M.adjust (\(Entry f t _) -> Entry f t False) f m) e

-- | Returns true iff the field is taken in the given row.
takenIn :: FieldName -> Row -> Bool
takenIn f (Row m _) = case M.lookup f m of
   Nothing -> False
   Just (Entry _ _ b) -> b

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

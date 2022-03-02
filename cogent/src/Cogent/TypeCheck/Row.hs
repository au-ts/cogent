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
  ( Entry (..)
  , Row
  , Shape
  , -- * Constructors
    mkEntry
  , complete
  , incomplete
  , fromMap
  , toEntryList
  , expand
  , close
  , shape
  , put
  , putMany
  , putAll
  , take
  , takeMany
  , takeAll
  -- * Queries on Rows
  , common
  , diff
  , entries
  , extract
  , fnames
  , isComplete
  , isEmpty
  , isIncomplete
  , justVar
  , payloads
  , presentLabels
  , presentPayloads
  , takenIn
  , var
  -- * Queries on Entries
  , fname
  , decl
  , payload
  , taken
  , present
  , compatEntry
  ) where

import           Cogent.Common.Syntax
import           Cogent.Compiler
import           Cogent.Surface
import           Cogent.Util (elemBy, notElemBy, (\\-))

import           Control.Monad (guard)
import           Data.Either (isRight)
import qualified Data.Foldable as F
import           Data.Function (on)
import           Data.List hiding (take)
import qualified Data.Map.Strict as M
import           Data.Maybe
import           Prelude hiding (take, null)


type Decl t = (t, Taken)

newtype Entry t = Entry { unE :: (FieldName, Decl t) }
  deriving (Show, Eq, Ord, Foldable, Functor, Traversable)

{-- | Rows represent the internal structure of variants and records. We
 --   refer to fields/constructors by the generic term "entries".
 --
 --   We have two types of rows:
 --
 --     * Complete: fully specified rows whose entries are ordered as
 --       they occur in the list.
 --
 --     * Incomplete: partially specified row with some known entries
 --       and a unification variable standing for the unknown
 --       entries. The order of the known entries in the list is
 --       immaterial since an incomplete row cannot specify the order
 --       of its entries yet.
 --
 --}
data Row t = Complete [Entry t] | Incomplete Int [Entry t]
  deriving (Show, Eq, Ord, Foldable, Functor, Traversable)

{--
 -- Shape: a unifier for a row variable occurring in an incomplete row which
 -- specifies the correct ordering of the entries.
 --}
type Shape = [FieldName]

-- | Construct an entry.
mkEntry :: FieldName -> t -> Taken -> Entry t
mkEntry f p t = Entry (f,(p,t))

-- | Retrieve the field name of an entry.
fname :: Entry t -> FieldName
fname (Entry (f,_)) = f

-- | Retrieve the declaraction from an entry
decl :: Entry t -> Decl t
decl (Entry (_,d)) = d

-- | Retrieve the takenness of an entry.
taken :: Entry t -> Bool
taken (Entry (_,(_,t))) = t

present = not . taken

-- | Retrieve the payload of an entry
payload :: Entry t -> t
payload (Entry (_,(p,_))) = p

-- | Given a list of entries, produce a complete row without a
-- unification row variable.
complete :: [Entry t] -> Row t
complete es = Complete es

-- | Given a list of entries, produce an incomplete row with a fresh
-- unification row variable.
incomplete :: [Entry t] -> Int -> Row t
incomplete es u = Incomplete u es

-- | Given a map of entries produce a complete row.
fromMap :: M.Map FieldName (t, Bool) -> Row t
fromMap m = Complete $ M.foldrWithKey (\k v es -> Entry (k, v) : es) [] m

-- | Convert a field:decl list structure to an entry list.
toEntryList :: [(FieldName, Decl t)] -> [Entry t]
toEntryList = map Entry

isEmpty :: Row t -> Bool
isEmpty (Complete []) = True
isEmpty _ = False

isComplete :: Row t -> Bool
isComplete (Complete _) = True
isComplete _ = False

isIncomplete :: Row t -> Bool
isIncomplete (Incomplete _ _) = True
isIncomplete _ = False

-- | A row with no concrete entries and a unification variable, which is
-- effectively an unconstrained unification variable
justVar :: Row t -> Bool
justVar (Incomplete _ []) = True
justVar _ = False

-- | Return the known entries for a row.
entries :: Row t -> [Entry t]
entries (Complete es) = es
entries (Incomplete _ es) = es

-- | Return the field names for all the known entries in the row.
fnames :: Row t -> [FieldName]
fnames r = map fname $ entries r

-- | Return the row variable, if any.
var :: Row t -> Maybe Int
var (Complete _) = Nothing
var (Incomplete v _) = Just v

-- | Return common constructors/fields between two rows.
common :: Row t -> Row t -> [(Entry t, Entry t)]
common (Complete es) (Complete es') = pointwise es es' []
common (Complete es) (Incomplete _ es') = foldr (unord es) [] es'
common (Incomplete _ es) (Incomplete _ es') = foldr (unord es) [] es'
common (Incomplete _ es) (Complete es') = foldr (unord es') [] es

-- | Internal helper function for extracting common fields from complete
-- records.
pointwise :: [Entry t] -> [Entry t] -> [(Entry t, Entry t)] ->
             [(Entry t, Entry t)]
pointwise (e : es) (e' : es') rs
  | fname e == fname e' = pointwise es es' ((e,e') : rs)
  | otherwise = []
pointwise [] [] rs = rs
pointwise [] _ _ = [] -- invariant broken
pointwise _ [] _ = [] -- invariant broken

-- | Internel helper function for extracting common fields from a
-- (in)complete record and an incomplete record.
unord :: [Entry t] -> Entry t -> [(Entry t, Entry t)] -> [(Entry t, Entry t)]
unord es e' acc | Just e <- find (\e -> fname e == fname e') es = (e,e') : acc
unord _ _ acc = acc

-- | Return the difference in constructors/fields between two rows.
-- The result is the first row with the second row's entries removed.
diff :: Row t -> Row t -> [Entry t]
diff r1 r2 = xs ++ ys
  where xs = filter (\e -> notElemBy compatEntry e (entries r2)) $ entries r1
        ys = filter (\e -> notElemBy compatEntry e (entries r1)) $ entries r2

-- | Expand an incomplete row. This operation does nothing if applied to a
-- complete row. For incomplete rows, the entries are assumed to be disjoint.
expand :: Show t => Row t -> Row t -> Row t
expand r@(Complete _) _ =
  __impossible ("Row.expand: attempting to expand complete row: " ++ show r)
expand (Incomplete _ es) (Complete es') =
  let f e' = case find (\e -> fname e == fname e') es of
        Just e -> e
        Nothing -> e' in
  Complete $ map f es'
expand (Incomplete _ es) (Incomplete v' es') = Incomplete v' (es ++ es')

close :: Show t => Row t -> Shape -> Row t
close (Incomplete _ es) s | compatShape es s =
  Complete $ zipWith (curry Entry) s $ mapMaybe (flip lookup $ map unE es) s
close r@(Incomplete _ _) s =
  __impossible ("Row.close: shape " ++ show s ++
                " is incompatible with row: " ++ show r)
close r _ =
  __impossible ("Row.close: attempting to close complete row: " ++ show r)

-- | Return the shape of a complete row. Empty if row not complete.
shape :: Row t -> Shape
shape (Complete es) = map fname es
shape _ = []

compatShape :: [Entry t] -> Shape -> Bool
compatShape es s =
  all ((`elem` s) . fname) es && all (`elem` (map fname es)) s

-- | Return the entries in the list which are known to be present.
presentEntries :: [Entry t] -> [Entry t]
presentEntries es = filter present es

presentLabels :: Row t -> [FieldName]
presentLabels r = map fname $ presentEntries (entries r)

-- | Return the payload all present entries in the row.
presentPayloads :: Row t -> [t]
presentPayloads r = map payload $ presentEntries (entries r)

-- | Retrieve all the payloads of the row.
payloads :: Row t -> [t]
payloads r = map payload (entries r)

-- | Returns true iff the field is taken in the given row.
takenIn :: FieldName -> Row t -> Bool
takenIn f r = case find ((f ==) . fname) (entries r) of
  Just e -> taken e
  Nothing -> False

-- | Given a set of field names extract their corresponding payload in the
-- provided row.
extract :: [FieldName] -> Row t -> [t]
extract s r = map payload (filter (\e -> fname e `elem` s) (entries r))

-- | Given a list of labels mark them as taken in the row (if they exist).
setMany :: Bool -> [FieldName] -> Row t -> Row t
setMany b fs r = case r of
  Complete es -> Complete $ foldr g [] es
  Incomplete v es -> Incomplete v $ foldr g [] es
  where
    g :: Entry t -> [Entry t] -> [Entry t]
    g e es | fname e `elem` fs = Entry (fname e, (payload e, b)) : es
    g e es = e : es

set :: Bool -> FieldName -> Row t -> Row t
set b f r = setMany b [f] r

setAll :: Bool -> Row t -> Row t
setAll b r = setMany b (map fname $ entries r) r

-- Take/Put variants.

take :: FieldName -> Row t -> Row t
take = set True

takeMany :: [FieldName] -> Row t -> Row t
takeMany = setMany True

takeAll :: Row t -> Row t
takeAll = setAll True

put :: FieldName -> Row t -> Row t
put = set False

putMany :: [FieldName] -> Row t -> Row t
putMany = setMany False

putAll :: Row t -> Row t
putAll = setAll False

-- | Returns true iff the two rows could be considered equal after
-- unification.
compatRow :: Row t -> Row t -> Bool
compatRow (Complete es) (Complete es') = map fname es == map fname es'
compatRow (Complete es) (Incomplete _ es') = all (\e -> elemBy compatEntry e es ) es'
compatRow (Incomplete _ es) (Complete es') = all (\e -> elemBy compatEntry e es') es
compatRow (Incomplete v es) (Incomplete v' es') = v /= v' || null ((\\-) compatEntry es es')

compatEntry :: Entry t -> Entry t -> Bool
compatEntry = (==) `on` fname


--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

module Cogent.Context
  ( Context
  , Assumption
  , addScope
  , contains
  , dropScope
  , empty
  , lookup
  , merge
  , join
  , mode
  , use
) where

import Cogent.Common.Syntax
import Cogent.Compiler (__impossible)
import Lens.Micro.GHC()
import Lens.Micro
import Data.List (foldl', partition)
import qualified Data.Sequence as Seq
import qualified Data.Map.Strict as M
import Prelude hiding (lookup)
import Text.Parsec.Pos

type Assumption t = (t, SourcePos, Seq.Seq SourcePos)
--                                 ^------ the locations where it's used; serves as an use count
newtype Context t = Context [M.Map VarName (Assumption t)] deriving (Eq)

empty :: Context t
empty = Context []

lookup :: VarName -> Context t -> Maybe (t, SourcePos, Seq.Seq SourcePos)
lookup v (Context (m:ms)) | Just r <- M.lookup v m = Just r
                          | otherwise              = lookup v (Context ms)
lookup _ (Context []) = Nothing

contains :: Context t -> VarName -> Bool
contains (Context ms) v = any (M.member v) ms

use :: VarName -> SourcePos -> Context t -> Context t
use v loc (Context ms) = Context (go ms)
  where go (x:xs) | M.member v x = M.adjust (\(t, p, us) -> (t, p, us Seq.|> loc)) v x:xs
                  | otherwise    = x:go xs
        go [] = []

addScope :: M.Map VarName (Assumption t) -> Context t -> Context t
addScope m (Context ms) = Context (m:ms)

dropScope :: Context t -> (M.Map VarName (Assumption t), Context t)
dropScope (Context (m:ms)) = (m, Context ms)
dropScope (Context [])     = error "dropScope of empty context!"

mode' :: M.Map VarName x -> [VarName] -> (x -> x) -> (M.Map VarName x, M.Map VarName x -> M.Map VarName x)
mode' c vs f =
  let c' = M.mapWithKey (\v x -> if v `elem` vs then f x else x) c 
      undo d = foldl' (\x v -> x & at v .~ M.lookup v c) d vs  -- update each `k |-> _' in map `d' to `k |-> lookup v c'
  in (c', undo)

-- It updates the `vs' in the context according to function `f',
-- returns the new context, and a function to revert this update.
-- Note that the `undo' function is completely independent to the given context.
mode :: Context t -> [VarName]
     -> ((t, SourcePos, Seq.Seq SourcePos) -> (t, SourcePos, Seq.Seq SourcePos))
     -> (Context t, Context t -> Context t)
mode (Context ms) vs f = let (c', f') = go ms vs
                         in (Context c', \(Context x) -> Context (f' x))
  where
    go []     _  = ([], id)
    go (x:xs) vs = let
        (as, bs) = partition (`M.member` x) vs
        (x', ux) = mode' x as f
        (xs', uxs) = go xs bs
        undo (n:ns) = (ux n : uxs ns)
        undo []     = []
      in (x':xs', undo)


data UnionHelper x = First x | Second x | Both x

unhelp :: UnionHelper x -> x
unhelp (First x) = x
unhelp (Second x) = x
unhelp (Both x) = x

isFirst :: UnionHelper x -> Bool
isFirst (First _) = True
isFirst _ = False

isSecond :: UnionHelper x -> Bool
isSecond (Second _) = True
isSecond _ = False

merge' :: M.Map VarName (Assumption x)
       -> M.Map VarName (Assumption x)
       -> (M.Map VarName (Assumption x), [(VarName, Assumption x)], [(VarName, Assumption x)])
merge' a b = let a' = fmap First a
                 b' = fmap Second b
                 m  = M.unionWith f a' b'
                 f (First (t, p, Seq.Empty)) (Second (_, _, Seq.Empty)) = Both (t, p, Seq.empty)
                 f (First (t, p, us)) (Second (_, _, Seq.Empty)) = First  (t, p, us)
                 f (First (_, _, Seq.Empty)) (Second (t, p, us)) = Second (t, p, us)
                 f (First (t, p, us)) (Second (_, _, vs)) = Both (t, p, us Seq.>< vs)
                 f _ _ = __impossible "merge'"
                 newM = fmap unhelp m
                 ls = M.toList $ unhelp <$> M.filter isFirst m
                 rs = M.toList $ unhelp <$> M.filter isSecond m
              in (newM, ls, rs)

merge :: Context t -> Context t -> (Context t, [(VarName, Assumption t)], [(VarName, Assumption t)])
merge (Context m) (Context n) = let (c, l, r) = go m n in (Context c, l, r)
  where
    go [] [] = ([], [], [])
    go [] _  = __impossible "merge"
    go _ []  = __impossible "merge"
    go (a:as) (b:bs) = let
      (cs, ls, rs) = go as bs
      (c,  l,  r ) = merge' a b
      in (c:cs, l ++ ls, r ++ rs)

data JoinHelper x = None x | One x | Two x

unhelp' :: JoinHelper x -> x
unhelp' (None x) = x
unhelp' (One  x) = x
unhelp' (Two  x) = x

isNone (None _) = True
isNone _ = False

isOne (One _) = True
isOne _ = False

isTwo (Two _) = True
isTwo _ = False

join' :: M.Map VarName (Assumption x)
      -> M.Map VarName (Assumption x)
      -> (M.Map VarName (Assumption x), [(VarName, Assumption x)], [(VarName, Assumption x)])
join' a b = let a' = fmap One a
                b' = fmap One b
                m  = M.unionWith f a' b'
                f (One (t, p, Seq.Empty)) (One (_, _, Seq.Empty)) = None (t, p, Seq.empty)
                f (One (t, p, us)) (One (_, _, Seq.Empty)) = One (t, p, us)
                f (One (_, _, Seq.Empty)) (One (t, p, us)) = One (t, p, us)
                f (One (t, p, us)) (One (_, _, vs)) = Two (t, p, us Seq.>< vs)
                f _ _ = __impossible "join'"
                newM = fmap unhelp' m
                ns = M.toList $ unhelp' <$> M.filter isNone m
                ts = M.toList $ unhelp' <$> M.filter isTwo  m
             in (newM, ns, ts)

join :: Context t -> Context t -> (Context t, [(VarName, Assumption t)], [(VarName, Assumption t)])
join (Context m) (Context n) = let (c, l, r) = go m n in (Context c, l, r)
  where
    go [] [] = ([], [], [])
    go [] _  = __impossible "join"
    go _ []  = __impossible "join"
    go (a:as) (b:bs) = let
      (cs, ls, rs) = go as bs
      (c,  l,  r ) = join' a b
      in (c:cs, l ++ ls, r ++ rs)

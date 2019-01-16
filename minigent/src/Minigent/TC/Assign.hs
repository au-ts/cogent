-- |
-- Module      : Minigent.TC.Assign
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- The assign phase of constraint solving.
--
-- May be used qualified or unqualified.
module Minigent.TC.Assign
  ( Assign (..)
  , substAssign
  , assign
  ) where
import Minigent.Syntax
import Minigent.Syntax.Utils

import qualified Minigent.Syntax.Utils.Rewrite as Rewrite


import qualified Data.Map as M

-- | An assignment to a unification variable (standing for various things)
data Assign = TyAssign VarName Type
            | RowAssign VarName Row
            | SigilAssign VarName Sigil

-- | Apply an assignment to a unification variable to a type.
substAssign :: Assign -> Rewrite.Rewrite Type
substAssign (TyAssign v t) = substUV (v, t)
substAssign (RowAssign v t) = substRowV (v, t)
substAssign (SigilAssign v t) = substSigilV (v, t)

data AssignMap = Candidates [ Type ]
               | Definite Type
               | DefiniteRow Row
               | CandidatesRow [ Row ]
               | DefiniteSigil Sigil
               | Blocked

instance Semigroup AssignMap where
   Definite x <> y = Definite x
   x <> Definite y = Definite y
   DefiniteRow x <> y = DefiniteRow x
   x <> DefiniteRow y = DefiniteRow y
   DefiniteSigil x <> y = DefiniteSigil x
   x <> DefiniteSigil y = DefiniteSigil y
   Blocked <> x = Blocked
   x <> Blocked = Blocked
   Candidates xs <> Candidates ys = Candidates (xs ++ ys)
   CandidatesRow xs <> CandidatesRow ys = CandidatesRow (xs ++ ys)

unambiguous :: AssignMap -> Maybe Type
unambiguous (Candidates [x]) = Just x
unambiguous (Definite x) = Just x
unambiguous _ = Nothing

unambiguousRows :: AssignMap -> Maybe Row
unambiguousRows (CandidatesRow [x]) = Just x
unambiguousRows (DefiniteRow x) = Just x
unambiguousRows _ = Nothing

unambiguousSigils :: AssignMap -> Maybe Sigil
unambiguousSigils (DefiniteSigil x) = Just x
unambiguousSigils _ = Nothing

findAssignCandidates :: [Constraint] -> (M.Map VarName AssignMap, M.Map VarName AssignMap)
findAssignCandidates [] = (M.empty, M.empty)
findAssignCandidates (c:cs) = let
    (sups, subs) = findAssignCandidates cs
  in case c of
       Variant (Row m (Just a)) :< Variant (Row r Nothing)
         | M.null m -> (M.insertWith (<>) a (CandidatesRow [Row r Nothing]) sups, subs)
         | otherwise -> (M.insertWith (<>) a Blocked sups, subs)
       Variant (Row m (Just a)) :=: Variant (Row r Nothing)
         | M.null m -> (M.insertWith (<>) a (DefiniteRow (Row r Nothing)) sups,
                        M.insertWith (<>) a (DefiniteRow (Row r Nothing)) subs)
       Variant (Row r Nothing) :< Variant (Row m (Just a))
         | M.null m  -> (sups, M.insertWith (<>) a (CandidatesRow [Row r Nothing]) subs)
         | otherwise -> (sups, M.insertWith (<>) a (Blocked) subs)
       Variant (Row r Nothing) :=: Variant (Row m (Just a))
         | M.null m -> (M.insertWith (<>) a (DefiniteRow (Row r Nothing)) sups,
                        M.insertWith (<>) a (DefiniteRow (Row r Nothing)) subs)
       Record r1 (UnknownSigil s1) :< Record r2 s2
         | UnknownSigil s1 /= s2 -> (M.insertWith (<>) s1 (DefiniteSigil s2) sups,
                                     M.insertWith (<>) s1 (DefiniteSigil s2) subs)
       Record r1 (UnknownSigil s1) :=: Record r2 s2
         | UnknownSigil s1 /= s2 -> (M.insertWith (<>) s1 (DefiniteSigil s2) sups,
                                     M.insertWith (<>) s1 (DefiniteSigil s2) subs)
       Record r2 s2 :< Record r1 (UnknownSigil s1)
         | UnknownSigil s1 /= s2 -> (M.insertWith (<>) s1 (DefiniteSigil s2) sups,
                                     M.insertWith (<>) s1 (DefiniteSigil s2) subs)
       Record r2 s2 :=: Record r1 (UnknownSigil s1)
         | UnknownSigil s1 /= s2 -> (M.insertWith (<>) s1 (DefiniteSigil s2) sups,
                                     M.insertWith (<>) s1 (DefiniteSigil s2) subs)

       Record (Row m (Just a)) s1 :< Record (Row r Nothing) s2
         | M.null m -> (M.insertWith (<>) a (CandidatesRow [Row r Nothing]) sups, subs)
         | otherwise -> (M.insertWith (<>) a Blocked sups, subs)
       Record (Row m (Just a)) s1 :=: Record (Row r Nothing) s2
         | M.null m -> (M.insertWith (<>) a (DefiniteRow (Row r Nothing)) sups,
                        M.insertWith (<>) a (DefiniteRow (Row r Nothing)) subs)
       Record (Row r Nothing) s1 :< Record (Row m (Just a)) s2
         | M.null m  -> (sups, M.insertWith (<>) a (CandidatesRow [Row r Nothing]) subs)
         | otherwise -> (sups, M.insertWith (<>) a (Blocked) subs)
       Record (Row r Nothing) s1 :=: Record (Row m (Just a)) s2
         | M.null m -> (M.insertWith (<>) a (DefiniteRow (Row r Nothing)) sups,
                        M.insertWith (<>) a (DefiniteRow (Row r Nothing)) subs)
       UnifVar a :=: b
         | rigid b && notOccurs a b -> (M.insertWith (<>) a (Definite b) sups, M.insertWith (<>) a (Definite b) subs)
       b :=: UnifVar a
         | rigid b && notOccurs a b -> (M.insertWith (<>) a (Definite b) sups, M.insertWith (<>) a (Definite b) subs)
       UnifVar a :< b
         | rigid b && notOccurs a b -> (M.insertWith (<>) a (Candidates [b]) sups, subs)
       b :< UnifVar a
         | rigid b && notOccurs a b -> (sups, M.insertWith (<>) a (Candidates [b]) subs)
       a :< b | rigid a && rigid b -> (sups,subs)
       a :< b | a == b             -> (sups,subs)
       a :< b | Just a' <- rootUnifVar a
              , Just b' <- rootUnifVar b
              -> ( M.insertWith (<>) a' Blocked sups
                 , M.insertWith (<>) b' Blocked subs)
       _ -> (sups,subs)
  where
    notOccurs a tau = a `notElem` typeUVs tau

-- | Find an assignment to a unification variable occuring in the given set of constraints
--   that preserves satisfiability.
assign :: [Constraint] -> Maybe Assign
assign cs
  = let (sups, subs) = findAssignCandidates cs
    in case M.toList (M.mapMaybe unambiguous sups ) ++ M.toList (M.mapMaybe unambiguous subs) of
         (v,t):_ -> Just (TyAssign v t)
         _       -> case M.toList (M.mapMaybe unambiguousRows sups ) ++ M.toList (M.mapMaybe unambiguousRows subs) of
                      (v,r):_ -> Just (RowAssign v r)
                      _ -> case M.toList (M.mapMaybe unambiguousSigils sups) ++ M.toList (M.mapMaybe unambiguousSigils subs) of
                             (v,s):_ -> Just (SigilAssign v s)
                             _       -> Nothing

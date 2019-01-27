-- |
-- Module      : Minigent.TC.Equate
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- The equate phase of constraint solving.
--
-- May be used qualified or unqualified.

module Minigent.TC.Equate (equate) where

import Minigent.Syntax
import Minigent.Syntax.Utils
import qualified Minigent.Syntax.Utils.Rewrite as Rewrite

import Minigent.Fresh
import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import Control.Applicative
import Data.Foldable (asum)
import qualified Data.Map as M

-- | The equate phase, which finds subtyping constraints that can be safely converted to equalities.
equate :: Rewrite.Rewrite [Constraint]
equate = Rewrite.withTransform findEquatable (pure . map toEquality)
  where
    findEquatable cs = let
         (sups, subs, others) = findEquateCandidates cs
         (eqs , others' )     = getUnambiguous (M.toList sups)
         (eqs', others'')     = getUnambiguous (M.toList subs)
         -- If we find candidates in both the LHS and RHS of the same variable, we cannot convert them both.
         -- Proof: Suppose T :< U but T /= U.
         -- If we have constraint system (T :< a :&: a :< U), either subtyping constraint are convertible
         -- to equalities without changing the satisfiability of the constraint system, however converting
         -- both makes the constraint system unsatisfiable.
         -- Thus, we convert LHS constraints if possible first, and only convert RHS if there are no available
         -- LHSes.
         allEqs = if null eqs then eqs' else eqs
         allOthers = (if not (null eqs) then eqs' else []) ++ others ++ others' ++ others''
      in guard (not (null allEqs)) >> pure (allEqs, allOthers)

    toEquality :: Constraint -> Constraint
    toEquality (a :< b) = a :=: b
    toEquality c = c


getUnambiguous :: [(VarName, [Constraint])] -> ([Constraint], [Constraint])
getUnambiguous [] = ([],[])
getUnambiguous ((v,cs):vs) = let (unambs, ambs) = getUnambiguous vs
                              in case cs of
                                        [c] -> (c:unambs, ambs)
                                        _   -> (unambs, cs ++ ambs)



findEquateCandidates :: [Constraint] -> (M.Map VarName [Constraint], M.Map VarName [Constraint], [Constraint])
findEquateCandidates [] = (M.empty, M.empty, [])
findEquateCandidates (c:cs) = let
    (sups, subs, others) = findEquateCandidates cs
  in case c of
       UnifVar a :< b
         | rigid b && notOccurs a b -> (M.insertWith (<>) a [c] sups, subs, others)
       b :< UnifVar a
         | rigid b && notOccurs a b -> (sups, M.insertWith (<>) a [c] subs, others)
       Variant r1 :< t
         | rigid t, Just a <- rowVar r1 -> (M.insertWith (<>) a [c] sups, subs, others)
       Record r1 s :< t
         | rigid t, Just a <- rowVar r1 -> (M.insertWith (<>) a [c] sups, subs, others)
       t :< Variant r1
         | rigid t, Just a <- rowVar r1 -> (sups, M.insertWith (<>) a [c] subs, others)
       t :< Record r1 s
         | rigid t, Just a <- rowVar r1 -> (sups, M.insertWith (<>) a [c] subs, others)
       _ -> (sups,subs, c:others)



notOccurs :: VarName -> Type -> Bool
notOccurs a tau = a `notElem` typeUVs tau

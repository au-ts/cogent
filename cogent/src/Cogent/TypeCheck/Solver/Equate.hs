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

module Cogent.TypeCheck.Solver.Equate (equate) where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Surface
import Cogent.TypeCheck.Base
import qualified Cogent.TypeCheck.Row as Row
import Cogent.TypeCheck.Solver.Goal
import Cogent.TypeCheck.Solver.Monad
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite

import Control.Applicative
import Control.Monad.Trans.Maybe
import Control.Monad.Writer
import Data.Foldable (asum)
import qualified Data.IntMap as IM
import Data.Maybe
import qualified Data.Set as S
import Lens.Micro

import Cogent.PrettyPrint
import Text.PrettyPrint.ANSI.Leijen (pretty)
import Debug.Trace

-- | The equate phase, which finds subtyping constraints that can be safely converted to equalities.
equate :: Rewrite.Rewrite [Goal]
equate = Rewrite.withTransform findEquatable (pure . map toEquality)
  where
    findEquatable cs = let
         mentions             = getMentions cs
         (sups, subs, others) = findEquateCandidates mentions cs
         -- If we find candidates in both the LHS and RHS of the same variable, we cannot convert them both.
         -- Proof: Suppose T :< U but T /= U.
         -- If we have constraint system (T :< a :&: a :< U), either subtyping constraint are convertible
         -- to equalities without changing the satisfiability of the constraint system, however converting
         -- both makes the constraint system unsatisfiable.
         -- Thus, we convert LHS constraints if possible first, and only convert LHS if there are no available.
         allEqs = if null sups then subs else sups 
         allOthers = (if null sups then [] else subs) ++ others
      in guard (not (null allEqs)) >> pure (allEqs, allOthers)

    toEquality :: Goal -> Goal
    toEquality (Goal c env (a :< b)) = Goal c env $ a :=: b
    toEquality c = c

findEquateCandidates :: IM.IntMap (Int,Int,Int,Bool) -> [Goal] -> ([Goal], [Goal], [Goal])
findEquateCandidates _ [] = ([], [], [])
findEquateCandidates mentions (c:cs) =
  let
    (sups, subs, others) = findEquateCandidates mentions cs
    canEquate f v t
     | Just m <- IM.lookup v mentions
     = f m <= 1 && rigid t && notOccurs v t
     | otherwise
     = False
    isBaseUnif x = case IM.lookup x mentions of
                     Just (_,_,_,True) -> True
                     _                 -> False
  in case c ^. goal of
       U a :< b
         | canEquate (\m -> m^._1 + m^._2) a b
         , not (isRefinementType b && isBaseUnif a)
         -> (c : sups, subs, others)
       a :< U b
         | canEquate (^._3) b a  -- why? / zilinc
         , not (isRefinementType a && isBaseUnif b)
         -> (sups, c : subs, others)
#ifdef REFINEMENT_TYPES
       t :< T (TRefine v b (HApp x _ _))
         | canEquate (^._3) x t
         , isRefinementType t
         -> (sups, c : subs, others)
       T (TRefine v b (HApp x _ _)) :< t
         | canEquate (^._2) x t
         , isRefinementType t
         -> (c : sups, subs, others)
#endif
       V r1 :< t
         | Just a <- Row.var r1
         , Row.justVar r1
         , canEquate (^._2) a t
         -> (c : sups, subs, others)
       R _ r1 s :< t
         | Just a <- Row.var r1
         , Row.justVar r1
         , canEquate (^._2) a t
         -> (c : sups, subs, others)
       t :< V r1
         | Just a <- Row.var r1
         , Row.justVar r1
         , canEquate (^._3) a t
         -> (sups, c : subs, others)
       t :< R _ r1 s
         | Just a <- Row.var r1
         , Row.justVar r1
         , canEquate (^._3) a t
         -> (sups, c : subs, others)
#ifdef REFINEMENT_TYPES
       -- NOTE: This is Ok and we don't need to look into unifVars in
       -- elt1, len1 and s1, because h here is the only thing which
       -- plays a role in array subtyping. If h is the only occurrence
       -- of a unifVar, then we can equate it. / zilinc
       A elt1 len1 s1 (Right h) :< t
         | canEquate (^._2) h t
         -> (c : sups, subs, others)
       t :< A elt2 len2 s2 (Right h)
         | canEquate (^._2) h t
         -> (sups, c : subs, others)
#endif
       _ -> (sups, subs, c : others)

notOccurs :: Int -> TCType -> Bool
notOccurs a tau = a `notElem` unifVars tau

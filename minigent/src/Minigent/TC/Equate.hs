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
import qualified Minigent.Syntax.Utils.Row as Row

import Minigent.Fresh
import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import Control.Applicative
import Data.Foldable (asum)
import Data.List(foldl')
import qualified Data.Map as M

import Debug.Trace

import Minigent.Syntax.PrettyPrint

-- | The equate phase, which finds subtyping constraints that can be safely converted to equalities.
equate :: Rewrite.Rewrite [Constraint]
equate = Rewrite.withTransform findEquatable (pure . map toEquality)
                          --  (\x -> 
                          --   let c = toEquality x 
                          --   in trace ("About to simpliy:\n" ++ debugPrettyConstraints [c]) c)
                          --  )
  where
    findEquatable cs = let
         mentions             = getMentions cs
         (sups, subs, others) = findEquateCandidates mentions cs
         -- If we find candidates in both the LHS and RHS of the same variable, we cannot convert them both.
         -- Proof: Suppose T :< U but T /= U.
         -- If we have constraint system (T :< a :&: a :< U), either subtyping constraint are convertible
         -- to equalities without changing the satisfiability of the constraint system, however converting
         -- both makes the constraint system unsatisfiable.
         -- Thus, we convert LHS constraints if possible first, and only convert RHS if there are no available
         -- LHSes.
         allEqs = if null sups then subs else sups
         allOthers = (if not (null sups) then subs else []) ++ others 
      in guard (not (null allEqs)) >> pure (allEqs, allOthers)

    toEquality :: Constraint -> Constraint
    toEquality (a :< b) = a :=: b
    toEquality c = c

getMentions :: [Constraint] -> M.Map VarName (Int,Int)
getMentions gs =
    foldl' (M.unionWith adds) M.empty
  $ fmap mentionsOfGoal gs
 where
  adds (a,b) (c,d) = (a + c, b + d)

  mentionsOfGoal (r :< s) = M.fromListWith adds (mentionL r ++ mentionR s)
  mentionsOfGoal _        = M.empty

  mentionL = fmap (\v -> (v, (1,0))) . typeUVs 
  mentionR = fmap (\v -> (v, (0,1))) . typeUVs 




findEquateCandidates :: M.Map VarName (Int,Int) 
                     -> [Constraint] 
                     -> ([Constraint], [Constraint], [Constraint])
findEquateCandidates mentions [] = ([], [], [])
findEquateCandidates mentions (c:cs) = let
    (sups, subs, others) = findEquateCandidates mentions cs
    canEquate f v t -- | trace (show (v,t, rigid t, notOccurs v t, M.lookup v mentions)) False = undefined
                    | Just m <- M.lookup v mentions
                    = f m <= 1 && rigid t && notOccurs v t
                    | otherwise = False
  in case c of
       UnifVar a :< b | canEquate fst a b
                     -> (c:sups, subs, others)
       a :< UnifVar b | canEquate snd b a
                     -> (sups, c:subs, others)
       Variant r1 :< t | Just a <- rowVar r1 
                       , Row.justVar r1 
                       , canEquate fst a t
                      -> (c:sups, subs, others)
       Record rp r1 s :< t | Just a <- rowVar r1
                        , Row.justVar r1
                        , canEquate fst a t
                       -> (c:sups, subs, others)
       t :< Variant r1 | Just a <- rowVar r1
                       , Row.justVar r1
                       , canEquate snd a t
                      -> (sups, c : subs, others)
       t :< Record rp r1 s | Just a <- rowVar r1
                        , Row.justVar r1
                        , canEquate snd a t
                       -> (sups, c : subs, others)
       _ -> (sups,subs, c:others)



notOccurs :: VarName -> Type -> Bool
notOccurs a tau = a `notElem` typeUVs tau

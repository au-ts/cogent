module Cogent.TypeCheck.Solver.Equate (equate) where
    

import Cogent.Surface
import Cogent.TypeCheck.Base 
import Cogent.Common.Types
import Cogent.Common.Syntax
import Cogent.TypeCheck.Solver.Goal 
import Cogent.TypeCheck.Solver.Monad
import qualified Cogent.TypeCheck.Row as Row
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import Control.Applicative
import Data.Foldable (asum)
import qualified Data.Map as M
import Data.Maybe
import Lens.Micro

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
         -- Thus, we convert LHS constraints if possible first, and only convert RHS if there are no available
         -- LHSes.
         allEqs = if null sups then subs else sups
         allOthers = (if not (null sups) then subs else []) ++ others
      in guard (not (null allEqs)) >> pure (allEqs, allOthers)

    toEquality :: Goal -> Goal 
    toEquality (Goal c (a :< b)) = Goal c $ a :=: b
    toEquality c = c

getMentions :: [Goal] -> M.Map Int (Int,Int)
getMentions gs =
    foldl (M.unionWith adds) M.empty
  $ fmap mentionsOfGoal gs
 where
  adds (a,b) (c,d) = (a + c, b + d)

  mentionsOfGoal g = case g ^. goal of
   r :< s -> M.fromListWith adds (mentionL r ++ mentionR s)
   _      -> M.empty

  mentionL = fmap (\v -> (v, (1,0))) . unifVars
  mentionR = fmap (\v -> (v, (0,1))) . unifVars


findEquateCandidates :: M.Map Int (Int,Int) -> [Goal] -> ([Goal], [Goal], [Goal])
findEquateCandidates _ [] = ([], [], [])
findEquateCandidates mentions (c:cs) =
  let
    (sups, subs, others) = findEquateCandidates mentions cs
    canEquate f v t
     | Just m <- M.lookup v mentions
     = f m <= 1 && rigid t && notOccurs v t
     | otherwise
     = False
  in case c ^. goal of
       U a :< b
         | canEquate fst a b
         -> (c : sups, subs, others)
       a :< U b
         | canEquate snd b a
         -> (sups, c : subs, others)
       V r1 :< t
         | Just a <- Row.var r1
         , Row.justVar r1
         , canEquate fst a t
         -> (c : sups, subs, others)
       R r1 s :< t
         | Just a <- Row.var r1
         , Row.justVar r1
         , canEquate fst a t
         -> (c : sups, subs, others)
       t :< V r1
         | Just a <- Row.var r1
         , Row.justVar r1
         , canEquate snd a t
         -> (sups, c : subs, others)
       t :< R r1 s
         | Just a <- Row.var r1
         , Row.justVar r1
         , canEquate snd a t
         -> (sups, c : subs, others)
       _ -> (sups, subs, c : others)



notOccurs :: Int -> TCType -> Bool
notOccurs a tau = a `notElem` unifVars tau

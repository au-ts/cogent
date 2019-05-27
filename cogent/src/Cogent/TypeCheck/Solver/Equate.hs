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

    toEquality :: Goal -> Goal 
    toEquality (Goal c (a :< b)) = Goal c $ a :=: b
    toEquality c = c


getUnambiguous :: [(Int, Either [Goal] [Goal])] -> ([Goal], [Goal])
getUnambiguous [] = ([],[])
getUnambiguous ((v,cs):vs) = let (unambs, ambs) = getUnambiguous vs
                              in case cs of
                                        Right [c] -> (c:unambs, ambs)
                                        _   -> (unambs, fromEither cs ++ ambs)

fromEither :: Either a a -> a
fromEither (Left a) = a
fromEither (Right a) = a

combine :: Either [Goal] [Goal] -> Either [Goal] [Goal] -> Either [Goal] [Goal]
combine (Right x) (Right y) = Right (x <> y)
combine (Left x)  (Right y) = Left (x <> y)
combine (Right x) (Left y)  = Left (x <> y)
combine (Left x)  (Left y)  = Left (x <> y)

findEquateCandidates :: [Goal] -> (M.Map Int (Either [Goal] [Goal]), M.Map Int (Either [Goal] [Goal]), [Goal])
findEquateCandidates [] = (M.empty, M.empty, [])
findEquateCandidates (c:cs) = let
    (sups, subs, others) = findEquateCandidates cs
  in case c ^. goal of
       U a :< b
         | rigid b && notOccurs a b -> (M.insertWith combine a (Right [c]) sups, subs, others)
       b :< U a
         | rigid b && notOccurs a b -> (sups, M.insertWith combine a (Right [c]) subs, others)
       V r1 :< t
         | rigid t
         , Row.justVar r1
         , Just a <- Row.var r1 -> (M.insertWith combine a (Right [c]) sups, subs, others)
       R r1 s :< t
         | rigid t
         , Row.justVar r1
         , Just a <- Row.var r1 -> (M.insertWith combine a (Right [c]) sups, subs, others)
       t :< V r1
         | rigid t
         , Row.justVar r1
         , Just a <- Row.var r1 -> (sups, M.insertWith combine a (Right [c]) subs, others)
       t :< R r1 s
         | rigid t
         , Row.justVar r1
         , Just a <- Row.var r1 -> (sups, M.insertWith combine a (Right [c]) subs, others)
       _ -> (sups,subs, c:others)



notOccurs :: Int -> TCType -> Bool
notOccurs a tau = a `notElem` unifVars tau

module Cogent.TypeCheck.Solver.Unify where 

import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
import Cogent.TypeCheck.Solver.Goal 
import Cogent.TypeCheck.Solver.Monad
import qualified Cogent.TypeCheck.Row as Row
import qualified Cogent.TypeCheck.Subst as Subst
import Cogent.Surface
import Cogent.TypeCheck.Base 
import Cogent.Common.Types
import Cogent.Common.Syntax
import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import Control.Applicative
import Data.Foldable (asum)
import Lens.Micro
import Lens.Micro.Mtl

-- TODO: Remove
import Debug.Trace

-- | The unify phase, which seeks out equality constraints to solve via substitution.
unify ::  Rewrite.Rewrite' TcSolvM [Goal]
unify = Rewrite.rewrite' $ \cs -> do
           as <- asum (map (assignOf . view goal) cs)
           tell as
           pure (foldr (\a -> map (goal %~ Subst.applyC a)) cs as)

assignOf :: Constraint -> MaybeT TcSolvM [Subst.Subst]
assignOf (U a :=: tau) | rigid tau, a `notOccurs` tau = pure [Subst.ofType a tau]
assignOf (tau :=: U a) | rigid tau, a `notOccurs` tau = pure [Subst.ofType a tau]

assignOf (R _ _ (Right v) :=: R _ _ (Left s))
  = pure [ Subst.ofSigil v s ]
assignOf (R _ _ (Left s) :=: R _ _ (Right v))
  = pure [ Subst.ofSigil v s ]
assignOf (R _ _ (Right v) :< R _ _ (Left s))
  = pure [ Subst.ofSigil v s ]
assignOf (R _ _ (Left s) :< R _ _ (Right v))
  = pure [ Subst.ofSigil v s ]
-- N.B. we know from the previous phase that common alternatives have been factored out.
assignOf (V r1 :=: V r2)
  | Row.var r1 /= Row.var r2
  , [] <- Row.common r1 r2
  = case (Row.var r1, Row.var r2) of
    (Just x, Nothing) -> pure [Subst.ofRow x r2]
    (Nothing, Just x) -> pure [Subst.ofRow x r1]
    (Just x , Just y) -> do v <- lift solvFresh
                            pure [ Subst.ofRow x (r2 { Row.var = Just v })
                                 , Subst.ofRow y (r1 { Row.var = Just v })
                                 ]

-- N.B. we know from the previous phase that common fields have been factored out.
assignOf (R _ r1 s1 :=: R _ r2 s2)
  | Row.var r1 /= Row.var r2, s1 == s2
  , [] <- Row.common r1 r2
  = case (Row.var r1, Row.var r2) of
    (Just x, Nothing) -> pure [Subst.ofRow x r2]
    (Nothing, Just x) -> pure [Subst.ofRow x r1]
    (Just x , Just y) -> do v <- lift solvFresh
                            pure [ Subst.ofRow x (r2 { Row.var = Just v })
                                 , Subst.ofRow y (r1 { Row.var = Just v })
                                 ]

-- Assign unification variables for recursive parameters
assignOf (R rp1 _ _ :=: R rp2 _ _)
  = case (rp1,rp2) of
      (Mu _, UP x) -> pure [Subst.ofRecPar x rp1]
      (UP x, Mu _) -> pure [Subst.ofRecPar x rp2]
      (UP x, None) -> pure [Subst.ofRecPar x rp2]
      (None, UP x) -> pure [Subst.ofRecPar x rp1]
      _            -> empty 

assignOf (R rp1 _ _ :< R rp2 _ _ )
  = case (rp1,rp2) of
      (Mu _, UP x) -> pure [Subst.ofRecPar x rp1]
      (UP x, Mu _) -> pure [Subst.ofRecPar x rp2]
      (UP x, None) -> pure [Subst.ofRecPar x rp2]
      (None, UP x) -> pure [Subst.ofRecPar x rp1]
      _            -> empty 

-- Unboxed records are not recursive
assignOf (UnboxedNotRecursive (R (UP x) _ (Left Unboxed))) 
  = pure [Subst.ofRecPar x None]

assignOf _ = empty


notOccurs :: Int -> TCType -> Bool
notOccurs a tau = a `notElem` unifVars tau

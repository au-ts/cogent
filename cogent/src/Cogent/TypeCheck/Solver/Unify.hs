--
-- Copyright 2019, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

module Cogent.TypeCheck.Solver.Unify where 

import           Cogent.Common.Syntax
import           Cogent.Common.Types
import           Cogent.Surface
import           Cogent.TypeCheck.Base 
import qualified Cogent.TypeCheck.Row            as Row
import           Cogent.TypeCheck.Solver.Goal 
import           Cogent.TypeCheck.Solver.Monad
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
import qualified Cogent.TypeCheck.Subst          as Subst

import Control.Applicative
import Control.Monad.Trans.Maybe
import Control.Monad.Writer
import Data.Foldable (asum)
import Lens.Micro
import Lens.Micro.Mtl


import Debug.Trace
import Text.PrettyPrint.ANSI.Leijen hiding (empty, indent, tupled, (<$>))

-- | The unify phase, which seeks out equality constraints to solve via substitution.
unify ::  Rewrite.RewriteT TcSolvM [Goal]
unify = Rewrite.rewrite' $ \cs -> do
           as <- asum (map (assignOf . view goal) cs)
           tell as
           pure (foldr (\a -> map (goal %~ Subst.applyC a)) cs as)

assignOf :: Constraint -> MaybeT TcSolvM [Subst.Subst]
assignOf (U a :=: tau) | rigid tau, a `notOccurs` tau = pure [Subst.ofType a tau]
assignOf (tau :=: U a) | rigid tau, a `notOccurs` tau = pure [Subst.ofType a tau]

assignOf (R _ (Right v) :=: R _ (Left s))
  = pure [ Subst.ofSigil v s ]
assignOf (R _ (Left s) :=: R _ (Right v))
  = pure [ Subst.ofSigil v s ]
assignOf (R _ (Right v) :< R _ (Left s))
  = pure [ Subst.ofSigil v s ]
assignOf (R _ (Left s) :< R _ (Right v))
  = pure [ Subst.ofSigil v s ]
-- N.B. Only rows with a unification variable and no known entries lead to
-- equality constraints (see Equate phase). Hence, the collection of common
-- fields is necessarily empty.
assignOf (V r1 :=: V r2)
  | Row.var r1 /= Row.var r2
  , [] <- Row.common r1 r2
  = case (Row.var r1, Row.var r2) of
    (Just x, Nothing) -> pure [Subst.ofRow x r2]
    (Nothing, Just x) -> pure [Subst.ofRow x r1]
    (Just x , Just y) ->
      do v <- lift solvFresh
         pure [ Subst.ofRow x (Row.incomplete (Row.entries r2) v)
              , Subst.ofRow y (Row.incomplete (Row.entries r1) v)
              ]
assignOf (R r1 s1 :=: R r2 s2)
  | Row.var r1 /= Row.var r2, s1 == s2
  , [] <- Row.common r1 r2
  = case (Row.var r1, Row.var r2) of
    (Just x, Nothing) -> pure [Subst.ofRow x r2]
    (Nothing, Just x) -> pure [Subst.ofRow x r1]
    (Just x , Just y) ->
      do v <- lift solvFresh
         pure [ Subst.ofRow x (Row.incomplete (Row.entries r2) v)
              , Subst.ofRow y (Row.incomplete (Row.entries r1) v)
              ]

assignOf _ = empty


notOccurs :: Int -> TCType -> Bool
notOccurs a tau = a `notElem` unifVars tau

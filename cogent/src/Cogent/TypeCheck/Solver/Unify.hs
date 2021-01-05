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
import           Cogent.Compiler
import           Cogent.Dargent.DefaultGen
import           Cogent.Dargent.TypeCheck
import           Cogent.Surface
import qualified Cogent.TypeCheck.ARow           as ARow
import           Cogent.TypeCheck.Base
import qualified Cogent.TypeCheck.LRow           as LRow
import qualified Cogent.TypeCheck.Row            as Row
import           Cogent.TypeCheck.Solver.Goal
import           Cogent.TypeCheck.Solver.Monad
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
import qualified Cogent.TypeCheck.Subst          as Subst
import           Cogent.TypeCheck.Util
import           Cogent.Util

import Control.Applicative
import Control.Monad.Trans.Maybe
import Control.Monad.Writer
import Data.Foldable (asum)
import qualified Data.IntMap as IM (null)
import Lens.Micro
import Lens.Micro.Mtl
import Text.PrettyPrint.ANSI.Leijen hiding (empty, indent, tupled, (<$>))

import Debug.Trace

-- | The unify phase, which seeks out equality constraints to solve via substitution.
unify :: Rewrite.RewriteT TcSolvM [Goal]
unify = Rewrite.rewrite' $ \cs -> do
           as <- asum (map (assignOf . view goal) cs)
           tell as
           traceTc "solver" (text "Unify writes subst:" <+> pretty as)
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
-- N.B. Only rows with a unification variable and no known entries lead to
-- equality constraints (see Equate phase). Hence, the collection of common
-- fields is necessarily empty.
#ifdef BUILTIN_ARRAYS
-- [NOTE: solving 'A' types]
-- For 'A' types, we need to first solve the sigil, and later it can get
-- simplified to constraints about the element types and lengths. / zilinc
assignOf (A _ _ (Left s) _ :=: A _ _ (Right v) _)
  = pure [ Subst.ofSigil v s ]
assignOf (A _ _ (Right v) _ :=: A _ _ (Left s) _)
  = pure [ Subst.ofSigil v s ]
assignOf (A _ _ (Left s) _ :< A _ _ (Right v) _)
  = pure [ Subst.ofSigil v s ]
assignOf (A _ _ (Right v) _ :< A _ _ (Left s) _)
  = pure [ Subst.ofSigil v s ]
assignOf (A _ _ _ (Left h) :=: A _ _ _ (Right v))
  = pure [ Subst.ofHole v h ]
assignOf (A _ _ _ (Right v) :=: A _ _ _ (Left h))
  = pure [ Subst.ofHole v h ]
#endif

-- N.B. we know from the previous phase that common alternatives have been factored out.
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
assignOf (R _ r1 s1 :=: R _ r2 s2)
  | Row.var r1 /= Row.var r2
  , [] <- Row.common r1 r2
  , s1 == s2
  = case (Row.var r1, Row.var r2) of
    (Just x, Nothing) -> pure [Subst.ofRow x r2]
    (Nothing, Just x) -> pure [Subst.ofRow x r1]
    (Just x , Just y) ->
      do v <- lift solvFresh
         pure [ Subst.ofRow x (Row.incomplete (Row.entries r2) v)
              , Subst.ofRow y (Row.incomplete (Row.entries r1) v)
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

assignOf (l1 :~< l2) = assignOfL l1 l2

assignOf (TLDU n :~ t) | Just l <- genDefaultLayout t = pure [Subst.ofLayout n l]

#ifdef BUILTIN_ARRAYS
-- TODO: This will be moved to a separately module for SMT-solving. Eventually the results
-- returned from the solver will be a Subst object. / zilinc
assignOf (Arith (SE t (PrimOp "==" [SU _ x, e]))) | null (unknownsE e)
  = pure [ Subst.ofExpr x e ]
assignOf (Arith (SE t (PrimOp "==" [e, SU _ x]))) | null (unknownsE e)
  = pure [ Subst.ofExpr x e ]
#endif

-- Unboxed records are not recursive
assignOf (UnboxedNotRecursive (R (UP x) _ (Left Unboxed))) 
  = pure [Subst.ofRecPar x None]

assignOf _ = empty

assignOfL :: TCDataLayout -> TCDataLayout -> MaybeT TcSolvM [Subst.Subst]
assignOfL (TLU n) (TL l) = pure [Subst.ofLayout n (TL l)]
assignOfL (TL l) (TLU n) = pure [Subst.ofLayout n (TL l)]
assignOfL (TLU _) (TLU _) = empty
#ifdef BUILTIN_ARRAYS
assignOfL (TLArray e1 _) (TLArray e2 _) = assignOfL e1 e2
#endif
assignOfL _ _ = empty

notOccurs :: Int -> TCType -> Bool
notOccurs a tau = a `notElem` unifVars tau

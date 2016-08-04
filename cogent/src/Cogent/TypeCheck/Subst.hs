--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

module Cogent.TypeCheck.Subst where

import Cogent.TypeCheck.Base
import qualified Data.IntMap as M
import Data.Monoid
import Prelude hiding (lookup)
import Data.Maybe

newtype Subst = Subst (M.IntMap TCType)

lookup :: Subst -> Int -> TCType
lookup (Subst m) i = fromMaybe (U i) (M.lookup i m)

instance Monoid Subst where
  mempty = Subst M.empty
  mappend a@(Subst a') b@(Subst b')
    = Subst (fmap (apply b) a' <> fmap (apply a) b')

apply :: Subst -> TCType -> TCType
apply = forFlexes . lookup

applyAlts :: Subst -> [Alt TCTypedName TCExpr] -> [Alt TCTypedName TCExpr]
applyAlts = map . applyAlt

applyAlt :: Subst -> Alt TCTypedName TCExpr -> Alt TCTypedName TCExpr
applyAlt s = fmap (applyE s) . ffmap (fmap (apply s))

applyCtx :: Subst -> ErrorContext -> ErrorContext
applyCtx s (SolvingConstraint c) = SolvingConstraint (applyC s c)
applyCtx s (InExpression e t) = InExpression e (apply s t)
applyCtx s c = c

applyErr :: Subst -> TypeError -> TypeError
applyErr s (TypeMismatch t1 t2)     = TypeMismatch (apply s t1) (apply s t2)
applyErr s (RequiredTakenField f t) = RequiredTakenField f (apply s t)
applyErr s (TypeNotShareable t m)   = TypeNotShareable (apply s t) m
applyErr s (TypeNotEscapable t m)   = TypeNotEscapable (apply s t) m
applyErr s (TypeNotDiscardable t m) = TypeNotDiscardable (apply s t) m
applyErr s (PatternsNotExhaustive t ts) = PatternsNotExhaustive (apply s t) ts
applyErr s (UnsolvedConstraint c) = UnsolvedConstraint (applyC s c)
applyErr s (NotAFunctionType t) = NotAFunctionType (apply s t)
applyErr s e = e

applyC :: Subst -> Constraint -> Constraint
applyC s (a :< b) = apply s a :< apply s b
applyC s (a :<~ b) = apply s a :<~ apply s b
applyC s (a :& b) = applyC s a :& applyC s b
applyC s (a :@ c) = applyC s a :@ applyCtx s c
applyC s (Share t m) = Share (apply s t) m
applyC s (Drop t m) = Drop (apply s t) m
applyC s (Escape t m) = Escape (apply s t) m
applyC s (Unsat e) = Unsat (applyErr s e)
applyC s Sat = Sat
applyC s (Exhaustive t ps) = Exhaustive (apply s t) (fmap (fmap (fmap (apply s))) ps)

singleton :: Int -> TCType -> Subst
singleton i t = Subst (M.fromList [(i, t)])


null :: Subst -> Bool
null (Subst x) = M.null x

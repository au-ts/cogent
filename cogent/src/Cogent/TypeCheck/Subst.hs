--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE LambdaCase #-}

module Cogent.TypeCheck.Subst where

import Cogent.Common.Syntax (VarName)
import Cogent.Common.Types
import Cogent.Compiler (__impossible)
import qualified Cogent.Context as C
import Cogent.Dargent.TypeCheck
import Cogent.Surface
import qualified Cogent.TypeCheck.ARow as ARow
import Cogent.TypeCheck.Base
import qualified Cogent.TypeCheck.Row as Row
import Cogent.Util

import Control.Arrow (first, left)
import Data.Bifunctor (second)
import qualified Data.IntMap as IM
import Data.Maybe
import Data.Monoid hiding (Alt)
import Prelude hiding (lookup)

import Debug.Trace

data AssignResult = Type TCType
                  | Sigil (Sigil (Maybe TCDataLayout))
                  | Row (Either (Row.Row TCType) Row.Shape)
                  | Taken Taken
                  | Layout' TCDataLayout
                    --    ^ to distinguish with Layout from Cogent.Dargent.Core
#ifdef REFINEMENT_TYPES
                  | ARow (ARow.ARow TCExpr)
                  | Hole (Maybe TCSExpr)
                  | Expr TCSExpr
#endif
                  | RecP RP
                  deriving Show

newtype Subst = Subst (IM.IntMap AssignResult)
              deriving Show

ofType :: Int -> TCType -> Subst
ofType i t = Subst (IM.fromList [(i, Type t)])

ofRow :: Int -> Row.Row TCType -> Subst 
ofRow i t = Subst (IM.fromList [(i, Row $ Left t)])

#ifdef REFINEMENT_TYPES
ofARow :: Int -> ARow.ARow TCExpr -> Subst
ofARow i t = Subst (IM.fromList [(i, ARow t)])

ofHole :: Int -> Maybe TCSExpr -> Subst
ofHole i h = Subst (IM.fromList [(i, Hole h)])
#endif

ofShape :: Int -> Row.Shape -> Subst
ofShape i t = Subst (IM.fromList [(i, Row $ Right t)])

ofSigil :: Int -> Sigil (Maybe TCDataLayout) -> Subst
ofSigil i t = Subst (IM.fromList [(i, Sigil t)])

#ifdef REFINEMENT_TYPES
ofExpr :: Int -> TCSExpr -> Subst
ofExpr i e = Subst (IM.fromList [(i, Expr e)])
#endif

ofLayout :: Int -> TCDataLayout -> Subst
ofLayout i l = Subst (IM.fromList [(i, Layout' l)])

ofRecPar :: Int -> RP -> Subst
ofRecPar i t = Subst (IM.fromList [(i, RecP t)])

null :: Subst -> Bool
null (Subst x) = IM.null x

#if __GLASGOW_HASKELL__ < 803
instance Monoid Subst where
  mempty = Subst IM.empty
  mappend (Subst a) (Subst b) = Subst (a <> b)
#else
instance Semigroup Subst where
  Subst a <> Subst b = Subst (a <> b)
instance Monoid Subst where
  mempty = Subst IM.empty
#endif

apply :: Subst -> TCType -> TCType
apply (Subst f) (U x)
  | Just (Type t) <- IM.lookup x f
  = apply (Subst f) t
  | otherwise
  = U x
apply sub@(Subst f) (V r)
  | Just rv <- Row.var r
  , Just (Row e) <- IM.lookup rv f =
    -- Expand an incomplete row with some more entries (and a fresh row
    -- variable), or close an incomplete row by assigning an ordering (a
    -- shape) to its fields.
    case e of
      Left r' -> apply sub (V (Row.expand r r'))
      Right sh -> apply sub (V (Row.close r sh))
apply sub@(Subst f) (R rp r s)
  | Just rv <- Row.var r
  , Just (Row e) <- IM.lookup rv f =
    case e of
      Left  r' -> apply sub (R rp (Row.expand r r') s)
      Right sh -> apply sub (R rp (Row.close  r sh) s)
apply (Subst f) t@(R rp r (Right x))
  | Just (Sigil s) <- IM.lookup x f = apply (Subst f) (R rp r (Left s))
apply f (V x) = V (fmap (apply f) x)
apply (Subst f) (R (UP x) r s)
  | Just (RecP rp) <- IM.lookup x f = apply (Subst f) (R rp r s)
apply f (R rp x s) = R rp (fmap (apply f) x) s
#ifdef REFINEMENT_TYPES
apply (Subst f) (A t l (Right x) mhole)
  | Just (Sigil s) <- IM.lookup x f = apply (Subst f) (A t l (Left s) mhole)
apply (Subst f) (A t l s (Right x))
  | Just (Hole mh) <- IM.lookup x f = apply (Subst f) (A t l s (Left mh))
apply f (A x l s tkns) = A (apply f x) (applySE f l) s (left (fmap $ applySE f) tkns)
apply f (T x) = T (fffmap (applySE f) $ fmap (apply f) x)
#else
apply f (T x) = T (fmap (apply f) x)
#endif
apply f (Synonym n ts) = Synonym n (fmap (apply f) ts)


applyAlts :: Subst -> [Alt TCPatn TCExpr] -> [Alt TCPatn TCExpr]
applyAlts = map . applyAlt

applyAlt :: Subst -> Alt TCPatn TCExpr -> Alt TCPatn TCExpr
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
applyErr s (UnsolvedConstraint env c os) = UnsolvedConstraint (applyGoalEnv s env) (applyC s c) os
applyErr s (NotAFunctionType t) = NotAFunctionType (apply s t)
applyErr s e = e

applyWarn :: Subst -> TypeWarning -> TypeWarning
applyWarn s (UnusedLocalBind v) = UnusedLocalBind v
applyWarn _ w = w

applyL :: Subst -> TCDataLayout -> TCDataLayout
applyL (Subst m) (TLU n)
  | Just (Layout' l) <- IM.lookup n m = applyL (Subst m) l
  | otherwise = TLU n
applyL s (TLRecord fs) = TLRecord $ (\(a,b,c) -> (a,b,applyL s c)) <$> fs
applyL s (TLVariant e fs) = TLVariant (applyL s e) $
                                      (\(a,b,c,d) -> (a,b,c,applyL s d)) <$> fs
#ifdef REFINEMENT_TYPES
applyL s (TLArray e p) = TLArray (applyL s e) p
#endif
applyL s (TLOffset e n) = TLOffset (applyL s e) n
applyL s l = l

applyGoalEnv :: Subst -> ConstraintEnv -> ConstraintEnv
#ifdef REFINEMENT_TYPES
applyGoalEnv s (g, es) = (applyGamma s g, fmap (applySE s) es)
#else
applyGoalEnv s (g, es) = (applyGamma s g, es)
#endif
  where
    applyGamma s m = fmap (first $ apply s) m

applyC :: Subst -> Constraint -> Constraint
applyC s (a :< b) = apply s a :< apply s b
applyC s (a :=: b) = apply s a :=: apply s b
applyC s (a :& b) = applyC s a :& applyC s b
applyC s (a :@ c) = applyC s a :@ applyCtx s c
applyC s (Upcastable a b) = apply s a `Upcastable` apply s b
applyC s (Share t m) = Share (apply s t) m
applyC s (Drop t m) = Drop (apply s t) m
applyC s (Escape t m) = Escape (apply s t) m
#ifdef REFINEMENT_TYPES
applyC s (Arith e) = Arith $ applySE s e
-- applyC s (a :-> b) = applyC s a :-> applyC s b
applyC s (env :|- a) = applyGoalEnv s env :|- applyC s a
applyC s (BaseType t) = BaseType $ apply s t
#endif
applyC s (Unsat e) = Unsat $ applyErr s e
applyC s (SemiSat w) = SemiSat (applyWarn s w)
applyC s Sat = Sat
applyC s (Exhaustive t ps) = Exhaustive (apply s t) ps
applyC s (UnboxedNotRecursive r) = UnboxedNotRecursive (apply s r)
applyC (Subst f) (NotReadOnly (Right x))
  | Just (Sigil s) <- IM.lookup x f = NotReadOnly (Left s)
  | otherwise = NotReadOnly (Right x)
applyC s (NotReadOnly x) = NotReadOnly x
applyC s (Solved t) = Solved (apply s t)
applyC s (IsPrimType t) = IsPrimType (apply s t)
applyC s (l :~  t) = applyL s l :~  apply s t
applyC s (l :~< m) = applyL s l :~< applyL s m
applyC s (a :~~ b) = apply s a :~~ apply s b

#ifdef REFINEMENT_TYPES
applySE :: Subst -> TCSExpr -> TCSExpr
applySE (Subst f) (SU t x)
  | Just (Expr e) <- IM.lookup x f
  = applySE (Subst f) e
  | otherwise
  = SU t x
applySE (Subst f) (HApp x v vs)
  | Just (Expr e) <- IM.lookup x f
  = applySE (Subst f) e  -- FIXME
  | otherwise
  = HApp x v vs
applySE s (SE t e) = SE (apply s t)
                          ( fmap (applySE s)
                          $ fffmap (fmap (apply s))
                          $ ffffmap (fmap (apply s))
                          $ fffffmap (apply s) e)
#endif

applyE :: Subst -> TCExpr -> TCExpr
applyE s (TE t e l) = TE (apply s t)
                         ( fmap (applyE s)
                         $ ffmap (applyL s)
                         $ fffmap (fmap (apply s))
                         $ ffffmap (fmap (apply s))
                         $ fffffmap (apply s) e)
                         l

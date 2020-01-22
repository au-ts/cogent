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

import Cogent.Common.Types
import Cogent.Compiler (__impossible)
import Cogent.Surface
import qualified Cogent.TypeCheck.ARow as ARow
import Cogent.TypeCheck.Base
import qualified Cogent.TypeCheck.Row as Row
import Cogent.Util

import qualified Data.IntMap as M
import qualified Data.Map as DM
import Data.Bifunctor (second)
import Data.Maybe
import Data.Monoid hiding (Alt)
import Prelude hiding (lookup)

import Debug.Trace

data AssignResult = Type TCType
                  | Sigil (Sigil (Maybe DataLayoutExpr))
                  | Row (Either (Row.Row TCType) Row.Shape)
                  | Taken Taken
#ifdef BUILTIN_ARRAYS
                  | ARow (ARow.ARow TCExpr)
                  | Expr TCSExpr
#endif
                  deriving Show

newtype Subst = Subst (M.IntMap AssignResult)
              deriving Show

ofType :: Int -> TCType -> Subst
ofType i t = Subst (M.fromList [(i, Type t)])

ofRow :: Int -> Row.Row TCType -> Subst 
ofRow i t = Subst (M.fromList [(i, Row $ Left t)])

#ifdef BUILTIN_ARRAYS
ofARow :: Int -> ARow.ARow TCExpr -> Subst
ofARow i t = Subst (M.fromList [(i, ARow t)])
#endif

ofSigil :: Int -> Sigil (Maybe DataLayoutExpr) -> Subst
ofSigil i t = Subst (M.fromList [(i, Sigil t)])

ofShape :: Int -> Row.Shape -> Subst
ofShape i t = Subst (M.fromList [(i, Row $ Right t)])

#ifdef BUILTIN_ARRAYS
ofExpr :: Int -> TCSExpr -> Subst
ofExpr i e = Subst (M.fromList [(i, Expr e)])
#endif

null :: Subst -> Bool
null (Subst x) = M.null x

#if __GLASGOW_HASKELL__ < 803
instance Monoid Subst where
  mempty = Subst M.empty
  mappend (Subst a) (Subst b) = Subst (a <> b)
#else
instance Semigroup Subst where
  Subst a <> Subst b = Subst (a <> b)
instance Monoid Subst where
  mempty = Subst M.empty
#endif

apply :: Subst -> TCType -> TCType
apply (Subst f) (U x)
  | Just (Type t) <- M.lookup x f
  = apply (Subst f) t
  | otherwise
  = U x
apply sub@(Subst f) (V r)
  | Just rv <- Row.var r
  , Just (Row e) <- M.lookup rv f =
    -- Expand an incomplete row with some more entries (and a fresh row
    -- variable), or close an incomplete row by assigning an ordering (a
    -- shape) to its fields.
    case e of
      Left r' -> apply sub (V (Row.expand r r'))
      Right sh -> apply sub (V (Row.close r sh))
apply sub@(Subst f) (R r s)
  | Just rv <- Row.var r
  , Just (Row e) <- M.lookup rv f =
    case e of
      Left r' -> apply sub (R (Row.expand r r') s)
      Right sh -> apply sub (R (Row.close r sh) s)
apply (Subst f) t@(R r (Right x))
  | Just (Sigil s) <- M.lookup x f = apply (Subst f) (R r (Left s))
apply f (V x) = V (fmap (apply f) x)
apply f (R x s) = R (fmap (apply f) x) s
#ifdef BUILTIN_ARRAYS
apply (Subst f) (A t l (Right x) mhole)
  | Just (Sigil s) <- M.lookup x f = apply (Subst f) (A t l (Left s) mhole)
apply f (A x l s tkns) = A (apply f x) (applySE f l) s (fmap (applySE f) tkns)
apply f (T x) = T (ffmap (applySE f) $ fmap (apply f) x)
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
applyErr s (UnsolvedConstraint c os) = UnsolvedConstraint (applyC s c) os
applyErr s (NotAFunctionType t) = NotAFunctionType (apply s t)
applyErr s e = e

applyWarn :: Subst -> TypeWarning -> TypeWarning
applyWarn s (UnusedLocalBind v) = UnusedLocalBind v
applyWarn _ w = w

applyC :: Subst -> Constraint -> Constraint
applyC s (a :< b) = apply s a :< apply s b
applyC s (a :=: b) = apply s a :=: apply s b
applyC s (a :& b) = applyC s a :& applyC s b
applyC s (a :@ c) = applyC s a :@ applyCtx s c
applyC s (Upcastable a b) = apply s a `Upcastable` apply s b
applyC s (Share t m) = Share (apply s t) m
applyC s (Drop t m) = Drop (apply s t) m
applyC s (Escape t m) = Escape (apply s t) m
#ifdef BUILTIN_ARRAYS
applyC s (Arith e) = Arith $ applySE s e
#endif
applyC s (Unsat e) = Unsat $ applyErr s e
applyC s (SemiSat w) = SemiSat (applyWarn s w)
applyC s Sat = Sat
applyC s (Exhaustive t ps) = Exhaustive (apply s t) ps
applyC s (Solved t) = Solved (apply s t)
applyC s (IsPrimType t) = IsPrimType (apply s t)

#ifdef BUILTIN_ARRAYS
applySE :: Subst -> TCSExpr -> TCSExpr
applySE (Subst f) (SU t x)
  | Just (Expr e) <- M.lookup x f
  = applySE (Subst f) e
  | otherwise
  = SU t x
applySE s (SE t e) = SE (apply s t)
                          ( fmap (applySE s)
                          $ ffmap (fmap (apply s))
                          $ fffmap (fmap (apply s))
                          $ ffffmap (apply s) e)
#endif

applyE :: Subst -> TCExpr -> TCExpr
applyE s (TE t e l) = TE (apply s t)
                         ( fmap (applyE s)
                         $ ffmap (fmap (apply s))
                         $ fffmap (fmap (apply s))
                         $ ffffmap (apply s) e)
                         l

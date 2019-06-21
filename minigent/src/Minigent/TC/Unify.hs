-- |
-- Module      : Minigent.TC.Unify
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- The unify phase of the constraint solver.
--
-- May be used qualified or unqualified.
{-# LANGUAGE FlexibleContexts #-}
module Minigent.TC.Unify
  ( -- * Unify Phase
    unify
  , -- * Assigns
    Assign (..)
  , substAssign
  ) where

import Minigent.Syntax
import Minigent.Syntax.Utils
import qualified Minigent.Syntax.Utils.Rewrite as Rewrite

import Minigent.Fresh
import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import Control.Applicative
import Data.Foldable (asum)

-- | An assignment to a unification variable (standing for various things)
data Assign = TyAssign VarName Type
            | RowAssign VarName Row
            | SigilAssign VarName Sigil

-- | Apply an assignment to a unification variable to a type.
substAssign :: Assign -> Rewrite.Rewrite Type
substAssign (TyAssign v t) = substUV (v, t)
substAssign (RowAssign v t) = substRowV (v, t)
substAssign (SigilAssign v t) = substSigilV (v, t)


-- | The unify phase, which seeks out equality constraints to solve via substitution.
unify :: (MonadFresh VarName m, MonadWriter [Assign] m) => Rewrite.Rewrite' m [Constraint]
unify = Rewrite.rewrite' $ \cs -> do
           a <- asum (map assignOf cs)
           tell a
           pure (map (constraintTypes (traverseType (foldMap substAssign a))) cs)

assignOf :: (MonadFresh VarName m, MonadWriter [Assign] m) => Constraint -> MaybeT m [Assign]
assignOf (UnifVar a :=: tau) | rigid tau && (a `notOccurs` tau) = pure [TyAssign a tau]
assignOf (tau :=: UnifVar a) | rigid tau && (a `notOccurs` tau) = pure [TyAssign a tau]

assignOf (Record _ _ (UnknownSigil v) :=: Record _ _ s)
  | s `elem` [ReadOnly, Unboxed, Writable]
  = pure [ SigilAssign v s ]
assignOf (Record _ _ s :=: Record _ _ (UnknownSigil v))
  | s `elem` [ReadOnly, Unboxed, Writable]
  = pure [ SigilAssign v s ]
assignOf (Record _ _ (UnknownSigil v) :< Record _ _ s)
  | s `elem` [ReadOnly, Unboxed, Writable]
  = pure [ SigilAssign v s ]
assignOf (Record _ _ s :< Record _ _ (UnknownSigil v))
  | s `elem` [ReadOnly, Unboxed, Writable]
  = pure [ SigilAssign v s ]
-- N.B. we know from the previous phase that common alternatives have been factored out.
assignOf (Variant r1 :=: Variant r2)
  | rowVar r1 /= rowVar r2
  = case (rowVar r1, rowVar r2) of
    (Just x, Nothing) -> pure [RowAssign x r2]
    (Nothing, Just x) -> pure [RowAssign x r1]
    (Just x , Just y) -> do v <- lift fresh
                            pure [ RowAssign x (r2 { rowVar = Just v })
                                 , RowAssign y (r1 { rowVar = Just v })
                                 ]

-- N.B. we know from the previous phase that common fields have been factored out.
assignOf (Record _ r1 s1 :=: Record _ r2 s2)
  | rowVar r1 /= rowVar r2, s1 == s2
  = case (rowVar r1, rowVar r2) of
    (Just x, Nothing) -> pure [RowAssign x r2]
    (Nothing, Just x) -> pure [RowAssign x r1]
    (Just x , Just y) -> do v <- lift fresh
                            pure [ RowAssign x (r2 { rowVar = Just v })
                                 , RowAssign y (r1 { rowVar = Just v })
                                 ]
assignOf _ = empty


notOccurs :: VarName -> Type -> Bool
notOccurs a tau = a `notElem` typeUVs tau

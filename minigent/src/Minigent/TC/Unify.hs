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
  ) where

import Minigent.Syntax
import Minigent.Syntax.Utils
import qualified Minigent.Syntax.Utils.Row as Row
import qualified Minigent.Syntax.Utils.Rewrite as Rewrite
import Minigent.TC.Assign
import Minigent.Fresh
import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import Control.Applicative
import Data.Foldable (asum)

import Debug.Trace

import Minigent.Syntax.PrettyPrint


-- | The unify phase, which seeks out equality constraints to solve via substitution.
unify :: (MonadFresh VarName m, MonadWriter [Assign] m) => Rewrite.Rewrite' m [Constraint]
unify = Rewrite.rewrite' $ \cs -> do
           a <- asum (map assignOf cs)
           tell a
           --traceM ("About to perform the substitutions:\n" ++ "[\n" ++ debugAssigns a ++ "]")
           pure (map (constraintTypes (normaliseType (foldMap substAssign a))) cs)

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
assignOf (Record (UnknownParameter x) _ s :< Record _ _ Unboxed) 
  = pure [RecParAssign x None]
-- N.B. we know from the previous phase that common alternatives have been factored out.
assignOf (Variant r1 :=: Variant r2)
  | rowVar r1 /= rowVar r2
  , [] <- Row.common r1 r2
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
  , [] <- Row.common r1 r2
  = case (rowVar r1, rowVar r2) of
    (Just x, Nothing) -> pure [RowAssign x r2]
    (Nothing, Just x) -> pure [RowAssign x r1]
    (Just x , Just y) -> do v <- lift fresh
                            pure [ RowAssign x (r2 { rowVar = Just v })
                                 , RowAssign y (r1 { rowVar = Just v })
                                 ]

-- TODO: Generalise
assignOf (Record n1 _ _ :=: Record n2 _ _)
  = case (n1,n2) of
      (Rec _, UnknownParameter x) -> pure [RecParAssign x n1]
      (UnknownParameter x, Rec _) -> pure [RecParAssign x n2]
      (UnknownParameter x, None)  -> pure [RecParAssign x None]
      (None, UnknownParameter x)  -> pure [RecParAssign x None]
      _              -> empty 

assignOf (Record n1 _ _ :< Record n2 _ _)
  = case (n1,n2) of
      (Rec _, UnknownParameter x) -> pure [RecParAssign x n1]
      (UnknownParameter x, Rec _) -> pure [RecParAssign x n2]
      (UnknownParameter x, None)  -> pure [RecParAssign x None]
      (None, UnknownParameter x)  -> pure [RecParAssign x None]
      _              -> empty 

-- If it is discovered that a record is unboxed, we can assign it's
-- unknown parameter to None
assignOf (UnboxedNoRecurse (Record (UnknownParameter x) _ Unboxed))
    = pure [RecParAssign x None]

assignOf (UnRoll t v t' :<  t'') = assignOf (t'  :<  t'')
assignOf (t'' :<  UnRoll t v t') = assignOf (t'' :<  t')

assignOf (UnRoll t v t' :=: t'') = assignOf (t'  :=: t'')
assignOf (t'' :=: UnRoll t v t') = assignOf (t'' :=: t')

assignOf _ = empty


notOccurs :: VarName -> Type -> Bool
notOccurs a tau = a `notElem` typeUVs tau
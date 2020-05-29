-- |
-- Module      : Minigent.TC.SinkFloat
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- The sink/float phase of constraint solving.
--
-- May be used qualified or unqualified.
{-# OPTIONS_GHC -Werror -Wall #-}
{-# LANGUAGE FlexibleContexts, TupleSections, ScopedTypeVariables #-}
module Minigent.TC.SinkFloat
  ( -- * Sink/Float Phase
    sinkFloat
  ) where

import Minigent.Syntax
import qualified Minigent.Syntax.Utils.Row as Row
import qualified Minigent.Syntax.Utils.Rewrite as Rewrite

import Minigent.TC.Assign
import Minigent.Fresh
import Control.Monad.Writer hiding (First(..))
import Control.Monad.Trans.Maybe

import qualified Data.Map as M

-- | The sinkFloat phase propagates the structure of types containing
--   rows (i.e. Records and Variants) through subtyping/equality constraints
sinkFloat :: forall m. (MonadFresh VarName m, MonadWriter [Assign] m) => Rewrite.Rewrite' m [Constraint]
sinkFloat = Rewrite.rewrite' $ \cs -> MaybeT $ do
              substs <- concat <$> traverse genStructSubsts cs
              tell substs
              if null substs
              then return Nothing
              else let (m1,m2,m3,m4) = substsToMapsDisjoint substs
                      -- n.b. if a substitution was generated, that
                      --      substitution will change the constraints when applied
                    in return . Just $ map (substConstraint' m1 m2 m3 m4) cs
  where
    genStructSubsts :: Constraint -> m [Assign]
    -- remove type operators first
    genStructSubsts (Bang t :< v)  = genStructSubsts (t :< v)
    genStructSubsts (v :< Bang t)  = genStructSubsts (v :< t)
    genStructSubsts (Bang t :=: v) = genStructSubsts (t :=: v)
    genStructSubsts (v :=: Bang t) = genStructSubsts (v :=: t)

    -- records
    genStructSubsts (Record n r s :< UnifVar i) = do
      s' <- case s of
        Unboxed -> return Unboxed -- unboxed is preserved by bang, so we may propagate it
        _       -> UnknownSigil <$> fresh
      rowUnifRowSubs (flip (Record n) s') i r

    genStructSubsts (UnifVar i :< Record n r s) = do
      s' <- case s of
        Unboxed -> return Unboxed -- unboxed is preserved by bang, so we may propagate it
        _       -> UnknownSigil <$> fresh
      rowUnifRowSubs (flip (Record n) s') i r

    genStructSubsts (Record _ r1 s1 :< Record _ r2 s2)
      {-
        The most tricky case.
        Untaken is the bottom of the order, Taken is the top.
        If untaken things are in r2, then we can infer they must be in r1.
        If taken things are in r1, then we can infer they must be in r2.
      -}
      | r1new <- Row.rowUntakenEntries r2 `M.difference` rowEntries r1
      , not $ M.null r1new
      , Just r1var <- rowVar r1
        = makeRowRowVarSubsts r1new r1var
      | r2new <- Row.rowTakenEntries r1 `M.difference` rowEntries r2
      , not $ M.null r2new
      , Just r2var <- rowVar r2
        = makeRowRowVarSubsts r2new r2var
      | Unboxed <- s1 , UnknownSigil i <- s2 = return [SigilAssign i Unboxed]
      | UnknownSigil i <- s1 , Unboxed <- s2 = return [SigilAssign i Unboxed]

    -- abstypes
    genStructSubsts (AbsType n s ts :< UnifVar i) = absTypeSubs n s ts i
    genStructSubsts (UnifVar i :< AbsType n s ts) = absTypeSubs n s ts i
    genStructSubsts (AbsType n s ts :=: UnifVar i) = absTypeSubs n s ts i
    genStructSubsts (UnifVar i :=: AbsType n s ts) = absTypeSubs n s ts i

    -- variants
    genStructSubsts (Variant r :< UnifVar i) = rowUnifRowSubs Variant i r
    genStructSubsts (UnifVar i :< Variant r) = rowUnifRowSubs Variant i r
    genStructSubsts (Variant r1 :< Variant r2)
      {-
        The most tricky case.
        Taken is the bottom of the order, Untaken is the top.
        If taken things are in r2, then we can infer they must be in r1.
        If untaken things are in r1, then we can infer they must be in r2.
      -}
      | r1new <- Row.rowTakenEntries r2 `M.difference` rowEntries r1
      , not $ M.null r1new
      , Just r1var <- rowVar r1
        = makeRowRowVarSubsts r1new r1var
      | r2new <- Row.rowUntakenEntries r1 `M.difference` rowEntries r2
      , not $ M.null r2new
      , Just r2var <- rowVar r2
        = makeRowRowVarSubsts r2new r2var

    -- tfun
    genStructSubsts (Function _ _ :< UnifVar i)  = makeFunUnifSubsts i
    genStructSubsts (UnifVar i :< Function _ _)  = makeFunUnifSubsts i
    genStructSubsts (Function _ _ :=: UnifVar i) = makeFunUnifSubsts i
    genStructSubsts (UnifVar i :=: Function _ _) = makeFunUnifSubsts i

    -- primitive types
    genStructSubsts (t@(PrimType _) :< UnifVar i) = return [TyAssign i t]
    genStructSubsts (UnifVar i :< t@(PrimType _)) = return [TyAssign i t]

    -- default
    genStructSubsts _ = return []

    --
    -- helper functions
    --
    rowUnifRowSubs tConstr i r = do
      let es = rowEntries r
      v' <- traverse (const fresh) (rowVar r)
      es' <- traverse (\(Entry n _ tk) -> Entry n <$> (UnifVar <$> fresh) <*> pure tk) es
      return [TyAssign i (tConstr (Row es' v'))]

    makeRowRowVarSubsts rnew rv = do
      rv' <- Just <$> fresh
      rnew' <- traverse (\(Entry n _ tk) -> Entry n <$> (UnifVar <$> fresh) <*> pure tk) rnew
      return [RowAssign rv $ Row rnew' rv']

    absTypeSubs n s ts i = do 
      ts' <- mapM (const (UnifVar <$> fresh)) ts
      return [TyAssign i (AbsType n s ts')]

    makeFunUnifSubsts i = do
      t' <- UnifVar <$> fresh
      u' <- UnifVar <$> fresh
      return [TyAssign i $ Function t' u']

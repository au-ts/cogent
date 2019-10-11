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
import Minigent.Syntax.Utils
import qualified Minigent.Syntax.Utils.Row as Row
import qualified Minigent.Syntax.Utils.Rewrite as Rewrite

import Minigent.TC.Assign
import Minigent.Fresh
import Control.Monad.Writer hiding (First(..))
import Control.Monad.Trans.Maybe
import Control.Applicative
import qualified Data.Map as M

import Data.Semigroup (First(..))

sinkFloat :: forall m. (MonadFresh VarName m, MonadWriter [Assign] m) => Rewrite.Rewrite' m [Constraint]
sinkFloat = Rewrite.rewrite' $ \cs -> do 
               (cs',as) <- tryEach cs
               tell as
               pure (map (constraintTypes (traverseType (foldMap substAssign as))) cs')
  where 
    tryEach :: [Constraint] -> MaybeT m ([Constraint], [Assign])
    tryEach cs =
      MaybeT $ do
        (mas :: [Maybe [Assign]]) <- traverse (runMaybeT . genStructSubst) cs
        let as :: Maybe [Assign]
            as = getFirst <$> (mconcat $ fmap (fmap First) mas :: Maybe (First [Assign]))
        return ((,) cs <$> as)

    genStructSubst :: Constraint -> MaybeT m [Assign]
    -- remove type operators first
    genStructSubst (Bang t :< v)  = genStructSubst (t :< v)
    genStructSubst (v :< Bang t)  = genStructSubst (v :< t)
    genStructSubst (Bang t :=: v) = genStructSubst (t :=: v)
    genStructSubst (v :=: Bang t) = genStructSubst (v :=: t)

    -- records
    genStructSubst (Record r s :< UnifVar i) = do
      s' <- case s of
        Unboxed -> return Unboxed -- unboxed is preserved by bang, so we may propagate it
        _       -> UnknownSigil <$> fresh
      rowUnifRowSubs (flip Record s') i r

    genStructSubst (UnifVar i :< Record r s) = do
      s' <- case s of
        Unboxed -> return Unboxed -- unboxed is preserved by bang, so we may propagate it
        _       -> UnknownSigil <$> fresh
      rowUnifRowSubs (flip Record s') i r

    genStructSubst (Record r1 s1 :< Record r2 s2)
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
      | Unboxed <- s1 , UnknownSigil i <- s2 = return [SigilAssign i Unboxed]
      | UnknownSigil i <- s1 , Unboxed <- s2 = return [SigilAssign i Unboxed]

    -- abstypes
    genStructSubst (AbsType n s ts :< UnifVar i) = absTypeSubs n s ts i
    genStructSubst (UnifVar i :< AbsType n s ts) = absTypeSubs n s ts i
    genStructSubst (AbsType n s ts :=: UnifVar i) = absTypeSubs n s ts i
    genStructSubst (UnifVar i :=: AbsType n s ts) = absTypeSubs n s ts i

    -- variants
    genStructSubst (Variant r :< UnifVar i) = rowUnifRowSubs Variant i r
    genStructSubst (UnifVar i :< Variant r) = rowUnifRowSubs Variant i r
    genStructSubst (Variant r1 :< Variant r2)
      {-
        The most tricky case.
        Untaken is the bottom of the order, Taken is the top.
        If untaken things are in r2, then we can infer they must be in r1.
        If taken things are in r1, then we can infer they must be in r2.
      -}
      | r1new <- Row.rowTakenEntries r2 `M.difference` rowEntries r1
      , not $ M.null r1new
      , Just r1var <- rowVar r1
        = makeRowRowVarSubsts r1new r1var
      | r2new <- Row.rowUntakenEntries r1 `M.difference` rowEntries r2
      , not $ M.null r2new
      , Just r2var <- rowVar r2
        = makeRowRowVarSubsts r2new r2var


    -- primitive types
    genStructSubst (t@(PrimType _) :< UnifVar i) = pure [TyAssign i t]
    genStructSubst (UnifVar i :< t@(PrimType _)) = pure [TyAssign i t]

    -- default
    genStructSubst _ = empty

    --
    -- helper functions
    --
    rowUnifRowSubs tConstr i r = do
      let es = rowEntries r
      v' <- traverse (const fresh) (rowVar r)
      es' <- traverse (\(Entry n _ tk) -> Entry n <$> (UnifVar <$> fresh) <*> pure tk) es
      pure [TyAssign i (tConstr (Row es' v'))]

    makeRowRowVarSubsts rnew rv = do
      rv' <- Just <$> fresh
      rnew' <- traverse (\(Entry n _ tk) -> Entry n <$> (UnifVar <$> fresh) <*> pure tk) rnew
      return [RowAssign rv $ Row rnew' rv']

    absTypeSubs n s ts i = do 
      ts' <- mapM (const (UnifVar <$> fresh)) ts
      return [TyAssign i (AbsType n s ts')]

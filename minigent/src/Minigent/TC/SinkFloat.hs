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
import qualified Data.Map.Merge.Lazy as MMg
import Data.Maybe (catMaybes)

import Data.Semigroup (First(..))

-- | The sinkFloat phase propagates the structure of types containing
--   rows (i.e. Records and Variants) through subtyping/equality constraints
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
    genStructSubst (Record n r _ :< UnifVar i) = do
      s' <- UnknownSigil <$> fresh
      rowUnifRowSubs (flip (Record n) s') i r

    genStructSubst (UnifVar i :< Record n r _) = do
      s' <- UnknownSigil <$> fresh
      rowUnifRowSubs (flip (Record n) s') i r

    genStructSubst (Record _ r1 s1 :< Record _ r2 s2) = do
      {-
        The most tricky case.
        Taken is the bottom of the order, Untaken is the top.
        If taken things are in r2, then we can infer they must be in r1.
        If untaken things are in r1, then we can infer they must be in r2.
      -}
      let fs1 = rowEntries r1
          fs2 = rowEntries r2
      -- construct the missing parts of fs1
      (row1' :: M.Map FieldName Entry) <- makeMissingUnifRow id  fs1 fs2
      -- construct the missing parts of fs2
      (row2' :: M.Map FieldName Entry) <- makeMissingUnifRow not fs2 fs1
      v1' <- fresh
      v2' <- fresh
      let as = catMaybes [ RowAssign <$> rowVar r1 <*> pure (Row row1' (Just v1'))
                         , RowAssign <$> rowVar r2 <*> pure (Row row2' (Just v2'))
                         ]
      if null as
        then empty
        else pure as

    -- abstypes
    genStructSubst (AbsType n s ts :< UnifVar i) = absTypeSubs n s ts i
    genStructSubst (UnifVar i :< AbsType n s ts) = absTypeSubs n s ts i
    genStructSubst (AbsType n s ts :=: UnifVar i) = absTypeSubs n s ts i
    genStructSubst (UnifVar i :=: AbsType n s ts) = absTypeSubs n s ts i

    -- variants
    genStructSubst (Variant r :< UnifVar i) = rowUnifRowSubs Variant i r
    genStructSubst (UnifVar i :< Variant r) = rowUnifRowSubs Variant i r
    genStructSubst (Variant r1 :< Variant r2) = do
      {-
        The most tricky case.
        Untaken is the bottom of the order, Taken is the top.
        If untaken things are in r2, then we can infer they must be in r1.
        If taken things are in r1, then we can infer they must be in r2.
      -}
      let fs1 = rowEntries r1
          fs2 = rowEntries r2
      -- construct the missing parts of fs1
      (row1' :: M.Map FieldName Entry) <- makeMissingUnifRow not fs1 fs2
      -- construct the missing parts of fs2
      (row2' :: M.Map FieldName Entry) <- makeMissingUnifRow id  fs2 fs1
      v1' <- fresh
      v2' <- fresh
      let as = catMaybes [ RowAssign <$> rowVar r1 <*> pure (Row row1' (Just v1'))
                         , RowAssign <$> rowVar r2 <*> pure (Row row2' (Just v2'))
                         ]
      if null as
        then empty
        else pure as


    -- primitive types
    genStructSubst (t@(PrimType p) :< UnifVar i) = pure [TyAssign i t]
    genStructSubst (UnifVar i :< t@(PrimType p)) = pure [TyAssign i t]

    -- default
    genStructSubst _ = empty

    --
    -- helper functions
    --
    rowUnifRowSubs tConstr i r = do
      let es = rowEntries r
      v' <- traverse (const fresh) (rowVar r)
      es' <- traverse (\(Entry n _ tk) -> Entry n <$> (UnifVar <$> fresh) <*> pure tk) es
      s' <- UnknownSigil <$> fresh
      pure [TyAssign i (tConstr (Row es' v'))]

    makeMissingUnifRow :: forall k. Ord k => (Bool -> Bool) -> M.Map k Entry -> M.Map k Entry -> MaybeT m (M.Map k Entry)
    makeMissingUnifRow tkIsOkay mInto mFrom = (MMg.mergeA
      -- handle when mFrom is missing keys from mInto
      MMg.dropMissing
      -- handle when mInto is missing keys from mFrom
      (MMg.traverseMaybeMissing $ \k (Entry n t tk) ->
        if tkIsOkay tk
          -- we want to transfer the field
          then (\i -> Just (Entry n (UnifVar i) tk)) <$> fresh
          -- we don't want to transfer the field
          else pure Nothing)
      -- handle when they are in both
      (MMg.zipWithMaybeAMatched $ \_ _ _ -> pure Nothing)
      mInto
      mFrom)

    absTypeSubs n s ts i = do 
      ts <- mapM (const (UnifVar <$> fresh)) ts
      return [TyAssign i (AbsType n s ts)]

    getTaken   = M.filter (\(Entry _ _ t) -> t)     . Row.entriesMap
    getPresent = M.filter (\(Entry _ _ t) -> not t) . Row.entriesMap
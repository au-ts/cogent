-- |
-- Module      : Minigent.TC.JoinMeet
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- The join/meet phase of constraint solving.
--
-- May be used qualified or unqualified.
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
module Minigent.TC.JoinMeet (joinMeet) where

import Minigent.Syntax.Utils
import Minigent.Syntax
import Minigent.Fresh
import qualified Minigent.Syntax.Utils.Row as Row
import qualified Minigent.Syntax.Utils.Rewrite as Rewrite

import Control.Monad
import Control.Applicative
import qualified Data.Set as S
import qualified Data.Map as M
import Data.List (partition)

import Debug.Trace

data Candidate = Meet Type Type Type
               | Join Type Type Type

-- | Find pairs of subtyping constraints that involve the same unification variable
--   on the right or left hand side, and compute the join/meet to simplify the
--   constraint graph.
joinMeet :: (Monad m, MonadFresh VarName m) => Rewrite.Rewrite' m [Constraint]
joinMeet = Rewrite.withTransform find $ \c -> case c of

-- TODO: Fix this

  Meet v (Function t1 t2) (Function r1 r2) -> do
    b1 <- UnifVar <$> fresh
    b2 <- UnifVar <$> fresh
    pure [ v :< Function b1 b2
         , b2 :< r2, b2 :< t2
         , t1 :< b1, r1 :< b1
         ]

  Meet v (Variant r1) (Variant r2) | r1 /= r2 -> do
    guard (Row.compatible r1 r2)
    r <- Row.union Row.mostTaken r1 r2
    pure [v :< Variant r, Variant r :< Variant r1, Variant r :< Variant r2 ]

  Meet v (Variant r1) (Variant r2) | r1 == r2 -> do
    pure [v :< Variant r1 ]

  Join v (Variant r1) (Variant r2) | r1 /= r2 -> do
    guard (Row.compatible r1 r2)
    r <- Row.union Row.leastTaken r1 r2
    pure [Variant r :< v, Variant r1 :< Variant r, Variant r2 :< Variant r ]

  Join v (Variant r1) (Variant r2) | r1 == r2 -> do
    pure [Variant r1 :< v ]

  Meet v (Record _ r1 s1) (Record _ r2 s2) | r1 /= r2 -> do
    guard (Row.compatible r1 r2)
    guard (sigilsCompatible s1 s2)
    r <- Row.union Row.leastTaken r1 r2
    s <- UnknownSigil <$> fresh
    pure [v :< Record undefined r s, Record undefined r s :< Record undefined r1 s1, Record undefined r s :< Record undefined r2 s2 ]

  Meet v (Record _ r1 s1) (Record _ r2 s2) | r1 == r2 && s1 == s2 -> do
    pure [v :< Record undefined r1 s1]

  Join v (Record _ r1 s1) (Record _ r2 s2) | r1 /= r2 -> do
    guard (Row.compatible r1 r2)
    guard (sigilsCompatible s1 s2)
    r <- Row.union Row.mostTaken r1 r2
    s <- UnknownSigil <$> fresh
    pure [Record undefined r s :< v, Record undefined r1 s1 :< Record undefined r s, Record undefined r2 s2 :< Record undefined r s]

  Join v (Record _ r1 s1) (Record _ r2 s2) | r1 == r2 && s1 == s2 -> do
    pure [Record undefined r1 s1 :< v ]

  Join v (Function t1 t2) (Function r1 r2) -> do
    b1 <- UnifVar <$> fresh
    b2 <- UnifVar <$> fresh
    pure [ v :> Function b1 b2
         , b2 :> r2, b2 :> t2
         , t1 :> b1, r1 :> b1
         ]
  _ -> empty


find :: [Constraint] -> Maybe (Candidate, [Constraint])
find [] = Nothing
find (c:cs) = case c of
  UnifVar v :< tau
    | rigid tau -> case partition (flexRigidSub v) cs of
                     ([]         , rs ) -> fmap (c:) <$> find cs
                     (_ :< rho:rs, rs') -> pure (Meet (UnifVar v) tau rho , rs ++ rs')
  tau :< UnifVar v
    | rigid tau -> case partition (flexRigidSup v) cs of
                     ([]         , rs ) -> fmap (c:) <$> find cs
                     (rho :< _:rs, rs') -> pure (Join (UnifVar v) tau rho , rs ++ rs')
  (Variant (Row m (Just v))) :< tau@(Variant (Row m' Nothing))
    | M.null m -> case partition (flexRowSub v) cs of
           ([]          , rs ) -> fmap (c:) <$> find cs
           (_ :< rho :rs, rs') -> pure (Meet (Variant (Row m (Just v))) tau rho , rs ++ rs')
  tau@(Variant (Row m' Nothing)) :< (Variant (Row m (Just v)))
    | M.null m -> case partition (flexRowSup v) cs of
           ([]         , rs ) -> fmap (c:) <$> find cs
           (rho :< _:rs, rs') -> pure (Join (Variant (Row m (Just v))) tau rho , rs ++ rs')

  (Record _ (Row m (Just v)) s) :< tau@(Record _ (Row m' Nothing) s')
    | M.null m -> case partition (flexRowSub v) cs of
           ([]          , rs ) -> fmap (c:) <$> find cs
           (_ :< rho :rs, rs') -> pure (Meet (Record undefined (Row m (Just v)) s) tau rho , rs ++ rs')
  tau@(Record _ (Row m' Nothing) s') :< (Record _ (Row m (Just v)) s)
    | M.null m -> case partition (flexRowSup v) cs of
           ([]          , rs ) -> fmap (c:) <$> find cs
           (rho :< _:rs, rs') -> pure (Join (Record undefined (Row m (Just v)) s) tau rho , rs ++ rs')


  _ -> fmap (c:) <$> find cs
  where
    flexRigidSub v (UnifVar v' :< rho) = rigid rho && v == v'
    flexRigidSub v _                   = False

    flexRowSub v (Variant (Row m (Just v')) :< Variant (Row m' Nothing)) = M.null m && v == v'
    flexRowSub v (Record _ (Row m (Just v')) s :< Record _ (Row m' Nothing) s') = M.null m && v == v'
    flexRowSub v _                                                       = False

    flexRigidSup v (rho :< UnifVar v') = rigid rho && v == v'
    flexRigidSup v _                   = False

    flexRowSup v (Variant (Row m Nothing) :< Variant (Row m' (Just v'))) = M.null m' && v == v'
    flexRowSup v (Record _ (Row m Nothing) s :< Record _ (Row m' (Just v')) s') = M.null m' && v == v'
    flexRowSup v _                                                       = False

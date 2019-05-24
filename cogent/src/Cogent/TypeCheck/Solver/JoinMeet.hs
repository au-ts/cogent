{-# LANGUAGE FlexibleContexts #-}
module Cogent.TypeCheck.Solver.JoinMeet (joinMeet) where

import Cogent.Surface
import Cogent.TypeCheck.Base
import Cogent.Common.Types
import Cogent.Common.Syntax
import Cogent.TypeCheck.Solver.Goal
import Cogent.TypeCheck.Solver.Monad
import qualified Cogent.TypeCheck.Row as Row
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
import Control.Monad.Trans
import Control.Monad
import Control.Applicative
import qualified Data.Set as S
import qualified Data.Map as M
import Data.List (partition)
import Lens.Micro
import Debug.Trace

data Candidate = Meet [ErrorContext] [ErrorContext] TCType TCType TCType
               | Join [ErrorContext] [ErrorContext] TCType TCType TCType


-- | Find pairs of subtyping constraints that involve the same unification variable
--   on the right or left hand side, and compute the join/meet to simplify the
--   constraint graph.
joinMeet :: Rewrite.Rewrite' TcSolvM [Goal]
joinMeet = Rewrite.withTransform find $ \c -> case c of
  Meet c1 c2 v (T (TFun t1 t2)) (T (TFun r1 r2)) -> do
    b1 <- U <$> lift solvFresh
    b2 <- U <$> lift solvFresh
    pure [ Goal c1 (v :< T (TFun b1 b2))
         , Goal c2 (b2 :< r2), Goal c1 (b2 :< t2)
         , Goal c1 (t1 :< b1), Goal c2 (r1 :< b1)
         ]
  Join c1 c2 v (T (TFun t1 t2)) (T (TFun r1 r2)) -> do
    b1 <- U <$> lift solvFresh
    b2 <- U <$> lift solvFresh
    pure [ Goal c1 (v >: T (TFun b1 b2))
         , Goal c2 (b2 >: r2), Goal c1 (b2 >: t2)
         , Goal c1 (t1 >: b1), Goal c2 (r1 >: b1)
         ]
  Meet c1 c2 v (T (TTuple ts)) (T (TTuple us)) -> do
    bs <- fmap U <$> lift (solvFreshes (length ts))
    pure [ Goal c1 (v :< T (TTuple bs))
         , Goal c1 (T (TTuple bs) :< T (TTuple ts) )
         , Goal c2 (T (TTuple bs) :< T (TTuple us) )
         ]
  Join c1 c2 v (T (TTuple ts)) (T (TTuple us)) -> do
    bs <- fmap U <$> lift (solvFreshes (length ts))
    pure [ Goal c1 (v >: T (TTuple bs))
         , Goal c1 (T (TTuple bs) >: T (TTuple ts) )
         , Goal c2 (T (TTuple bs) >: T (TTuple us) )
         ]
  Meet c1 c2 v (V r1) (V r2) | r1 /= r2 -> do
    guard (Row.compatible r1 r2)
    r <- lift (union mostTaken r1 r2)
    pure [Goal c1 (v :< V r), Goal c1 (V r :< V r1), Goal c2 (V r :< V r2) ]

  Meet c1 c2 v (V r1) (V r2) | r1 == r2 -> do
    pure [ Goal c1 (v :< V r1) ]

  Join c1 c2 v (V r1) (V r2) | r1 /= r2 -> do
    guard (Row.compatible r1 r2)
    r <- lift (union leastTaken r1 r2)
    pure [ Goal c1 (V r :< v), Goal c2 (V r1 :< V r), Goal c2 (V r2 :< V r) ]

  Join c1 c2 v (V r1) (V r2) | r1 == r2 -> do
    pure [Goal c1 (V r1 :< v) ]

  Meet c1 c2 v (R r1 s1) (R r2 s2) | r1 /= r2 -> do
    guard (Row.compatible r1 r2)
    guard (sigilsCompatible s1 s2)
    r <- lift (union leastTaken r1 r2)
    s <- Right <$> lift solvFresh
    pure [Goal c1 (v :< R r s), Goal c1 (R r s :< R r1 s1), Goal c2 (R r s :< R r2 s2) ]

  Meet c1 c2 v (R r1 s1) (R r2 s2) | r1 == r2 && s1 == s2 -> do
    pure [Goal c1 (v :< R r1 s1)]

  Join c1 c2 v (R r1 s1) (R r2 s2) | r1 /= r2 -> do
    guard (Row.compatible r1 r2)
    guard (sigilsCompatible s1 s2)
    r <- lift (union mostTaken r1 r2)
    s <- Right <$> lift solvFresh
    pure [Goal c1 (R r s :< v), Goal c1 (R r1 s1 :< R r s), Goal c2 (R r2 s2 :< R r s)]

  Join c1 c2 v (R r1 s1) (R r2 s2) | r1 == r2 && s1 == s2 -> do
    pure [Goal c1 (R r1 s1 :< v) ]

  _ -> empty

sigilsCompatible :: Either (Sigil ()) Int -> Either (Sigil ()) Int -> Bool
sigilsCompatible (Left s) (Left s') = s == s'
sigilsCompatible _ _ = True

find :: [Goal] -> Maybe (Candidate, [Goal])
find [] = Nothing
find (c:cs) = case c ^. goal of
  U v :< tau
    | rigid tau -> case partition (flexRigidSub v) cs of
           ([], rs ) -> fmap (c:) <$> find cs
           (Goal ctx (_ :< rho):rs, rs')
             -> pure (Meet (c ^. goalContext) ctx (U v) tau rho , rs ++ rs')
  tau :< U v
    | rigid tau -> case partition (flexRigidSup v) cs of
           ([], rs ) -> fmap (c:) <$> find cs
           (Goal ctx (rho :< _):rs, rs')
             -> pure (Join (c ^. goalContext) ctx (U v) tau rho , rs ++ rs')
  (V (Row.Row m (Just v))) :< tau@(V (Row.Row m' Nothing))
    | M.null m -> case partition (flexRowSub v) cs of
           ([], rs ) -> fmap (c:) <$> find cs
           (Goal ctx (_ :< rho) :rs, rs')
             -> pure (Meet (c ^. goalContext) ctx (V (Row.Row m (Just v))) tau rho , rs ++ rs')
  (V (Row.Row m' Nothing)) :< tau@(V (Row.Row m (Just v)))
    | M.null m -> case partition (flexRowSup v) cs of
           ([], rs ) -> fmap (c:) <$> find cs
           (Goal ctx  (rho :< _):rs, rs')
             -> pure (Join (c ^. goalContext) ctx (V (Row.Row m (Just v))) tau rho , rs ++ rs')

  (R (Row.Row m (Just v)) s) :< tau@(R (Row.Row m' Nothing) s')
    | M.null m -> case partition (flexRowSub v) cs of
           ([], rs ) -> fmap (c:) <$> find cs
           (Goal ctx (_ :< rho):rs, rs')
             -> pure (Meet (c ^. goalContext) ctx (R (Row.Row m (Just v)) s) tau rho , rs ++ rs')
  (R (Row.Row m' Nothing) s') :< tau@(R (Row.Row m (Just v)) s)
    | M.null m -> case partition (flexRowSup v) cs of
           ([], rs ) -> fmap (c:) <$> find cs
           (Goal ctx (rho :< _):rs, rs')
             -> pure (Join (c ^. goalContext) ctx (R (Row.Row m (Just v)) s) tau rho , rs ++ rs')
  _ -> fmap (c:) <$> find cs
  where
    flexRigidSub v (Goal _ (U v' :< rho)) = rigid rho && v == v'
    flexRigidSub v _ = False

    flexRowSub v (Goal _ (V (Row.Row m (Just v')) :< V (Row.Row m' Nothing)))
         = M.null m && v == v'
    flexRowSub v (Goal _ (R (Row.Row m (Just v')) s :< R (Row.Row m' Nothing) s'))
         = M.null m && v == v'
    flexRowSub v _ = False

    flexRigidSup v (Goal _ (rho :< U v')) = rigid rho && v == v'
    flexRigidSup v _= False
    flexRowSup v (Goal _ (V (Row.Row m Nothing) :< V (Row.Row m' (Just v'))))
         = M.null m' && v == v'
    flexRowSup v (Goal _ (R (Row.Row m Nothing) s :< R (Row.Row m' (Just v')) s'))
         = M.null m' && v == v'
    flexRowSup v _ = False

type UnionMethod = (FieldName -> Row.Row TCType -> Row.Row TCType -> Bool)
union :: UnionMethod -> Row.Row TCType -> Row.Row TCType -> TcSolvM (Row.Row TCType)
union method r1@(Row.Row m1 _) r2@(Row.Row m2 _)= do
  let keys = S.toList (M.keysSet m1 `S.union` M.keysSet m2)
  entries <- mapM (\x -> (\f -> (x, (U f, method x r1 r2))) <$> solvFresh) keys
  Row.incomplete entries <$> solvFresh


-- | If the field or constructor is taken in all the rows in which it appears, then it
--   is taken in the union row.
leastTaken :: UnionMethod
leastTaken x r1@(Row.Row m1 v1) r2@(Row.Row m2 v2)
  | x `S.member` M.keysSet m1 && x `S.member` M.keysSet m2 = x `Row.takenIn` r1 && x `Row.takenIn` r2
  | x `S.member` M.keysSet m1 = x `Row.takenIn` r1
  | x `S.member` M.keysSet m2 = x `Row.takenIn` r2
  | otherwise                 = False

-- | If the field is taken in any of the rows in which it appears, then the field is taken
--   in the union row.
mostTaken :: UnionMethod
mostTaken x r1@(Row.Row m1 v1) r2@(Row.Row m2 v2)
  | x `S.member` M.keysSet m1 && x `S.member` M.keysSet m2 = x `Row.takenIn` r1 || x `Row.takenIn` r2
  | x `S.member` M.keysSet m1 = x `Row.takenIn` r1
  | x `S.member` M.keysSet m2 = x `Row.takenIn` r2
  | otherwise                 = True

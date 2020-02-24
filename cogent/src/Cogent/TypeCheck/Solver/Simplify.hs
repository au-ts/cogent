--
-- Copyright 2019, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE MultiWayIf #-}

module Cogent.TypeCheck.Solver.Simplify where

import           Cogent.Common.Syntax
import           Cogent.Common.Types
import           Cogent.Compiler
import           Cogent.TypeCheck.ARow as ARow
import           Cogent.TypeCheck.Base
import qualified Cogent.TypeCheck.Row as Row
#ifdef BUILTIN_ARRAYS
import           Cogent.TypeCheck.Solver.SMT (smtSimp)
#endif
import           Cogent.TypeCheck.Solver.Goal
import           Cogent.TypeCheck.Solver.Monad
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
import           Cogent.Surface
import           Cogent.Util (hoistMaybe)

import           Control.Applicative
import           Control.Monad
import           Control.Monad.IO.Class (liftIO)
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.Class (lift)
import qualified Data.Foldable as F (any)
import qualified Data.IntMap as IM (null)
import qualified Data.Map as M
import           Data.Maybe
import           Data.List as L (elemIndex, null)
import qualified Data.Set as S
import           Data.Word (Word32)
import           Lens.Micro

import           Cogent.Common.Syntax
import           Cogent.Common.Types
import           Cogent.Compiler
import           Cogent.TypeCheck.ARow as ARow
import           Cogent.TypeCheck.Base
import qualified Cogent.TypeCheck.Row as Row
import           Cogent.TypeCheck.Row (Entry)
import           Cogent.TypeCheck.Solver.Goal 
import           Cogent.TypeCheck.Solver.Monad
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
import           Cogent.Surface

onGoal :: (Monad m) => (Constraint -> MaybeT m [Constraint]) -> Goal -> MaybeT m [Goal]
onGoal f g = fmap (map (derivedGoal g)) (f (g ^. goal))

unsat :: (Monad m) => TypeError -> MaybeT m [Constraint]
unsat x = hoistMaybe $ Just [Unsat x]

elseDie :: (Monad m) => Bool -> TypeError -> MaybeT m [Constraint]
elseDie b e = (hoistMaybe $ guard b >> Just []) <|> unsat e

liftTcSolvM :: Rewrite.RewriteT IO a -> Rewrite.RewriteT TcSolvM a
liftTcSolvM (Rewrite.RewriteT m) = Rewrite.RewriteT (\a -> MaybeT $ liftIO $ runMaybeT (m a))

simplify :: [(TyVarName, Kind)] -> Rewrite.RewriteT IO [Goal]
simplify axs = Rewrite.pickOne' $ onGoal $ \c -> case c of
  Sat      -> hoistMaybe $ Just []
  c1 :& c2 -> hoistMaybe $ Just [c1,c2]

  Drop   t@(T (TVar v False False)) m
    | Just k <- lookup v axs ->
        canDiscard k `elseDie` TypeNotDiscardable t m
  Share  t@(T (TVar v False False)) m
    | Just k <- lookup v axs ->
        canShare k   `elseDie` TypeNotShareable t m
  Escape t@(T (TVar v False False)) m
    | Just k <- lookup v axs ->
        canEscape k  `elseDie` TypeNotEscapable t m

  Drop     (T (TVar v b u)) m | b || u -> hoistMaybe $ Just []
  Share    (T (TVar v b u)) m | b || u -> hoistMaybe $ Just []
  Escape t@(T (TVar v True False)) m -> unsat (TypeNotEscapable t m)

  Drop   t@(T (TCon n ts s)) m ->
    not (writable s) `elseDie` TypeNotDiscardable t m
  Share  t@(T (TCon n ts s)) m ->
    not (writable s) `elseDie` TypeNotShareable t m
  Escape t@(T (TCon n ts s)) m ->
    not (readonly s) `elseDie` TypeNotEscapable t m

  Drop   (T (TFun {})) _ -> hoistMaybe $ Just []
  Share  (T (TFun {})) _ -> hoistMaybe $ Just []
  Escape (T (TFun {})) _ -> hoistMaybe $ Just []

  Drop   (T TUnit) _ -> hoistMaybe $ Just []
  Share  (T TUnit) _ -> hoistMaybe $ Just []
  Escape (T TUnit) _ -> hoistMaybe $ Just []

  Drop   (T (TTuple xs)) m -> hoistMaybe $ Just (map (flip Drop   m) xs)
  Share  (T (TTuple xs)) m -> hoistMaybe $ Just (map (flip Share  m) xs)
  Escape (T (TTuple xs)) m -> hoistMaybe $ Just (map (flip Escape m) xs)

  Share  (V r) m
    | isNothing (Row.var r) -> hoistMaybe $ Just (map (flip Share  m) (Row.untakenTypes r))
  Drop   (V r) m
    | isNothing (Row.var r) -> hoistMaybe $ Just (map (flip Drop   m) (Row.untakenTypes r))
  Escape (V r) m
    | isNothing (Row.var r) -> hoistMaybe $ Just (map (flip Escape m) (Row.untakenTypes r))

  Share  (R r (Left s)) m
    | isNothing (Row.var r)
    , not (writable s) -> hoistMaybe $ Just (map (flip Share  m) (Row.untakenTypes r))
  Drop   (R r (Left s)) m
    | isNothing (Row.var r)
    , not (writable s) -> hoistMaybe $ Just (map (flip Drop   m) (Row.untakenTypes r))
  Escape (R r (Left s)) m
    | isNothing (Row.var r)
    , not (readonly s) -> hoistMaybe $ Just (map (flip Escape m) (Row.untakenTypes r))

#ifdef BUILTIN_ARRAYS
  Share  (A t _ (Left s) _) m | not (writable s) -> hoistMaybe $ Just [Share  t m]  -- TODO: deal with the taken fields!!! / zilinc
  Drop   (A t _ (Left s) _) m | not (writable s) -> hoistMaybe $ Just [Drop   t m]  -- TODO
  Escape (A t _ (Left s) _) m | not (readonly s) -> hoistMaybe $ Just [Escape t m]  -- TODO
#endif

  Exhaustive t ps | any isIrrefutable ps -> hoistMaybe $ Just []
  Exhaustive (V r) []
    | isNothing (Row.var r) ->
      L.null (Row.untakenTypes r)
        `elseDie` PatternsNotExhaustive (V r) (Row.untakenLabels r)
  Exhaustive (V r) (RP (PCon t _):ps)
    | isNothing (Row.var r) ->
      hoistMaybe $ Just [Exhaustive (V (Row.take t r)) ps]

  Exhaustive tau@(T (TCon "Bool" [] Unboxed)) [RP (PBoolLit t), RP (PBoolLit f)]
    -> (not (t && f) && (t || f)) `elseDie` PatternsNotExhaustive tau []

  Upcastable (T (TCon n [] Unboxed)) (T (TCon m [] Unboxed))
    | Just n' <- elemIndex n primTypeCons
    , Just m' <- elemIndex m primTypeCons
    , n' <= m' , not (m `elem` ["String","Bool"]) -> hoistMaybe $ Just []

  -- [amos] New simplify rule:
  -- If both sides of an equality constraint are equal, we can't completely discharge it;
  -- we need to make sure all unification variables in the type are instantiated at some point
  t :=: u | t == u -> hoistMaybe $ if isSolved t then Just [] else Just [Solved t]

  Solved t | isSolved t -> hoistMaybe $ Just []

  IsPrimType (T (TCon x _ Unboxed)) | x `elem` primTypeCons -> hoistMaybe $ Just []

  T (TFun t1 t2) :=: T (TFun r1 r2) -> hoistMaybe $ Just [r1 :=: t1, t2 :=: r2]
  T (TFun t1 t2) :<  T (TFun r1 r2) -> hoistMaybe $ Just [r1 :<  t1, t2 :<  r2]

  T (TTuple ts) :<  T (TTuple us) | length ts == length us -> hoistMaybe $ Just (zipWith (:< ) ts us)
  T (TTuple ts) :=: T (TTuple us) | length ts == length us -> hoistMaybe $ Just (zipWith (:=:) ts us)

  V r1 :< V r2 | Row.null r1 && Row.null r2 -> hoistMaybe $ Just []
               | Just (r1',r2') <- extractVariableEquality r1 r2 -> hoistMaybe $ Just [V r1' :=: V r2']
               | otherwise -> do
    let commons  = Row.common r1 r2
        (ls, rs) = unzip commons
    guard (not (L.null commons))
    guard (untakenLabelsSet ls `S.isSubsetOf` untakenLabelsSet rs)
    let (r1',r2') = Row.withoutCommon r1 r2
        cs = map (\ ((_, e),(_,e')) -> fst e :< fst e') commons
        c   = V r1' :< V r2'
    hoistMaybe $ Just (c:cs)

  V r1 :=: V r2 | Row.null r1 && Row.null r2 -> hoistMaybe $ Just []
                | otherwise -> do
    let commons  = Row.common r1 r2
        (ls, rs) = unzip commons
    guard (not (L.null commons))
    guard (untakenLabelsSet ls == untakenLabelsSet rs)
    let (r1',r2') = Row.withoutCommon r1 r2
        cs = map (\ ((_, e),(_,e')) -> fst e :=: fst e') commons
        c   = V r1' :=: V r2'
    hoistMaybe $ Just (c:cs)

  R r1 s1 :< R r2 s2 | Row.null r1 && Row.null r2 && s1 == s2 -> hoistMaybe $ Just []
                     | Just (r1',r2') <- extractVariableEquality r1 r2 -> hoistMaybe $ Just [R r1' s1 :=: R r2' s2]
                     | otherwise -> do
    let commons  = Row.common r1 r2
        (ls, rs) = unzip commons
    guard (not (L.null commons))
    guard (untakenLabelsSet rs `S.isSubsetOf` untakenLabelsSet ls)
    let (r1',r2') = Row.withoutCommon r1 r2
        cs = map (\ ((_, e),(_,e')) -> fst e :< fst e') commons
        ds = map (flip Drop ImplicitlyTaken) $ Row.typesFor (untakenLabelsSet ls S.\\ untakenLabelsSet rs) r1
        c  = R r1' s1 :< R r2' s2
    hoistMaybe $ Just (c:cs ++ ds)

  R r1 s1 :=: R r2 s2 | Row.null r1 && Row.null r2 && s1 == s2 -> hoistMaybe $ Just []
                      | otherwise -> do
    let commons  = Row.common r1 r2
        (ls, rs) = unzip commons
    guard (not (L.null commons))
    guard (untakenLabelsSet rs == untakenLabelsSet ls)
    let (r1',r2') = Row.withoutCommon r1 r2
        cs = map (\ ((_, e),(_,e')) -> fst e :=: fst e') commons
        ds = map (flip Drop ImplicitlyTaken) $ Row.typesFor (untakenLabelsSet ls S.\\ untakenLabelsSet rs) r1
        c  = R r1' s1 :=: R r2' s2
    hoistMaybe $ Just (c:cs ++ ds)

#ifdef BUILTIN_ARRAYS
  -- See [NOTE: solving 'A' types] in Cogent.Solver.Unify
  A t1 l1 s1 (Left r1) :<  A t2 l2 s2 (Left r2) | s1 == s2 -> do
    -- guard (isJust r1 && isJust r2 || isNothing r1 && isNothing r2)
    guard (not $ isJust r1 && isNothing r2)
    let drop = case (r1,r2) of
                 (r1, r2) | r1 == r2 -> Sat
                 (Nothing, Just i2) -> Drop t1 ImplicitlyTaken
                 (Just i1, Just i2) -> Arith (SE (T (TCon "Bool" [] Unboxed)) (PrimOp "==" [i1,i2]))
    hoistMaybe $ Just [Arith (SE (T (TCon "Bool" [] Unboxed)) (PrimOp "==" [l1,l2])), t1 :< t2, drop]

  A t1 l1 s1 (Left r1) :=: A t2 l2 s2 (Left r2) | s1 == s2 -> do
    guard (isJust r1 && isJust r2 || isNothing r1 && isNothing r2)
    let drop = case (r1,r2) of
                 (r1, r2) | r1 == r2 -> Sat
                 (Just i1, Just i2) -> Arith (SE (T (TCon "Bool" [] Unboxed)) (PrimOp "==" [i1,i2]))
    hoistMaybe $ Just [Arith (SE (T (TCon "Bool" [] Unboxed)) (PrimOp "==" [l1,l2])), t1 :=: t2, drop]

  a :-> b -> hoistMaybe $ Just [b]  -- FIXME: cuerently we ignore the impls. / zilinc

  -- TODO: Here we will call a SMT procedure to simplify all the Arith constraints.
  -- The only things left will be non-trivial predicates. / zilinc
  Arith e | isTrivialSE e -> do
              r <- lift $ smtSimp e 
              if r then hoistMaybe $ Just []
                   else hoistMaybe $ Nothing
          | otherwise -> hoistMaybe $ Nothing
#endif

  T t1 :< x | unorderedType t1 -> hoistMaybe $ Just [T t1 :=: x]
  x :< T t2 | unorderedType t2 -> hoistMaybe $ Just [x :=: T t2]

  (T (TCon n ts s)) :=: (T (TCon n' us s'))
    | s == s', n == n' -> hoistMaybe $ Just (zipWith (:=:) ts us)

  t -> hoistMaybe $ Nothing

-- | Returns 'True' iff the given argument type is not subject to subtyping. That is, if @a :\< b@
--   (subtyping) is equivalent to @a :=: b@ (equality), then this function returns true.
unorderedType :: Type e t -> Bool
unorderedType (TCon {}) = True
unorderedType (TVar {}) = True
unorderedType (TUnit)   = True
unorderedType _ = False

untakenLabelsSet :: [Entry TCType] -> S.Set FieldName
untakenLabelsSet = S.fromList . mapMaybe (\(l, (_,t)) -> guard (either not (const False) t) >> pure l)

isIrrefutable :: RawPatn -> Bool
isIrrefutable (RP (PIrrefutable _)) = True
isIrrefutable _ = False

-- | Check if the variable parts must be equal.
--   Returns true iff the two rows have the same keys, but one of the variables
--   is Nothing and the other is a Just
extractVariableEquality :: Row.Row t -> Row.Row t -> Maybe (Row.Row t, Row.Row t)
extractVariableEquality (Row.Row m1 v1) (Row.Row m2 v2)
 | (isJust v1 && isNothing v2) || (isNothing v1 && isJust v2)
 , M.null m1
 , M.null m2
 = Just (Row.Row M.empty v1, Row.Row M.empty v2)
 | otherwise
 = Nothing

isSolved :: TCType -> Bool
isSolved t = L.null (unifVars t)
#ifdef BUILTIN_ARRAYS
          && L.null (unknowns t)
#endif


normaliseSExpr :: TCSExpr -> Maybe Int
normaliseSExpr (SU _ x) = Nothing
normaliseSExpr (SE _ (IntLit n)) = Just $ fromIntegral n
normaliseSExpr (SE {}) = __todo "normaliseSExpr"


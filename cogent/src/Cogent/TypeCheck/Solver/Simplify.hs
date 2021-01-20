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

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ViewPatterns #-}

module Cogent.TypeCheck.Solver.Simplify where

import           Cogent.Common.Syntax
import           Cogent.Common.Types
import           Cogent.Compiler
import qualified Cogent.Context as C
import           Cogent.Dargent.Surface
import           Cogent.Dargent.TypeCheck
import           Cogent.Dargent.Util
import           Cogent.TypeCheck.Base
import qualified Cogent.TypeCheck.LRow as LRow
import qualified Cogent.TypeCheck.Row as Row
#ifdef REFINEMENT_TYPES
import           Cogent.TypeCheck.Solver.SMT (smtSat)
#endif
import           Cogent.TypeCheck.Solver.Goal
import           Cogent.TypeCheck.Solver.Monad
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
import qualified Cogent.TypeCheck.Solver.Normalise as Normalise
import           Cogent.Surface
import           Cogent.Util (hoistMaybe)

import           Control.Applicative
import           Control.Monad
import           Control.Monad.IO.Class (liftIO)
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.Class (lift)
import           Data.List as L (elemIndex, isSubsequenceOf, null, (\\))
import qualified Data.Map as M
import           Data.Maybe
import qualified Data.Set as S
import           Data.Word (Word32)
import           Lens.Micro

import           Debug.Trace

import           Cogent.PrettyPrint (prettyC)
-- import qualified Text.PrettyPrint.ANSI.Leijen as P
-- import Debug.Trace


unsat :: (Monad m) => TypeError -> MaybeT m [Constraint]
unsat x = hoistMaybe $ Just [Unsat x]

elseDie :: (Monad m) => Bool -> TypeError -> MaybeT m [Constraint]
elseDie b e = (hoistMaybe $ guard b >> Just []) <|> unsat e

liftTcSolvM :: Rewrite.RewriteT IO a -> Rewrite.RewriteT TcSolvM a
liftTcSolvM (Rewrite.RewriteT m) = Rewrite.RewriteT (\a -> MaybeT $ liftIO $ runMaybeT (m a))

simplify :: [(TyVarName, Kind)] -> [(DLVarName, TCType)] -> Rewrite.RewriteT TcSolvM [Goal]
simplify ks ts = Rewrite.pickOne' $ onGoal $ \case
  Sat      -> hoistMaybe $ Just []
  c1 :& c2 -> hoistMaybe $ Just [c1,c2]

  Drop   t@(T (TVar v False False)) m
    | Just k <- lookup v ks ->
        canDiscard k `elseDie` TypeNotDiscardable t m
  Share  t@(T (TVar v False False)) m
    | Just k <- lookup v ks ->
        canShare k   `elseDie` TypeNotShareable t m
  Escape t@(T (TVar v False False)) m
    | Just k <- lookup v ks ->
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

  Share  (V r) m | Row.isComplete r ->
    hoistMaybe $ Just (map (flip Share  m) (Row.presentPayloads r))
  Drop   (V r) m | Row.isComplete r ->
    hoistMaybe $ Just (map (flip Drop   m) (Row.presentPayloads r))
  Escape (V r) m | Row.isComplete r ->
    hoistMaybe $ Just (map (flip Escape m) (Row.presentPayloads r))

  Share  (R _ r (Left s)) m
    | Row.isComplete r
    , not (writable s) -> hoistMaybe $ Just (map (flip Share  m) (Row.presentPayloads r))
  Drop   (R _ r (Left s)) m
    | Row.isComplete r
    , not (writable s) -> hoistMaybe $ Just (map (flip Drop   m) (Row.presentPayloads r))
  Escape (R _ r (Left s)) m
    | Row.isComplete r
    , not (readonly s) -> hoistMaybe $ Just (map (flip Escape m) (Row.presentPayloads r))

#ifdef REFINEMENT_TYPES
  Share  (A t _ (Left s) _) m | not (writable s) -> hoistMaybe $ Just [Share  t m]  -- TODO: deal with the taken fields!!! / zilinc
  Drop   (A t _ (Left s) _) m | not (writable s) -> hoistMaybe $ Just [Drop   t m]  -- TODO
  Escape (A t _ (Left s) _) m | not (readonly s) -> hoistMaybe $ Just [Escape t m]  -- TODO

  Share  (T (TRefine _ b _)) m -> hoistMaybe $ Just [Share  b m]
  Drop   (T (TRefine _ b _)) m -> hoistMaybe $ Just [Drop   b m]
  Escape (T (TRefine _ b _)) m -> hoistMaybe $ Just [Escape b m]
#endif

  Exhaustive t ps | any isIrrefutable ps -> hoistMaybe $ Just []
  Exhaustive (V r) []
    | Row.isComplete r ->
      null (Row.presentPayloads r) 
        `elseDie` PatternsNotExhaustive (V r) (Row.presentLabels r) 
  Exhaustive (V r) (RP (PCon t _):ps) 
    | isNothing (Row.var r) -> 
      hoistMaybe $ Just [Exhaustive (V (Row.take t r)) ps]

  Exhaustive tau@(T (TCon "Bool" [] Unboxed)) [RP (PBoolLit t), RP (PBoolLit f)]
    -> (not (t && f) && (t || f)) `elseDie` PatternsNotExhaustive tau []

  Upcastable (T (TCon n [] Unboxed)) (T (TCon m [] Unboxed))
    | Just n' <- elemIndex n primTypeCons
    , Just m' <- elemIndex m primTypeCons
    , n' <= m' , not (m `elem` ["String","Bool"]) -> hoistMaybe $ Just []
#ifdef REFINEMENT_TYPES
  Upcastable t@(T (TCon n [] Unboxed)) (T (TRefine _ b _))
    | Just n' <- elemIndex n primTypeCons
    -> hoistMaybe $ Just [Upcastable t b]
  Upcastable (T (TRefine _ b _)) t@(T (TCon n [] Unboxed))
    | Just n' <- elemIndex n primTypeCons
    -> hoistMaybe $ Just [Upcastable b t]
  Upcastable (T (TRefine _ b1 _)) (T (TRefine _ b2 _))
    -> hoistMaybe $ Just [Upcastable b1 b2]
#endif

  Drop  (T (TRPar _ True _)) m -> hoistMaybe $ Just []
  Share (T (TRPar _ True _)) m -> hoistMaybe $ Just []

  -- [amos] New simplify rule:
  -- If both sides of an equality constraint are equal, we can't completely discharge it;
  -- we need to make sure all unification variables in the type are instantiated at some point
  t :=: u | t == u -> hoistMaybe $ if isSolved t then Just [] else Just [Solved t]
  t :<  u | t == u -> hoistMaybe $ if isSolved t then Just [] else Just [Solved t]

  Solved t | isSolved t -> hoistMaybe $ Just []

  PrimType (T (TCon x _ Unboxed)) | x `elem` primTypeCons -> hoistMaybe $ Just []

  TLVar n        :~ tau | Just t <- lookup n ts
                        -> hoistMaybe $ Just [tau :~~ t]
  TLRepRef _ _   :~ _ -> hoistMaybe Nothing
  TLRecord fs    :~ R _ _ (Left (Boxed _ (Just l))) -> hoistMaybe $ Just [l :~< TLRecord fs]
  TLRecord fs    :~ R _ r (Left (Boxed _ Nothing))
    | ls <- M.fromList $ (\(f,_,l) -> (f,l)) <$> fs
    , rs <- M.fromList $ Row.unE <$> Row.entries r
    , cs <- M.intersectionWith (,) ls rs
    , M.null $ M.difference rs cs
    -> hoistMaybe $ Just $ (\(e,(t,_)) -> e :~ toBoxedType t) <$> M.elems cs
  TLRecord _     :~ R _ _ (Right _) -> __todo "TLRecord fs :~ R r1 (Right n) => is this possible?"

  TLVariant _ fs :~ V r
    | ls <- M.fromList $ (\(f,_,_,l) -> (f,l)) <$> fs
    , rs <- M.fromList $ Row.unE <$> Row.entries r
    , cs <- M.intersectionWith (,) ls rs
    , M.null $ M.difference rs cs
    -> hoistMaybe $ Just $ (\(e,(t,_)) -> e :~ toBoxedType t) <$> M.elems cs

#ifdef REFINEMENT_TYPES
  TLArray e _    :~ A _ _ (Left (Boxed _ (Just l))) _ -> hoistMaybe $ Just [l :~< e]
  TLArray e _    :~ A t _ (Left (Boxed _ Nothing)) _ -> hoistMaybe $ Just [e :~ toBoxedType t]
  TLArray e _    :~ A _ _ (Right _) _ -> __todo "TLArray e p :~ A t l (Right n) h => is this possible?"
#endif

  TLOffset e _   :~ tau -> hoistMaybe $ Just [e :~ tau]

  TLPrim n       :~ T TUnit | evalSize n >= 0 -> hoistMaybe $ Just []
  TLPrim n       :~ tau
    | isPrimType tau
    , primTypeSize tau <= evalSize n
    -> hoistMaybe $ Just []
    | isBoxedType tau
    , evalSize n == pointerSizeBits
    -> hoistMaybe $ Just []

  TLPtr          :~ tau
    | isBoxedType tau -> hoistMaybe $ Just []

  l              :~ T (TBang tau)    -> hoistMaybe $ Just [l :~ tau]
  l              :~ T (TTake _ tau)  -> hoistMaybe $ Just [l :~ tau]
  l              :~ T (TPut  _ tau)  -> hoistMaybe $ Just [l :~ tau]
#ifdef REFINEMENT_TYPES
  l              :~ T (TATake _ tau) -> hoistMaybe $ Just [l :~ tau]
  l              :~ T (TAPut  _ tau) -> hoistMaybe $ Just [l :~ tau]
#endif
  _              :~ Synonym _ _      -> hoistMaybe Nothing
  l              :~ tau | TLU _ <- l -> hoistMaybe Nothing
                        | otherwise  -> unsat $ LayoutDoesNotMatchType l tau

  TLRepRef _ _     :~< TLRepRef _ _  -> hoistMaybe Nothing
  TLRepRef _ _     :~< _             -> hoistMaybe Nothing
  _                :~< TLRepRef _ _  -> hoistMaybe Nothing
  TLVar v1         :~< TLVar v2      | v1 == v2 -> hoistMaybe $ Just []
  TLPrim n1        :~< TLPrim n2     | n1 <= n2 -> hoistMaybe $ Just []
  TLOffset e1 _    :~< TLOffset e2 _ -> hoistMaybe $ Just [e1 :~< e2]

  TLRecord fs1     :~< TLRecord fs2
    | r1 <- LRow.fromList $ map (\(a,b,c) -> (a,c,())) fs1
    , r2 <- LRow.fromList $ map (\(a,b,c) -> (a,c,())) fs2
    , r1 `LRow.isSubRow` r2
    -> hoistMaybe $ Just $ (\((_,l1,_),(_,l2,_)) -> l1 :~< l2) <$> LRow.common r1 r2

  TLVariant e1 fs1 :~< TLVariant e2 fs2
    | r1 <- LRow.fromList $ map (\(a,b,c,d) -> (a,d,c)) fs1
    , r2 <- LRow.fromList $ map (\(a,b,c,d) -> (a,d,c)) fs2
    , r1 `LRow.isSubRow` r2
    -> hoistMaybe $ Just $ ((\((_,l1,_),(_,l2,_)) -> l1 :~< l2) <$> LRow.common r1 r2) <> [e1 :~< e2]

#ifdef REFINEMENT_TYPES
  TLArray e1 _     :~< TLArray e2 _ -> hoistMaybe $ Just [e1 :~< e2]
#endif

  l1               :~< l2 | TLU _ <- l1 -> hoistMaybe Nothing
                          | TLU _ <- l2 -> hoistMaybe Nothing
                          | otherwise   -> unsat $ LayoutsNotCompatible l1 l2  -- FIXME!

  T (TVar n1 _ _) :~~ T (TVar n2 _ _) | n1 == n2 -> hoistMaybe $ Just []
  Synonym _ _     :~~ _               -> hoistMaybe Nothing
  _               :~~ Synonym _ _     -> hoistMaybe Nothing

  R rp1 r1 s1 :~~ R rp2 r2 s2
    | Row.isEmpty r1
    , Just c <- doSigilMatch (rmF s1) (rmF s2)
    , sameRecursive rp1 rp2
    -> hoistMaybe $ Just c
    | Row.isComplete r1 && Row.isComplete r2
    , psub r2 r1
    -> let commons  = Row.common r1 r2 in
       do guard (not (null commons))
          let cs = map (\ (e,e') -> Row.payload e :~~ Row.payload e') commons
              ds = map (flip Drop ImplicitlyTaken) $ Row.extract (pdiff r1 r2) r1
          hoistMaybe $ Just (cs ++ ds)

  V r1 :~~ V r2 | Row.isEmpty r1 -> hoistMaybe $ Just []
                | Row.isComplete r1 && Row.isComplete r2 && peq r1 r2 ->
    let commons  = Row.common r1 r2 in
    do guard (not (null commons))
       hoistMaybe $ Just $ map (\(e,e') -> Row.payload e :~~ Row.payload e') commons

#ifdef REFINEMENT_TYPES
  A t1 _ s1 _ :~~ A t2 _ s2 _ | (Just c) <- doSigilMatch (rmF s1) (rmF s2)
                              -> hoistMaybe $ Just ((t1 :~~ t2):c)
                              | otherwise -> hoistMaybe Nothing
#endif
  T (TVar n1 _ _) :~~ T (TVar n2 _ _) | n1 == n2 -> hoistMaybe $ Just []

  t1 :~~ t2 | t1 == t2 -> hoistMaybe $ Just []
            | isPrimType t1 && isPrimType t2
            , primTypeSize t1 <= primTypeSize t2
            -> hoistMaybe $ Just []
            | otherwise -> unsat $ TypesNotFit t1 t2

  T (TLayout l1 t1) :=: T (TLayout l2 t2) -> hoistMaybe $ Just [l1 :~< l2, t1 :=: t2, l1 :~ t1, l2 :~ t2]
  T (TLayout l1 t1) :<  T (TLayout l2 t2) -> hoistMaybe $ Just [l1 :~< l2, t1 :<  t2, l1 :~ t1, l2 :~ t2]

  T (TFun Nothing t1 t2) :=: T (TFun Nothing r1 r2) -> hoistMaybe $ Just [r1 :=: t1, t2 :=: r2]
  T (TFun Nothing t1 t2) :<  T (TFun Nothing r1 r2) -> hoistMaybe $ Just [r1 :<  t1, t2 :<  r2]

  T (TFun Nothing t1 t2) :=: T (TFun (Just u) r1 r2) -> do
    v <- freshRefVarName _2
    hoistMaybe $ Just [T (TFun (Just v) t1 t2) :=: T (TFun (Just u) r1 r2)]
  T (TFun (Just v) t1 t2) :=: T (TFun Nothing r1 r2) -> do
    u <- freshRefVarName _2
    hoistMaybe $ Just [T (TFun (Just v) t1 t2) :=: T (TFun (Just u) r1 r2)]

  T (TFun Nothing t1 t2) :<  T (TFun (Just u) r1 r2) -> do
    v <- freshRefVarName _2
    hoistMaybe $ Just [T (TFun (Just v) t1 t2) :<  T (TFun (Just u) r1 r2)]
  T (TFun (Just v) t1 t2) :<  T (TFun Nothing r1 r2) -> do
    u <- freshRefVarName _2
    hoistMaybe $ Just [T (TFun (Just v) t1 t2) :<  T (TFun (Just u) r1 r2)]

  T (TFun (Just v) t1 t2) :=: T (TFun (Just u) r1 r2) -> do
    let r2' = if v == u then r2 else substVarExprT [(u, v)] r2
#ifdef REFINEMENT_TYPES
    hoistMaybe $ Just [r1 :=: t1, (M.singleton u (r1,0), []) :|- t2 :=: r2']
#else
    hoistMaybe $ Just [r1 :=: t1, t2 :=: r2']
#endif
  T (TFun (Just v) t1 t2) :<  T (TFun (Just u) r1 r2) -> do
    let r2' = if v == u then r2 else substVarExprT [(u, v)] r2
#ifdef REFINEMENT_TYPES
    hoistMaybe $ Just [r1 :<  t1, (M.singleton u (r1,0), []) :|- t2 :<  r2']
#else
    hoistMaybe $ Just [r1 :<  t1, t2 :<  r2']
#endif

  T (TTuple ts) :<  T (TTuple us) | length ts == length us -> hoistMaybe $ Just (zipWith (:< ) ts us)
  T (TTuple ts) :=: T (TTuple us) | length ts == length us -> hoistMaybe $ Just (zipWith (:=:) ts us)

  T (TLayout (TLVar _) t1) :<  t2 -> hoistMaybe $ Just [t1 :<  t2]
  T (TLayout (TLVar _) t1) :=: t2 -> hoistMaybe $ Just [t1 :=: t2]

  V r1 :< V r2 | Row.isEmpty r1 && Row.isEmpty r2 -> hoistMaybe $ Just []
               | Row.isComplete r1 && Row.isComplete r2 && psub r1 r2 ->
    let commons = Row.common r1 r2 in
    do guard (not (null commons))
       hoistMaybe $ Just $ map (\(e,e') -> Row.payload e :< Row.payload e') commons

  V r1 :=: V r2 | Row.isEmpty r1 && Row.isEmpty r2 -> hoistMaybe $ Just []
                | Row.isComplete r1 && Row.isComplete r2 && peq r1 r2 ->
    let commons = Row.common r1 r2 in
    do guard (not (null commons))
       hoistMaybe $ Just $ map (\(e,e') -> Row.payload e :=: Row.payload e') commons

  R rp1 r1 s1 :< R rp2 r2 s2
    -- \ | trace ("r1 = " ++ show r1 ++ "\nr2 = " ++ show r2 ++ "\ns1 = " ++ show s1 ++ "\ns2 = " ++ show s2) False -> undefined
    | Row.isEmpty r1 && Row.isEmpty r2
    , Just c <- doSigilMatch s1 s2
    , sameRecursive rp1 rp2
    -> hoistMaybe $ Just c
    | Row.isComplete r1 && Row.isComplete r2
    , Just c <- doSigilMatch s1 s2
    , psub r2 r1 ->
      let commons = Row.common r1 r2 in
      do guard (not (null commons))
         let cs = map (\(e,e') -> Row.payload e :< Row.payload e') commons
             ds = map (flip Drop ImplicitlyTaken) $ Row.extract (pdiff r1 r2) r1
         hoistMaybe $ Just (c ++ cs ++ ds)

  R rp1 r1 s1 :=: R rp2 r2 s2
    | Row.isEmpty r1 && Row.isEmpty r2
    , Just c <- doSigilMatch s1 s2
    , sameRecursive rp1 rp2
    -> hoistMaybe $ Just c
    | Row.isComplete r1 && Row.isComplete r2
    , Just c <- doSigilMatch s1 s2
    , peq r1 r2 ->
      let commons = Row.common r1 r2 in
      do guard (not (null commons))
         let cs = map (\(e,e') -> Row.payload e :=: Row.payload e') commons
             ds = map (flip Drop ImplicitlyTaken) $ Row.extract (pdiff r1 r2) r1
         hoistMaybe $ Just (c ++ cs ++ ds)

#ifdef REFINEMENT_TYPES
  -- See [NOTE: solving 'A' types] in Cogent.Solver.Unify
  A t1 l1 s1 (Left r1) :<  A t2 l2 s2 (Left r2) | Just c <- doSigilMatch s1 s2 -> do
    guard (not $ isJust r1 && isNothing r2)
    let drop = case (r1,r2) of
                 (r1, r2) | r1 == r2 -> Sat
                 (Nothing, Just i2) -> Drop t1 ImplicitlyTaken
                 (Just i1, Just i2) -> Arith (SE (T bool) (PrimOp "==" [i1,i2]))
    hoistMaybe $ Just ([Arith (SE (T bool) (PrimOp "==" [l1,l2])), t1 :< t2, drop] <> c)

  A t1 l1 s1 (Left r1) :=: A t2 l2 s2 (Left r2) | Just c <- doSigilMatch s1 s2 -> do
    guard (isJust r1 && isJust r2 || isNothing r1 && isNothing r2)
    let drop = case (r1,r2) of
                 (r1, r2) | r1 == r2 -> Sat
                 (Just i1, Just i2) -> Arith (SE (T bool) (PrimOp "==" [i1,i2]))
    hoistMaybe $ Just ([Arith (SE (T bool) (PrimOp "==" [l1,l2])), t1 :=: t2, drop] <> c)

  T (TRefine v1 b1 e1) :< T (TRefine v2 b2 e2) | null (unknownsE e1 ++ unknownsE e2) -> do
    let e2' = if v1 == v2 then e2 else substVarExpr [(v2, v1)] e2
    return [ b1 :< b2
           , (M.singleton v1 (b2,0), []) :|- Arith (SE (T bool) (PrimOp "||" [SE (T bool) (PrimOp "not" [e1]), e2']))
           ]

  T (TRefine v1 b1 e1) :=: T (TRefine v2 b2 e2) | null (unknownsE e1 ++ unknownsE e2) -> do
    let e2' = if v1 == v2 then e2 else substVarExpr [(v2, v1)] e2
    return [ b1 :=: b2
           , (M.singleton v1 (b2,0), []) :|- Arith (SE (T bool) (PrimOp "==" [e1, e2']))
           ]

  t1 :< t2@(T (TRefine v _ _)) | notRefinementType t1 ->
    return [T (TRefine v t1 (SE (T bool) (BoolLit True))) :< t2]

  t1@(T (TRefine v _ _)) :< t2 | notRefinementType t2 ->
    -- NOTE: Even though the truth value of the refinement predicate
    -- in t1 no longer matters, we still keep it from being optimised
    -- away, as it may contain unifiers, that needs to be solved, at
    -- a later stage. / zilinc
    return [t1 :< T (TRefine v t2 (SE (T bool) (BoolLit True)))]
 
  t1 :=: t2@(T (TRefine v _ _)) | notRefinementType t1 ->
    return [T (TRefine v t1 (SE (T bool) (BoolLit True))) :=: t2]

  t1@(T (TRefine v _ _)) :=: t2 | notRefinementType t2 ->
    return [t1 :=: T (TRefine v t2 (SE (T bool) (BoolLit True)))]

  BaseType (T (TCon _ ts _)) -> hoistMaybe $ Just $ map BaseType ts
  BaseType (T (TUnit)) -> hoistMaybe $ Just []
  BaseType (T (TTuple ts)) -> hoistMaybe $ Just $ map BaseType ts
  BaseType (R {}) -> hoistMaybe $ Just []  -- FIXME: descend into the rows / zilinc
  BaseType (V {}) -> hoistMaybe $ Just []  -- FIXME: ditto
  BaseType (A t _ _ _) -> hoistMaybe $ Just [BaseType t]

#endif

  T t1 :< x | unorderedType t1 -> hoistMaybe $ Just [T t1 :=: x]
  x :< T t2 | unorderedType t2 -> hoistMaybe $ Just [x :=: T t2]

  T (TCon n ts s) :=: T (TCon n' us s')
    | s == s', n == n' -> hoistMaybe $ Just (zipWith (:=:) ts us)

  -- Recursive types

  T (TRPar v1 b1 (Just m1)) :<  T (TRPar v2 b2 (Just m2)) -> hoistMaybe $ Just [ ifBang b1 (m1 M.! v1) :< ifBang b2 (m2 M.! v2) ]
  T (TRPar v1 b1 (Just m1)) :=: T (TRPar v2 b2 (Just m2)) -> hoistMaybe $ Just [ ifBang b1 (m1 M.! v1) :=: ifBang b2 (m2 M.! v2) ]

  T (TRPar v1 b1 Nothing) :<  T (TRPar v2 b2 Nothing) | b1 == b2  -> hoistMaybe $ Just []
                                                      | otherwise -> hoistMaybe $ Nothing
  T (TRPar v1 b1 Nothing) :=: T (TRPar v2 b2 Nothing) | b1 == b2  -> hoistMaybe $ Just []
                                                      | otherwise -> hoistMaybe $ Nothing

  T (TRPar v b m) :< x@(R _ _ _)  -> hoistMaybe $ Just [unroll v b m :< x]
  x@(R _ _ _) :<  T (TRPar v b m) -> hoistMaybe $ Just [x :< unroll v b m]
  x@(R _ _ _) :=: T (TRPar v b m) -> hoistMaybe $ Just [x :=: unroll v b m]
  T (TRPar v b m) :=: x@(R _ _ _) -> hoistMaybe $ Just [unroll v b m :=: x]

  UnboxedNotRecursive (R None _ (Left Unboxed))     -> hoistMaybe $ Just []
  UnboxedNotRecursive (R _ _    (Left (Boxed _ _))) -> hoistMaybe $ Just []

  NotReadOnly (Left (Boxed False _)) -> hoistMaybe $ Just []
  NotReadOnly (Left (Unboxed      )) -> hoistMaybe $ Just []

  t -> hoistMaybe $ Nothing

-- | Returns 'True' iff the given argument type is not subject to subtyping. That is, if @a :\< b@
--   (subtyping) is equivalent to @a :=: b@ (equality), then this function returns true.
unorderedType :: Type e l t -> Bool
#ifdef REFINEMENT_TYPES
unorderedType (TCon tn [] Unboxed) | tn `elem` primTypeCons = False
#endif
unorderedType (TCon {}) = True
unorderedType (TVar {}) = True
unorderedType (TUnit)   = True
unorderedType _ = False

psub :: Row.Row t -> Row.Row t -> Bool
psub r1 r2 = isSubsequenceOf (Row.presentLabels r1) (Row.presentLabels r2)

peq :: Row.Row t -> Row.Row t -> Bool
peq r1 r2 = Row.presentLabels r1 == Row.presentLabels r2

pdiff :: Row.Row t -> Row.Row t -> [FieldName]
pdiff r1 r2 = Row.presentLabels r1 L.\\ Row.presentLabels r2

isIrrefutable :: RawPatn -> Bool
isIrrefutable (RP (PIrrefutable _)) = True
isIrrefutable _ = False

isSolved :: TCType -> Bool
isSolved t = L.null (unifVars t) && L.null (unifLVarsT t)
#ifdef REFINEMENT_TYPES
          && L.null (unknowns t)
#endif

isPrimType :: TCType -> Bool
isPrimType (T (TCon n [] Unboxed))
  | n `elem` primTypeCons = True
  | otherwise = False
isPrimType (T (TBang t)) = isPrimType t
isPrimType (T (TUnbox t)) = isPrimType t
isPrimType _ = False

fullyNormalise :: TCType -> Rewrite.RewriteT TcSolvM TCType
fullyNormalise t = undefined

isBoxedType :: TCType -> Bool
isBoxedType (R _ _ (Left (Boxed _ _))) = True
#ifdef REFINEMENT_TYPES
isBoxedType (A _ _ (Left (Boxed _ _)) _) = True
#endif
isBoxedType _ = False

toBoxedType :: TCType -> TCType
toBoxedType (R rp r (Left Unboxed)) = R rp r (Left (Boxed undefined Nothing))
#ifdef REFINEMENT_TYPES
toBoxedType (A t l (Left Unboxed) h) = A t l (Left (Boxed undefined Nothing)) h
#endif
toBoxedType (T (TUnbox t)) = toBoxedType t
toBoxedType t = t

primTypeSize :: TCType -> Size
primTypeSize (T (TCon "U8"   [] Unboxed)) = 8
primTypeSize (T (TCon "U16"  [] Unboxed)) = 16
primTypeSize (T (TCon "U32"  [] Unboxed)) = 32
primTypeSize (T (TCon "U64"  [] Unboxed)) = 64
primTypeSize (T (TCon "Bool" [] Unboxed)) = 1
primTypeSize (T (TBang t))                = primTypeSize t
primTypeSize (T (TUnbox t))               = primTypeSize t
primTypeSize _                            = __impossible "call primTypeSize on non-prim types"

rmF :: TCSigil -> TCSigil
rmF (Left (Boxed _ l)) = Left (Boxed True l)
rmF s = s

doSigilMatch :: TCSigil -> TCSigil -> Maybe [Constraint]
doSigilMatch s1 s2
  | s1 == s2 = Just []
  | Left (Boxed ro1 l1) <- s1
  , Left (Boxed ro2 l2) <- s2
  , ro1 == ro2
  = case (l1, l2) of
      (Just l1', Just l2') -> Just [l1' :~< l2']
      (Nothing , Nothing ) -> Just []
      _                    -> Nothing
  | otherwise = Nothing


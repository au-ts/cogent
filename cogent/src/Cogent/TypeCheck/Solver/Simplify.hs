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
{-# LANGUAGE ViewPatterns #-}

module Cogent.TypeCheck.Solver.Simplify where

import           Cogent.Common.Syntax
import           Cogent.Common.Types
import           Cogent.Compiler
import           Cogent.Dargent.Surface
import           Cogent.Dargent.TypeCheck
import           Cogent.Dargent.Util
import           Cogent.TypeCheck.Base
import qualified Cogent.TypeCheck.LRow as LRow
import qualified Cogent.TypeCheck.Row as Row
import           Cogent.TypeCheck.Row (Entry)
#ifdef BUILTIN_ARRAYS
import           Cogent.TypeCheck.Solver.SMT (smtSat)
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
import           Data.List (elemIndex, null)
import qualified Data.Map as M
import           Data.Maybe
import qualified Data.Set as S
import           Data.Word (Word32)
import           Lens.Micro

import           Debug.Trace

type TCSigil = Either (Sigil (Maybe TCDataLayout)) Int  -- local synonym

onGoal :: (Monad m) => (Constraint -> MaybeT m [Constraint]) -> Goal -> MaybeT m [Goal]
onGoal f g = fmap (map (derivedGoal g)) (f (g ^. goal))

unsat :: (Monad m) => TypeError -> MaybeT m [Constraint]
unsat x = hoistMaybe $ Just [Unsat x]

elseDie :: (Monad m) => Bool -> TypeError -> MaybeT m [Constraint]
elseDie b e = (hoistMaybe $ guard b >> Just []) <|> unsat e

liftTcSolvM :: Rewrite.RewriteT IO a -> Rewrite.RewriteT TcSolvM a
liftTcSolvM (Rewrite.RewriteT m) = Rewrite.RewriteT (\a -> MaybeT $ liftIO $ runMaybeT (m a))

simplify :: [(TyVarName, Kind)] -> [(DLVarName, TCType)] -> Rewrite.RewriteT IO [Goal]
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
    Just (map (flip Share  m) (Row.presentPayloads r))
  Drop   (V r) m | Row.isComplete r ->
    Just (map (flip Drop   m) (Row.presentPayloads r))
  Escape (V r) m | Row.isComplete r ->
    Just (map (flip Escape m) (Row.presentPayloads r))

  Share  (R r (Left s)) m
    | Row.isComplete r
    , not (writable s) -> Just (map (flip Share  m) (Row.presentPayloads r))
  Drop   (R r (Left s)) m
    | Row.isComplete r
    , not (writable s) -> Just (map (flip Drop   m) (Row.presentPayloads r))
  Escape (R r (Left s)) m
    | Row.isComplete r
    , not (readonly s) -> Just (map (flip Escape m) (Row.presentPayloads r))

#ifdef BUILTIN_ARRAYS
  Share  (A t _ (Left s) _) m | not (writable s) -> hoistMaybe $ Just [Share  t m]  -- TODO: deal with the taken fields!!! / zilinc
  Drop   (A t _ (Left s) _) m | not (writable s) -> hoistMaybe $ Just [Drop   t m]  -- TODO
  Escape (A t _ (Left s) _) m | not (readonly s) -> hoistMaybe $ Just [Escape t m]  -- TODO
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

  -- [amos] New simplify rule:
  -- If both sides of an equality constraint are equal, we can't completely discharge it;
  -- we need to make sure all unification variables in the type are instantiated at some point
  t :=: u | t == u -> hoistMaybe $ if isSolved t then Just [] else Just [Solved t]

  Solved t | isSolved t -> hoistMaybe $ Just []

  IsPrimType (T (TCon x _ Unboxed)) | x `elem` primTypeCons -> hoistMaybe $ Just []

  TLVar n        :~ tau | Just t <- lookup n ts
                        -> case doLayoutMatchT tau t of
                             Right c -> hoistMaybe $ Just c
                             Left () -> hoistMaybe Nothing
  TLRepRef _ _   :~ _ -> hoistMaybe Nothing
  TLRecord fs    :~ R _ (Left (Boxed _ (Just l))) -> hoistMaybe $ Just [TLRecord fs :~: l]
  TLRecord fs    :~ R r (Left (Boxed _ Nothing))
    | ls <- LRow.entries $ LRow.fromList $ (\(a,b,c) -> (a,c,())) <$> fs
    , rs <- Row.entries r
    -> hoistMaybe $ Just $ (\((_,e,_),(_,(t,_))) -> e :~ toBoxedType t)
                    <$> M.elems (M.intersectionWith (,) ls rs)
  TLRecord _     :~ R _ (Right _) -> __todo "TLRecord fs :~ R r1 (Right n) => is this possible?"
  TLVariant _ fs :~ V r
    | ls <- LRow.entries $ LRow.fromList $ (\(a,b,c,d) -> (a,d,c)) <$> fs
    , rs <- Row.entries r
    -> hoistMaybe $ Just $ (\((_,e,_),(_,(t,_))) -> e :~ toBoxedType t)
                    <$> M.elems (M.intersectionWith (,) ls rs)
#ifdef BUILTIN_ARRAYS
  TLArray e _    :~ A _ _ (Left (Boxed _ (Just l))) _ -> hoistMaybe $ Just [e :~: l]
  TLArray e _    :~ A t _ (Left (Boxed _ Nothing)) _ -> hoistMaybe $ Just [e :~ t]
  TLArray e _    :~ A _ _ (Right _) _ -> __todo "TLArray e p :~ A t l (Right n) h => is this possible?"
#endif
  TLOffset e _   :~ tau -> hoistMaybe $ Just [e :~ tau]
  TLPrim n       :~ tau
    | isPrimitiveType tau
    , primitiveTypeSize tau <= evalSize n
    -> hoistMaybe $ Just []
    | isBoxedType tau
    , evalSize n == pointerSizeBits
    -> hoistMaybe $ Just []
  TLPtr          :~ tau
    | isBoxedType tau -> hoistMaybe $ Just []
  l              :~ T (TBang tau)    -> hoistMaybe $ Just [l :~ tau]
  l              :~ T (TTake _ tau)  -> hoistMaybe $ Just [l :~ tau]
  l              :~ T (TPut  _ tau)  -> hoistMaybe $ Just [l :~ tau]
#ifdef BUILTIN_ARRAYS
  l              :~ T (TATake _ tau) -> hoistMaybe $ Just [l :~ tau]
  l              :~ T (TAPut  _ tau) -> hoistMaybe $ Just [l :~ tau]
#endif
  _              :~ Synonym _ _      -> hoistMaybe Nothing
  l              :~ tau | TLU _ <- l -> hoistMaybe Nothing
                        | otherwise  -> unsat $ LayoutDoesNotMatchType l tau

  TLRepRef _ _     :~: TLRepRef _ _ -> hoistMaybe Nothing
  TLRepRef _ _     :~: _            -> hoistMaybe Nothing
  _                :~: TLRepRef _ _ -> hoistMaybe Nothing
  TLVar v1         :~: TLVar v2       | v1 == v2 -> hoistMaybe $ Just []
  TLPrim n1        :~: TLPrim n2      | n1 == n2 -> hoistMaybe $ Just []
  TLOffset e1 n1   :~: TLOffset e2 n2 | n1 == n2 -> hoistMaybe $ Just [e1 :~: e2]
  TLRecord fs1     :~: TLRecord fs2
    | r1 <- LRow.fromList $ map (\(a,b,c) -> (a,c,())) fs1
    , r2 <- LRow.fromList $ map (\(a,b,c) -> (a,c,())) fs2
    -> hoistMaybe $ Just $ (\((_,l1,_),(_,l2,_)) -> l1 :~: l2) <$> LRow.common r1 r2
  TLVariant e1 fs1 :~: TLVariant e2 fs2
    | r1 <- LRow.fromList $ map (\(a,b,c,d) -> (a,d,c)) fs1
    , r2 <- LRow.fromList $ map (\(a,b,c,d) -> (a,d,c)) fs2
    , LRow.identicalFields r1 r2
    -> hoistMaybe $ Just $ ((\((_,l1,_),(_,l2,_)) -> l1 :~: l2) <$> LRow.common r1 r2) <> [e1 :~: e2]
#ifdef BUILTIN_ARRAYS
  TLArray e1 _     :~: TLArray e2 _ -> hoistMaybe $ Just [e1 :~: e2]
#endif
  l1               :~: l2 | TLU _ <- l1 -> hoistMaybe Nothing
                          | TLU _ <- l2 -> hoistMaybe Nothing
                          | otherwise   -> do
    traceM ("l1: " ++ show l1 ++ "\nl2: " ++ show l2 ++ "\n")
    unsat $ LayoutsNotCompatible l1 l2

  R r1 s1 :~~ R r2 s2 | Row.null r1 && Row.null r2, (Right c) <- doSigilMatch s1 s2 -> hoistMaybe $ Just c
                      | Just (r1',r2') <- extractVariableEquality r1 r2 -> hoistMaybe $ Just [R r1' s1 :~~ R r2' s2]
                      | otherwise -> do
    let commons  = Row.common r1 r2
    guard (not (L.null commons))
    let (r1',r2') = Row.withoutCommon r1 r2
        cs = map (\ ((_, e),(_,e')) -> fst e :< fst e') commons
        c  = R r1' s1 :< R r2' s2
    hoistMaybe $ Just (c:cs)
  V r1 :~~ V r2 | Row.null r1 && Row.null r2 -> hoistMaybe $ Just []
                | Just (r1',r2') <- extractVariableEquality r1 r2 -> hoistMaybe $ Just [V r1' :~~ V r2']
                | otherwise -> do
    let commons = Row.common r1 r2
        (ls, rs) = unzip commons
    guard (not (L.null commons))
    let (r1', r2') = Row.withoutCommon r1 r2
        cs = map (\((_,e), (_,e')) -> fst e :~~ fst e') commons
        c = V r1' :~~ V r2'
    hoistMaybe $ Just (c:cs)
#ifdef BUILTIN_ARRAYS
  A t1 _ s1 _ :~~ A t2 _ s2 _ | (Right c) <- doSigilMatch s1 s2
                              -> hoistMaybe $ Just ((t1 :~~ t2):c)
#endif
  t1 :~~ t2 | t1 == t2 -> hoistMaybe $ Just []

  T (TLayout l1 t1) :=: T (TLayout l2 t2) -> hoistMaybe $ Just [l1 :~: l2, t1 :=: t2, l1 :~ t1, l2 :~ t2]
  T (TLayout l1 t1) :<  T (TLayout l2 t2) -> hoistMaybe $ Just [l1 :~: l2, t1 :<  t2, l1 :~ t1, l2 :~ t2]

  T (TFun t1 t2) :=: T (TFun r1 r2) -> hoistMaybe $ Just [r1 :=: t1, t2 :=: r2]
  T (TFun t1 t2) :<  T (TFun r1 r2) -> hoistMaybe $ Just [r1 :<  t1, t2 :<  r2]

  T (TTuple ts) :<  T (TTuple us) | length ts == length us -> hoistMaybe $ Just (zipWith (:< ) ts us)
  T (TTuple ts) :=: T (TTuple us) | length ts == length us -> hoistMaybe $ Just (zipWith (:=:) ts us)

  T (TLayout (TLVar _) t1) :<  t2 -> hoistMaybe $ Just [t1 :<  t2]
  T (TLayout (TLVar _) t1) :=: t2 -> hoistMaybe $ Just [t1 :=: t2]

  V r1 :< V r2 | Row.isEmpty r1 && Row.isEmpty r2 -> Just []
               | Row.isComplete r1 && Row.isComplete r2 && psub r1 r2 ->
    let commons  = Row.common r1 r2 in
    do guard (not (null commons))
       hoistMaybe $ Just $ map (\(e,e') -> Row.payload e :< Row.payload e') commons
    
  V r1 :=: V r2 | Row.isEmpty r1 && Row.isEmpty r2 -> Just []
                | Row.isComplete r1 && Row.isComplete r2 && peq r1 r2 ->
    let commons  = Row.common r1 r2 in
    do guard (not (null commons))
       hoistMaybe $ Just $ map (\(e,e') -> Row.payload e :=: Row.payload e') commons

  R r1 s1 :< R r2 s2 | Row.isEmpty r1 && Row.isEmpty r2, Right c <- doSigilMatch s1 s2 -> Just c
                     | Row.isComplete r1 && Row.isComplete r2 && psub r2 r1 ->
    let commons  = Row.common r1 r2 in
    do guard (not (null commons))
       let cs = map (\ (e,e') -> Row.payload e :< Row.payload e') commons
           ds = map (flip Drop ImplicitlyTaken) $ Row.extract (pdiff r1 r2) r1
       hoistMaybe $ Just (cs ++ ds)

  R r1 s1 :=: R r2 s2 | Row.isEmpty r1 && Row.isEmpty r2, Right c <- doSigilMatch s1 s2 -> Just c
                      | Row.isComplete r1 && Row.isComplete r2 && peq r1 r2 ->
    let commons  = Row.common r1 r2 in
    do guard (not (null commons))
       let cs = map (\ (e,e') -> Row.payload e :=: Row.payload e') commons
           ds = map (flip Drop ImplicitlyTaken) $ Row.extract (pdiff r1 r2) r1
       hoistMaybe $ Just (cs ++ ds)

#ifdef BUILTIN_ARRAYS
  -- See [NOTE: solving 'A' types] in Cogent.Solver.Unify
  A t1 l1 s1 (Left r1) :<  A t2 l2 s2 (Left r2) | (Right c) <- doSigilMatch s1 s2 -> do
    guard (not $ isJust r1 && isNothing r2)
    let drop = case (r1,r2) of
                 (r1, r2) | r1 == r2 -> Sat
                 (Nothing, Just i2) -> Drop t1 ImplicitlyTaken
                 (Just i1, Just i2) -> Arith (SE (T (TCon "Bool" [] Unboxed)) (PrimOp "==" [i1,i2]))
    hoistMaybe $ Just ([Arith (SE (T (TCon "Bool" [] Unboxed)) (PrimOp "==" [l1,l2])), t1 :< t2, drop] <> c)

  A t1 l1 s1 (Left r1) :=: A t2 l2 s2 (Left r2) | (Right c) <- doSigilMatch s1 s2 -> do
    guard (isJust r1 && isJust r2 || isNothing r1 && isNothing r2)
    let drop = case (r1,r2) of
                 (r1, r2) | r1 == r2 -> Sat
                 (Just i1, Just i2) -> Arith (SE (T (TCon "Bool" [] Unboxed)) (PrimOp "==" [i1,i2]))
    hoistMaybe $ Just ([Arith (SE (T (TCon "Bool" [] Unboxed)) (PrimOp "==" [l1,l2])), t1 :=: t2, drop] <> c)

  a :-> b -> __fixme $ hoistMaybe $ Just [b]  -- FIXME: cuerently we ignore the impls. / zilinc

  -- TODO: Here we will call a SMT procedure to simplify all the Arith constraints.
  -- The only things left will be non-trivial predicates. / zilinc
  Arith e | isTrivialSE e -> do
              r <- lift $ smtSat e
              if r then hoistMaybe $ Just []
                   else hoistMaybe $ Nothing
          | otherwise -> hoistMaybe $ Nothing
#endif

  T t1 :< x | unorderedType t1 -> hoistMaybe $ Just [T t1 :=: x]
  x :< T t2 | unorderedType t2 -> hoistMaybe $ Just [x :=: T t2]

  T (TCon n ts s) :=: T (TCon n' us s')
    | s == s', n == n' -> hoistMaybe $ Just (zipWith (:=:) ts us)

  t -> hoistMaybe Nothing


-- | Returns 'True' iff the given argument type is not subject to subtyping. That is, if @a :\< b@
--   (subtyping) is equivalent to @a :=: b@ (equality), then this function returns true.
unorderedType :: Type e l t -> Bool
unorderedType (TCon {}) = True
unorderedType (TVar {}) = True
unorderedType (TUnit)   = True
unorderedType _ = False

psub :: Row t -> Row t -> Bool
psub r1 r2 = isSubsequenceOf (Row.presentLabels r1) (Row.presentLabels r2)

peq :: Row t -> Row t -> Bool
peq r1 r2 = Row.presentLabels r1 == Row.presentLabels r2

pdiff :: Row t -> Row t -> [FieldName]
pdiff r1 r2 = Row.presentLabels r1 \\ Row.presentLabels r2

isIrrefutable :: RawPatn -> Bool
isIrrefutable (RP (PIrrefutable _)) = True
isIrrefutable _ = False

isSolved :: TCType -> Bool
isSolved t = L.null (unifVars t) && L.null (unifLVarsT t)
#ifdef BUILTIN_ARRAYS
          && L.null (unknowns t)
#endif

isPrimitiveType :: TCType -> Bool
isPrimitiveType (T (TCon n [] Unboxed))
  | n `elem` words "U8 U16 U32 U64 Bool" = True
  | otherwise = False
isPrimitiveType (T (TBang t)) = isPrimitiveType t
isPrimitiveType (T (TUnbox t)) = isPrimitiveType t
isPrimitiveType _ = False

isBoxedType :: TCType -> Bool
isBoxedType (R _ (Left (Boxed _ _))) = True
#ifdef BUILTIN_ARRAYS
isBoxedType (A _ _ (Left (Boxed _ _)) _) = True
#endif
isBoxedType _ = False

toBoxedType :: TCType -> TCType
toBoxedType (R r (Left Unboxed)) = R r (Left (Boxed undefined Nothing))
#ifdef BUILTIN_ARRAYS
toBoxedType (A t l (Left Unboxed) h) = A t l (Left (Boxed undefined Nothing)) h
#endif
toBoxedType (T (TUnbox t)) = toBoxedType t
toBoxedType t = t

primitiveTypeSize :: TCType -> Size
primitiveTypeSize (T (TCon "U8"   [] Unboxed)) = 8
primitiveTypeSize (T (TCon "U16"  [] Unboxed)) = 16
primitiveTypeSize (T (TCon "U32"  [] Unboxed)) = 32
primitiveTypeSize (T (TCon "U64"  [] Unboxed)) = 64
primitiveTypeSize (T (TCon "Bool" [] Unboxed)) = 8
primitiveTypeSize (T (TBang t))                = primitiveTypeSize t
primitiveTypeSize (T (TUnbox t))               = primitiveTypeSize t
primitiveTypeSize _                            = __impossible "call primitiveTypeSize on non-primitive types"

(<<>>) :: (Semigroup b) => Either a b -> Either a b -> Either a b
(<<>>) (Left a) b = (Left a)
(<<>>) a (Left b) = (Left b)
(<<>>) (Right a) (Right b) = Right (a <> b)

doLayoutMatchT :: TCType -> TCType -> Either () [Constraint]
doLayoutMatchT (T (TVar n1 _ _)) (T (TVar n2 _ _)) = if n1 == n2 then Right []
                                                                 else Left ()
doLayoutMatchT (T (TBang t1)) (T (TBang t2)) = doLayoutMatchT t1 t2
doLayoutMatchT (T (TBang t1)) t2 = doLayoutMatchT t1 t2
doLayoutMatchT t1 (T (TBang t2)) = doLayoutMatchT t1 t2
doLayoutMatchT (R r1 s1) (R r2 s2) = doLayoutMatchR r1 r2 <<>> doSigilMatch s1 s2
doLayoutMatchT (V r1) (V r2) = doLayoutMatchR r1 r2
#ifdef BUILTIN_ARRAYS
doLayoutMatchT (A t1 _ s1 _) (A t2 _ s2 _) = doLayoutMatchT t1 t2 <<>> doSigilMatch s1 s2
#endif
doLayoutMatchT t1@(Synonym{}) t2 = Right [t1 :~~ t2]
doLayoutMatchT t1 t2@(Synonym{}) = Right [t1 :~~ t2]
doLayoutMatchT t1 t2 | t1 == t2 = Right []
                     | otherwise = trace (show t1 ++ "\n" ++ show t2) $ Left ()

doLayoutMatchR :: Row.Row TCType -> Row.Row TCType -> Either () [Constraint]
doLayoutMatchR r1 r2
  | (r1', r2') <- Row.withoutCommon r1 r2
  , Row.null r1' && Row.null r2'
  , rs <- Row.common r1 r2
  = foldr (<<>>) (Right []) $ (\((_, (t1, _)), (_, (t2, _))) -> doLayoutMatchT t1 t2) <$> rs

doSigilMatch :: TCSigil -> TCSigil -> Either () [Constraint]
doSigilMatch s1 s2
  | Left (Boxed _ Nothing) <- s1
  , Left (Boxed _ Nothing) <- s2
  = Right []
  | Left Unboxed <- s1
  , Left (Boxed _ _) <- s2
  = Left ()
  | Left (Boxed _ _) <- s1
  , Left Unboxed <- s2
  = Left ()
  | Left (Boxed _ (Just l1)) <- s1
  , Left (Boxed _ (Just l2)) <- s2
  = Right [l1 :~: l2]
  | Left Unboxed <- s1
  , Left Unboxed <- s2
  = Right []
  | otherwise = trace ("s1: " ++ show s1 ++ "\ns2: " ++ show s2) $ __impossible "doSigilMatch"


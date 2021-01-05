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
import           Lens.Micro

import           Debug.Trace

onGoal :: (Monad m) => (Constraint -> MaybeT m [Constraint]) -> Goal -> MaybeT m [Goal]
onGoal f g = fmap (map (derivedGoal g)) (f (g ^. goal))

unsat :: (Monad m) => TypeError -> MaybeT m [Constraint]
unsat x = hoistMaybe $ Just [Unsat x]

elseDie :: (Monad m) => Bool -> TypeError -> MaybeT m [Constraint]
elseDie b e = (hoistMaybe $ guard b >> Just []) <|> unsat e

liftTcSolvM :: Rewrite.RewriteT IO a -> Rewrite.RewriteT TcSolvM a
liftTcSolvM (Rewrite.RewriteT m) = Rewrite.RewriteT (\a -> MaybeT $ liftIO $ runMaybeT (m a))

simplify :: [(TyVarName, Kind)] -> [(DLVarName, TCType)] -> Rewrite.RewriteT IO [Goal]
simplify ks lts = Rewrite.pickOne' $ onGoal $ \case
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

  Drop  (T (TRPar _ True _)) m -> hoistMaybe $ Just []
  Share (T (TRPar _ True _)) m -> hoistMaybe $ Just []

  -- [amos] New simplify rule:
  -- If both sides of an equality constraint are equal, we can't completely discharge it;
  -- we need to make sure all unification variables in the type are instantiated at some point
  t :=: u | t == u -> 
    hoistMaybe $ if isSolved t then 
      Just [] 
    else
      Just [Solved t]

  Solved t | isSolved t -> hoistMaybe $ Just []

  IsPrimType (T (TCon x _ Unboxed)) | x `elem` primTypeCons -> hoistMaybe $ Just []

  LayoutOk t | isBoxedType t -> hoistMaybe $ Just [TLPtr :~ t]
  LayoutOk (R rp r (Left Unboxed)) -> hoistMaybe $ Just $ (LayoutOk . fst . snd) <$> (Row.unE <$> Row.entries r)
  LayoutOk (V r) -> hoistMaybe $ Just $ (LayoutOk . fst . snd) <$> (Row.unE <$> Row.entries r)
#ifdef BUILTIN_ARRAYS
  LayoutOk (A t e (Left Unboxed) h) -> hoistMaybe $ Just [LayoutOk t]
#endif
  LayoutOk t -> hoistMaybe $ Just []  -- for all the rest, the layouts should be trivially well-formed, as there's no layout.
  TLVar n        :~ tau | Just t <- lookup n lts -> hoistMaybe $ Just [tau :~~ t]  -- `l :~ t ==> l :~ tau` gets simplified to `tau :~~ t`
  TLRepRef _ _   :~ _ -> hoistMaybe Nothing

  TLRecord fs    :~ R _ r (Left Unboxed)
    | ls <- M.fromList $ (\(f,_,l) -> (f,l)) <$> fs
    , rs <- M.fromList $ Row.unE <$> Row.entries r
    , cs <- M.intersectionWith (,) ls rs
    , M.null $ M.difference rs cs
    -> hoistMaybe $ Just $ (\(l,(t,_)) -> l :~ t) <$> M.elems cs
  TLRecord _     :~ R _ _ (Right _) -> __todo "TLRecord fs :~ R r1 (Right n) => is this possible?"

  TLVariant _ fs :~ V r
    | ls <- M.fromList $ (\(f,_,_,l) -> (f,l)) <$> fs
    , rs <- M.fromList $ Row.unE <$> Row.entries r
    , cs <- M.intersectionWith (,) ls rs
    , M.null $ M.difference rs cs
    -> hoistMaybe $ Just $ (\(l,(t,_)) -> l :~ t) <$> M.elems cs

#ifdef BUILTIN_ARRAYS
  TLArray e _    :~ A t _ (Left Unboxed) _ -> hoistMaybe $ Just [e :~ t]
  TLArray e _    :~ A _ _ (Right _) _ -> __todo "TLArray e p :~ A t l (Right n) h => is this possible?"
#endif

  TLOffset e _   :~ tau -> hoistMaybe $ Just [e :~ tau]

  TLPrim n       :~ T TUnit | evalSize n >= 0 -> hoistMaybe $ Just []
  TLPrim n       :~ tau
    | isPrimType tau
    , primTypeSize tau == evalSize n
    -> hoistMaybe $ Just []
    | isBoxedType tau
    , evalSize n == pointerSizeBits
    -> hoistMaybe $ Just []

  TLPtr          :~ R rp r (Left (Boxed _ (Just l))) -> hoistMaybe $ Just [l :~ R rp r (Left Unboxed)]
  TLPtr          :~ R rp r (Left (Boxed _ Nothing )) -> hoistMaybe $ Just [LayoutOk (R rp r (Left Unboxed))]
#ifdef BUILTIN_ARRAYS
  TLPtr          :~ A t e (Left (Boxed _ (Just l))) h -> hoistMaybe $ Just [l :~ A t e (Left Unboxed) h]
  TLPtr          :~ A t e (Left (Boxed _ Nothing )) h -> hoistMaybe $ Just [LayoutOk (A t e (Left Unboxed) h)]
#endif
  l              :~ T (TBang tau)    -> hoistMaybe $ Just [l :~ tau]
  l              :~ T (TTake _ tau)  -> hoistMaybe $ Just [l :~ tau]
  l              :~ T (TPut  _ tau)  -> hoistMaybe $ Just [l :~ tau]
#ifdef BUILTIN_ARRAYS
  l              :~ T (TATake _ tau) -> hoistMaybe $ Just [l :~ tau]
  l              :~ T (TAPut  _ tau) -> hoistMaybe $ Just [l :~ tau]
#endif
  _              :~ Synonym _ _      -> hoistMaybe Nothing
  l              :~ tau | TLU _ <- l -> hoistMaybe Nothing

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

#ifdef BUILTIN_ARRAYS
  TLArray e1 _     :~< TLArray e2 _ -> hoistMaybe $ Just [e1 :~< e2]
#endif

  l1               :~< l2 | TLU _ <- l1 -> hoistMaybe Nothing
                          | TLU _ <- l2 -> hoistMaybe Nothing
                          | otherwise   -> unsat $ LayoutsNotCompatible l1 l2  -- FIXME!

  t1 :~~ t2 | isBoxedType t1, isBoxedType t2 -> hoistMaybe $ Just []  -- If both are pointers, then their layouts will be compatible

  T (TVar n1 _ _) :~~ T (TVar n2 _ _) | n1 == n2 -> hoistMaybe $ Just []

  R rp1 r1 (Left Unboxed) :~~ R rp2 r2 (Left Unboxed)
    | Row.isComplete r1, Row.isComplete r2, S.fromList (Row.fnames r1) `S.isSubsetOf` S.fromList (Row.fnames r2)
    -> hoistMaybe $ Just $ map (\(e1,e2) -> Row.payload e1:~~ Row.payload e2) (Row.common r1 r2)

  V r1 :~~ V r2
    | Row.isComplete r1, Row.isComplete r2, S.fromList (Row.fnames r1) `S.isSubsetOf` S.fromList (Row.fnames r2)
    -> hoistMaybe $ Just $ map (\(e1,e2) -> Row.payload e1 :~~ Row.payload e2) (Row.common r1 r2)

#ifdef BUILTIN_ARRAYS
  A t1 _ (Left Unboxed) _ :~~ A t2 _ (Left Unboxed) _ -> hoistMaybe $ Just [t1 :~~ t2]
#endif
  T (TVar n1 _ _) :~~ T (TVar n2 _ _) | n1 == n2 -> hoistMaybe $ Just []

  t1 :~~ t2 | t1 == t2 -> hoistMaybe $ Just []
            | isPrimType t1 && isPrimType t2
            , primTypeSize t1 <= primTypeSize t2
            -> hoistMaybe $ Just []
            | otherwise -> unsat $ TypesNotFit t1 t2

  T (TFun t1 t2) :=: T (TFun r1 r2) -> hoistMaybe $ Just [r1 :=: t1, t2 :=: r2]
  T (TFun t1 t2) :<  T (TFun r1 r2) -> hoistMaybe $ Just [r1 :<  t1, t2 :<  r2]

  T (TTuple ts) :<  T (TTuple us) | length ts == length us -> hoistMaybe $ Just (zipWith (:< ) ts us)
  T (TTuple ts) :=: T (TTuple us) | length ts == length us -> hoistMaybe $ Just (zipWith (:=:) ts us)

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
    , Just c <- sigilMatch s1 s2
    , sameRecursive rp1 rp2
    -> hoistMaybe $ Just c
    | Row.isComplete r1 && Row.isComplete r2
    , Just c <- sigilMatch s1 s2
    , psub r2 r1 ->
      let commons = Row.common r1 r2 in
      do guard (not (null commons))
         let cs = map (\(e,e') -> Row.payload e :< Row.payload e') commons
             ds = map (flip Drop ImplicitlyTaken) $ Row.extract (pdiff r1 r2) r1
         hoistMaybe $ Just (c ++ cs ++ ds)

  R rp1 r1 s1 :=: R rp2 r2 s2
    | Row.isEmpty r1 && Row.isEmpty r2
    , Just c <- sigilMatch s1 s2
    , sameRecursive rp1 rp2
    -> hoistMaybe $ Just c
    | Row.isComplete r1 && Row.isComplete r2
    , Just c <- sigilMatch s1 s2
    , peq r1 r2 ->
      let commons = Row.common r1 r2 in
      do guard (not (null commons))
         let cs = map (\(e,e') -> Row.payload e :=: Row.payload e') commons
             ds = map (flip Drop ImplicitlyTaken) $ Row.extract (pdiff r1 r2) r1
         hoistMaybe $ Just (c ++ cs ++ ds)

#ifdef BUILTIN_ARRAYS
  -- See [NOTE: solving 'A' types] in Cogent.Solver.Unify
  A t1 l1 s1 (Left r1) :<  A t2 l2 s2 (Left r2) | Just c <- sigilMatch s1 s2 -> do
    guard (not $ isJust r1 && isNothing r2)
    let drop = case (r1,r2) of
                 (r1, r2) | r1 == r2 -> Sat
                 (Nothing, Just i2) -> Drop t1 ImplicitlyTaken
                 (Just i1, Just i2) -> Arith (SE (T (TCon "Bool" [] Unboxed)) (PrimOp "==" [i1,i2]))
    hoistMaybe $ Just (c <> [Arith (SE (T (TCon "Bool" [] Unboxed)) (PrimOp "==" [l1,l2])), t1 :< t2, drop])

  A t1 l1 s1 (Left r1) :=: A t2 l2 s2 (Left r2) | Just c <- sigilMatch s1 s2 -> do
    guard (isJust r1 && isJust r2 || isNothing r1 && isNothing r2)
    let drop = case (r1,r2) of
                 (r1, r2) | r1 == r2 -> Sat
                 (Just i1, Just i2) -> Arith (SE (T (TCon "Bool" [] Unboxed)) (PrimOp "==" [i1,i2]))
    hoistMaybe $ Just (c <> [Arith (SE (T (TCon "Bool" [] Unboxed)) (PrimOp "==" [l1,l2])), t1 :=: t2, drop])

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

  -- Recursive types

  T (TRPar v1 b1 (Just m1)) :<  T (TRPar v2 b2 (Just m2)) -> hoistMaybe $ Just [ ifBang b1 (m1 M.! v1) :< ifBang b2 (m2 M.! v2) ]
  T (TRPar v1 b1 (Just m1)) :=: T (TRPar v2 b2 (Just m2)) -> hoistMaybe $ Just [ ifBang b1 (m1 M.! v1) :=: ifBang b2 (m2 M.! v2) ]

  T (TRPar v1 b1 Nothing) :<  T (TRPar v2 b2 Nothing) | b1 == b2  -> hoistMaybe $ Just []
                                                      | otherwise -> hoistMaybe $ Nothing
  T (TRPar v1 b1 Nothing) :=: T (TRPar v2 b2 Nothing) | b1 == b2  -> hoistMaybe $ Just []
                                                      | otherwise -> hoistMaybe $ Nothing

  T (TRPar v b m) :< x@(R _ _ _)  -> hoistMaybe $ Just [unroll v b m :< x]
  x@(R _ _ _) :< T (TRPar v b m)  -> hoistMaybe $ Just [x :< unroll v b m]
  x@(R _ _ _) :=: T (TRPar v b m) -> hoistMaybe $ Just [x :=: unroll v b m]
  T (TRPar v b m) :=: x@(R _ _ _) -> hoistMaybe $ Just [unroll v b m :=: x]

  UnboxedNotRecursive (R None _ (Left Unboxed))     -> hoistMaybe $ Just []
  UnboxedNotRecursive (R _ _    (Left (Boxed _ _))) -> hoistMaybe $ Just []

  NotReadOnly (Left (Boxed False _)) -> hoistMaybe $ Just []
  NotReadOnly (Left (Unboxed      )) -> hoistMaybe $ Just []

  -- TODO TODO TODO
  Wellformed l -> hoistMaybe $ Just []
  -- TODO TODO TODO

  t -> hoistMaybe $ Nothing

-- | Returns 'True' iff the given argument type is not subject to subtyping. That is, if @a :\< b@
--   (subtyping) is equivalent to @a :=: b@ (equality), then this function returns true.
unorderedType :: Type e l t -> Bool
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
#ifdef BUILTIN_ARRAYS
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
isBoxedType (R _ _ (Left (Boxed {}))) = True
isBoxedType (T (TCon _ _ (Boxed {}))) = True
#ifdef BUILTIN_ARRAYS
isBoxedType (A _ _ (Left (Boxed {})) _) = True
#endif
isBoxedType _ = False

primTypeSize :: TCType -> Size
primTypeSize (T (TCon "U8"   [] Unboxed)) = 8
primTypeSize (T (TCon "U16"  [] Unboxed)) = 16
primTypeSize (T (TCon "U32"  [] Unboxed)) = 32
primTypeSize (T (TCon "U64"  [] Unboxed)) = 64
primTypeSize (T (TCon "Bool" [] Unboxed)) = 1
primTypeSize (T (TBang t))                = primTypeSize t
primTypeSize (T (TUnbox t))               = primTypeSize t
primTypeSize _                            = __impossible "call primTypeSize on non-prim types"

sigilMatch :: TCSigil -> TCSigil -> Maybe [Constraint]
sigilMatch s1 s2
  | s1 == s2 = Just []
  | Left (Boxed ro1 l1) <- s1
  , Left (Boxed ro2 l2) <- s2
  , ro1 == ro2
  = case (l1, l2) of
      (Just l1', Just l2') -> Just [l1' :~< l2']
      (Nothing , Nothing ) -> Just []
      _                    -> Nothing
  | otherwise = Nothing

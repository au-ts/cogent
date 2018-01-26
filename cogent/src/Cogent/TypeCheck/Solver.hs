--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Cogent.TypeCheck.Solver (runSolver, solve) where

import           Cogent.Common.Syntax
import           Cogent.Common.Types
import           Cogent.Compiler (__impossible)
import           Cogent.PrettyPrint (prettyC)
import           Cogent.Surface
import           Cogent.TypeCheck.Base
import qualified Cogent.TypeCheck.Subst as Subst
import           Cogent.TypeCheck.Subst (Subst)
import           Cogent.TypeCheck.Util
import           Cogent.TypeCheck.GoalSet (Goal (..), goal, goalContext, GoalSet)
import qualified Cogent.TypeCheck.GoalSet as GS

import           Control.Applicative
import           Control.Lens hiding ((:<))
import           Control.Monad.State
import qualified Data.Foldable as F
import           Data.Function (on)
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
--import qualified Data.List as L
import           Data.List (elemIndex)
import qualified Data.Map as M
import           Data.Maybe
import           Data.Monoid
import qualified Data.Set as S
import qualified Text.PrettyPrint.ANSI.Leijen as P
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))

data SolverState = SS { _flexes      :: Int
                      , _tc          :: TCState
                      , _substs      :: Subst
                      , _axioms      :: [(TyVarName, Kind)]
                      , _flexOrigins :: IM.IntMap VarOrigin
                      }

makeLenses ''SolverState

type Solver = StateT SolverState IO


runSolver :: Solver a -> Int -> IM.IntMap VarOrigin -> [(VarName, Kind)] -> TC (a, Subst, IM.IntMap VarOrigin)
runSolver act i os ks = do
  x <- get
  (a, SS _ x' s _ o) <- lift $ runStateT act (SS i x mempty ks os)
  put x'
  return (a,s,o)

-- Flatten a constraint tree into a set of flat goals
crunch :: Constraint -> TC [Goal]
crunch (x :@ e) = map (goalContext %~ (++[e])) <$> crunch x
crunch (x :& y) = (++) <$> crunch x <*> crunch y
crunch Sat   = return []
crunch x     = return [Goal [] x]

-- Rewrites out type synonyms, TUnbox, TBang, TTake, and TPut
-- so that the "head" of the type is guaranteed to be a concrete type.
-- Operators like TUnbox, TBang etc. are left in place if there is
-- a unification variable.

whnf :: TCType -> TC TCType
whnf (T (TUnbox t)) = do
   t' <- whnf t
   return $ case t' of
     _ | notWhnf t'    -> T (TUnbox t')
     (T (TCon x ps _)) -> T (TCon x ps Unboxed)
     (T (TRecord l _)) -> T (TRecord l Unboxed)
     (T o)             -> T (fmap (T . TUnbox) o)
     _                 -> error "impossible"

whnf (T (TBang t)) = do
   t' <- whnf t
   return $ case t' of
     _ | notWhnf t'    -> T (TBang t')
     (T (TCon x ps s)) -> T (TCon x (map (T . TBang) ps) (bangSigil s))
     (T (TRecord l s)) -> T (TRecord (map (fmap (_1 %~ T . TBang)) l) (bangSigil s))
     (T (TVar b _))    -> T (TVar b True)
     (T (TFun {}))     -> t'
     (T o)             -> T (fmap (T . TBang) o)
     _                 -> error "impossible"

whnf (T (TTake fs t)) = do
   t' <- whnf t
   return $ case t' of
     (T (TRecord l s)) -> T (TRecord (takeFields fs l) s)
     (T (TVariant l))  -> T (TVariant (M.fromList $ takeFields fs $ M.toList l))
     _ | Just fs' <- fs, null fs'  -> t'
     _                 -> T (TTake fs t')
 where
   takeFields :: Maybe [FieldName] -> [(FieldName, (a , Bool))] -> [(FieldName, (a, Bool))]
   takeFields Nothing   = map (fmap (fmap (const True)))
   takeFields (Just fs) = map (\(f, (t, b)) -> (f, (t, f `elem` fs || b)))

whnf (T (TPut fs t)) = do
   t' <- whnf t
   return $ case t' of
     (T (TRecord l s)) -> T (TRecord (putFields fs l) s)
     (T (TVariant l))  -> T (TVariant (M.fromList $ putFields fs $ M.toList l))
     _ | Just fs' <- fs, null fs'  -> t'
     _                 -> T (TPut fs t')
 where
   putFields :: Maybe [FieldName] -> [(FieldName, (a, Bool))] -> [(FieldName, (a, Bool))]
   putFields Nothing   = map (fmap (fmap (const False)))
   putFields (Just fs) = map (\(f, (t, b)) -> (f, (t,  (f `notElem` fs) && b)))

whnf (T (TCon n as b)) = do
  kts <- use knownTypes
  case lookup n kts of
    Just (as', Just b) -> whnf (substType (zip as' as) b)
    _ -> return (T (TCon n as b))

whnf t = return t


-- Used internally in whnf, to check if a type has been normalised. If not,
-- it means that there is a flex or type variable preventing evaluation.
notWhnf :: TCType -> Bool
notWhnf (T TTake  {})    = True
notWhnf (T TPut   {})    = True
notWhnf (T TUnbox {})    = True
notWhnf (T TBang  {})    = True
notWhnf (U u)            = True
notWhnf _                = False

isIrrefutable :: RawPatn -> Bool
isIrrefutable (RP (PIrrefutable _)) = True
isIrrefutable _ = False

patternTag :: RawPatn -> Maybe TagName
patternTag (RP (PCon t _)) = Just t
patternTag _ = Nothing

-- isVarCon :: Pattern a -> Bool
-- isVarCon (PCon {}) = True
-- isVarCon _ = False

-- Explodes a rigid/rigid constraint into subgoals necessary
-- for that to be true. E.g, (a,b) :< (c,d) becomes a :< c :& b :< d.
-- Assumes that the input is simped (i.e conjunction and context free, with types in whnf)
-- Returns `Nothing' if the constraint cannot be further transformed.
rule' :: (?lvl :: Int) => Constraint -> IO (Maybe Constraint)
rule' c = ruleT c >>= return . ((:@ SolvingConstraint c) <$>)

ruleT :: (?lvl :: Int) => Constraint -> IO (Maybe Constraint)
ruleT c = do
  traceTc "sol" (brackets (int ?lvl) <+> text "apply rule to" <+> prettyC c)
  mc <- rule c
  traceTc "sol" . ((brackets (int ?lvl) <+> prettyC c) <+>) $ case mc of
    Nothing -> text "doesn't change"
    Just c' -> text "becomes" <+> prettyC c'
  return mc

rule :: (?lvl :: Int) => Constraint -> IO (Maybe Constraint)
rule (Exhaustive t ps) | any isIrrefutable ps = return $ Just Sat
rule (Exhaustive (T (TVariant n)) ps)
  | s1 <- S.fromList (mapMaybe patternTag ps)
  , s2 <- S.fromList (map fst $ filter (not . snd . snd) $ M.toList n)
  = return $ if s1 == s2
               then Just Sat
               else Just $ Unsat (PatternsNotExhaustive (T (TVariant n)) (S.toList (s2 S.\\ s1)))

rule (Exhaustive (T (TCon "Bool" [] Unboxed)) [RP (PBoolLit t), RP (PBoolLit f)])
   = return $ if not (t && f) && (t || f) then Just Sat
              else Just $ Unsat $ PatternsNotExhaustive (T (TCon "Bool" [] Unboxed)) []

rule (Exhaustive t ps)
  | not (notWhnf t) = return . Just . Unsat $ PatternsNotExhaustive t []

rule (x :@ c) = do
  let ?lvl = ?lvl + 1
  return . ((:@ c) <$>) =<< ruleT x

rule (x :& y) = do
  let ?lvl = ?lvl + 1
  x' <- ruleT x
  y' <- ruleT y
  return ((:&) <$> x' <*> y'
      <|> (x :&) <$> y'
      <|> (:& y) <$> x')

rule Unsat   {} = return Nothing
rule SemiSat {} = return Nothing
rule Sat     {} = return Nothing

rule (Share  (T (TVar _ s)) _) | s         = return $ Just Sat
                               | otherwise = return $ Nothing
rule (Drop   (T (TVar _ s)) _) | s         = return $ Just Sat
                               | otherwise = return $ Nothing
rule (Escape (T TVar {}) _) = return Nothing

rule (Share  (T (TTuple xs)) m) = return . Just . mconcat $ map (flip Share m) xs
rule (Drop   (T (TTuple xs)) m) = return . Just . mconcat $ map (flip Drop m) xs
rule (Escape (T (TTuple xs)) m) = return . Just . mconcat $ map (flip Escape m) xs

rule (Share  (T TUnit) m) = return $ Just Sat
rule (Drop   (T TUnit) m) = return $ Just Sat
rule (Escape (T TUnit) m) = return $ Just Sat

rule (Share  (T TFun {}) m) = return $ Just Sat
rule (Drop   (T TFun {}) m) = return $ Just Sat
rule (Escape (T TFun {}) m) = return $ Just Sat

rule (Share  (T (TVariant n)) m) = return . Just $ foldMap (\(ts, t) -> if t then Sat else mconcat $ map (flip Share  m) ts) n
rule (Drop   (T (TVariant n)) m) = return . Just $ foldMap (\(ts, t) -> if t then Sat else mconcat $ map (flip Drop   m) ts) n
rule (Escape (T (TVariant n)) m) = return . Just $ foldMap (\(ts, t) -> if t then Sat else mconcat $ map (flip Escape m) ts) n

rule (Share  t@(T (TRecord fs s)) m)
  | s /= Writable = return . Just $ foldMap (\(x, t) -> if not t then Share x m else Sat) $ map snd fs
  | otherwise     = return . Just $ Unsat $ TypeNotShareable t m
rule (Drop   t@(T (TRecord fs s)) m)
  | s /= Writable = return . Just $ foldMap (\(x, t) -> if not t then Drop x m else Sat) $ map snd fs
  | otherwise     = return . Just $ Unsat $ TypeNotDiscardable t m
rule (Escape t@(T (TRecord fs s)) m)
  | s /= ReadOnly = return . Just $ foldMap (\(x, t) -> if not t then Escape x m else Sat) $ map snd fs
  | otherwise     = return . Just $ Unsat $ TypeNotEscapable t m

rule (Share  t@(T (TCon n ts s)) m)
  | s /= Writable = return $ Just Sat
  | otherwise     = return $ Just $ Unsat $ TypeNotShareable t m
rule (Drop   t@(T (TCon n ts s)) m)
  | s /= Writable = return $ Just Sat
  | otherwise     = return $ Just $ Unsat $ TypeNotDiscardable t m
rule (Escape t@(T (TCon n ts s)) m)
  | s /= ReadOnly = return $ Just Sat
  | otherwise     = return $ Just $ Unsat $ TypeNotEscapable t m


rule (F (T (TTuple xs)) :< F (T (TTuple ys)))
  | length xs /= length ys = return $ Just $ Unsat (TypeMismatch (F (T (TTuple xs))) (F (T (TTuple ys))))
  | otherwise              = return $ Just $ mconcat (zipWith (:<) (map F xs) (map F ys))
rule ct@(F (T (TFun a b))  :< F (T (TFun c d))) = 
  return . Just $ (F c :< F a) :& (F b :< F d)
rule (F (T TUnit     )  :< F (T TUnit))      = return $ Just Sat
rule (F (T (TVar v b))  :< F (T (TVar u c)))
  | v == u, b == c = return $ Just Sat
  | otherwise      = return $ Just $ Unsat (TypeMismatch (F $ T (TVar v b)) (F $ T (TVar u c)))
rule (F (T (TCon n ts s)) :< F (T (TCon m us r)))
  | n == m, length ts == length us, s == r = return $ Just $ mconcat (zipWith (:<) (map F ts) (map F us))
 --                  ++ zipWith (:<) (map F us) (map F ts))
  | otherwise                              = return $ Just $ Unsat (TypeMismatch (F $ T (TCon n ts s)) (F $ T (TCon m us r)))
rule ct@(F (T (TRecord fs s)) :< F (T (TRecord gs r)))
  | or (zipWith ((/=) `on` fst) fs gs) = do
      traceTc "sol" (text "apply rule to" <+> prettyC ct <> semi
               P.<$> text "record fields do not match")
      return $ Just $ Unsat (TypeMismatch (F $ T (TRecord fs s)) (F $ T (TRecord gs r)))
  | length fs /= length gs             = return $ Just $ Unsat (TypeMismatch (F $ T (TRecord fs s)) (F $ T (TRecord gs r)))
  | s /= r                             = return $ Just $ Unsat (TypeMismatch (F $ T (TRecord fs s)) (F $ T (TRecord gs r)))
  | otherwise                          = do
     let each (_, (t, False)) (_, (u, True )) = (F t :< F u) :& Drop t ImplicitlyTaken
         each (_, (t, False)) (_, (u, False)) = F t :< F u
         each (_, (t, True )) (_, (u, True )) = F t :< F u
         each (f, (t, True )) (_, (u, False)) = Unsat (RequiredTakenField f t)
         cs = zipWith each fs gs
     traceTc "sol" (text "solve each field of constraint" <+> prettyC ct <> colon
       P.<$> foldl
               (\a (f,c) -> a P.<$> text "field" <+> pretty (fst f) P.<> colon <+> prettyC c)
               P.empty
               (zip fs cs))
     return . Just $ mconcat cs
rule (F (T (TVariant m)) :< F (T (TVariant n)))
  | M.keys m /= M.keys n = return $ Just $ Unsat (TypeMismatch (F $ T (TVariant m)) (F $ T (TVariant n)))
  | otherwise = let
      each (f, (ts, False)) (_, (us, True )) = Unsat (DiscardWithoutMatch f)
      each (f, (ts, _)) (_, (us, _)) | length ts /= length us = Unsat (DifferingNumberOfConArgs f (length ts) (length us))
      each (f, (ts, False)) (_, (us, False)) = mconcat (zipWith (:<) (map F ts) (map F us))
      each (f, (ts, True )) (_, (us, True )) = mconcat (zipWith (:<) (map F ts) (map F us))
      each (f, (ts, True )) (_, (us, False)) = mconcat (zipWith (:<) (map F ts) (map F us))
    in return $ Just $ mconcat (zipWith each (M.toList m) (M.toList n))
-- This rule is a bit dodgy
-- rule (T (TTake (Just a) b) :< T (TTake (Just a') c))
--   | x <- L.intersect a a'
--   , not (null x)
--   = let
--       ax  = a L.\\ x
--       a'x = a' L.\\ x
--      in Just $  ((if null ax then id else T . TTake (Just ax)) b)
--              :< ((if null a'x then id else T . TTake (Just a'x)) c)
rule (F (T (TTake fs (U x))) :< F y)
  | not (notWhnf y)
  = return $ Just $ F (U x) :< F (T (TPut fs y))
rule (F (T (TPut fs (U x))) :< F y)
  | not (notWhnf y)
  = return $ Just $ F (U x) :< F (T (TTake fs y))
rule (F y :< F (T (TTake fs (U x))))
  | not (notWhnf y)
  = return $ Just $ F (T (TPut fs y)) :< F (U x)
rule (F y :< F (T (TPut fs (U x))))
  | not (notWhnf y)
  = return $ Just $ F (T (TTake fs y)) :<  F (U x)
-- rule (F (T (TTake (Just fs) (U x))) :< FVariant vs es)
--   = return $ Just $ F ( U x) :< uncurry FVariant (putVariant fs vs es)
-- rule (F (T (TPut (Just fs) (U x))) :< FVariant vs es)
--   = return $ Just $ F ( U x) :< uncurry FVariant (takeVariant fs vs es)
-- rule ( FVariant vs es :< F (T (TTake (Just fs) (U x))))
--   = return $ Just $ uncurry FVariant (putVariant fs vs es) :< F (U x)
-- rule (FVariant vs es :< F (T (TPut (Just fs) (U x))) )
--   = return $ Just $ uncurry FVariant (takeVariant fs vs es) :<  F ( U x)
rule (F (T (TBang a)) :< F b)
  | isBangInv b = return $ Just (F a :< F b)
rule (F a :< F (T (TBang b)))
  | isBangInv a = return $ Just (F a :< F b)
rule ct@(F a :< b)
  | notWhnf a = do
      traceTc "sol" (text "constraint" <+> prettyC ct <+> text "with LHS non-WHNF")
      return Nothing
rule ct@(a :< F b)
  | notWhnf b = do
      traceTc "sol" (text "constraint" <+> prettyC ct <+> text "with RHS non-WHNF")
      return Nothing
rule (Upcastable (T (TCon n [] Unboxed)) (T (TCon m [] Unboxed)))
  | Just n' <- elemIndex n primTypeCons
  , Just m' <- elemIndex m primTypeCons
  , n' <= m'
  , m /= "String"
  = return $ Just Sat
rule ct@(FVariant n :< F (T (TVariant m)))
  | ns <- M.keysSet n
  , ns `S.isSubsetOf` M.keysSet m
  , n'' <- fmap (_1 %~ Just) n
  , m'' <- fmap (_1 %~ Just) m
  = parVariants n'' m'' ns
rule ct@(F (T (TVariant n)) :< FVariant m)
  | ms <- M.keysSet m
  , ms `S.isSubsetOf` M.keysSet n
  , n'' <- fmap (_1 %~ Just) n
  , m'' <- fmap (_1 %~ Just) m
  = parVariants n'' m'' ms
rule ct@(FVariant n :< FVariant m )
  | ns <- M.keysSet n
  , ns == M.keysSet m
  , m'' <- fmap (_1 %~ Just) m
  , n'' <- fmap (_1 %~ Just) n
  = parVariants n'' m'' ns
rule ct@(FRecord (M.fromList -> n) :< F (T (TRecord (M.fromList -> m) s)))
  | ns <- M.keysSet n
  , ns `S.isSubsetOf` M.keysSet m
  = parRecords n m ns
rule ct@(F (T (TRecord (M.fromList -> n) s)) :< FRecord (M.fromList -> m))
  | ms <- M.keysSet m
  , ms `S.isSubsetOf` M.keysSet n
  = parRecords n m ms
rule ct@(FRecord (M.fromList -> n) :< FRecord (M.fromList -> m))
  | ns <- M.keysSet n
  , ns == M.keysSet m
  = parRecords n m ns
rule ct@(a :< b) = do
  traceTc "sol" (text "apply rule to" <+> prettyC ct <> semi
           P.<$> text "yield type mismatch")
  return . Just $ Unsat (TypeMismatch a b)
rule ct = do
  -- traceTc "sol" (text "apply rule to" <+> prettyC ct <> semi
  --          P.<$> text "yield nothing")
  return Nothing

-- `parRecords' and `parVariant' are used internally in `rule'
parRecords n m ks =
  let each f (t, False) (u, True ) = (F t :< F u) :& Drop t ImplicitlyTaken
      each f (t, False) (u, False) = F t :< F u
      each f (t, True ) (u, True ) = F t :< F u
      each f (t, True ) (u, False) = Unsat (RequiredTakenField f t)
      ks' = S.toList ks
      cs  = map (\k -> each k (n M.! k) (m M.! k)) ks'
  in return . Just $ mconcat cs

parVariants n m ks =
  let each t (Nothing, _)    (_, False)       = Sat
      each t (Nothing, True) (_, True)        = Sat
      each t (Just ts, _)    (Just us, _) | length ts /= length us  = Unsat (DifferingNumberOfConArgs t (length ts) (length us))
      each t (Just ts, _)    (Just us, False) = mconcat (zipWith (:<) (map F ts) (map F us))
      each t (Just ts, True) (Just us, True)  = mconcat (zipWith (:<) (map F ts) (map F us))
      each t (_, False)      (_, True)        = Unsat (RequiredTakenTag t)
      ks' = S.toList ks
      cs  = map (\k -> each k (n M.! k) (m M.! k)) ks'
  in return . Just $ mconcat cs

-- putVariant [] vs es = (vs,es)
-- putVariant (f:fs) vs es | f `M.member` vs = putVariant fs (M.adjust (\(t,b) -> (t, True)) f vs ) es
--                         | otherwise       = putVariant fs vs (M.insertWith (||) f True es)
-- takeVariant [] vs es = (vs,es)
-- takeVariant (f:fs) vs es | f `M.member` vs = takeVariant fs (M.adjust (\(t,b) -> (t, False)) f vs ) es
--                          | otherwise       = takeVariant fs vs (M.insertWith (&&) f False es)

apply :: (Constraint -> TC Constraint) -> [Goal] -> TC [Goal]
apply tactic = fmap concat . mapM each
  where each (Goal ctx c) = do
          traceTc "sol" (text "apply tactic to goal" <+> prettyC c)
          c' <- tactic c
          traceTc "sol" (text "after tactic" <+> prettyC c </> text "becomes" <+> prettyC c')
          map (goalContext %~ (++ ctx)) <$> crunch c'

-- Applies simp and rules as much as possible
auto :: Constraint -> TC Constraint
auto c = do
  traceTc "sol" (text "auto")
  let ?lvl = 0
  c' <- simp c
  liftIO (rule' c') >>= \case
    Nothing  -> return c'
    Just c'' -> auto c''

-- applies whnf to every type in a constraint.
simp :: Constraint -> TC Constraint
simp (a :< b)          = (:<)       <$> traverse whnf a <*> traverse whnf b
simp (Upcastable a b)  = Upcastable <$> whnf a <*> whnf b
simp (a :& b)          = (:&)       <$> simp a <*> simp b
simp (Share  t m)      = Share      <$> whnf t <*> pure m
simp (Drop   t m)      = Drop       <$> whnf t <*> pure m
simp (Escape t m)      = Escape     <$> whnf t <*> pure m
simp (a :@ c)          = (:@)       <$> simp a <*> pure c
simp (Unsat e)         = pure (Unsat e)
simp (SemiSat w)       = pure (SemiSat w)
simp Sat               = pure Sat
simp (Exhaustive t ps) = Exhaustive <$> whnf t <*> pure ps

fresh :: VarOrigin -> Solver TCType
fresh ctx = do
  i <- flexes <<%= succ
  flexOrigins %= IM.insert i ctx
  return $ U i


glb = bound GLB
lub = bound LUB

-- Constructs a partially specified type that could plausibly be :< the two inputs.
-- We re-check some basic equalities here for better error messages
bound :: Bound -> TypeFragment TCType -> TypeFragment TCType -> Solver (Maybe (TypeFragment TCType), TypeFragment TCType, TypeFragment TCType)
bound d (F a) (F b) = fmap ((, F a, F b) . fmap F) (bound' d a b)
bound d a@(FVariant is) b@(F (T (TVariant js)))
  | M.keysSet is `S.isSubsetOf` M.keysSet js
  , a' <- F (T (TVariant $ M.union is js))  -- FIXME: left-biased. is it a problem? / zilinc
  = bound d a' b
bound d a@(F (T (TVariant js))) b@(FVariant is) = bound d b a  -- symm
bound d a@(FVariant is_) b@(FVariant js_)
  | is <- M.union is_ js_
  , js <- M.union js_ is_
  = if or (zipWith ((/=) `on` length . fst) (F.toList is) (F.toList js))  -- F.toList only returns values, no keys!
      then return (Nothing, a, b)
      else do
        rs <- M.fromList <$> traverse (each is js) (M.keys is)
        traceTc "sol" (text "calculate" <+> text (show b) <+> text "of"
                       P.<+> pretty a <+> text "and" <+> pretty b <> colon
                       P.<$> pretty (FVariant rs))
        return (Just (FVariant rs), FVariant is, FVariant js)
  where
    op = case d of GLB -> (||); LUB -> (&&)
    each is js k = let
      (i, ib) = is M.! k
      (_, jb) = js M.! k
     in do ts <- replicateM (length i) (fresh $ BoundOf a b d)
           return (k, (ts, ib `op` jb))
bound d a@(FRecord isL) b@(F (T (TRecord jsL s)))
  | is <- M.fromList isL
  , js <- M.fromList jsL
  , M.keysSet is `S.isSubsetOf` M.keysSet js
  , a' <- F (T (TRecord (map (\(k,v) -> (k, case M.lookup k is of Nothing -> v; Just v' -> v')) jsL) s))  -- left-biased
  = bound d a' b
bound d a@(F (T (TRecord jsL s))) b@(FRecord isL) = bound d b a  -- symm
bound d a@(FRecord is_) b@(FRecord js_)
  | isM <- M.fromList is_
  , jsM <- M.fromList js_
  , is <- M.union isM jsM
  , js <- M.union jsM isM
  = let op = case d of GLB -> (&&); LUB -> (||)
        each (f,(_,t)) (_,(_,t')) = (f,) . (,t `op` t') <$> fresh (BoundOf a b d)
        is' = M.toList is
        js' = M.toList js
    in do t <- FRecord <$> zipWithM each is' js'
          traceTc "sol" (text "calculate" <+> text (show b) <+> text "of"
                         P.<+> pretty a <+> text "and" <+> pretty b <> colon
                         P.<$> pretty t)
          return (Just t, FRecord is', FRecord js')
bound _ a b = do
  traceTc "sol" (text "calculate bound of"
                 P.<$> pretty a
                 P.<$> text "and"
                 P.<$> pretty b <> semi
                 P.<$> text "result nothing")
  return (Nothing, a, b)

bound' :: Bound -> TCType -> TCType -> Solver (Maybe TCType)
bound' d t1@(T (TVariant is)) t2@(T (TVariant js))
  | M.keysSet is /= M.keysSet js = return Nothing
  | or (zipWith ((/=) `on` length . fst) (F.toList is) (F.toList js)) = return Nothing
  | otherwise = do
      t <- T . TVariant . M.fromList <$> traverse each (M.keys is)
      traceTc "sol" (text "calculate" <+> text (show d) <+> text "of"
                     P.<+> pretty t1 <+> text "and" <+> pretty t2 <> colon
                     P.<$> pretty t)
      return $ Just t
  where
    op = case d of GLB -> (||); LUB -> (&&)
    each :: TagName -> Solver (TagName, ([TCType], Taken))
    each k = let
      (i, ib) = is M.! k
      (_, jb) = js M.! k
     in do ts <- replicateM (length i) (fresh $ BoundOf (F t1) (F t2) d)
           return (k, (ts, ib `op` jb))
bound' d t1@(T (TTuple is)) t2@(T (TTuple js))
  | length is /= length js = return Nothing
  | otherwise = do t <- T . TTuple <$> traverse (const $ (fresh $ BoundOf (F t1) (F t2) d) ) is
                   traceTc "sol" (text "calculate bound of" <+> pretty t1 <+> text "and" <+> pretty t2 <> colon
                                  P.<$> pretty t)
                   return $ Just t
bound' x t1@(T (TFun a b)) t2@(T (TFun c d)) = do
  t <-  T <$> (TFun <$> fresh (BoundOf (F t1) (F t2) x) <*> fresh (BoundOf (F t1) (F t2) x))
  traceTc "sol" (text "calculate bound of" <+> pretty t1 <+> text "and" <+> pretty t2 <> colon
                 P.<$> pretty t)
  return $ Just t
bound' x t1@(T (TCon c as s)) t2@(T (TCon d bs r))
  | c /= d || s /= r       = return Nothing
  | length as /= length bs = return Nothing
  | otherwise = do
      t <- T <$> (TCon d <$> traverse (const $ fresh (BoundOf (F t1) (F t2) x)) as <*> pure r)
      traceTc "sol" (text "calculate bound of" <+> pretty t1 <+> text "and" <+> pretty t2 <> colon
                     P.<$> pretty t)
      return $ Just t
bound' _ (T (TVar a x)) (T (TVar b y))
  | x /= y || a /= b = return Nothing
  | otherwise        = return $ Just . T $ TVar a x
bound' _ (T TUnit) (T TUnit) = return $ Just (T TUnit)
bound' d t1@(T (TRecord fs s)) t2@(T (TRecord gs r))
  | s /= r = return Nothing
  | map fst fs /= map fst gs = return Nothing
  | otherwise = do
      let op = case d of GLB -> (&&); LUB -> (||)
          each (f,(_,b)) (_, (_,b')) = (f,) . (,b `op` b') <$> fresh (BoundOf (F t1) (F t2) d)
      t <- T <$> (TRecord <$> zipWithM each fs gs <*> pure s)
      traceTc "sol" (text "calculate bound of" <+> pretty t1 <+> text "and" <+> pretty t2 <> colon
                     P.<$> pretty t)
      return $ Just t
bound' _ a b = do
  traceTc "sol" (text "calculate bound (bound') of"
           P.<$> pretty a
           P.<$> text "and"
           P.<$> pretty b <+> semi
           P.<$> text "result nothing")
  return Nothing

primGuess :: Bound -> TCType -> TCType -> Solver (Maybe TCType)
primGuess d (T (TCon n [] Unboxed)) (T (TCon m [] Unboxed))
  | Just n' <- elemIndex n primTypeCons
  , Just m' <- elemIndex m primTypeCons
  = let f = case d of GLB -> min; LUB -> max
    in return $ Just (T (TCon (primTypeCons !! f n' m') [] Unboxed))
primGuess _ a b = do
  traceTc "sol" (text "primitive guess on"
           P.<$> pretty a
           P.<$> text "and"
           P.<$> pretty b <+> semi
           P.<$> text "result nothing")
  return Nothing

glbGuess = primGuess GLB
lubGuess = primGuess LUB


-- A simple classification scheme for soluble flex/rigid constraints
data GoalClasses
  = Classes
    { ups :: IM.IntMap GoalSet
    , downs :: IM.IntMap GoalSet
    , upcastables :: IM.IntMap GoalSet
    , downcastables :: IM.IntMap GoalSet
    , unsats :: [Goal]
    , semisats :: [Goal]
    , rest :: [Goal]
    , upflexes :: IS.IntSet
    , downflexes :: IS.IntSet
    }

instance Show GoalClasses where
  show (Classes u d uc dc un ss r uf df) = "ups:\n" ++
                              unlines (map (("  " ++) . show) (F.toList u)) ++
                              "\ndowns:\n" ++
                              unlines (map (("  " ++) . show) (F.toList d)) ++
                              "\nupcastables:\n" ++
                              unlines (map (("  " ++) . show) (F.toList uc)) ++
                              "\ndowncastables:\n" ++
                              unlines (map (("  " ++) . show) (F.toList dc)) ++
                              "\nunsats:\n" ++
                              unlines (map (("  " ++) . show) (F.toList un)) ++
                              "\nsemimsats:\n" ++
                              unlines (map (("  " ++) . show) (F.toList ss)) ++
                              "\nrest:\n" ++
                              unlines (map (("  " ++) . show) (F.toList r)) ++
                              "\nflexUp:\n" ++
                              unlines (map (("  " ++) . show) (IS.toList uf)) ++
                              "\nflexDown:\n" ++
                              unlines (map (("  " ++) . show) (IS.toList df))

instance Monoid GoalClasses where
  Classes u d uc dc e s r uf df `mappend` Classes u' d' uc' dc' e' s' r' uf' df'
    = Classes (IM.unionWith (<>) u u')
              (IM.unionWith (<>) d d')
              (IM.unionWith (<>) uc uc')
              (IM.unionWith (<>) dc dc')
              (e ++ e')
              (s ++ s')
              (r ++ r')
              (IS.union uf uf')
              (IS.union df df')
  mempty = Classes IM.empty IM.empty IM.empty IM.empty [] [] [] IS.empty IS.empty

-- Collects all flexes
flexesIn :: TypeFragment TCType -> IS.IntSet
flexesIn = F.foldMap f
  where f (U x) = IS.singleton x
        f (T y) = F.foldMap f y

-- Break goals into their form
-- Expects all goals to be broken down as far as possible first
-- Consider using auto first, or using explode instead of this function.
classify :: Goal -> GoalClasses
classify g = case g of
  (Goal _ (a       :< F (U x))) | rigid a     -> mempty {ups   = IM.singleton x $ GS.singleton g, downflexes = flexesIn a }
  (Goal _ (F (U x) :< b      )) | rigid b     -> mempty {downs = IM.singleton x $ GS.singleton g, upflexes   = flexesIn b }
  (Goal _ (b `Upcastable` U x)) | rigid (F b) -> mempty {upcastables   = IM.singleton x $ GS.singleton g }
  (Goal _ (U x `Upcastable` b)) | rigid (F b) -> mempty {downcastables = IM.singleton x $ GS.singleton g }
  (Goal _ (Unsat _))                          -> mempty {unsats = [g]}
  (Goal _ (SemiSat _))                        -> mempty {semisats = [g]}
  (Goal _ Sat)                                -> mempty
  (Goal _ (F a :< F b)) | Just a' <- flexOf a
                        , Just b' <- flexOf b
                        , a' /= b'            -> mempty {upflexes = IS.singleton b', downflexes = IS.singleton a', rest = [g]}
                        | Just a' <- flexOf a
                        , Nothing <- flexOf b -> mempty {downflexes = IS.singleton a', rest = [g]}
                        | Just b' <- flexOf b
                        , Nothing <- flexOf a -> mempty {upflexes = IS.singleton b', rest = [g]}
  _                                           -> mempty {rest = [g]}
  where
    rigid (F (U x)) = False
    rigid _ = True

-- Push type information down from the RHS of :< to the LHS
-- Expects a series of goals of the form U x :< tau
impose :: [Goal] -> Solver [Goal]
impose (Goal x1 (v :< tau_) : Goal x2 (_ :< tau'_) : xs) = do
  (mt, tau, tau') <- glb tau_ tau'_
  case mt of
    Nothing    -> return [Goal x1 (Unsat (TypeMismatch tau tau'))]
    Just tau'' -> ([Goal x1 (tau'' :< tau), Goal x2 (tau'' :< tau')] ++)
                  <$> impose (Goal x2 (v :< tau'') : xs)
impose xs = return xs

imposeCast :: [Goal] -> Solver [Goal]
imposeCast (Goal x1 (v `Upcastable` tau) : Goal x2 (_ `Upcastable` tau') : xs) = do
  mt <- glbGuess tau tau'
  case mt of
    Nothing    -> return [Goal x1 (Unsat (TypeMismatch (F tau) (F tau')))]
    Just tau'' -> imposeCast (Goal x2 (v `Upcastable` tau'') : xs)
imposeCast xs = return xs

-- Push type information up from the LHS of :< to the RHS
-- Expects a series of goals of the form tau :< U x
suggest :: [Goal] -> Solver [Goal]
suggest (Goal x1 (tau_ :< v) : Goal x2 (tau'_ :< _) : xs) = do
  (mt,tau,tau') <- lub tau_ tau'_
  case mt of
    Nothing    -> return [Goal x1 (Unsat (TypeMismatch tau tau'))]
    Just tau'' -> ([Goal x1 (tau :< tau''), Goal x2 (tau' :< tau'')] ++)
                  <$> suggest (Goal x2 (tau'' :< v) : xs)
suggest xs = return xs

suggestCast :: [Goal] -> Solver [Goal]
suggestCast (Goal x1 (tau `Upcastable` v) : Goal x2 (tau' `Upcastable` _) : xs) = do
  mt <- lubGuess tau tau'
  case mt of
    Nothing    -> return [Goal x1 (Unsat (TypeMismatch (F tau) (F tau')))]
    Just tau'' -> suggestCast (Goal x2 (tau'' `Upcastable` v) : xs)
suggestCast xs = return xs

-- guess :: [Goal] -> Solver [Goal]
-- guess (Goal x1 a@(Partial tau d v) : Goal x2 b@(Partial tau' d' _) : xs) = do
--   mt <- lub' tau tau'
--   case mt of
--     Nothing    -> return [Goal x1 (Unsat (UnsolvedConstraint (a :& b)))]
--     Just tau'' -> ([Goal x1 (tau `op` tau''), Goal x2 (tau' `op'` tau'')] ++)
--                   <$> suggest (Goal x2 (tau'' `op` v) : Goal x2 (tau'' `op'` v) : xs)
--   where
--     op  = case d  of Less -> (:<); _ -> flip (:<)
--     op' = case d' of Less -> (:<); _ -> flip (:<)
-- guess xs = return xs

noBrainersT :: [Goal] -> Solver Subst
noBrainersT g@[Goal _ c] = do
  traceTc "sol" (text "apply no-brainer to" <+> prettyC c)
  noBrainers g
noBrainersT g = do
  traceTc "sol" (text "apply no-brainer to several goals")
  noBrainers g

-- Produce substitutions when it is safe to do so (the variable can't get any more general).
noBrainers :: [Goal] -> Solver Subst
noBrainers [Goal _ c@(F (U x) :<  F (T t))] | Nothing <- flexOf (T t) =
  return $ Subst.singleton x (T t)
noBrainers [Goal _ c@(F (T t) :<  F (U x))] | Nothing <- flexOf (T t) =
  return $ Subst.singleton x (T t)
noBrainers [Goal _ c@(Upcastable (T t@(TCon v [] Unboxed)) (U x))]
  | v `elem` primTypeCons = return $ Subst.singleton x (T t)
noBrainers [Goal _ c@(Upcastable (U x) (T t@(TCon v [] Unboxed)))]
  | v `elem` primTypeCons = return $ Subst.singleton x (T t)
noBrainers _ = return mempty

applySubst :: Subst -> Solver ()
applySubst s = traceTc "sol" (text "apply subst") >> substs <>= s

-- Applies the current substitution to goals.
instantiate :: GoalClasses -> Solver [Goal]
instantiate (Classes ups downs upcasts downcasts errs semisats rest upfl downfl) = do
  s <- use substs
  let al  = (GS.toList =<< (F.toList =<< [ups, downs, upcasts, downcasts]) ) ++ errs ++ semisats ++ rest
      al' = al & map (goal %~ Subst.applyC s) & map (goalContext %~ map (Subst.applyCtx s))
  -- traceTc "sol" (text "instantiate" <+> pretty (show al) P.<$> text "with substitution" P.<$> pretty s <> semi
  --                P.<$> text "end up with goals:" <+> pretty (show al'))
  return al'

-- Eliminates all known facts about type variables from the goal set.
assumption :: [Goal] -> Solver [Goal]
assumption gs = do
  axs <- use axioms
  let isKnown :: Constraint -> Bool
      isKnown (Share  (T (TVar v b)) _)
        | Just k <- lookup v axs = canShare   (if b then bangKind k else k)
      isKnown (Drop   (T (TVar v b)) _)
        | Just k <- lookup v axs = canDiscard (if b then bangKind k else k)
      isKnown (Escape (T (TVar v b)) _)
        | Just k <- lookup v axs = canEscape  (if b then bangKind k else k)
      isKnown _ = False
  return (filter (not . isKnown . view goal) gs)

-- Take an assorted list of goals, and break them down into neatly classified, simple flex/rigid goals.
-- Removes any known facts about type variables.
explode :: [Goal] -> Solver GoalClasses
explode = assumption >=> (zoom tc . apply auto) >=> (return . foldMap classify)

irreducible :: IM.IntMap [Goal] -> IS.IntSet -> Bool
irreducible m ds | IM.null m = True
                 | xs <- F.toList m = all irreducible' xs
  where
    irreducible' :: [Goal] -> Bool
    irreducible' [] = True
    irreducible' [Goal _ c]
            = case c of
                (F a :< F b) | groundConstraint a b                   -> False
                             | Just a' <- flexOf a, a' `IS.member` ds -> True
                             | Just b' <- flexOf b, b' `IS.member` ds -> True
                             | otherwise                              -> False
                (F (U x) :< _) -> True
                (_ :< F (U x)) -> True
                (_ :< _)       -> False
                (_)            -> True
    irreducible' _ = False

isGround (T (TCon x [] Unboxed)) = True
isGround _ = False

-- when `!' is invertible
isBangInv (T (TCon x [] Unboxed)) = True
isBangInv (T (TFun {})) = True
isBangInv (T TUnit) = True
isBangInv _ = False

groundConstraint a b | Just a' <- flexOf a, isGround b = True
                     | Just b' <- flexOf b, isGround a = True
                     | otherwise = False

data GoalClass = UpClass | DownClass | UpcastClass | DowncastClass

-- In a loop, we:
--   1. Smash all goals into smaller, simple flex/rigid goals. Exit if any of them are Unsat, remove any Sat.
--   2.1. Apply any no-brainer substitutions from the downward goals (? :< R)
--        If we did any substituting go to 1
--   2.2. If there are any downward goals,
--          push type information down from the RHS to the LHS of :< constraints and go to 1
--   3.1. Apply any no-brainer substitutions from the upward goals (R :< ?)
--        If we did any substituting, go to 1
--   3.2. If there are any upward goals,
--          pull type information up from the LHS to the RHS of :< constraints and go to 1
--   4. If there are any remaining constraints, report unsolved error, otherwise return empty list.
solve :: Constraint -> Solver [ContextualisedEW]
solve = zoom tc . crunch >=> explode >=> go
  where
    go :: GoalClasses -> Solver [ContextualisedEW]
    go g | not (null (unsats g)) = return (map (\(Goal ctx (Unsat e)) -> (ctx, Left e)) (unsats g) ++ map toWarn (semisats g))
    go g | not (irreducible (fmap GS.toList $ downs g) (downflexes g)) = go' g DownClass
    go g | not (irreducible (fmap GS.toList $ ups   g) (upflexes   g)) = go' g UpClass
    go g | not (IM.null (downcastables g)) = go' g DowncastClass
    go g | not (IM.null (upcastables   g)) = go' g UpcastClass
    go g | not (null (rest g)) = do
      os <- use flexOrigins
      return (map (\(Goal c x) -> (c, Left $ UnsolvedConstraint x os)) (rest g) ++ map toWarn (semisats g))
    go g = return $ map toWarn (semisats g)

    go' :: GoalClasses -> GoalClass -> Solver [ContextualisedEW]
    go' g c = do
      let (msg, f, cls, g'', flexes) = case c of
            UpClass       -> ("upward"  , suggest    , ups          , g { ups           = IM.empty }, upflexes)
            DownClass     -> ("downward", impose     , downs        , g { downs         = IM.empty }, downflexes)
            UpcastClass   -> ("upcast"  , suggestCast, upcastables  , g { upcastables   = IM.empty }, mempty)
            DowncastClass -> ("downcast", imposeCast , downcastables, g { downcastables = IM.empty }, mempty)
          groundNB [Goal _ (F a :< F b)] = groundConstraint a b
          groundNB _                     = False
          groundKeys = IM.keysSet (IM.filter (groundNB . GS.toList) (cls g))
      s <- F.fold <$> mapM (noBrainersT . GS.toList) (cls g `removeKeys` IS.toList (flexes g IS.\\ groundKeys))
      traceTc "sol" (text "solve" <+> text msg <+> text "goals"
                     P.<$> bold (text "produce subst:")
                     P.<$> pretty s)
      if Subst.null s then do
          g' <- explode =<< concat . F.toList <$> traverse (f . GS.toList) (cls g)
          go (g' <> g'')
      else do
          applySubst s
          instantiate g >>= explode >>= go

    removeKeys = foldr IM.delete

    toWarn (Goal ctx (SemiSat w)) = (ctx, Right w)
    toWarn _ = __impossible "toWarn (in solve)"

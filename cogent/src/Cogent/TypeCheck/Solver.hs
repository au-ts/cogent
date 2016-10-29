--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Cogent.TypeCheck.Solver (runSolver, solve) where

import           Cogent.Common.Syntax
import           Cogent.Common.Types
import           Cogent.PrettyPrint (prettyCtx)
import           Cogent.Surface
import           Cogent.TypeCheck.Base
import qualified Cogent.TypeCheck.Subst as Subst
import           Cogent.TypeCheck.Subst (Subst)
import           Cogent.TypeCheck.Util

import           Control.Applicative
import           Control.Lens hiding ((:<))
import           Control.Monad.State
import qualified Data.Foldable as F
import           Data.Function (on)
--import qualified Data.List as L
import           Data.List (elemIndex)

import qualified Data.Map as M
import           Data.Maybe
import           Data.Monoid
import qualified Data.Set as S
import qualified Text.PrettyPrint.ANSI.Leijen as P
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))


data SolverState = SS { _flexes :: Int, _tc :: TCState, _substs :: Subst, _axioms :: [(VarName, Kind)] }

makeLenses ''SolverState

type Solver = StateT SolverState IO

data Goal = Goal { _goalContext :: [ErrorContext], _goal :: Constraint }

instance Show Goal where
  show (Goal c g) = const (show big) big
    where big = (small P.<$> (P.vcat $ map (flip prettyCtx True) c))
          small = pretty g

makeLenses ''Goal

runSolver :: Solver a -> Int -> [(VarName, Kind)] -> TC (a, Subst)
runSolver act i ks = do
  x <- get
  (a, SS _ x' s _) <- lift $ runStateT act (SS i x mempty ks)
  put x'
  return (a,s)

-- Flatten a constraint tree into a set of flat goals
crunch :: Constraint -> TC [Goal]
crunch (x :@ e) = map (goalContext %~ (e:)) <$> crunch x
crunch (x :& y) = (++) <$> crunch x <*> crunch y
crunch Sat   = return []
crunch x     = return [Goal [] x]

-- Rewrites out type synonyms, TUnbox, TBang, TTake, and TPut
-- so that the "head" of the type is guaranteed to be a concrete type
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
    Just (as', Just b)  | b' <- toTCType b -> whnf (substType (zip as' as) b')
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

isIrrefutable :: Pattern n -> Bool
isIrrefutable (PIrrefutable p) = True
isIrrefutable _ = False

patternTag :: Pattern n -> Maybe TagName
patternTag (PCon t _) = Just t
patternTag _ = Nothing

-- isVarCon :: Pattern a -> Bool
-- isVarCon (PCon {}) = True
-- isVarCon _ = False

-- Explodes a rigid/rigid constraint into subgoals necessary
-- for that to be true. E.g, (a,b) :< (c,d) becomes a :< c :& b :< d.
-- Assumes that the input is simped (i.e conjunction and context free, with types in whnf)
rule' :: Constraint -> IO (Maybe Constraint)
rule' c = ruleT c >>= return . ((:@ SolvingConstraint c) <$>)

ruleT :: Constraint -> IO (Maybe Constraint)
ruleT c = do
  traceTC "sol" (text "apply rule to" <+> pretty c)
  rule c

rule :: Constraint -> IO (Maybe Constraint)
rule (Exhaustive t ps) | any isIrrefutable ps = return $ Just Sat
rule (Exhaustive (T (TVariant n)) ps)
  | s1 <- S.fromList (mapMaybe patternTag ps)
  , s2 <- S.fromList (map fst $ filter (not . snd . snd) $ M.toList n)
  = return $ if s1 == s2
               then Just Sat
               else Just $ Unsat (PatternsNotExhaustive (T (TVariant n)) (S.toList (s2 S.\\ s1)))

rule (Exhaustive (T (TCon "Bool" [] Unboxed)) [PBoolLit t, PBoolLit f])
   = return $ if not (t && f) && (t || f) then Just Sat
              else Just $ Unsat $ PatternsNotExhaustive (T (TCon "Bool" [] Unboxed)) []

rule (Exhaustive t ps)
  | not (notWhnf t) = return . Just . Unsat $ PatternsNotExhaustive t []

rule (x :@ c) = return . ((:@ c) <$>) =<< ruleT x

rule (x :& y) = do
  x' <- ruleT x
  y' <- ruleT y
  return ((:&) <$> x' <*> y'
      <|> (x :&) <$> y'
      <|> (:& y) <$> x')

rule Unsat {} = return Nothing
rule Sat   {} = return Nothing

rule (Share  (T TVar {}) _) = return Nothing
rule (Drop   (T TVar {}) _) = return Nothing
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
rule ct@(F (T (TFun a b))  :< F (T (TFun c d))) = do
  let ct' = (F c :< F a) :& (F b :< F d)
  traceTC "sol" (text "constraint" <+> pretty ct <+> text "is decomposed into"
                 P.<$> pretty ct')
  return $ Just ct' 
rule (F (T TUnit     )  :< F (T TUnit))      = return $ Just Sat
rule (F (T (TVar v b))  :< F (T (TVar u c)))
  | v == u, b == c = return $ Just Sat
  | otherwise      = return $ Just $ Unsat (TypeMismatch (F $ T (TVar v b)) (F $ T (TVar u c)))
rule (F (T (TCon n ts s)) :< F (T (TCon m us r)))
  | n == m, length ts == length us, s == r = return $ Just $ mconcat (zipWith (:<) (map F ts) (map F us)
                                                                  ++ zipWith (:<) (map F us) (map F ts))
  | otherwise                              = return $ Just $ Unsat (TypeMismatch (F $ T (TCon n ts s)) (F $ T (TCon m us r)))
rule ct@(F (T (TRecord fs s)) :< F (T (TRecord gs r)))
  | or (zipWith ((/=) `on` fst) fs gs) = return $ Just $ Unsat (TypeMismatch (F $ T (TRecord fs s)) (F $ T (TRecord gs r)))
  | length fs /= length gs             = return $ Just $ Unsat (TypeMismatch (F $ T (TRecord fs s)) (F $ T (TRecord gs r)))
  | s /= r                             = return $ Just $ Unsat (TypeMismatch (F $ T (TRecord fs s)) (F $ T (TRecord gs r)))
  | otherwise                          = do
     let each (f, (t, False)) (_, (u, True )) = (F t :< F u) :& Drop t ImplicitlyTaken
         each (f, (t, False)) (_, (u, False)) = F t :< F u
         each (f, (t, True )) (_, (u, True )) = F t :< F u
         each (f, (t, True )) (_, (u, False)) = Unsat (RequiredTakenField f t)
         cs = zipWith each fs gs
     traceTC "sol" (text "solve each field of constraint" <+> pretty ct
       P.<$> foldl 
               (\a (f,c) -> a P.<$> text "field" <+> pretty (fst f) P.<> colon <+> pretty c)
               P.empty
               (zip fs cs))
     return . Just $ mconcat cs
rule (F (T (TVariant m)) :< F (T (TVariant n)))
  | M.keys m /= M.keys n = return $ Just $ Unsat (TypeMismatch (F $ T (TVariant m)) (F $ T (TVariant n)))
  | otherwise = let
      each (f, (ts, False)) (_, (us, True )) = Unsat (DiscardWithoutMatch f) 
      each (f, (ts, False)) (_, (us, False)) = mconcat (zipWith (:<) (map F ts) (map F us))
      each (f, (ts, True )) (_, (us, True )) = mconcat (zipWith (:<) (map F ts) (map F us))
      each (f, (ts, True )) (_, (us, False)) = mconcat (zipWith (:<) (map F ts) (map F us))
    in return $ Just $ mconcat (zipWith (each) (M.toList m) (M.toList n))
-- This rule is a bit dodgy
-- rule (T (TTake (Just a) b) :< T (TTake (Just a') c))
--   | x <- L.intersect a a'
--   , not (null x)
--   = let
--       ax  = a L.\\ x
--       a'x = a' L.\\ x
--      in Just $  ((if null ax then id else T . TTake (Just ax)) b)
--              :< ((if null a'x then id else T . TTake (Just a'x)) c)
rule ct@(F a :< b)
  | notWhnf a = do
      traceTC "sol" (text "constraint" <+> pretty ct <+> text "with left side in non-WHNF is disregarded")
      return Nothing
rule ct@(b :< F a)
  | notWhnf a = do
      traceTC "sol" (text "constraint" <+> pretty ct <+> text "with right side in non-WHNF is disregarded")
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
  = parVariants n m ns
rule ct@(F (T (TVariant n)) :< FVariant m)
  | ms <- M.keysSet m
  , ms `S.isSubsetOf` M.keysSet n
  = parVariants n m ms
rule ct@(FVariant n :< FVariant m)
  | ns <- M.keysSet n
  , ns == M.keysSet m
  = parVariants n m ns
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
rule (a :< b) = return $ Just $ Unsat (TypeMismatch a b)

rule c = return Nothing

-- `parRecords' and `parVariant' are used internally in `rule'
parRecords n m ks =
  let each f (t, False) (u, True ) = Unsat (RequiredTakenField f t)
      each f (t, False) (u, False) = F t :< F u
      each f (t, True ) (u, True ) = F t :< F u
      each f (t, True ) (u, False) = (F t :< F u) :& Drop t ImplicitlyTaken
      ks' = S.toList ks 
      cs  = map (\k -> each k (n M.! k) (m M.! k)) ks'
  in return . Just $ mconcat cs

parVariants n m ks =
  let each t (ts, _) (us, False)  = mconcat (zipWith (:<) (map F ts) (map F us))
      each t (ts, _) (us, True)   = Unsat (RequiredTakenTag t)
      ks' = S.toList ks
      cs  = map (\k -> each k (n M.! k) (m M.! k)) ks'
  in return . Just $ mconcat cs


-- Applies rules and simp as much as possible
auto :: Constraint -> TC Constraint
auto c = do
  traceTC "sol" (text "auto" <+> pretty c)
  c' <- simpT c
  liftIO (rule' c') >>= \case
    Nothing  -> return c'
    Just c'' -> auto c''

apply :: (Constraint -> TC Constraint) -> [Goal] -> TC [Goal]
apply tactic = fmap concat . mapM each
  where each (Goal ctx c) = do
          c' <- tactic c
          map (goalContext %~ (ctx ++)) <$> crunch c'

simpT :: Constraint -> TC Constraint
simpT c = do
  traceTC "sol" (text "simp" <+> pretty c)
  simp c

-- applies whnf to every type in a constraint.
simp :: Constraint -> TC Constraint
simp (a :< b)         = (:<)       <$> traverse whnf a <*> traverse whnf b
simp (Upcastable a b) = Upcastable <$> whnf  a <*> whnf  b
simp (a :& b)         = (:&)       <$> simpT a <*> simpT b
simp (Share  t m)     = Share      <$> whnf  t <*> pure  m
simp (Drop   t m)     = Drop       <$> whnf  t <*> pure  m
simp (Escape t m)     = Escape     <$> whnf  t <*> pure  m
simp (a :@ c)         = (:@)       <$> simpT a <*> pure  c
simp (Unsat e)        = pure (Unsat e)
simp Sat              = pure Sat
simp (Exhaustive t ps)
  = Exhaustive <$> whnf t
               <*> traverse (traverse (traverse whnf)) ps -- poetry!

fresh :: Solver TCType
fresh = U <$> (flexes <<%= succ)


data Bound = GLB | LUB

glb = bound GLB
lub = bound LUB

-- Constructs a partially specified type that could plausibly be :< the two inputs.
-- We re-check some basic equalities here for better error messages
bound :: Bound -> TypeFragment TCType -> TypeFragment TCType -> Solver (Maybe (TypeFragment TCType), TypeFragment TCType, TypeFragment TCType)
bound d (F a) (F b) = fmap ((, F a, F b) . fmap F) (bound' d a b)
bound d a@(FVariant is) b@(F (T (TVariant js))) 
  | M.keysSet is `S.isSubsetOf` M.keysSet js
  , a' <- F (T (TVariant $ M.union is js))
  = bound d a' b
bound d a@(F (T (TVariant js))) b@(FVariant is) = bound d b a  -- symm
bound d a@(FVariant is_) b@(FVariant js_) 
  | is <- M.union is_ js_
  , js <- M.union js_ is_
  = if or (zipWith ((/=) `on` length) (F.toList is) (F.toList js)) then return (Nothing, a, b)
    else 
    (,FVariant is, FVariant js) . Just . FVariant . M.fromList <$> traverse (each is js) (M.keys is)
  where
    op = case d of GLB -> (||); LUB -> (&&)
    each is js k = let
      (i, ib) = is M.! k
      (_, jb) = js M.! k
     in do ts <- replicateM (length i) fresh
           return (k, (ts, ib `op` jb))
bound d a@(FRecord isL) b@(F (T (TRecord jsL s)))
  | is <- M.fromList isL
  , js <- M.fromList jsL
  , M.keysSet is `S.isSubsetOf` M.keysSet js
  , a' <- F (T (TRecord (M.toList $ M.union is js) s))
  = bound d a' b
bound d a@(F (T (TRecord jsL s))) b@(FRecord isL) = bound d b a  -- symm
bound d a@(FRecord is_) b@(FRecord js_) 
  | isM <- M.fromList is_
  , jsM <- M.fromList js_
  , is <- M.union isM jsM
  , js <- M.union jsM isM
  = let op = case d of GLB -> (&&); LUB -> (||)
        each (f,(_,b)) (_, (_,b')) = (f,) . (,b `op` b') <$> fresh
    in (, FRecord (M.toList is), FRecord (M.toList js)) . Just <$> (FRecord <$> zipWithM each (M.toList is) (M.toList js))
bound _ a b = return (Nothing, a, b)

bound' :: Bound -> TCType -> TCType -> Solver (Maybe TCType)
bound' d (T (TVariant is)) (T (TVariant js))
  | M.keysSet is /= M.keysSet js
  = return Nothing
  | or (zipWith ((/=) `on` length) (F.toList is) (F.toList js))
  = return Nothing
  | otherwise
  = Just . T . TVariant . M.fromList <$> traverse each (M.keys is)
  where
    op = case d of GLB -> (||); LUB -> (&&)
    each :: TagName -> Solver (TagName, ([TCType], Taken))
    each k = let
      (i, ib) = is M.! k
      (_, jb) = js M.! k
     in do ts <- replicateM (length i) fresh
           return (k, (ts, ib `op` jb))
bound' _ (T (TTuple is)) (T (TTuple js))
  | length is /= length js = return Nothing
  | otherwise = Just . T . TTuple <$> traverse (const fresh) is
bound' _ (T (TFun a b)) (T (TFun c d))
  = Just . T <$> (TFun <$> fresh <*> fresh)
bound' _ (T (TCon c as s)) (T (TCon d bs r))
  | c /= d || s /= r       = return Nothing
  | length as /= length bs = return Nothing
  | otherwise = Just . T <$> (TCon d <$> traverse (const fresh) as <*> pure r)
bound' _ (T (TVar a x)) (T (TVar b y))
  | x /= y || a /= b = return Nothing
  | otherwise        = return $ Just . T $ TVar a x
bound' _ (T TUnit) (T TUnit) = return $ Just (T TUnit)
bound' d (T (TRecord fs s)) (T (TRecord gs r))
  | s /= r = return Nothing
  | map fst fs /= map fst gs = return Nothing
  | otherwise = let
      op = case d of GLB -> (&&); LUB -> (||) 
      each (f,(_,b)) (_, (_,b')) = (f,) . (,b `op` b') <$> fresh
    in Just . T <$> (TRecord <$> zipWithM each fs gs <*> pure s)
bound' _ _ _ = return Nothing

primGuess :: Bound -> TCType -> TCType -> Solver (Maybe TCType)
primGuess d (T (TCon n [] Unboxed)) (T (TCon m [] Unboxed)) 
  | Just n' <- elemIndex n primTypeCons
  , Just m' <- elemIndex m primTypeCons
  = let f = case d of GLB -> min; LUB -> max
    in return $ Just (T (TCon (primTypeCons !! f n' m') [] Unboxed))
primGuess _ _ _ = return Nothing

glbGuess = primGuess GLB
lubGuess = primGuess LUB


-- A simple classification scheme for soluble flex/rigid constraints
data GoalClasses
  = Classes
    { ups :: M.Map Int [Goal]
    , downs :: M.Map Int [Goal]
    , upcastables :: M.Map Int [Goal]
    , downcastables :: M.Map Int [Goal]
    , unsats :: [Goal]
    , rest :: [Goal]
    }

instance Show GoalClasses where
  show (Classes u d uc dc un r) = "ups:\n" ++
                              unlines (map (("  " ++) . show) (F.toList u)) ++
                              "\ndowns:\n" ++
                              unlines (map (("  " ++) . show) (F.toList d)) ++
                              "\nupcastables:\n" ++
                              unlines (map (("  " ++) . show) (F.toList uc)) ++
                              "\ndowncastables:\n" ++
                              unlines (map (("  " ++) . show) (F.toList dc)) ++
                              "\nunsats:\n" ++
                              unlines (map (("  " ++) . show) (F.toList un)) ++
                              "\nrest:\n" ++
                              unlines (map (("  " ++) . show) (F.toList r))
instance Monoid GoalClasses where
  Classes u d uc dc e r `mappend` Classes u' d' uc' dc' e' r'
    = Classes (M.unionWith (++) u u')
              (M.unionWith (++) d d')
              (M.unionWith (++) uc uc')
              (M.unionWith (++) dc dc')
              (e ++ e')
              (r ++ r')

  mempty = Classes M.empty M.empty M.empty M.empty [] []

exhaustives :: Goal -> Solver Goal
-- exhaustives (Goal ctx (Exhaustive (U x) ps)) | all isVarCon ps = do
--         ts <- fromPatterns ps
--         return (Goal [] $ U x :< T (TVariant ts))
--   where
--     fromPattern :: Pattern TCName -> Solver (M.Map TagName [TCType])
--     fromPattern (PCon t ps) = M.singleton t <$> (mapM (const fresh) ps)
--     fromPattern _ = error "impossible"
--     fromPatterns ps = mconcat <$> mapM fromPattern ps
exhaustives x = return x

-- Break goals into their form
-- Expects all goals to be broken down as far as possible first
-- Consider using auto first, or using explode instead of this function.
classify :: Goal -> GoalClasses
classify g = case g of
  (Goal _ (a       :< F (U x))) | rigid a -> Classes (M.singleton x [g]) M.empty M.empty M.empty [] []
  (Goal _ (F (U x) :< b      )) | rigid b -> Classes M.empty (M.singleton x [g]) M.empty M.empty [] []
  (Goal _ (b `Upcastable` U x)) | rigid (F b) -> Classes M.empty M.empty (M.singleton x [g]) M.empty [] []
  (Goal _ (U x `Upcastable` b)) | rigid (F b) -> Classes M.empty M.empty M.empty (M.singleton x [g]) [] []
  (Goal _ (Unsat _))            -> Classes M.empty M.empty M.empty M.empty [g] []
  (Goal _ Sat)                  -> mempty
  _                             -> Classes M.empty M.empty M.empty M.empty [] [g]
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

-- Produce substitutions when it is safe to do so (the variable can't get any more general).
noBrainers :: [Goal] -> Solver Subst
noBrainers [Goal _ c@(F (U x) :<  F (T t))] = do
  traceTC "sol" (text "apply no brainer to" <+> pretty c)
  return $ Subst.singleton x (T t)
noBrainers [Goal _ c@(F (T t) :<  F (U x))] = do
  traceTC "sol" (text "apply no brainer to" <+> pretty c)
  return $ Subst.singleton x (T t)
noBrainers [Goal _ c@(Upcastable (T t@(TCon v [] Unboxed)) (U x))] | v `elem` primTypeCons = do
  traceTC "sol" (text "apply no brainer to" <+> pretty c)
  return $ Subst.singleton x (T t)
noBrainers [Goal _ c@(Upcastable (U x) (T t@(TCon v [] Unboxed)))] | v `elem` primTypeCons = do
  traceTC "sol" (text "apply no brainer to" <+> pretty c)
  return $ Subst.singleton x (T t)
noBrainers _ = return mempty

applySubst :: Subst -> Solver ()
applySubst s = substs <>= s

-- Applies the current substitution to goals.
instantiate :: GoalClasses -> Solver [Goal]
instantiate (Classes ups downs upcasts downcasts errs rest) = do
  s <- use substs
  let al = concat (F.toList ups ++ F.toList downs ++ F.toList upcasts ++ F.toList downcasts) ++ errs ++ rest
  return (al & map (goal %~ Subst.applyC s) & map (goalContext %~ map (Subst.applyCtx s)))

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
  return (filter (not  . isKnown . view goal) gs)

-- Take an assorted list of goals, and break them down into neatly classified, simple flex/rigid goals.
-- Removes any known facts about type variables.
explode :: [Goal] -> Solver GoalClasses
explode = assumption >=> (zoom tc . apply auto) >=> mapM exhaustives >=> (return . foldMap classify)

irreducible :: M.Map Int [Goal] -> Bool
irreducible m | M.null m = True
            | xs <- F.toList m
            = all irreducible' xs
            | otherwise = False
  where
    irreducible' :: [Goal] -> Bool
    irreducible' []         =  True
    irreducible' [Goal _ c]
            = case c of
                (F _ :< F _)   -> False
                (F (U x) :< _) -> True
                (_ :< F (U x)) -> True
                (_ :< _)       -> False
                (_)            -> True
    irreducible' _ = False


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
solve :: Constraint -> Solver [ContextualisedError]
solve = zoom tc . crunch >=> explode >=> go
  where
    go :: GoalClasses -> Solver [ContextualisedError]
    --go g | traceShow g False = undefined
    go g | not (null (unsats g)) = return $ map toError (unsats g)

    go g | not (irreducible (downs g)) = do
      s <- F.fold <$> mapM noBrainers (downs g)
      traceTC "sol" (text "solve downward goals"
                     P.<$> text "produce subst:"
                     P.<$> pretty s)
      if Subst.null s then do
          g' <- explode =<< concat . F.toList <$> traverse impose (downs g)
          go (g' <> g { downs = M.empty } )
      else do
          applySubst s
          instantiate g >>= explode >>= go

    go g | not (irreducible (ups g)) = do
      s <- F.fold <$> mapM noBrainers (ups g)
      traceTC "sol" (text "solve upward goals" 
                     P.<$> text "produce subst:"
                     P.<$> pretty s)
      if Subst.null s then do
          g' <- explode =<< concat . F.toList <$> traverse suggest (ups g)
          go (g' <> g { ups = M.empty } )
      else do
          applySubst s
          instantiate g >>= explode >>= go

    go g | not (M.null (downcastables g)) = do
     s <- F.fold <$> mapM noBrainers (downcastables g)
     traceTC "sol" (text "solve downcast goals" 
                    P.<$> text "produce subst:"
                    P.<$> pretty s)
     if Subst.null s then do
         g' <- explode =<< concat . F.toList <$> traverse imposeCast (downcastables g)
         go (g' <> g { downcastables = M.empty } )
     else do
         applySubst s
         instantiate g >>= explode >>= go

    go g | not (M.null (upcastables g)) = do
     s <- F.fold <$> mapM noBrainers (upcastables g)
     traceTC "sol" (text "solve upcast goals" 
                    P.<$> text "produce subst:"
                    P.<$> pretty s)
     if Subst.null s then do
         g' <- explode =<< concat . F.toList <$> traverse suggestCast (upcastables g)
         go (g' <> g { upcastables = M.empty } )
     else do
         applySubst s
         instantiate g >>= explode >>= go

    go g | not (null (rest g)) =
      let f (Goal c x) = (c, UnsolvedConstraint x)
      in  return $ map f (rest g)

    go _ = return []

    toError :: Goal -> ContextualisedError
    toError (Goal ctx (Unsat e)) = (ctx, e)
    toError _ = error "impossible"


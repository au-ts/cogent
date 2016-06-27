--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE TemplateHaskell #-}
module COGENT.TypeCheck.Solver where

import COGENT.TypeCheck.Base


import COGENT.Common.Types
import COGENT.Common.Syntax
import COGENT.Surface

import Data.List(elemIndex)
import Data.Function(on)
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Lens hiding ((:<))

data Goal = Goal { _goalContext :: [ErrorContext], _goal :: Constraint }

makeLenses ''Goal

-- Flatten a constraint tree into a set of flat goals
crunch :: Constraint -> TC [Goal]
crunch (x :@ e) = map (goalContext %~ (e:)) <$> crunch x
crunch (x :& y) = (++) <$> crunch x <*> crunch y
crunch (Sat) = return []
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
     _                 -> T (TTake fs t')
 where
   takeFields :: Maybe [FieldName] -> [(FieldName, (TCType, Bool))] -> [(FieldName, (TCType, Bool))]
   takeFields Nothing   = map (fmap (fmap (const True)))
   takeFields (Just fs) = map (\(f, (t, b)) -> (f, (t, f `elem` fs || b)))

whnf (T (TPut fs t)) = do
   t' <- whnf t
   return $ case t' of
     (T (TRecord l s)) -> T (TRecord (putFields fs l) s)
     _                 -> T (TTake fs t')
 where
   putFields :: Maybe [FieldName] -> [(FieldName, (TCType, Bool))] -> [(FieldName, (TCType, Bool))]
   putFields Nothing   = map (fmap (fmap (const False)))
   putFields (Just fs) = map (\(f, (t, b)) -> (f, (t,  (f `notElem` fs) && b)))

whnf (T (TCon n as b)) = do
  kts <- use knownTypes
  case lookup n kts of
    Just (as', Just b)  | b' <- toTCType b -> whnf (substType (zip as' as) b')
    _ -> return (T (TCon n as b))

whnf (RemoveCase p t) = do
  t' <- whnf t
  return $ fromMaybe (RemoveCase p t') (removeCase p t')

whnf t = return t

-- Remove a pattern from a type, for case expressions.
removeCase :: Pattern x -> TCType -> Maybe TCType
removeCase (PIrrefutable _) _                       = Just (T (TVariant M.empty))
removeCase (PIntLit _)      x                       = Just x
removeCase (PCharLit _)     x                       = Just x
removeCase (PBoolLit _)     x                       = Just x
removeCase (PCon t _)       (T (TVariant m))        = Just (T (TVariant (M.delete t m)))
removeCase _ _                                      = Nothing

-- Used internally in whnf, to check if a type has been normalised. If not,
-- it means that there is a flex or type variable preventing evaluation.
notWhnf :: TCType -> Bool
notWhnf (T (TTake  {}))  = True
notWhnf (T (TPut   {}))  = True
notWhnf (T (TUnbox {}))  = True
notWhnf (T (TBang  {}))  = True
notWhnf (U u)            = True
notWhnf (RemoveCase t p) = True
notWhnf _                = False

isIrrefutable :: Pattern n -> Bool
isIrrefutable (PIrrefutable p) = True
isIrrefutable _ = False

patternTag :: Pattern n -> Maybe TagName
patternTag (PCon t _) = Just t
patternTag _ = Nothing

-- Explodes a rigid/rigid constraint into subgoals necessary
-- for that to be true. E.g, (a,b) :< (c,d) becomes a :< c :& b :< d.
-- Assumes that the input is simped (i.e conjunction and context free, with types in whnf)
rule :: Constraint -> Maybe Constraint
rule (Exhaustive t ps) | any isIrrefutable ps = Just Sat
rule (Exhaustive (T (TVariant n)) ps)
  | s1 <- S.fromList (mapMaybe patternTag ps)
  , s2 <- M.keysSet n
  = if s1 == s2
    then Just Sat
    else Just $ Unsat (PatternsNotExhaustive (T (TVariant n)) (S.toList (s2 S.\\ s1)))
rule (Exhaustive (T (TCon "Bool" [] Unboxed)) [PBoolLit t, PBoolLit f])
   = if not (t && f) && (t || f) then Just Sat
     else Just $ Unsat $ PatternsNotExhaustive (T (TCon "Bool" [] Unboxed)) []
rule (Exhaustive t ps) | not (notWhnf t) = Just $ Unsat $ PatternsNotExhaustive t []
rule (Unsat {}) = Nothing
rule (Sat   {}) = Nothing
rule (Share  (T (TVar {})) _) = Nothing
rule (Drop   (T (TVar {})) _) = Nothing
rule (Escape (T (TVar {})) _) = Nothing
rule (x :@ c) = (:@ c) <$> rule x
rule (x :& y) = (:&) <$> rule x <*> rule y
rule (Share  (T (TTuple xs)) m) = Just $ mconcat $ map (flip Share m) xs
rule (Escape (T (TTuple xs)) m) = Just $ mconcat $ map (flip Escape m) xs
rule (Drop   (T (TTuple xs)) m) = Just $ mconcat $ map (flip Drop m) xs
rule (Share  (T TUnit) m) = Just Sat
rule (Escape (T TUnit) m) = Just Sat
rule (Drop   (T TUnit) m) = Just Sat
rule (Share  (T (TFun {})) m) = Just Sat
rule (Escape (T (TFun {})) m) = Just Sat
rule (Drop   (T (TFun {})) m) = Just Sat
rule (Share  (T (TVariant n)) m) = Just $ foldMap (mconcat . map (flip Share m)) n
rule (Drop   (T (TVariant n)) m) = Just $ foldMap (mconcat . map (flip Drop  m)) n
rule (Escape (T (TVariant n)) m) = Just $ foldMap (mconcat . map (flip Escape m)) n
rule (Share  t@(T (TRecord fs s)) m) | s /= Writable = Just $ foldMap (\(x, t) -> if not t then Share x m else Sat) $ map snd fs
                                       | otherwise     = Just $ Unsat $ TypeNotShareable t m
rule (Drop   t@(T (TRecord fs s)) m) | s /= Writable = Just $ foldMap (\(x, t) -> if not t then Drop x m else Sat) $ map snd fs
                                       | otherwise     = Just $ Unsat $ TypeNotDiscardable t m
rule (Escape t@(T (TRecord fs s)) m) | s /= ReadOnly = Just $ foldMap (\(x, t) -> if not t then Escape x m else Sat) $ map snd fs
                                       | otherwise     = Just $ Unsat $ TypeNotEscapable t m
rule (Share  t@(T (TCon n ts s)) m) | s /= Writable = Just Sat
                                      | otherwise     = Just $ Unsat $ TypeNotShareable t m
rule (Drop   t@(T (TCon n ts s)) m) | s /= Writable = Just Sat
                                      | otherwise     = Just $ Unsat $ TypeNotDiscardable t m
rule (Escape t@(T (TCon n ts s)) m) | s /= ReadOnly = Just Sat
                                      | otherwise     = Just $ Unsat $ TypeNotEscapable t m
rule (T (TTuple xs) :< T (TTuple ys))
  | length xs /= length ys = Just $ Unsat (TypeMismatch (T (TTuple xs)) (T (TTuple ys))) 
  | otherwise              = Just $ mconcat (zipWith (:<) xs ys)
rule (T (TFun a b)  :< T (TFun c d)) = Just $ (c :< a) :& (b :< d)
rule (T TUnit       :< T TUnit)      = Just Sat
rule (T (TVar v b)  :< T (TVar u c))
  | v == u, b == c = Just Sat
  | otherwise      = Just $ Unsat (TypeMismatch (T (TVar v b)) (T (TVar u c)))
rule (T (TCon n ts s) :< T (TCon m us r))
  | n == m, ts == us, s == r = Just Sat
  | otherwise                = Just $ Unsat (TypeMismatch (T (TCon n ts s)) (T (TCon m us r)))
rule (T (TRecord fs s) :< T (TRecord gs r))
                                         -- TODO: More precise errors
  | or (zipWith ((/=) `on` fst) fs gs) = Just $ Unsat (TypeMismatch (T (TRecord fs s)) (T (TRecord gs r)))
  | length fs /= length gs             = Just $ Unsat (TypeMismatch (T (TRecord fs s)) (T (TRecord gs r)))
  | s /= r                             = Just $ Unsat (TypeMismatch (T (TRecord fs s)) (T (TRecord gs r)))
  | otherwise                          = let
      each (f, (t, False)) (_, (u, True )) = (t :< u) :& Drop t ImplicitlyTaken
      each (f, (t, False)) (_, (u, False)) = t :< u
      each (f, (t, True )) (_, (u, True )) = t :< u
      each (f, (t, True )) (_, (u, False)) = Unsat (RequiredTakenField f t)
    in Just $ mconcat (zipWith each fs gs)
rule (T (TVariant m) :< T (TVariant n))
  | M.keys m /= M.keys n = Just $ Unsat (TypeMismatch (T (TVariant m)) (T (TVariant n)))
  | otherwise = let
      each ts us = mconcat (zipWith (:<) ts us)
    in Just $ mconcat (zipWith (each `on` snd) (M.toList m) (M.toList n))
rule (a :< b) | notWhnf a || notWhnf b = Nothing
                | otherwise              = Just $ Unsat (TypeMismatch a b)
rule (T (TCon n [] Unboxed) :<~ T (TCon m [] Unboxed))
  | Just n' <- elemIndex n primTypeCons
  , Just m' <- elemIndex m primTypeCons
  , n' <= m'
  , m /= "String"
  = Just Sat
rule (T (TVariant n) :<~ T (TVariant m))
  | ks <- M.keysSet n
  , ks `S.isSubsetOf` M.keysSet m
  = let each ts us = mconcat (zipWith (:<) ts us)
    in Just $ mconcat (map (\k -> each (n M.! k) (m M.! k)) $ S.toList ks)
rule (T (TRecord fs _) :<~ T (TRecord gs s))
  | ks <- S.fromList (map fst fs)
  , m <- M.fromList gs
  , ks `S.isSubsetOf` M.keysSet m
  , n <- M.fromList fs
  =  let
       each f (t, False) (u, True ) = (t :< u) :& Drop t ImplicitlyTaken
       each f (t, False) (u, False) = t :< u
       each f (t, True ) (u, True ) = t :< u
       each f (t, True ) (u, False) = Unsat (RequiredTakenField f t)
     in Just $ mconcat (map (\k -> each k (n M.! k) (m M.! k)) $ S.toList ks)
rule (a :<~ b) = rule (a :< b)
rule _ = Nothing

-- Applys rules and simp as much as possible
auto :: Constraint -> TC Constraint
auto c = do
  c' <- simp c
  case rule c of
    Nothing  -> return c'
    Just c'' -> auto c''

apply :: (Constraint -> TC Constraint) -> [Goal] -> TC [Goal]
apply tactic = fmap concat . mapM each
  where each (Goal ctx c) = do
          c' <- tactic c
          map (goalContext %~ (ctx ++)) <$> crunch c'

-- applies whnf to every type in a constraint.
simp :: Constraint -> TC Constraint
simp (a :< b)     = (:<)   <$> whnf a <*> whnf b
simp (a :<~ b)    = (:<~)  <$> whnf a <*> whnf b
simp (a :& b)     = (:&)   <$> simp a <*> simp b
simp (Share t m)  = Share  <$> whnf t <*> pure m
simp (Drop  t m)  = Drop   <$> whnf t <*> pure m
simp (Escape t m) = Escape <$> whnf t <*> pure m
simp (a :@ c)     = (:@)   <$> simp a <*> pure c
simp (Unsat e)    = pure (Unsat e)
simp Sat          = pure Sat
simp (Exhaustive t ps)
  = Exhaustive <$> whnf t
               <*> traverse (traverse (traverse whnf)) ps -- poetry!




-- tc :: [(SourcePos, TopLevel LocType VarName LocExpr)]
--    -> ((Either (TypeError, [ErrorContext]) [TopLevel RawType TypedName TypedExpr], WarningErrorLog), TCState)
-- tc defs = undefined

-- data Constraint = (:<) TCType TCType
--                 | (:<~) TCType TCType
--                 | (:&) Constraint Constraint
--                 | Share TCType Metadata
--                 | Drop TCType Metadata
--                 | Escape TCType Metadata
--                 | (:@) Constraint ErrorContext
--                 | Unsat TypeError
--                 | Sat
--                 | Exhaustive TCType [Pattern TCTypedName]

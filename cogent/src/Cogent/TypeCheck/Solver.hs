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

whnf (RemoveCase t p) = undefined -- TODO

whnf t = return t

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

-- Explodes a rigid/rigid constraint into subgoals necessary
-- for that to be true. E.g, (a,b) :< (c,d) becomes [a :< c, b :< d].
intros :: Constraint -> TC [Constraint]
intros = undefined


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

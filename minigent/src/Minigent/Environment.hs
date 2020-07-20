-- |
-- Module      : Minigent.Environment
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- Definitions for global environments and local type contexts.
--
-- May be used qualified or unqualified.
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor #-}
module Minigent.Environment
  ( -- * Global Environments
    GlobalEnvironments (..)
  , emptyGlobalEnvironments
  , -- * Contexts
    Context
  , push
  , pop
  , use
  , topUsed
  , unused
  , factor
  , alter
  , reconcile
  ) where

import Minigent.Syntax

import Data.Maybe (mapMaybe)
import qualified Data.Map as M
import qualified Data.List as L

-- | Global environments are for top-level functions, both definitions and types.
data GlobalEnvironments
   = GlobalEnvs
   { defns :: M.Map FunName (VarName, Expr)
   , types :: M.Map FunName PolyType
   , noTermChecks :: M.Map FunName Bool
   } deriving (Show)

emptyGlobalEnvironments = GlobalEnvs M.empty M.empty M.empty

-- | A value of type @Context a@ maps variable names to values of type @a@,
--   keeping track of the amount of times the variable is "used". It can be
--   thought of as a /stack/ of bindings, with below 'push' and 'pop' functions.
newtype Context a = Ctx [(VarName, Int, a)] deriving (Semigroup, Monoid, Functor, Show)

-- | Add a new binding for the given variable to the context, shadowing existing bindings.
push :: (VarName, a) -> Context a -> Context a
push (v, x) (Ctx m) = Ctx ( (v, 0,x) : m)

-- | Returns true if the topmost bound variable in the context has been "used".
topUsed :: Context a -> Bool
topUsed (Ctx ((_,u,_):_)) = u > 0
topUsed _ = error "topUsed called on empty context"

-- | Removes the topmost binding from the context. If the context is empty, does nothing.
pop :: Context a -> Context a
pop (Ctx xs) = Ctx (drop 1 xs)

-- | Given a variable name, look it up in the context, returning its associated value.
--   Also returns a new context where the variable's usage count has been increased,
--   and a boolean that is true if the variable had already been used before.
use :: (Show a) => VarName -> Context a -> (a, Bool, Context a)
use v (Ctx ls) = let (a, r, ls') = go ls in (a, r, Ctx ls')
  where
    go [] = error "use called on an out of scope variable"
    go (x@(var, usage, a) : xs)
      | v == var = (a, usage > 0, (var, usage + 1, a) : xs)
      | v /= var = let (a', i, xs') = go xs
                    in (a', i, x:xs')

-- | Returns all elements in the context that have been left unused.
unused :: Context a -> [a]
unused (Ctx ls) = mapMaybe (\(v,u,a) -> if u == 0 then Just a else Nothing) ls

-- | Extract specific variables from a context. Given a list of variable names
--   and an input context, the output will contain only those variables in
--   the input context mentioned in the list. 
--
--   This is used in let! expressions to extract observer variables from the
--   rest of the context.
factor :: [VarName] -> Context a -> Context a
factor vs (Ctx xs) = let as = go vs xs in Ctx as
  where
    go vs [] = []
    go vs ((v,u,a):xs)
      | v `elem` vs = (v,u,a): go (L.delete v vs) xs
      | otherwise   = go vs xs

-- | Alter specific bindings using the provided function.
--   
--   This is used in let! expressions to modify observer variable bindings.
alter :: [VarName] -> ((a, Int) -> (a, Int)) -> Context a -> Context a 
alter vs f (Ctx xs) = Ctx (map go xs)
  where 
    go (v,u,a)
      | v `elem` vs = let (a',u') = f (a,u) in (v,u',a')
      | otherwise   = (v,u,a)

-- | Given two contexts that are assumed to have the same variables
--   and elements, but may
--   differ in their usage counts, return a combined context where
--   the usage count is the maximum of the inputs, along with any elements
--   where the usage counts differed.
--
--   This is used in situations like if and case expressions, where
--   control flow branches, and the same linear variables must be used in both
--   branches.
reconcile :: Context a -> Context a -> ([a], Context a)
reconcile (Ctx xs) (Ctx ys) = let (as, zs) = go xs ys in (as, Ctx zs)
  where
    go [] [] = ([], [])
    go ((v,u,a):xs) ((_,u',_):ys)
      = let (as, zs) = go xs ys
            z        = (v,max u u',a)
            as'      = if u /= u' then a:as else as
         in (as', z:zs)

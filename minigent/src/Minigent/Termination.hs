
-- |
-- Module      : Minigent.Termination
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- The termination checking module
--
-- May be used qualified or unqualified.
module Minigent.Termination
  ( termCheck ) where

import Minigent.Fresh
import Minigent.Syntax
import Minigent.Syntax.Utils
import Minigent.Environment

import Control.Monad.State.Strict
import Data.Maybe (maybeToList)

import qualified Data.Map as M
import qualified Data.Set as S

-- A directed graph
type Node  = String
type Graph = M.Map Node [Node]

-- Our environment
type Env a = FreshT VarName (State (M.Map VarName VarName)) a

infixr 0 :<:
data Assertion = 
    VarName :<: VarName  -- ^ Structurally less than
  | VarName :~: VarName  -- ^ Structurally equal to 
  deriving (Eq, Ord, Show)


termCheck :: GlobalEnvironments -> [String]
termCheck = undefined

termAssertionGen :: Expr -> Env ([Assertion], [VarName])
termAssertionGen expr
  = case expr of
    PrimOp _ es ->
      join $ map termAssertionGen es
    Sig e _ -> 
      termAssertionGen e
    Apply f e -> do
      a <- termAssertionGen f
      b <- termAssertionGen e
      c <- getv e
      return $ flatten [([],maybeToList c), a, b]
    Struct fs ->
      let es = map snd fs 
      in join $ map termAssertionGen es
    If b e1 e2 ->
      join $ map termAssertionGen [b, e1, e2]
    Let x e1 e2 -> do
      -- First evaluate the variable binding expression
      a <- termAssertionGen e1

      -- Preserve the old state
      env <- lift $ get
      let old = M.lookup x env

      -- Map our bound program variable to a new name
      fvar <- insert x

      -- Evaluate the rest
      res <- termAssertionGen e2

      -- Roll back the state for the program variable
      undo x old

      -- calculate the assertion for the old variable
      env <- lift $ get
      mv <- getv e1
      let l = (case mv of
                Just x' -> [fvar :~: (env M.! x')]
                Nothing -> [])

      return $ flatten [(l,[]), res]

    _ -> return ([],[])

  where

    -- Returns the variable name from an environment if it exists, otherwise nothing
    getv :: Expr -> Env (Maybe VarName)
    getv e = do
      env <- lift $ get
      return $
        case e of
          Var v -> Just $ env M.! v
          _ -> Nothing

    -- Updates an environment binding
    insert :: VarName -> Env VarName
    insert v = do
      e <- lift $ get
      n <- fresh
      lift $ put (M.insert v n e)
      return n
    
    undo :: VarName -> Maybe VarName -> Env ()
    undo x m = do
      env <- lift $ get 
      lift $ put (M.delete x env)
      case m of
        Just v -> lift $ put (M.insert x v env)
        _      -> return ()
    
    join :: [Env ([Assertion], [VarName])] -> Env ([Assertion], [VarName])
    join (e:es) = do
      (a,b) <- e
      (as,bs) <- join es
      return (a ++ as, b ++ bs)
    join [] = return ([],[])

    flatten :: [([Assertion], [VarName])] -> ([Assertion], [VarName])
    flatten (x:xs) = 
      let rest = flatten xs
      in (fst x ++ fst rest, snd x ++ snd rest)
    flatten [] = ([],[])
    
    add :: [Maybe Assertion] -> [VarName] -> ([Maybe Assertion], [VarName]) -> ([Maybe Assertion], [VarName])
    add a g t = (a ++ fst t, g ++ snd t)

hasPathTo :: Node -> Node -> Graph -> Bool
hasPathTo src dst g
  = hasPathTo' src dst g S.empty
    where
      hasPathTo' :: Node -> Node -> Graph -> S.Set Node -> Bool
      hasPathTo' s d g seen =
        case M.lookup s g of
          Nothing  -> False
          Just nbs ->
            any (\n -> 
                  n == dst ||
                    (notElem n seen &&
                      hasPathTo' n d g (S.insert n seen))
                ) nbs


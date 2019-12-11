
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



-- Our environment, a mapping between program variables and fresh variables
type Env = M.Map VarName VarName

infixr 0 :<:
data Assertion = 
    VarName :<: VarName  -- ^ Structurally less than
  | VarName :~: VarName  -- ^ Structurally equal to 
  deriving (Eq, Ord, Show)


termCheck :: GlobalEnvironments -> [String]
termCheck = undefined

termAssertionGen ::  Env -> Expr -> Fresh VarName ([Assertion], [VarName])
termAssertionGen env expr
  = case expr of
    PrimOp _ es ->
      join $ map (termAssertionGen env) es
    Sig e _ -> 
      termAssertionGen env e
    Apply f e -> do
      a <- termAssertionGen env f
      b <- termAssertionGen env e
      let c = getv env e
      return $ flatten [([], maybeToList c), a, b]
    Struct fs ->
      let es = map snd fs 
      in join $ map (termAssertionGen env) es
    If b e1 e2 ->
      join $ map (termAssertionGen env) [b, e1, e2]
    Let x e1 e2 -> do
      -- First evaluate the variable binding expression
      a <- termAssertionGen env e1

      let old = M.lookup x env

      -- Map our bound program variable to a new name and evaluate the rest
      alpha <- fresh
      let env' = M.insert x alpha env 
      res <- termAssertionGen env' e2

      -- Generate assertion
      let l = (case getv env e1 of
                Just x' -> [alpha :~: (env M.! x')]
                Nothing -> [])
      return $ flatten [(l,[]), res]
    
    LetBang vs v e1 e2 ->
      termAssertionGen env (Let v e1 e2) -- TODO - Correct?
    Take r' f x e1 e2 -> do
      alpha <- fresh 
      beta  <- fresh
      
      res <- termAssertionGen env e1

      -- Update variable to fresh name bindings
      let env' = M.insert r' beta (M.insert x alpha env)
      res' <- termAssertionGen env' e2

      -- generate assertions
      let res'' = (case getv env e1 of
                    Just x' -> [alpha :<: (env M.! x')]
                    Nothing -> [])
                  ++
                  (case getv env e2 of
                    Just x' -> [beta :~: (env M.! x')]
                    Nothing -> [])

      return $ flatten [(res'', []), res', res]

    _ -> return ([],[])

  where

    -- Returns the variable name from an environment if it exists, otherwise nothing
    getv :: Env -> Expr -> Maybe VarName
    getv env e =
      case e of
        Var v -> Just $ env M.! v
        _ -> Nothing

    join :: [Fresh VarName ([Assertion], [VarName])] -> Fresh VarName ([Assertion], [VarName])
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


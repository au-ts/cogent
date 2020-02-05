
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
  ( termCheck
  , genGraphDotFile
  , Assertion (..) 
  ) where

import Minigent.Fresh
import Minigent.Syntax
import Minigent.Syntax.Utils
import Minigent.Environment
import Minigent.Syntax.PrettyPrint

import Control.Monad.State.Strict
import Data.Maybe (maybeToList)

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List

import Debug.Trace

-- A directed graph
type Node  = String
type Graph = M.Map Node [Node]

-- Our environment, a mapping between program variables and fresh variables
type FreshVar = String
type Env = M.Map VarName FreshVar

termCheck :: GlobalEnvironments -> ([String], [(FunName, [Assertion], String)])
termCheck genvs = M.foldrWithKey go ([],[]) (defns genvs)
  where
    go :: FunName -> (VarName, Expr) -> ([String], [(FunName, [Assertion], String)]) -> ([String], [(FunName, [Assertion], String)])
    go f (x,e) (errs, dumps) =  
      let (pass, g, d) = fst $ runFresh unifVars (init f x e)
          er =  if pass then
                  errs
                else
                  ("Error: Function " ++ f ++ " cannot be shown to terminate.") : errs
        in 
          (er, (f, g, d):dumps)

    -- Maps the function argument to a name, then runs the termination
    -- assertion generator.
    -- Return true if the function terminates
    init :: FunName -> VarName -> Expr -> Fresh VarName (Bool, [Assertion], String)
    init f x e = do
      alpha <- fresh
      let env = M.insert x alpha M.empty
      (a,c) <- termAssertionGen env e

      let graph = toGraph a
      let goals = noNothing c

      -- If any goals are nothing, or our path condition is not met, then we cannot determine if the function terminates
      let terminates = length goals == length c 
                       && all (\goal -> hasPathTo alpha goal graph
                                        && (not $ hasPathTo goal alpha graph)
                              ) goals
      return $ 
        (
          terminates,
          a,
          genGraphDotFile f graph
        )

    noNothing :: [Maybe a] -> [a]
    noNothing = foldr (\m l -> 
      case m of
        Nothing -> l
        Just x -> x:l
      ) []

termAssertionGen ::  Env -> Expr -> Fresh VarName ([Assertion], [Maybe FreshVar])
termAssertionGen env expr
  = case expr of
    PrimOp _ es ->
      join $ map (termAssertionGen env) es
      
    Sig e _ -> 
      termAssertionGen env e

    Apply f e -> do
      a <- termAssertionGen env f
      b <- termAssertionGen env e
      return $ flatten [([], [getv env e]), a, b]
      
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
      let l = toAssertion env e1 (alpha :~:)
      return $ flatten [(l,[]), res]
    
    LetBang vs v e1 e2 ->
      termAssertionGen env (Let v e1 e2) -- TODO - Correct?

    Take r' f x e1 e2 -> do
      alpha <- fresh 
      beta  <- fresh
      
      res <- termAssertionGen env e1

      -- Update variable to fresh name bindings and generate assertions recursively
      let env' = M.insert r' beta (M.insert x alpha env)
      res' <- termAssertionGen env' e2

      -- generate assertions
      let assertions = toAssertion env e1 (alpha :<:)
                    ++ toAssertion env e1 (beta :~:)

      return $ flatten [(assertions, []), res', res]

    Put e1 f e2 -> do
      alpha <- fresh
      beta  <- fresh

      res  <- termAssertionGen env e1
      res' <- termAssertionGen env e2

      let assertions = [alpha :<: beta] 
                    ++ toAssertion env e1 (beta :~:)
                    ++ toAssertion env e2 (alpha :~:)

      return $ flatten [(assertions, []), res', res]

    Member e f -> 
      termAssertionGen env e

    Case e1 _ x e2 y e3 -> do
      alpha <- fresh
      beta  <- fresh
      gamma <- fresh

      res <- termAssertionGen env e1

      let env' = M.insert x alpha env
      res' <- termAssertionGen env' e2

      let env'' = M.insert y gamma env
      res'' <- termAssertionGen env'' e3

      let assertions = toAssertion env e1 (beta :~:)
                    ++ [alpha :<: beta, gamma :~: beta]

      return $ flatten [(assertions, []), res, res', res'']

    Esac e1 _ x e2 -> do
      alpha <- fresh
      beta  <- fresh

      res <- termAssertionGen env e1

      let env' = M.insert x alpha env
      res' <- termAssertionGen env' e2

      let assertions = toAssertion env e1 (beta :~:)
                    ++ [alpha :<: beta]

      return $ flatten [(assertions, []), res, res']

    -- All other cases, like literals and nonrecursive expressions
    _ -> return ([],[])

  where
    
    toAssertion :: Env -> Expr -> (FreshVar -> Assertion) -> [Assertion]
    toAssertion env e f = 
      case getv env e of
        Just x -> [f x]
        Nothing -> []

    -- Returns the variable name from an environment if it exists, otherwise nothing
    getv :: Env -> Expr -> Maybe FreshVar 
    getv env e =
      case e of
        Var v -> Just $ env M.! v
        _ -> Nothing

    join :: [Fresh VarName ([a], [b])] -> Fresh VarName ([a], [b])
    join (e:es) = do
      (a,b) <- e
      (as,bs) <- join es
      return (a ++ as, b ++ bs)
    join [] = return ([],[])

    flatten :: [([a], [b])] -> ([a], [b])
    flatten (x:xs) = 
      let rest = flatten xs
      in (fst x ++ fst rest, snd x ++ snd rest)
    flatten [] = ([],[])

toGraph :: [Assertion] -> Graph
toGraph []     = mempty
toGraph (x:xs) = 
  case x of
    (a :<: b) -> addEdge b a $ toGraph xs
    (a :~: b) -> addEdge a b $ addEdge b a $ toGraph xs 
  where
    addEdge a b =
      M.insertWith (++) a [b]


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


-- To use:
--   run `dot -Tpdf graph.dot -o outfile.pdf`
-- where graph.dot is the output from this function.
genGraphDotFile :: String -> Graph -> String
genGraphDotFile name g = 
  "digraph " ++ name ++ " {\n" ++ intercalate "\n" (edges g) ++ "\n}"
  where
    pairs :: Graph -> [(Node,Node)]
    pairs = concatMap (\(a, bs) -> map (\b -> (a,b)) bs) . M.assocs

    edges :: Graph -> [String]
    edges = map (\(a,b) -> "\t" ++ a ++ " -> " ++ b ++ ";") . pairs
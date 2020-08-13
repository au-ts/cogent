
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
import Data.Maybe (maybeToList, catMaybes)

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List

-- Size is either empty, or a tuple containing
-- Int: number of constructors
-- [FreshVar]: components making up the expression
data Size = Empty | V FreshVar | Size (Int, [FreshVar]) deriving (Show, Eq)

-- C -> (1, [A]) <=> C = A + 1

-- B -> (1, [C])

-- 5 * (alpha * (6 * (beta *)))
-- sumList : rec t { l: < Nil Unit | Cons { data: U32, rest: t! }# >}! -> U32;
-- sumList r = 
--   case r.l of
--     Nil u -> 0
--     | v2 ->
--       case v2 of
--         Cons s ->
--           s.data + sumList s.rest
--       end
--   end;

-- -- s(r) = Mult (N 2) s(v)
-- -- s(v) = max (s(Nil Unit), s(Cons ...))
-- -- s(Nil Unit) = 2*s(Unit)
-- -- s(Cons r') = 2*s(r')
-- -- s(r') = 2*(Add s(r'.data), s(r'.rest))
-- -- s(data) = Int 
-- -- s(rest) = fV 
-- x = {Cons {1, Nil Unit}}

-- x -> 
-- s(x) = 2*(2*(2*(Add 1 2*(1)))
-- y = Cons (1, Cons 1 Nil)
-- FreshVar -> ASize

-- s(r) = Mult (N 2) s(r.l)
-- s(r.l) = max (2*s(Unit), 2*(s({..})))
-- s(0) = Int 

-- s(v2) = s(r.l) 
-- s(s) = 2*(Add s(s.data) s(s.rest))
-- s(s.data) = Int 
-- s(s.rest) = fVar 

-- s(s.rest) < s(r)
-- fVar < Mult(N 2) (... fV)

-- 1) Definition of determining size for each type 
-- 2) Types 
-- 3) 


-- size list
-- size int 
-- size String

-- size :: Int -> ASize
-- size x = Nat x

-- size :: Record -> ASize
-- size r = Mult (N 2) (Add r.1 ... r.n)

-- size :: Variant -> ASize
-- size v = max (2*v1... 2*vn)

-- Cons (1, Cons (1, Nil Unit))
-- 2*(1 + 2*(1 + 2*(1)))


-- data ASize = N Int | V FreshVar | Add ASize ASize | Mult ASize ASize

-- Cons (1, Cons (2, Nil Unit))

-- L-> Cons (1, Nil Unit)
-- L2-> Cons (2, Nil Unit)

-- l_size = Empty

-- A -> 1
-- B -> Nil Unit
-- C -> Unit

-- Sizes
-- C-> Empty
-- B-> (1, [C])
-- A-> Empty
-- L-> (1, [A, B])
-- L2-> (1, [E, F])


-- Size is list of PrimTypes (and their values?) and an Int (number of constructors)
-- data Size = Empty | Size [(FreshVar, Maybe PrimType)] Int deriving (Show, Eq)

-- A directed graph maps a node name to all reachable nodes from that node
type Node  = String
type Graph = M.Map Node [Node]

-- Our environment, a mapping between program variables and fresh variables
type FreshVar = String

data Env
  = Env
  {
    oenv :: M.Map VarName FreshVar -- var -> fresh var original mapping
  , fenv :: M.Map FreshVar (Expr, Maybe VarName, Size) -- freshvar mapping
  , eenv :: [(Expr, FreshVar)] -- expression -> fresh var (for non-variables)
  }

emptyEnv = Env M.empty M.empty []

initialiseEnv :: VarName -> FreshVar -> Expr -> Env
initialiseEnv x alpha e =
  let 
    oenv = M.insert x alpha M.empty
    fenv = M.insert alpha (e, Just x, Empty) M.empty
    eenv = [(e, alpha)]
  in Env oenv fenv eenv

-- data FreshVarMap = M.Map FreshVar Expr
-- convert :: Env -> FreshVarMap -> FreshVarMap
-- convert env fenv = 
--   map (insert) (fromList )

-- convertE :: Env -> FreshVarMap -> FreshVarMap
-- convertE env fenv = 
-- (env'' {oenv = M.insert x alpha (oenv env'')})

type Error    = String
type DotGraph = String

termCheck :: GlobalEnvironments -> ([Error], [(FunName, [Assertion], String)])
termCheck genvs = M.foldrWithKey go ([],[]) (defns genvs)
  where
    go :: FunName -> (VarName, Expr) -> ([Error], [(FunName, [Assertion], DotGraph)]) -> ([Error], [(FunName, [Assertion], DotGraph)])
    go f (x,e) (errs, dumps) =  
      let (terminates, g, dotGraph) = fst $ runFresh unifVars (init f x e)
          -- runFresh: runs the fresh monad. unifVars: the stream. (init f x e): the computation
          errs' = if terminates then
                    errs
                  else
                    ("Error: Function: " ++ f ++ " cannot be shown to terminate.") : errs
        in 
          (errs', (f, g, dotGraph) : dumps)

    -- Maps the function argument to a name, then runs the termination
    -- assertion generator.
    -- Returns: 
    --  ( true if the function terminates
    --  , the list of assertions produced from the function
    --  , the `dot' graph file for this particular termination graph
    --  )
    init :: FunName -> VarName -> Expr -> Fresh VarName (Bool, [Assertion], String)
    -- Fresh: monad. VarName: type of the stream. (Bool, [Assertion], String): return type
    init f x e = do
      alpha <- fresh
      let env = initialiseEnv x alpha e
      ((a,c), newE) <- termAssertionGen env e

      let graph = toGraph a
      let goals = catMaybes c

      -- If all goals are not nothing, and our path condition is met, then the function terminates
      -- Otherwise, we cannot say anything about the function
      let terminates = length goals == length c 
                    && all (\goal -> hasPathTo alpha goal graph
                                  && (not $ hasPathTo goal alpha graph)
                           ) goals
      return $ 
        (
          terminates,
          a,
          genGraphDotFile f graph [alpha] goals
        )


termAssertionGen ::  Env -> Expr -> Fresh VarName (([Assertion], [Maybe FreshVar]), Env)
termAssertionGen env expr
  = case expr of
    PrimOp _ es -> do
      -- termAssertionGen env (head es)
      -- join $ map (termAssertionGen env) es
      (res, env') <- termAssertionGenList env es
      return $ (res, env')

    Sig e _ -> 
      termAssertionGen env e

    Apply f e -> do
      -- a <- termAssertionGen env f
      -- b <- termAssertionGen env e
      (a, env') <- termAssertionGen env f
      (b, env'') <- termAssertionGen env' e
      return $ (flatten [([], [getv env'' e]), a, b], env'')
      
    Struct fs -> do
      let es = map snd fs
      -- termAssertionGen env (head es) 
      -- in join $ map (termAssertionGen env) es
      (res, env') <- termAssertionGenList env es
      return $ (res, env')

    If b e1 e2 -> do
      (a, env') <- termAssertionGen env b
      (a', env'') <- termAssertionGen env' e1
      (a'', env''') <- termAssertionGen env'' e2
      return $(flatten [a, a', a''], env'')

      -- join $ map (termAssertionGen env) [b, e1, e2]
      
    Let x e1 e2 -> do
      -- First evaluate the variable binding expression
      (a, env') <- termAssertionGen env e1

      -- Map our bound program variable to a new name and evaluate the rest
      alpha <- fresh
      let env'' = (env' {oenv = M.insert x alpha (oenv env')})
      (res, env''') <- termAssertionGen env'' e2

      -- Generate assertion
      let l = toAssertion env''' e1 (alpha :~:)
      return $ (flatten [(l,[]), res], env''')
    
    LetBang vs v e1 e2 ->
      termAssertionGen env (Let v e1 e2)

    Take r' f x e1 e2 -> do
      alpha <- fresh 
      beta  <- fresh
      
      (res, env') <- termAssertionGen env e1

      -- Update variable to fresh name bindings and generate assertions recursively
      let env'' = (env {oenv = M.insert r' beta (oenv env')})
      let env''' = (env'' {oenv = M.insert x alpha (oenv env'')})
      (res', env4) <- termAssertionGen env''' e2

      -- Generate assertions
      let assertions = toAssertion env4 e1 (alpha :<:)
                    ++ toAssertion env4 e1 (beta :~:)

      return $ (flatten [(assertions, []), res', res], env4)

    Put e1 f e2 -> do
      alpha <- fresh
      beta  <- fresh

      (res, env')  <- termAssertionGen env e1
      (res', env'') <- termAssertionGen env' e2

      let assertions = [alpha :<: beta] 
                    ++ toAssertion env e1 (beta :~:)
                    ++ toAssertion env e2 (alpha :~:)

      return $ (flatten [(assertions, []), res', res], env'')

    Member e f -> do
      alpha <- fresh -- e.f: alpha
      let env' = (env {eenv = ((Member e f), alpha):(eenv env)})

      -- find e inside the env
      -- find the related freshvar
      -- set e.f < e
      (res, env'') <- termAssertionGen env' e
      let assertions = toAssertion env'' e (alpha :<:)
      return $ (flatten [(assertions, []), res], env'')

    Case e1 _ x e2 y e3 -> do
      -- Assertions we want to make:
      -- x < e1
      -- y = e1
      -- where x: alpha, y:gamma, e1: beta (if it exists)

      -- run on e1.
      (res, env1) <- termAssertionGen env e1

      alpha <- fresh -- x
      beta  <- fresh -- e1, if it can be found
      gamma <- fresh -- y

      let env2 = (env1 {oenv = M.insert x alpha (oenv env1)})
      (res', env3) <- termAssertionGen env2 e2

      let env4 = (env3 {oenv = M.insert y gamma (oenv env3)})
      (res'', env5) <- termAssertionGen env4 e3

      let assertions = toAssertion env5 e1 (beta :~:)
                    ++ [alpha :<: beta, gamma :~: beta]

      return $ (flatten [(assertions, []), res, res', res''], env5)

    Esac e1 _ x e2 -> do
      alpha <- fresh
      beta  <- fresh

      (res, env') <- termAssertionGen env e1

      let env'' = (env' {oenv = M.insert x alpha (oenv env')})
      (res', env3) <- termAssertionGen env'' e2

      let assertions = toAssertion env3 e1 (beta :~:)
                    ++ [alpha :<: beta]

      return $ (flatten [(assertions, []), res, res'], env3)

    -- Con k e -> 
    -- All other cases, like literals and nonrecursive expressions
    _ -> return (([],[]), env)

  where
    termAssertionGenList :: Env -> [Expr] -> Fresh VarName (([Assertion], [Maybe FreshVar]), Env)
    termAssertionGenList env [] = do
      return (([],[]), env)
    termAssertionGenList env (x:xs) = do
      (res, env') <- termAssertionGen env x
      (res', env'') <- termAssertionGenList env' xs
      return $ (flatten[res, res'], env'')
    
    toAssertion :: Env -> Expr -> (FreshVar -> Assertion) -> [Assertion]
    toAssertion env e f = 
      case getv env e of
        Just x -> [f x]
        Nothing -> []

    getFreshVarFromExp :: [(Expr, FreshVar)] -> Expr -> Maybe FreshVar
    getFreshVarFromExp [] e = Nothing
    getFreshVarFromExp (x:xs) e = 
      if (fst x == e) then Just $ snd x 
      else getFreshVarFromExp xs e

    -- Returns the variable name from an environment if it exists, otherwise nothing
    getv :: Env -> Expr -> Maybe FreshVar 
    getv env e =
      case e of
        Var v -> Just $ (oenv env) M.! v
        x -> getFreshVarFromExp (eenv env) e 

    join :: [Fresh VarName ([a], [b])] -> Fresh VarName ([a], [b])
    join (e:es) = do
      (a,b) <- e
      (as,bs) <- join es
      return (a ++ as, b ++ bs)
    join [] = return ([],[])


    -- [([a], [b]), ([c], [d])] -> ([a,b], [c,d])
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
--   where graph.dot is the output from this function.
genGraphDotFile :: String -> Graph -> [Node] -> [Node] -> String
genGraphDotFile name g args goals = 
  "digraph " ++ name ++ 
    " {\n"
      ++ "\tforcelabels=true;\n" 
      ++ highlight "blue" "argument" args
      ++ highlight "red"  "goal"     goals
      ++ intercalate "\n" (edges g) 
      ++ "\n}"
  where
    pairs :: Graph -> [(Node,Node)]
    pairs = concatMap (\(a, bs) -> map (\b -> (a,b)) bs) . M.assocs

    edges :: Graph -> [String]
    edges = map (\(a,b) -> "\t" ++ a ++ " -> " ++ b ++ ";") . pairs

    highlight :: String -> String -> [Node] -> String
    highlight color label nodes = "\t" ++ (concat . intersperse "\n" $
                                  map (\n -> n ++ " [ color = " ++ color ++ ", xlabel = " ++ label ++ " ];\n") nodes)

fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a

-- Size Functions
-- Arithmetic

-- will add the second arg to the first arg, returning the first.
add :: Size -> FreshVar -> Size
add s f =
  case s of
    Empty -> Size (1, [f])
    Size (n, x) -> 
      if f `elem` x then
        Size (n, x)
      else
        Size (n, f:x)
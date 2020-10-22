

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

import qualified Data.Matrix as Matrix
import qualified Data.Vector as V

import Debug.Trace

data MeasureOp
  = ProjectOp String MeasureOp -- field 
  | UnfoldOp String String MeasureOp -- recpar, field 
  | RecParMeasure String -- recpar 
  | CaseOp [(String,MeasureOp)] -- field 
  | IntConstOp Int
  -- | VarAST 
  deriving (Show, Eq)

buildMeasure :: Type -> [MeasureOp] -> [MeasureOp]
buildMeasure t res = 
  case t of 
    PrimType p -> IntConstOp 0 : res 
    Record recpar row sig -> parseRecord recpar $ M.toList (rowEntries row)
    Variant row -> parseVariant $ M.toList (rowEntries row)
    RecPar t rc -> RecParMeasure t : res
    RecParBang t rc -> RecParMeasure t : res 
    AbsType name sig ty -> IntConstOp 0: res
    TypeVar v -> IntConstOp 0 : res 
    TypeVarBang v -> IntConstOp 0 : res 
    UnifVar v -> IntConstOp 0 : res
    Function x y -> IntConstOp 0 : res 
    Bang t -> buildMeasure t []

parseRecord :: RecPar -> [(FieldName, Entry)] -> [MeasureOp]
parseRecord _ [] = []
parseRecord recpar ((f, Entry _ ty _): rs) = 
  let children = buildMeasure ty []
      rest = parseRecord recpar rs
  in case recpar of 
    None -> (map (\x -> ProjectOp f x) children) ++ rest
    Rec recpar' -> (map (\x -> UnfoldOp recpar' f x) children) ++ rest
    UnknownParameter t -> [] -- shouldn't happen, should be caught by type checker

parseVariant :: [(FieldName, Entry)] -> [MeasureOp]
parseVariant [] = []
parseVariant ((f, Entry _ ty _): rs) = 
  let cur = buildMeasure ty []
      rest = parseVariant rs 
  in cartesianProduct f cur rest 

cartesianProduct :: FieldName -> [MeasureOp] -> [MeasureOp] -> [MeasureOp]
cartesianProduct f [] [] = []
cartesianProduct f ms [] = map (\x -> CaseOp x) [[(f, m)] | m <- ms] 
cartesianProduct f ms cs = map (\x -> CaseOp x) [(f, m):c | m <- ms, c <- map (\(CaseOp v) -> v) cs] 

-- A directed graph maps a node name to all reachable nodes from that node
type Node  = String
type Graph = M.Map Node [Node]

-- Our environment, a mapping between program variables and fresh variables
type FreshVar = String
type Env = M.Map VarName FreshVar

type Error    = String
type DotGraph = String

getMeasure :: FunName -> GlobalEnvironments -> [MeasureOp]
getMeasure f genvs = 
  case M.lookup f (types genvs) of 
    Nothing -> [] 
    Just (Forall _ _ ty) -> 
      case ty of 
        Function x y -> (buildMeasure x [])
        _ -> []

-- get functions
getRecursiveCalls :: FunName -> Expr -> [Expr] -- starting exp, result list 
getRecursiveCalls f exp = case exp of 
  PrimOp o es -> concat $ map (getRecursiveCalls f) es
  Literal _ -> []
  Var _ -> []
  Con _ e -> getRecursiveCalls f e
  TypeApp _ _ -> []
  Sig e t -> getRecursiveCalls f e 
  Apply e1 e2 -> case e1 of 
    TypeApp funName ts -> if f == funName then [e2] else []
    _ -> []
  Struct es -> concat $ map (\(_, e) -> getRecursiveCalls f e) es
  If e1 e2 e3 -> getRecursiveCalls f e1 ++ getRecursiveCalls f e2 ++ getRecursiveCalls f e3
  Let v e1 e2 -> getRecursiveCalls f e1 ++ getRecursiveCalls f e2
  LetBang vs v e1 e2 -> getRecursiveCalls f e1 ++ getRecursiveCalls f e2
  Take v f' v2 e1 e2 -> getRecursiveCalls f e2
  Put e1 f' e2 -> getRecursiveCalls f e2
  Member e f' -> getRecursiveCalls f e
  Case e1 c v e2 v2 e3 -> getRecursiveCalls f e1 ++ getRecursiveCalls f e2 ++ getRecursiveCalls f e3
  Esac e1 c v e2 -> getRecursiveCalls f e1 ++ getRecursiveCalls f e2

type Size = (Maybe Expr, Int) -- leftover expression, number of unfoldings

-- applyMeasure :: AST -> Size -> Size
-- applyMeasure ast (e, n) = case ast of 
--   RecursiveRecordAST t f ast' -> 
--     let e' = cutExpr True f e
--     in applyMeasure ast' (e', n)
--   RecordAST f ast' -> 
--     let e' = cutExpr True f e
--     in applyMeasure ast' (e', n)
--   VariantAST f ast' -> 
--     let e' = cutExpr False f e 
--     in applyMeasure ast' (e', n)
--   RecParAST t -> (e, n+1)
--   _ -> (e, n)


-- cutExpr :: Bool -> String -> Maybe Expr -> Maybe Expr 
-- -- true: take, false: case, string: field 
-- cutExpr b s Nothing = Nothing
-- cutExpr b s (Just exp) = 
--   case exp of 
--     PrimOp o (x:xs) -> 
--       case cutExpr b s (Just x) of 
--         Nothing -> case xs of 
--           [] -> Nothing 
--           (y:ys) -> cutExpr b s (Just y)
--         Just me -> Just me
--     Literal v -> Nothing
--     Var v -> Nothing
--     Con c e -> cutExpr b s (Just e)
--     TypeApp f ts -> Nothing
--     Sig e t -> cutExpr b s (Just e)
--     Apply e1 e2 -> case cutExpr b s (Just e1) of 
--       Nothing -> cutExpr b s (Just e2)
--       Just me -> Just me
--     Struct fs -> Nothing -- TODO
--     If e1 e2 e3 -> case cutExpr b s (Just e1) of 
--       Nothing -> case cutExpr b s (Just e2) of
--         Nothing -> cutExpr b s (Just e3)
--         Just me -> Just me 
--       Just me -> Just me
--     Let v e1 e2 -> case cutExpr b s (Just e1) of 
--       Nothing -> cutExpr b s (Just e2)
--       Just me -> Just me
--     LetBang vs v e1 e2 -> case cutExpr b s (Just e1) of 
--       Nothing -> cutExpr b s (Just e2)
--       Just me -> Just me
--     Take v1 f v2 e1 e2 -> 
--       case b of 
--         True -> if f == s then (Just e2) else cutExpr b s (Just e2)
--         False -> cutExpr b s (Just e2)
--     Put e1 f e2 -> case cutExpr b s (Just e1) of 
--       Nothing -> cutExpr b s (Just e2)
--       Just me -> Just me
--     Member e f -> cutExpr b s (Just e)
--     Case e1 c v1 e2 v2 e3 -> 
--       case b of 
--         True -> cutExpr b s (Just e3)
--         False -> if c == s then (Just e2) else cutExpr b s (Just e3)
--     Esac e1 c v e2 ->
--       case b of 
--         True -> cutExpr b s (Just e2)
--         False -> if c == s then (Just e2) else cutExpr b s (Just e2)

-- GLOBAL DESCENT -- 
data Cmp = Le | Eq | Unknown | Solved deriving (Show, Eq)
globalDescent :: Matrix.Matrix Cmp -> Bool
globalDescent m = case (Matrix.ncols m) of 
  0 -> True -- empty
  n -> case findCol m n of
    Nothing -> False
    Just col -> globalDescent (removeRows m (Matrix.nrows m) col)

removeRows :: Matrix.Matrix Cmp -> Int -> Int -> Matrix.Matrix Cmp -- row, col
removeRows m 1 col = case m Matrix.! (1, col) of 
  Le -> Matrix.fromLists [[]]
  _ -> m
removeRows m row col = 
  case m Matrix.! (row, col) of 
    Le ->
      let newM = Matrix.fromLists $ deleteRow (Matrix.toLists m) row 
      in removeRows newM (row-1) col
    _ -> removeRows m (row-1) col

deleteRow :: [[Cmp]] -> Int -> [[Cmp]]
deleteRow [] _ = []
deleteRow (r:rs) 1 = rs
deleteRow (r:rs) n = r:deleteRow rs (n-1)

findCol :: Matrix.Matrix Cmp -> Int -> Maybe Int -- matrix, col that we're counting, result
findCol m 0 = Nothing
findCol m n = 
  if checkCol (Matrix.getCol n m) 0 then (Just n)
  else findCol m (n-1)

checkCol :: V.Vector Cmp -> Int -> Bool
checkCol v n = 
  case V.null v of
    True -> case n of
      0 -> False 
      1 -> True
    False -> case V.head v of 
      Le -> checkCol (V.tail v) 1
      Eq -> checkCol (V.tail v) n
      Unknown -> False

termCheck :: GlobalEnvironments -> ([Error], [(FunName, [Assertion], String)])
termCheck genvs = M.foldrWithKey go ([],[]) (defns genvs)
  where
    go :: FunName -> (VarName, Expr) -> ([Error], [(FunName, [Assertion], DotGraph)]) -> ([Error], [(FunName, [Assertion], DotGraph)])
    go f (x,e) (errs, dumps) =  
      let measure = getMeasure f genvs
          recursiveCalls = getRecursiveCalls f e
          -- size = applyMeasure (head $ tail measure) (Just e, 0)
          (terminates, g, dotGraph) = fst $ runFresh unifVars (init f x e)
          errs' = if terminates then
                    (show measure ++ " ---- \n" 
                    ++ show e ++ "-------\n" 
                    ++ show recursiveCalls ++ "-------\n") 
                    -- ++ "size: " ++ show size) 
                    :errs
                  else
                    (show measure ++ " ---- \n" ++ show e ++ "-------\n" ++ show recursiveCalls ++  "Error: Function " ++ f ++ " cannot be shown to terminate.") : errs
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
    init f x e = do
      alpha <- fresh
      let env = M.insert x alpha M.empty
      (a,c) <- termAssertionGen env e

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

      -- Map our bound program variable to a new name and evaluate the rest
      alpha <- fresh
      let env' = M.insert x alpha env 
      res <- termAssertionGen env' e2

      -- Generate assertion
      let l = toAssertion env e1 (alpha :~:)
      return $ flatten [(l,[]), res]
    
    LetBang vs v e1 e2 ->
      termAssertionGen env (Let v e1 e2)

    Take r' f x e1 e2 -> do
      alpha <- fresh 
      beta  <- fresh
      
      res <- termAssertionGen env e1

      -- Update variable to fresh name bindings and generate assertions recursively
      let env' = M.insert r' beta (M.insert x alpha env)
      res' <- termAssertionGen env' e2

      -- Generate assertions
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

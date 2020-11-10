

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
  -- , genGraphDotFile
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

-- A directed graph maps a node name to all reachable nodes from that node
type Node  = String
type Graph = M.Map Node [Node]

-- Our environment, a mapping between program variables and fresh variables
type FreshVar = String
type Env' = M.Map VarName FreshVar

type Error    = String
type DotGraph = String

-- TYPES AST
data Template 
  = RecordAST (Maybe VarName) [(FieldName, (Maybe VarName), Template)]
  | RecursiveRecordAST RecParName (Maybe VarName) [(FieldName, (Maybe VarName), Template)]
  | VariantAST (Maybe VarName) [(FieldName, (Maybe VarName), Template)]
  | PrimitiveAST (Maybe VarName)
  | RecParAST RecParName (Maybe VarName)
  deriving (Show, Eq)

buildTemplate :: Type -> Template
buildTemplate t = case t of
  PrimType p -> PrimitiveAST Nothing
  Record recpar row sig -> 
    let res = parseTypes $ M.toList (rowEntries row)
    in case recpar of 
      Rec t -> RecursiveRecordAST t Nothing res 
      _ -> RecordAST Nothing res -- None, but could also be unknown.
  Variant row -> VariantAST Nothing $ parseTypes $ M.toList (rowEntries row)
  RecPar t rc -> RecParAST t Nothing
  RecParBang t rc -> RecParAST t Nothing
  AbsType name sig ty -> PrimitiveAST Nothing
  TypeVar v -> PrimitiveAST Nothing
  TypeVarBang v -> PrimitiveAST Nothing
  UnifVar v -> PrimitiveAST Nothing
  Function x y -> PrimitiveAST Nothing
  Bang t -> buildTemplate t

parseTypes :: [(FieldName, Entry)] -> [(FieldName, (Maybe VarName), Template)]
parseTypes [] = []
parseTypes xs = map (\(f, Entry _ ty _) -> (f, Nothing, buildTemplate ty)) xs

-- MEASURES AST --
data MeasureOp
  = ProjectOp FieldName MeasureOp -- field 
  | UnfoldOp RecParName FieldName MeasureOp -- recpar, field 
  | RecParMeasure RecParName -- recpar 
  | CaseOp [(String,MeasureOp)] -- field 
  | IntConstOp Int
  deriving (Show, Eq)

-- BUILD MEASURE FROM REC ARG TYPE -- 
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

getType :: FunName -> GlobalEnvironments -> Maybe Type
getType f genvs = 
  case M.lookup f (types genvs) of 
    Nothing -> Nothing 
    Just (Forall _ _ ty) -> case ty of 
      Function x y -> Just x
      _ -> Nothing

-- EXTRACT RECURSIVE CALLS -- 
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

-- GLOBAL DESCENT -- 
data Cmp = Le | Eq | Unknown deriving (Show, Eq)
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

-- Fill env and templates
type FreshEnv = M.Map FreshVar Expr
type ExprEnv = [(Expr, FreshVar)]

data Env = Env {
  freshEnv :: M.Map FreshVar Expr,
  exprEnv :: [Expr],
  assertionsEnv :: M.Map FreshVar [FreshVar] -- each freshvar may be linked to a series of other freshvars.
} deriving (Show)

emptyEnv = Env M.empty [] M.empty

termCheck :: GlobalEnvironments -> ([Error], [(FunName, Bool)])
termCheck genvs = M.foldrWithKey go ([], []) (defns genvs)
  where 
    go :: FunName -> (VarName, Expr) -> ([Error], [(FunName, Bool)]) -> ([Error], [(FunName, Bool)])
    go f (x, e) (errs, dumps) = 
      case getType f genvs of 
        Nothing -> ([], [])
        Just ty ->
          let (funName, b, m, te, tt, env) = (init' f x e ty)
              msg = ("\n\nMatrix\n" ++ (show m) 
                  ++ "\n\nTemplate Expr Tuples\n" ++ (show te)
                  ++ "\n\nTemplate Tuples\n" ++ (show tt)
                  ++ "\n\nEnv\n" ++ (show env)
                  )
              errs' = case b of 
                True -> ((show "Passes termination") ++ msg):errs
                False -> ((show "Fails termination") ++ msg):errs
            in (errs', (funName, b):[])

    init' :: FunName -> VarName -> Expr -> Type -> (FunName, Bool, Matrix.Matrix Cmp, [(Template, Expr)], [(Template, Template)], Env)
    init' funName x e ty =
      let 
        -- generate list of measures
        measures = buildMeasure ty []
        -- generate template
        template = buildTemplate ty
        -- generate (template, expr) tuples, environment and error msg
        (templateExpr, env, err) = fst $ runFresh unifVars $ fillTemplates funName e template (envAdd (Var "r") emptyEnv) 0
        -- convert the expressions into templates
        templateExprChar = zip templateExpr ['a'..'z'] -- lol, fix later
        (templateTemplate, env1) = fillTemplateExp template templateExprChar env
        -- generate assertions
        env2 = assertions templateTemplate env1
        env3 = resolveEnv env2
        -- apply measures 
        -- matrix = Matrix.fromLists [[]]
        -- generate local descent arrays
        -- generate matrix
        matrix = Matrix.fromLists $ generateMatrix env2 templateTemplate measures
        -- run global descent
        result = globalDescent matrix
        -- result = True
      in (funName, result, matrix, templateExpr, templateTemplate, env3)

-- for each template + expression, apply the measure
generateMatrix :: Env -> [(Template, Template)] -> [MeasureOp] -> [[Cmp]]
generateMatrix _ [] _ = [[]]
generateMatrix _ _ [] = [[]]
generateMatrix env (t:ts) ms = 
  -- for each template, apply ALL the measures 
  let input = map (\m -> applyMeasure env m (fst t) m) ms 
      recCalls = map (\m -> applyMeasure env m (snd t) m) ms
  in
    [map (\(i, r) -> compareMeasure i r env) $ zip input recCalls] ++ (generateMatrix env ts ms)

type Size = (Maybe MeasureOp, Maybe FreshVar, Int)
compareMeasure :: Size -> Size -> Env -> Cmp
-- input, then recursive measure.
-- These are errors.
-- Not all cases covered - check nothing cases.
compareMeasure (_, _, -1) _ _ = Unknown
compareMeasure _ (_, _, -1) _ = Unknown
compareMeasure (_, Just e1, n1) (_, Just e2, n2) env = 
  if (n1 > n2 && (equivExpr e1 e2 env)) then Le 
  else 
    if (n1 == n2 && (equivExpr e1 e2 env)) then Eq 
    else Unknown

-- do something fancier?? Resolve somehow
equivExpr :: FreshVar -> FreshVar -> Env -> Bool
equivExpr e1 e2 env = 
  if (e1 == e2) then True 
  else case M.lookup e1 (assertionsEnv env) of 
    Nothing -> False 
    Just xs -> case find (\x -> x == e2) xs of 
      Nothing -> False 
      Just x -> True

fillTemplateExp :: Template -> [((Template, Expr), Char)] -> Env -> ([(Template, Template)], Env)
fillTemplateExp tem [] env = ([], env)
fillTemplateExp tem (((t, e), c):ts) env = 
  let (t', env1) = exprToTemplate e env tem (c:[c])
      (res, env2) = fillTemplateExp tem ts env1
  in ((t, t'):res, env2)

-- Build template from expression
-- TODO: finish this off.
exprToTemplate :: Expr -> Env -> Template -> String -> (Template, Env)
exprToTemplate exp env tem alpha =
  case exp of 
    Member e f ->
      case tem of 
        RecursiveRecordAST rp mv t ->
          (RecursiveRecordAST rp (Just alpha) t, (envAddFresh [(alpha, exp)] env))
        _ -> (tem, env)
    Var v -> 
      case tem of 
        RecursiveRecordAST rp mv t ->
          (RecursiveRecordAST rp (Just alpha) t, (envAddFresh [(alpha, exp)] env))
        _ -> (tem, env)
    _ -> (tem, env)

applyMeasure :: Env -> MeasureOp -> Template -> MeasureOp -> Size
-- original template, current template, current measureOp
applyMeasure env mOp (RecordAST (Just alpha) [(f, (Just v), t)]) (ProjectOp f' m) = 
  if (f == f') then 
    case applyMeasure env mOp t m of 
      -- if it's an error, return the current position.
      (Nothing, Nothing, -1) -> (Just (ProjectOp f' m), Just alpha, 0)
      x -> x
  else (Nothing, Nothing, -1)
applyMeasure env mOp (RecursiveRecordAST rp (Just alpha) [(f, (Just v), t)]) (UnfoldOp rp' f' m) = 
  if (f == f') then 
    case applyMeasure env mOp t m of -- continue
      -- if error, return the current position.
      (Nothing, Nothing, -1) -> (Just (UnfoldOp rp' f' m), Just alpha, 0)
      x -> x
  else (Nothing, Nothing, -1)
applyMeasure env mOp (VariantAST (Just alpha) [(f, Just v, t)]) (CaseOp cs) =
  case (find (\(f', m') -> f' == f) cs) of 
    Nothing -> (Nothing, Nothing, -1)
    -- found, so move on.
    Just (f', m') -> case applyMeasure env mOp t m' of 
      (Nothing, Nothing, -1) -> (Just (CaseOp cs), Just alpha, 0)
      x -> x
applyMeasure env mOp (RecParAST rp (Just alpha)) (RecParMeasure rp') =
  case (rp == rp') of
    -- make sure they match
    False -> (Nothing, Nothing, -1)
    -- search up the exp related to alpha
    True -> (Just mOp, Just alpha, 1)
-- Check this: no unfoldings have happened. so its ok.
applyMeasure env mOp (PrimitiveAST (Just alpha)) (IntConstOp n) = (Nothing, Nothing, 0)
-- if any of the variable names are 'Nothing'
-- if any of the template/mOp pairs don't match
applyMeasure env mOp _ _ = (Nothing, Nothing, -1)

resolveEnv :: Env -> Env 
resolveEnv env = 
  -- take stuff out from the freshEnv and group on the second element
  -- flipAL :: (Eq key, Eq val) => [(key, val)] -> [(val, [key])]Source
  let x = map (\x -> snd x) $ flipAL $ M.toList (freshEnv env)
  in case x of 
    [] -> env 
    xs -> foldr (resolveEnvHelper) env xs
-- envAddAssertion :: FreshVar -> FreshVar -> Env -> Env 
-- envAddAssertion f1 f2 env = 
--   let env' = addAssertion f1 f2 env 
--   in addAssertion f2 f1 env'

-- from the MissingH library
{- | Flips an association list.  Converts (key1, val), (key2, val) pairs
to (val, [key1, key2]). -}
flipAL :: (Eq key, Eq val) => [(key, val)] -> [(val, [key])]
flipAL oldl =
    let worker :: (Eq key, Eq val) => [(key, val)] -> [(val, [key])] -> [(val, [key])]
        worker [] accum = accum
        worker ((k, v):xs) accum =
            case lookup v accum of
                                Nothing -> worker xs ((v, [k]) : accum)
                                Just y  -> worker xs (addToAL accum v (k:y))
        in
        worker oldl []
{- | Adds the specified (key, value) pair to the given list, removing any
existing pair with the same key already present. -}
addToAL :: Eq key => [(key, elt)] -> key -> elt -> [(key, elt)]
addToAL l key value = (key, value) : delFromAL l key

{- | Removes all (key, value) pairs from the given list where the key
matches the given one. -}
delFromAL :: Eq key => [(key, a)] -> key -> [(key, a)]
delFromAL l key = filter (\a -> (fst a) /= key) l

resolveEnvHelper :: [FreshVar] -> Env -> Env
resolveEnvHelper [] env = env 
resolveEnvHelper (f:fs) env = 
  let env' = foldr (envAddAssertion f) env fs
  in resolveEnvHelper fs env'

assertions :: [(Template, Template)] -> Env -> Env 
assertions [] env = env 
assertions ((t1, t2):ts) env = 
  let env1 = generateAssertions t1 env 
      env2 = generateAssertions t2 env1
  in assertions ts env2

generateAssertions :: Template -> Env -> Env 
generateAssertions tem env = 
  case tem of 
    RecordAST (Just alpha) [(f', (Just beta), t')] -> 
      case t' of 
        RecordAST (Just gamma) _ -> generateAssertions t' (envAddAssertion beta gamma env)
        RecursiveRecordAST rp (Just gamma) _ -> generateAssertions t' (envAddAssertion beta gamma env)
        VariantAST (Just gamma) _ -> generateAssertions t' (envAddAssertion beta gamma env)
        PrimitiveAST (Just gamma) -> envAddAssertion beta gamma env
        RecParAST rp (Just gamma) -> envAddAssertion beta gamma env
    RecursiveRecordAST rp (Just alpha) [(f', (Just beta), t')] ->
      case t' of 
        RecordAST (Just gamma) _ -> generateAssertions t' (envAddAssertion beta gamma env)
        RecursiveRecordAST rp (Just gamma) _ -> generateAssertions t' (envAddAssertion beta gamma env)
        VariantAST (Just gamma) _ -> generateAssertions t' (envAddAssertion beta gamma env)
        PrimitiveAST (Just gamma) -> envAddAssertion beta gamma env
        RecParAST rp (Just gamma) -> envAddAssertion beta gamma env
    VariantAST (Just alpha) [(f', (Just beta), t')] -> generateAssertions t' (envAddAssertion alpha beta env)
    _ -> env

-- ASSUMPTIONS:
-- Case e1s: only contain Var v or Member e f expressions.
fillTemplateHelper :: [(Template, Expr)] -> Template -> Env -> [Error] -> Int -> ([(Template, Expr)], Env, [Error])
-- list of results, template to wrap with, env, error, freshvar to use, int (for more fresh vars)
fillTemplateHelper [] tem env err n = ([], env, err)
fillTemplateHelper ((t, e):ts) tem env err n = 
  let (res, env1, err1) = fillTemplateHelper ts tem env err (n+1)
  in
    case tem of 
      RecordAST mv [(f', mv', x)] -> 
        (((RecordAST mv [(f', mv', t)], e):res), env, err ++ err1 ++ ["helper func"])
      RecursiveRecordAST rp mv [(f', mv', x)] -> 
        (((RecursiveRecordAST rp mv [(f', mv', t)], e):res), env, err ++ err1 ++ ["helper func"])
      VariantAST mv [(f', mv', x)] ->
        case mv of 
          Nothing -> ([], env, ["Helper: Missing freshvar"])
          (Just x) -> (((VariantAST mv [(f', mv', t)], e):res), env, err ++ err1 ++ ["helper func"])
      _ -> ([], env, ["Helper: template does not match"]++ [show tem])

fillTemplates :: FunName -> Expr -> Template -> Env -> Int -> Fresh VarName ([(Template, Expr)], Env, [Error])
fillTemplates funName exp tem env n = 
  case exp of 
    PrimOp op (e:es) -> case es of 
      [x] -> do
          (res1, env1, err1) <- fillTemplates funName e tem env n
          (res2, env2, err2) <- fillTemplates funName x tem env n
          return (res1 ++ res2, env2, err1 ++ err2)
      _ -> fillTemplates funName e tem env n
    Literal _ -> return ([], env, ["Empty Lit"])
    Var y -> return ([], env, ["Empty Var"])
    -- v.j : recurse here.
    Con c e -> return ([], env, ["Empty Con"])
    TypeApp f ts -> return ([], env, ["Empty TypeApp"])
    -- v.j: recurse here.
    Sig e t -> return ([], env, ["Empty Sig"])
    Apply e1 e2 -> case e1 of 
      TypeApp f ts -> 
        -- check that this is the recursive function
        if f == funName then do
          let env1 = envAdd e2 env
          (res1, env2, err1) <- fillTemplates funName e2 tem env1 n
          alpha <- fresh
          return $
            case res1 of
              [] -> case tem of
                -- map alpha:e2 (e2 is the recursive arg)
                RecParAST rp mv -> ([(RecParAST rp (Just alpha), e2)], (envAddFresh [(alpha, e2)] env1), err1)
                _ -> ([], env2, err1 ++ ["Error: Apply not happening on RP"])
                -- do we need to recurse here, or just leave it?
              _ -> (res1, env2, err1)
        else return ([], env, ["TypeApp: not the recursive function"])
    -- v.j: recurse here
    Struct [(fieldname, e)] -> return ([], env, ["Empty Struct"])
    If e1 e2 e3 -> return ([], env, ["Empty If"])
    Let v e1 e2 -> return ([], env, ["Empty Let"])
    LetBang vs v e1 e2 -> return ([], env, ["Empty LetBang"])
    Take v1 f v2 e1 e2 -> 
      -- TODO: check that e1 is the correct record
      case tem of 
        RecordAST mv xs -> 
          case find (\(f', mv', t') -> f == f') xs of 
            Nothing -> return ([], env, ["Take R Empty"])
            Just (f', mv', t') -> do
              let env1 = envAdd (Var v2) env
              alpha <- fresh
              beta <- fresh
              (res1, env2, err1) <- fillTemplates funName e2 t' env1 (n+1)
              return $ case res1 of
                -- if res1 is empty, then take res2
                [] -> ([], env2, err1 ++ ["Take R"])
                -- map alpha:e1, which is the original record
                -- map beta:(Var v2), where v2 is the variable assigned to hold the taken element.
                -- pass beta in as the INSIDE thing. 
                _ -> fillTemplateHelper res1 (RecordAST (Just alpha) [(f', (Just beta), t')]) (envAddFresh [(alpha, e1), (beta, Var v2)] env2) err1 0
        RecursiveRecordAST rp mv xs -> 
          -- check that e1 exists in the env as well.
          case find (\(f', mv', t') -> f == f') xs of 
            Nothing -> return ([], env, ["Take RR Empty"])
            Just (f', mv', t') -> do
              alpha <- fresh
              beta <- fresh
              let env1 = envAdd (Var v2) env
                  xs' = delete (f', mv', t') xs
              (res1, env2, err1) <- fillTemplates funName e2 t' env1 (n+1)
              return $ case res1 of
                [] -> ([], env2, err1 ++ ["Take RR"])
                -- map alpha:e1, which is the original record
                -- map beta:(Var v2), where v2 is the variable assigned to hold the taken element.
                _ -> fillTemplateHelper res1 (RecursiveRecordAST rp (Just alpha) [(f', (Just beta), t')]) (envAddFresh [(alpha, e1), (beta, Var v2)] env2) err1 0
        _ -> return ([], env, ["Take Error"]) -- Error, should only be seeing a record when taking.
    -- TODO
    Put e1 f e2 -> return ([], env, ["Empty Put"])
    Member e f ->
      -- Check that e exists in the env. 
      case envExists e env of 
        False -> return ([], env, ["Member e does not exist"])
        True -> 
          case tem of 
          -- Check for records. This doesn't recurse bc no expression to work on.
            RecordAST mv xs ->
              case find (\(f', mv', t') -> f == f') xs of 
                Nothing -> return ([], env, ["Member R:" ++ f ++ " missing"])
                Just (f', mv', t') ->
                  case t' of
                    PrimitiveAST mv1 -> return ([], env, ["Member R Primitive"])
                    RecParAST rp mv1 -> do 
                      alpha <- fresh -- recursive param (Member e f)
                      beta <- fresh -- recursive param record (Member e f)
                      gamma <- fresh -- record (e)
                      return ([(RecordAST (Just gamma) [(f', Just beta, RecParAST rp (Just alpha))], (Member e f))], (envAddFresh [(alpha, (Member e f)), (beta, (Member e f)), (gamma, e)] env), ["Member R RecPar"])
                    -- anything else?
                    _ -> return ([], env, ["Member R Other"])
            RecursiveRecordAST rp mv xs -> 
              case find (\(f', mv', t') -> f == f') xs of 
                Nothing -> return ([], env, ["Member RR"])
                Just (f', mv', t') ->
                  case t' of 
                    PrimitiveAST mv1 -> return ([], env, ["Member-RR-Primitive"])
                    RecParAST rp mv1 -> do 
                      alpha <- fresh -- recursive param (Member e f)
                      beta <- fresh -- recursive param record (Member e f)
                      gamma <- fresh -- record (e)
                      return ([(RecursiveRecordAST rp (Just gamma) [(f', (Just beta), RecParAST rp (Just alpha))], (Member e f))], (envAddFresh [(alpha, (Member e f)), (beta, (Member e f)), (gamma, e)] env), ["Member-RR-RecPar"])
                    -- anything else?
                    _ -> return ([], env, ["Member RR"])
            _ -> return ([], env, ["Member RR"])
    Case e1 c v1 e2 v2 e3 -> 
      case e1 of 
        Var v -> 
          case tem of 
            VariantAST mv xs -> 
              -- check what v is inside the environment.
              case envExists (Var v) env of 
                False -> return ([], env, ["Case V does not exist"])
                True -> 
                  -- 1. If OK, add v1 into the env, get results for e2 and e3.
                  -- 2. Find the matching ConName + template, try it. 
                  -- 3. Try on the others and then combine.
                  case find (\(f', mv', t') -> c == f') xs of 
                    Nothing -> return ([], env, ["Case V"]) -- error; we should always be able to find a match in the variant list from the template.
                    Just (f', mv', t') -> do
                      let env1 = envAdd (Var v2) env
                          xs' = delete (f', mv', t') xs
                      -- try on e2
                      (res1, env2, err1) <- fillTemplates funName e2 t' env1 (n+1)
                      -- try on e3 with the match removed from the variant list
                      (res2, env3, err2) <- fillTemplates funName e3 (VariantAST mv xs') env2 n
                      alpha <- fresh
                      return $ case res1 of 
                        -- if the first one is empty, return the second
                        [] -> (res2, env3, err1 ++ err2)
                        -- else, add them together
                        _ ->
                          -- add alpha:e1 into env, as e1 is the variant exp (the thing we are casing on)
                          -- same thing for inside + outside: variant with choices is the same size as variant without choices.
                          let (res3, env4, err3) = fillTemplateHelper res1 (VariantAST (Just alpha) [(f', (Just alpha), t')]) (envAddFresh [(alpha, e1)] env3) (err1 ++ err2) 0
                          in (res2 ++ res3, env4, err3)
            -- not a variant, problem.
            _ -> return ([], env, ["Case error: not V"])
        Member e4 f -> 
          case tem of
            -- unpack the record.
            RecordAST mv xs ->
              case find (\(f', mv', t') -> f == f') xs of 
                Nothing -> return ([], env, ["Case-MR"])
                Just (f', mv', t') ->
                  -- the leftover thing _should_ be a variant (for casing on) 
                  case t' of
                    VariantAST mv1 xs1 ->
                      -- match the variant with the ConName and try.
                      case find (\(f'', mv'', t'') -> c == f'') xs1 of 
                        Nothing -> return ([], env, ["Case-MRV error"]) -- error; we should always be able to find a match in the variant list.
                        Just (f'', mv'', t'') -> do
                          -- try on e2 
                          -- add v2 into the env
                          let env1 = envAdd (Var v2) env
                              xs1' = delete (f'', mv'', t'') xs1 
                          (res1, env2, err1) <- fillTemplates funName e2 t'' env1 (n+1) 
                          (res2, env3, err2) <- fillTemplates funName e3 (VariantAST mv xs1') env2 n
                          alpha <- fresh -- for variant e1
                          beta <- fresh -- for record e4
                          gamma <- fresh -- for record (Member e4 f)
                          return $ case res1 of
                              [] -> 
                                -- wrap in record for res2
                                -- add beta:e4 to the env, as that's the record we took from.
                                fillTemplateHelper res2 (RecordAST (Just beta) [(f', (Just gamma), t')]) (envAddFresh [(beta, e4), (gamma, (Member e4 f))] env3) (err1 ++ err2) 0
                                --(res2, env3, err1 ++ err2)
                              _ ->
                                -- wrap in variant for res1
                                -- add alpha:e1 to the env, as that is the variant we case on.
                                let (res3, env4, err3) = fillTemplateHelper res1 (VariantAST (Just alpha) [(f', (Just alpha), t')]) (envAddFresh [(alpha, e1)] env3) err2 0
                                -- wrap in record for all.
                                -- add beta:e4 to the env, as that is the record that we took from.
                                in fillTemplateHelper (res2 ++ res3) (RecordAST (Just beta) [(f', (Just gamma), t')]) (envAddFresh [(beta, e4), (gamma, (Member e4 f))] env4) err3 0
                    -- Error, we should always be seeing a variant template here.
                    _ -> return ([], env, ["Case-MRV error not V"])
            RecursiveRecordAST rp mv xs ->
              case find (\(f', mv', t') -> f == f') xs of 
                Nothing -> return ([], env, ["Case-MRR"])
                Just (f', mv', t') ->
                  -- the leftover thing _should_ be a variant (for casing on)
                  case t' of
                    VariantAST mv1 xs1 ->
                      -- match the variant with the ConName and try.
                      case find (\(f'', mv'', t'') -> c == f'') xs1 of 
                        Nothing -> return ([], env, ["Case-MRRV"]) -- error; we should always be able to find a match in the variant list.
                        Just (f'', mv'', t'') -> do
                          -- try on e2 
                          let env1 = envAdd (Var v2) env 
                              xs1' = delete (f'', mv'', t'') xs1 
                          (res1, env2, err1) <- fillTemplates funName e2 t'' env1 (n+1)     
                          (res2, env3, err2) <- fillTemplates funName e3 (VariantAST mv xs1') env2 n
                          alpha <- fresh -- for the variant (e1)
                          beta <- fresh -- for the record (e4)
                          gamma <- fresh -- for the record element (Member e4 f)
                          return $ case res1 of 
                            [] ->
                              -- wrap res2 inside a record.
                              let (res3, env4, err3) = fillTemplateHelper res2 (RecursiveRecordAST rp (Just beta) [(f', (Just gamma), t')]) (envAddFresh [(beta, e4), (gamma, (Member e4 f))] env3) (err1 ++ err2) 0
                              in (res3, env4, err3 ++ ["Case-MRRV no res1"])
                            _ -> 
                              -- wrap in variant for res1
                              let (res3, env4, err3) = fillTemplateHelper res1 (VariantAST (Just alpha) [(f'', (Just alpha), t'')]) (envAddFresh [(alpha, e1)] env3) (err1 ++ err2) 0
                              -- wrap in record for all.
                              in fillTemplateHelper res3 (RecursiveRecordAST rp (Just beta) [(f', (Just gamma), t')]) (envAddFresh [(beta, e4), (gamma, (Member e4 f))] env4) err3 0
                    -- Error, we should always be seeing a variant template here.
                    _ -> return ([], env, ["Case-MRRV error no V"])
            -- Member is neither a R or RR, problem.
            _ -> return ([], env, ["CaseM isn't R or RR"])  
        -- case and esac only cover var and member expressions
        _ -> return ([], env, ["Case only covers Var and Member exps"])
    Esac e1 c v1 e2 -> 
      case e1 of 
        Var v -> 
          case tem of 
            VariantAST mv xs -> 
              -- check what v1 is inside the environment.
              case envExists (Var v) env of 
                False -> return ([], env, ["EsacVV does not exist"])
                True -> 
                  -- if OK, add v1 into the env, get results for e2 and e3.
                  -- find the matching ConName + template, try it. 
                  -- Try on the others and then combine.
                  -- Match on the ConName
                  case find (\(f', mv', t') -> c == f') xs of 
                    Nothing -> return ([], env, ["EsacVV"]) -- error; we should always be able to find a match in the variant list from the template.
                    Just (f', mv', t') -> do
                      -- try on e2
                      let env1 = envAdd (Var v1) env 
                      (res1, env2, err1) <- fillTemplates funName e2 t' env1 (n+1)
                      alpha <- fresh -- for the variant e1
                      return $ case res1 of 
                        [] -> ([], env2, err1 ++ ["EsacVV res1 empty"])
                        _ -> fillTemplateHelper res1 (VariantAST (Just alpha) [(f', (Just alpha), t')]) (envAddFresh [(alpha, e1)] env2) err1 0
            -- not a variant, problem.
            _ -> return ([], env, ["Case not a variant"])
        Member e4 f -> 
          case tem of
            -- unpack the record.
            RecordAST mv xs ->
              case find (\(f', mv', t') -> f == f') xs of 
                Nothing -> return ([], env, ["EsacMR"])
                Just (f', mv', t') ->
                  -- the leftover thing _should_ be a variant (for casing on) 
                  case t' of
                    VariantAST mv1 xs1 ->
                      -- match the variant with the ConName and try.
                      case find (\(f'', mv'', t'') -> c == f'') xs1 of 
                        Nothing -> return ([], env, ["Case-MV no match"]) -- error; we should always be able to find a match in the variant list.
                        Just (f'', mv'', t'') -> do
                          -- try on e2 
                          let env1 = envAdd (Var v1) env
                          (res1, env2, err1) <- fillTemplates funName e2 t'' env1 (n+1) 
                          alpha <- fresh -- for the variant e1
                          beta <- fresh -- for the record e4
                          gamma <- fresh -- for the record field (Member e4 f)
                          return $ case res1 of 
                            [] -> ([], env2, err1 ++ ["EsacMR"])
                            _ -> 
                              -- wrap in variant for res1
                              let (res2, env3, err2) = fillTemplateHelper res1 (VariantAST (Just alpha) [(f'', (Just alpha), t'')]) (envAddFresh [(alpha, e1)] env2) err1 0
                              -- wrap in record for all.
                              in fillTemplateHelper res2 (RecordAST (Just beta) [(f', (Just gamma), t')]) (envAddFresh [(beta, e4), (gamma, (Member e4 f))] env3) err2 0
                    -- Error, we should always be seeing a variant template here.
                    _ -> return ([], env, ["Case-M no variant"])
            RecursiveRecordAST rp mv xs ->
              case find (\(f', mv', t') -> f == f') xs of 
                Nothing -> return ([], env, ["EsacMRR"])
                Just (f', mv', t') -> 
                  -- the leftover thing _should_ be a variant (for casing on) 
                  case t' of
                    VariantAST mv1 xs1 ->
                      -- match the variant with the ConName and try.
                      case find (\(f'', mv'', t'') -> c == f'') xs1 of 
                        Nothing -> return ([], env, ["EsacMRRV"]) -- error; we should always be able to find a match in the variant list.
                        Just (f'', mv'', t'') -> do
                          -- try on e2 
                          let env1 = envAdd (Var v1) env 
                          (res1, env2, err1) <- fillTemplates funName e2 t'' env1 (n+1) 
                          alpha <- fresh -- for the variant e1
                          beta <- fresh -- for the record e4
                          gamma <- fresh -- for the record field (Member e4 f)
                          return $ case res1 of 
                            [] -> ([], env2, err1 ++ ["EsacMRRV"])
                            _ -> 
                              -- wrap in variant for res1
                              let (res2, env3, err2) = fillTemplateHelper res1 (VariantAST (Just alpha) [(f'', (Just alpha), t'')]) (envAddFresh [(alpha, e1)] env2) err1 0
                              in 
                              -- wrap in record for all.
                              fillTemplateHelper res2 (RecursiveRecordAST rp (Just beta) [(f', (Just gamma), t')]) (envAddFresh [(beta, e4), (gamma, (Member e4 f))] env3) err2 0
                    -- Error, we should always be seeing a variant template here.
                    _ -> return ([], env, ["EsacMRR Error"])
            -- Member is neither a R or RR, problem.
            _ -> return ([], env, ["EsacM is neither R nor RR"])  
        -- case and esac only cover var and member expressions
        _ -> return ([], env, ["EsacM only covers var and member exps"])
    _ -> return ([], env, ["Expr did not match"])

envExists :: Expr -> Env -> Bool
envExists exp env = 
  case find (\x -> x == exp) (exprEnv env) of 
    Just _ -> True
    Nothing -> False

envAdd :: Expr -> Env -> Env
envAdd exp env =   
  case envExists exp env of 
    True -> env 
    False -> let env1 = (env {exprEnv = exp:(exprEnv env)})
          in env1

envAddFresh :: [(FreshVar, Expr)] -> Env -> Env
envAddFresh [] env = env 
envAddFresh ((fvar, exp): xs) env = 
  let env' = envAddFresh xs env 
  in env' {freshEnv = M.insert fvar exp (freshEnv env')}

envAddAssertion :: FreshVar -> FreshVar -> Env -> Env 
envAddAssertion f1 f2 env = 
  let env' = addAssertion f1 f2 env 
  in addAssertion f2 f1 env'

addAssertion :: FreshVar -> FreshVar -> Env -> Env
addAssertion f1 f2 env = 
  case M.lookup f1 (assertionsEnv env) of 
    Nothing -> env {assertionsEnv = M.insert f1 [f2] (assertionsEnv env)}
    Just xs -> case find (\x -> x == f2) xs of 
      Just x -> env
      Nothing -> env {assertionsEnv = M.insert f1 (f2:xs) (assertionsEnv env)}

-- termCheck' :: GlobalEnvironments -> ([Error], [(FunName, [Assertion], String)])
-- termCheck' genvs = M.foldrWithKey go ([],[]) (defns genvs)
--   where
--     go :: FunName -> (VarName, Expr) -> ([Error], [(FunName, [Assertion], DotGraph)]) -> ([Error], [(FunName, [Assertion], DotGraph)])
--     go f (x,e) (errs, dumps) =  
--       case getType f genvs of 
--         Nothing -> ([], [])
--         Just ty ->
--           let 
--               measure = buildMeasure ty []
--               typeast = buildTemplate ty
--               recursiveCalls = getRecursiveCalls f e
--               -- size = applyMeasure (head $ tail measure) (Just e, 0)
--               (terminates, g, dotGraph) = fst $ runFresh unifVars (init f x e)
--               errs' = if terminates then
--                         (show measure ++ " ---- \n" 
--                         ++ show typeast ++ " ---- \n" 
--                         ++ show e ++ "-------\n" 
--                         ++ show recursiveCalls ++ "-------\n")
--                         :errs
--                       else
--                         (show measure ++ " ---- \n" ++ show e ++ "-------\n" ++ show recursiveCalls ++  "Error: Function " ++ f ++ " cannot be shown to terminate.") : errs
--             in
--               (errs', (f, g, dotGraph) : dumps)

--     -- Maps the function argument to a name, then runs the termination
--     -- assertion generator.
--     -- Returns:
--     --  ( true if the function terminates
--     --  , the list of assertions produced from the function
--     --  , the `dot' graph file for this particular termination graph
--     --  )
--     init :: FunName -> VarName -> Expr -> Fresh VarName (Bool, [Assertion], String)
--     init f x e = do
--       alpha <- fresh
--       let env = M.insert x alpha M.empty
--       (a,c) <- termAssertionGen env e

--       let graph = toGraph a
--       let goals = catMaybes c

--       -- If all goals are not nothing, and our path condition is met, then the function terminates
--       -- Otherwise, we cannot say anything about the function
--       let terminates = length goals == length c 
--                     && all (\goal -> hasPathTo alpha goal graph
--                                   && (not $ hasPathTo goal alpha graph)
--                            ) goals
--       return $ 
--         (
--           terminates,
--           a,
--           genGraphDotFile f graph [alpha] goals
--         )

-- termAssertionGen ::  Env -> Expr -> Fresh VarName ([Assertion], [Maybe FreshVar])
-- termAssertionGen env expr
--   = case expr of
--     PrimOp _ es ->
--       join $ map (termAssertionGen env) es
      
--     Sig e _ -> 
--       termAssertionGen env e

--     Apply f e -> do
--       a <- termAssertionGen env f
--       b <- termAssertionGen env e
--       return $ flatten [([], [getv env e]), a, b]
      
--     Struct fs ->
--       let es = map snd fs 
--       in join $ map (termAssertionGen env) es
      
--     If b e1 e2 ->
--       join $ map (termAssertionGen env) [b, e1, e2]
      
--     Let x e1 e2 -> do
--       -- First evaluate the variable binding expression
--       a <- termAssertionGen env e1

--       -- Map our bound program variable to a new name and evaluate the rest
--       alpha <- fresh
--       let env' = M.insert x alpha env 
--       res <- termAssertionGen env' e2

--       -- Generate assertion
--       let l = toAssertion env e1 (alpha :~:)
--       return $ flatten [(l,[]), res]
    
--     LetBang vs v e1 e2 ->
--       termAssertionGen env (Let v e1 e2)

--     Take r' f x e1 e2 -> do
--       alpha <- fresh 
--       beta  <- fresh
      
--       res <- termAssertionGen env e1

--       -- Update variable to fresh name bindings and generate assertions recursively
--       let env' = M.insert r' beta (M.insert x alpha env)
--       res' <- termAssertionGen env' e2

--       -- Generate assertions
--       let assertions = toAssertion env e1 (alpha :<:)
--                     ++ toAssertion env e1 (beta :~:)

--       return $ flatten [(assertions, []), res', res]

--     Put e1 f e2 -> do
--       alpha <- fresh
--       beta  <- fresh

--       res  <- termAssertionGen env e1
--       res' <- termAssertionGen env e2

--       let assertions = [alpha :<: beta] 
--                     ++ toAssertion env e1 (beta :~:)
--                     ++ toAssertion env e2 (alpha :~:)

--       return $ flatten [(assertions, []), res', res]

--     Member e f -> 
--       termAssertionGen env e

--     Case e1 _ x e2 y e3 -> do
--       alpha <- fresh
--       beta  <- fresh
--       gamma <- fresh

--       res <- termAssertionGen env e1

--       let env' = M.insert x alpha env
--       res' <- termAssertionGen env' e2

--       let env'' = M.insert y gamma env
--       res'' <- termAssertionGen env'' e3

--       let assertions = toAssertion env e1 (beta :~:)
--                     ++ [alpha :<: beta, gamma :~: beta]

--       return $ flatten [(assertions, []), res, res', res'']

--     Esac e1 _ x e2 -> do
--       alpha <- fresh
--       beta  <- fresh

--       res <- termAssertionGen env e1

--       let env' = M.insert x alpha env
--       res' <- termAssertionGen env' e2

--       let assertions = toAssertion env e1 (beta :~:)
--                     ++ [alpha :<: beta]

--       return $ flatten [(assertions, []), res, res']

--     -- All other cases, like literals and nonrecursive expressions
--     _ -> return ([],[])

--   where
    
--     toAssertion :: Env -> Expr -> (FreshVar -> Assertion) -> [Assertion]
--     toAssertion env e f = 
--       case getv env e of
--         Just x -> [f x]
--         Nothing -> []

--     -- Returns the variable name from an environment if it exists, otherwise nothing
--     getv :: Env -> Expr -> Maybe FreshVar 
--     getv env e =
--       case e of
--         Var v -> Just $ env M.! v
--         _ -> Nothing

--     join :: [Fresh VarName ([a], [b])] -> Fresh VarName ([a], [b])
--     join (e:es) = do
--       (a,b) <- e
--       (as,bs) <- join es
--       return (a ++ as, b ++ bs)
--     join [] = return ([],[])

--     flatten :: [([a], [b])] -> ([a], [b])
--     flatten (x:xs) = 
--       let rest = flatten xs
--       in (fst x ++ fst rest, snd x ++ snd rest)
--     flatten [] = ([],[])

-- toGraph :: [Assertion] -> Graph
-- toGraph []     = mempty
-- toGraph (x:xs) = 
--   case x of
--     (a :<: b) -> addEdge b a $ toGraph xs
--     (a :~: b) -> addEdge a b $ addEdge b a $ toGraph xs 
--   where
--     addEdge a b =
--       M.insertWith (++) a [b]


-- hasPathTo :: Node -> Node -> Graph -> Bool
-- hasPathTo src dst g
--   = hasPathTo' src dst g S.empty
--     where
--       hasPathTo' :: Node -> Node -> Graph -> S.Set Node -> Bool
--       hasPathTo' s d g seen =
--         case M.lookup s g of
--           Nothing  -> False
--           Just nbs ->
--             any (\n -> 
--                   n == dst ||
--                     (notElem n seen &&
--                       hasPathTo' n d g (S.insert n seen))
--                 ) nbs


-- -- To use:
-- --   run `dot -Tpdf graph.dot -o outfile.pdf`
-- -- where graph.dot is the output from this function.
-- genGraphDotFile :: String -> Graph -> [Node] -> [Node] -> String
-- genGraphDotFile name g args goals = 
--   "digraph " ++ name ++ 
--     " {\n"
--       ++ "\tforcelabels=true;\n" 
--       ++ highlight "blue" "argument" args
--       ++ highlight "red"  "goal"     goals
--       ++ intercalate "\n" (edges g) 
--       ++ "\n}"
--   where
--     pairs :: Graph -> [(Node,Node)]
--     pairs = concatMap (\(a, bs) -> map (\b -> (a,b)) bs) . M.assocs

--     edges :: Graph -> [String]
--     edges = map (\(a,b) -> "\t" ++ a ++ " -> " ++ b ++ ";") . pairs

--     highlight :: String -> String -> [Node] -> String
--     highlight color label nodes = "\t" ++ (concat . intersperse "\n" $
--                                   map (\n -> n ++ " [ color = " ++ color ++ ", xlabel = " ++ label ++ " ];\n") nodes)

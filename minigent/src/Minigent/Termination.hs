

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
  -- | VarAST 
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

removeExpr :: Bool -> String -> Expr -> Maybe Expr 
-- true(unfold) false(case), field, expression to search, result 
removeExpr b f exp = 
  case exp of 
    PrimOp op (x:xs) -> 
      case removeExpr b f x of
        Nothing -> case xs of
          [] -> Nothing
          (y:ys) -> removeExpr b f y
        Just r -> Just r
    Literal v -> Nothing 
    Var v -> Nothing 
    Con c e -> removeExpr b f e
    TypeApp f ts -> Nothing
    Sig e t -> removeExpr b f e
    -- double check this. 
    Apply e1 e2 -> case removeExpr b f e1 of 
      Nothing -> removeExpr b f e2
      Just r -> Just r
    Struct fs -> Nothing -- TODO
    -- Cont fixing up here
    If e1 e2 e3 -> case removeExpr b f e1 of 
      Nothing -> case removeExpr b f e2 of
        Nothing -> removeExpr b f e3
        Just r -> Just r 
      Just r -> Just r
    Let v e1 e2 -> case removeExpr b f e1 of 
      Nothing -> removeExpr b f e2
      Just r -> Just r
    LetBang vs v e1 e2 -> case removeExpr b f e1 of 
      Nothing -> removeExpr b f e2
      Just r -> Just r
    Take v1 f' v2 e1 e2 -> 
      case b of 
        True -> if f == f' then (Just e2) else removeExpr b f e2
        False -> removeExpr b f e2
    Put e1 f e2 -> case removeExpr b f e1 of 
      Nothing -> removeExpr b f e2
      Just r -> Just r
    -- Member has same problem as prev thing, need to access the outer scope.
    Member e' f' -> removeExpr b f e'
    Case e1 c v1 e2 v2 e3 -> 
      case b of 
        -- unfold: check member
        True -> case e1 of 
          -- check e2 and also check e3? Depends on the measure?
          Member e f' -> removeExpr b f e2
          _ -> removeExpr b f e3
        -- case
        False -> if c == f then (Just e2) else removeExpr b f e3
    Esac e1 c v e2 ->
      case b of 
        True -> removeExpr b f e2
        False -> if c == f then (Just e2) else removeExpr b f e2

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

-- Fill env and templates
type FreshEnv = M.Map FreshVar Expr
type ExprEnv = [(Expr, FreshVar)]

data Env = Env {
  freshEnv :: M.Map FreshVar Expr,
  exprEnv :: [Expr]
} deriving (Show)

emptyEnv = Env M.empty []

termCheck :: GlobalEnvironments -> ([Error], [(FunName, Bool)])
termCheck genvs = M.foldrWithKey go ([], []) (defns genvs)
  where 
    go :: FunName -> (VarName, Expr) -> ([Error], [(FunName, Bool)]) -> ([Error], [(FunName, Bool)])
    go f (x, e) (errs, dumps) = 
      case getType f genvs of 
        Nothing -> ([], [])
        Just ty ->
          let (funName, b) = fst $ runFresh unifVars (init' f x e ty)
              measure = buildMeasure ty []
              template = buildTemplate ty
              (templates, env, err) = fillTemplates funName e template (envAdd (Var "r") emptyEnv) 0
              recursiveCalls = getRecursiveCalls f e
              -- (b', t, mt) = split e template
              msg = ("\n\nExpression:\n"
                    ++ show e ++ "-------\n\nRecursive Calls:\n" 
                    ++ show recursiveCalls ++ "-------\n\nMeasures:\n"
                    ++ show measure ++ " ---- \n\nTemplate:\n" 
                    ++ show template ++ " ---- \n\nFilled Templates:\n" 
                    ++ show templates ++ "-------\n\nEnv:\n"
                    ++ show env ++ "-------\n\nErr:\n"
                    ++ show err)
                    -- ++ show (b', t, mt) ++ "-------\n\n")
              errs' = case b of 
                        True -> ((show "terminates") ++ msg) : errs
                        _ -> ((show "fails terminates") ++ msg) : errs
            in (errs', (funName, b):dumps)

    init' :: FunName -> VarName -> Expr -> Type -> Fresh VarName (FunName, Bool)
    init' f x e ty = do
      -- get measures + typeasts
      let measures = buildMeasure ty []
          -- template = buildTemplate ty
          -- templates = fill f e emptyEnv 0 template []
      -- SETUP
        -- Map each recursive argument to a template - link using a freshvar? Put these freshvars into the env. 
        -- Go through the func expression.
          -- Add stuff to the environment: freshvars + expr, expr + freshvars
          -- Add stuff to the templates.
      -- Take EACH template and compare to input template for local descent.
      -- Generate a matrix from local descent.
      -- Solve matrix with global descent. 
  
      -- initialise the env
      -- templateEnv <- initEnv typeast
      -- fill fs out the typeASTs and environment.
      -- env' <- setUp f x e typeast env
          -- matrix <- localDescent measures typeASTs env
          -- result <- globalDescent Matrix.fromList $ matrix
      -- get measures 
      -- get type ast
      return $ (f, True)
      -- return $ (f, result)
-- function name, expression, env, counter, COMPLETE template, PARTIAL template.

-- ASSUMPTIONS:
-- Case e1s: only contain Var v or Member e f expressions.
fillTemplates :: FunName -> Expr -> Template -> Env -> Int -> ([(Template, Expr)], Env, [Error])
fillTemplates funName exp tem env n = 
  case exp of 
    PrimOp op (e:es) -> case es of 
      [x] -> 
        let (res1, env1, err1) = fillTemplates funName e tem env n
            (res2, env2, err2) = fillTemplates funName x tem env n
        in (res1 ++ res2, env2, err1 ++ err2)
      _ -> fillTemplates funName e tem env n
    Literal _ -> ([], env, ["Empty Lit"])
    Var y -> 
      -- if it doesn't exist, add to env. Maybe unnecessary?
      let env1 = envAdd (Var y) env
      in ([], env1, [])-- do we need to add to env .. surely not? If we do, we do it already.. 
    Con c e -> ([], env, ["Empty Con"]) -- CHECK THIS LATER
    TypeApp f ts -> ([], env, ["Empty TypeApp"])
    Sig e t -> ([], env, ["Empty Sig"]) -- ???
    Apply e1 e2 -> case e1 of 
      TypeApp f ts -> 
        if f == funName then 
          let env1 = envAdd e2 env 
          in fillTemplates funName e2 tem env1 (n+1)         
        else ([], env, ["TypeApp Error"])
    Struct [(fieldname, e)] -> ([], env, ["Empty Struct"])
    If e1 e2 e3 -> ([], env, ["Empty If"])
    Let v e1 e2 -> ([], env, ["Empty Let"])
    LetBang vs v e1 e2 -> ([], env, ["Empty LetBang"])
    Take v1 f v2 e1 e2 -> 
      -- check that e1 is the correct record ?
      case tem of 
        RecordAST mv xs -> 
          case find (\(f', mv', t') -> f == f') xs of 
            Nothing -> ([], env, ["Take R"])
            Just (f', mv', t') -> 
              let (res1, env1, err1) = fillTemplates funName e2 t' env (n+1)
              in case res1 of 
                [] -> ([], env1, err1 ++ ["Take R"])
                _ -> (map (\(x, y) -> (RecordAST mv [(f', mv', x)], y)) res1, env1, err1)
        RecursiveRecordAST rp mv xs -> 
          case find (\(f', mv', t') -> f == f') xs of 
            Nothing -> ([], env, ["Take RR"])
            Just (f', mv', t') -> 
              let (res1, env1, err1) = fillTemplates funName e2 t' env (n+1)
              in case res1 of 
                [] -> ([], env1, ["Take RR"])
                _ -> (map (\(x, y) -> (RecursiveRecordAST rp mv [(f', mv', x)], y)) res1, env1, err1)
        _ -> ([], env, ["Take Error"]) -- Error, as we should only be seeing a record when taking ?
    Put e1 f e2 -> ([], env, ["Empty Put"])
    Member e f ->
      -- check that e exists inside the thing. 
      case envExists e env of 
        False -> ([], env, ["Member e does not exist"])
        True -> 
          case tem of 
          -- check for records. this doesn't continue bc no expression to work on.
            RecordAST mv xs -> 
              case find (\(f', mv', t') -> f == f') xs of 
                Nothing -> ([], env, ["Member R:" ++ f ++ " missing"])
                Just (f', mv', t') ->
                  case t' of 
                    PrimitiveAST mv1 -> ([], env, ["Member R Primitive"])
                    RecParAST rp mv1 -> ([(RecParAST rp mv1, e)], env, ["Member R RecPar"])
                    -- anything else?
                    _ -> ([], env, ["Member R Other"])
            RecursiveRecordAST rp mv xs -> 
              case find (\(f', mv', t') -> f == f') xs of 
                Nothing -> ([], env, ["Member RR"])
                Just (f', mv', t') ->
                  case t' of 
                    PrimitiveAST mv1 -> ([], env, ["Member RR"])
                    RecParAST rp mv1 -> ([(RecParAST rp mv1, e)], env, [])
                    -- anything else?
                    _ -> ([], env, ["Member RR"])
            _ -> ([], env, ["Member RR"])
    Case e1 c v1 e2 v2 e3 -> 
      case e1 of 
        Var v -> 
          case tem of 
            VariantAST mv xs -> 
              -- check what v is inside the environment.
              case envExists (Var v) env of 
                False -> ([], env, ["Case V does not exist"])
                True -> 
                  -- if OK, add v1 into the env, get results for e2 and e3.
                  -- find the matching ConName + template, try it. 
                  -- Try on the others and then combine.
                  -- Match on the ConName
                  case find (\(f', mv', t') -> c == f') xs of 
                    Nothing -> ([], env, ["Case V"]) -- error; we should always be able to find a match in the variant list from the template.
                    Just (f', mv', t') ->
                      -- try on e2
                      let env1 = envAdd (Var v2) env
                          (res1, env2, err1) = fillTemplates funName e2 t' env1 (n+1)
                          -- remove the match from the variant list
                          xs' = delete (f', mv', t') xs
                          -- try the variant stuff on e3
                          (res2, env3, err2) = fillTemplates funName e3 (VariantAST mv xs') env2 n
                      in 
                        case res1 of 
                          -- if the first one is empty, return the second
                          [] -> (res2, env3, err1 ++ err2)
                          -- else, add them together
                          _ -> 
                            let res3 = map (\(x, y) -> (VariantAST mv [(f', mv', t')], y)) res1
                            in (res2 ++ res3, env3, err1 ++ err2)
            -- not a variant, problem.
            _ -> ([], env, ["Case error: not V"])
        Member e4 f -> 
          case tem of
            -- unpack the record.
            RecordAST mv xs ->
              case find (\(f', mv', t') -> f == f') xs of 
                Nothing -> ([], env, ["Case-MR"])
                Just (f', mv', t') ->
                  -- the leftover thing _should_ be a variant (for casing on) 
                  case t' of
                    VariantAST mv1 xs1 ->
                      -- match the variant with the ConName and try.
                      case find (\(f'', mv'', t'') -> c == f'') xs1 of 
                        Nothing -> ([], env, ["Case-MRV error"]) -- error; we should always be able to find a match in the variant list.
                        Just (f'', mv'', t'') -> 
                          -- try on e2 
                          -- add v2 into the env
                          let env1 = envAdd (Var v2) env
                              (res1, env2, err1) = fillTemplates funName e2 t''   env1 (n+1) 
                              xs1' = delete (f'', mv'', t'') xs1 
                              (res2, env3, err2) = fillTemplates funName e3 (VariantAST mv xs1') env2 n
                          in
                            case res1 of
                              [] -> (res2, env3, err1 ++ err2)
                              _ ->
                                -- wrap in variant for res1
                                -- wrap in record for all.
                                let res3 = map (\(x, y) -> (VariantAST mv1 [(f', mv', t')], y)) res1 
                                    res4 = map (\(x, y) -> (RecordAST mv [(f', mv', x)], y)) (res2 ++ res3)
                                in (res4, env3, err1 ++ err2)
                    -- Error, we should always be seeing a variant template here.
                    _ -> ([], env, ["Case-MRV error not V"])
            RecursiveRecordAST rp mv xs ->
              case find (\(f', mv', t') -> f == f') xs of 
                Nothing -> ([], env, ["Case-MRR"])
                Just (f', mv', t') ->
                  -- the leftover thing _should_ be a variant (for casing on) 
                  case t' of
                    VariantAST mv1 xs1 ->
                      -- match the variant with the ConName and try.
                      case find (\(f'', mv'', t'') -> c == f'') xs1 of 
                        Nothing -> ([], env, ["Case-MRRV"]) -- error; we should always be able to find a match in the variant list.
                        Just (f'', mv'', t'') -> 
                          -- try on e2 
                          let env1 = envAdd (Var v2) env 
                              (res1, env2, err1) = fillTemplates funName e2 t'' env1 (n+1) 
                              xs1' = delete (f'', mv'', t'') xs1 
                              (res2, env3, err2) = fillTemplates funName e3 (VariantAST mv xs1') env2 n
                          in 
                            case res1 of 
                              [] ->
                                -- wrap res2 inside a record.
                                let res3 = map (\(x, y) -> (RecursiveRecordAST rp mv [(f', mv', x)], y)) res2 
                                in (res3, env3, err1 ++ err2 ++ ["Case-MRRV no res1"])
                              _ -> 
                                -- wrap in variant for res1
                                -- wrap in record for all.
                                let res3 = map (\(x, y) -> (VariantAST mv1 [(f', mv', t')], y)) res1 
                                    res4 = map (\(x, y) -> (RecursiveRecordAST rp mv [(f', mv', x)], y)) (res2 ++ res3)
                                in (res4, env3, err1 ++ err2)
                    -- Error, we should always be seeing a variant template here.
                    _ -> ([], env, ["Case-MRRV error no V"])
            -- Member is neither a R or RR, problem.
            _ -> ([], env, ["CaseM isn't R or RR"])  
        -- case and esac only cover var and member expressions
        _ -> ([], env, ["Case only covers Var and Member exps"])
    Esac e1 c v1 e2 -> 
      case e1 of 
        Var v -> 
          case tem of 
            VariantAST mv xs -> 
              -- check what v1 is inside the environment.
              case envExists (Var v) env of 
                False -> ([], env, ["EsacVV does not exist"])
                True -> 
                  -- if OK, add v1 into the env, get results for e2 and e3.
                  -- find the matching ConName + template, try it. 
                  -- Try on the others and then combine.
                  -- Match on the ConName
                  case find (\(f', mv', t') -> c == f') xs of 
                    Nothing -> ([], env, ["EsacVV"]) -- error; we should always be able to find a match in the variant list from the template.
                    Just (f', mv', t') ->
                      -- try on e2
                      let env1 = envAdd (Var v1) env 
                          (res1, env2, err1) = fillTemplates funName e2 t' env1 (n+1)
                      in 
                        case res1 of 
                          -- if the first one is empty, return the second
                          [] -> ([], env2, err1 ++ ["EsacVV res1 empty"])
                          -- else, add them together
                          _ -> (map (\(x, y) -> (VariantAST mv [(f', mv', t')], y)) res1, env2, err1)
            -- not a variant, problem.
            _ -> ([], env, ["Case not a variant"])
        Member e4 f -> 
          case tem of
            -- unpack the record.
            RecordAST mv xs ->
              case find (\(f', mv', t') -> f == f') xs of 
                Nothing -> ([], env, ["EsacMR"])
                Just (f', mv', t') ->
                  -- the leftover thing _should_ be a variant (for casing on) 
                  case t' of
                    VariantAST mv1 xs1 ->
                      -- match the variant with the ConName and try.
                      case find (\(f'', mv'', t'') -> c == f'') xs1 of 
                        Nothing -> ([], env, ["Case-MV no match"]) -- error; we should always be able to find a match in the variant list.
                        Just (f'', mv'', t'') -> 
                          -- try on e2 
                          let env1 = envAdd (Var v1) env
                              (res1, env2, err1) = fillTemplates funName e2 t'' env1 (n+1) 
                          in 
                            case res1 of 
                              [] -> ([], env2, err1 ++ ["EsacMR"])
                              _ -> 
                                -- wrap in variant for res1
                                -- wrap in record for all.
                                let res2 = map (\(x, y) -> (VariantAST mv1 [(f', mv', t')], y)) res1 
                                    res3 = map (\(x, y) -> (RecordAST mv [(f', mv', x)], y)) res2
                                in (res3, env2, err1)
                    -- Error, we should always be seeing a variant template here.
                    _ -> ([], env, ["Case-M no variant"])
            RecursiveRecordAST rp mv xs ->
              case find (\(f', mv', t') -> f == f') xs of 
                Nothing -> ([], env, ["EsacMRR"])
                Just (f', mv', t') ->
                  -- the leftover thing _should_ be a variant (for casing on) 
                  case t' of
                    VariantAST mv1 xs1 ->
                      -- match the variant with the ConName and try.
                      case find (\(f'', mv'', t'') -> c == f'') xs1 of 
                        Nothing -> ([], env, ["EsacMRRV"]) -- error; we should always be able to find a match in the variant list.
                        Just (f'', mv'', t'') -> 
                          -- try on e2 
                          let env1 = envAdd (Var v1) env 
                              (res1, env2, err1) = fillTemplates funName e2 t'' env1 (n+1) 
                          in 
                            case res1 of 
                              [] -> ([], env2, err1 ++ ["EsacMRRV"])
                              _ -> 
                                -- wrap in variant for res1
                                -- wrap in record for all.
                                let res2 = map (\(x, y) -> (VariantAST mv1 [(f', mv', t')], y)) res1 
                                    res3 = map (\(x, y) -> (RecursiveRecordAST rp mv [(f', mv', x)], y)) res2
                                in (res3, env2, err1)
                    -- Error, we should always be seeing a variant template here.
                    _ -> ([], env, ["EsacMRR Error"])
            -- Member is neither a R or RR, problem.
            _ -> ([], env, ["EsacM is neither R nor RR"])  
        -- case and esac only cover var and member expressions
        _ -> ([], env, ["EsacM only covers var and member exps"])
    -- _ -> ([], env)

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

-- Helper functions:
-- Expression exists inside environment
-- Add expression to environment

-- fill :: FunName -> Expr -> Env -> Int -> Template -> Template -> [(Template, Template)]
-- fill f exp env n ft pt = case exp of
--     -- TODO
--     PrimOp op (x:xs) ->
--       let res' = fill f x env (n+1) ft pt
--       in 
--         case xs of 
--           [y] -> res' ++ (fill f y env (n+1) ft pt)
--           _ -> res'
--     Literal v -> []
--     Var v -> []
--     Con c e -> fill f e env (n+1) ft pt 
--     TypeApp f ts -> []
--     Sig e t' -> fill f e env n ft pt
--     Apply e1 e2 -> 
--       -- If you see a recursive call, add to the results list.
--       case e1 of 
--         TypeApp funName ts -> 
--           if funName == f then
--             -- check up on e2 as a type?? Maybe - TO DO.
--             -- fill in the templates with stuff as well. Resolve e2 
--             [(pt, ft)] -- Add in the var names tho.
--           else []
--         _ -> []

--     Struct fs -> [] -- TODO
--     If e1 e2 e3 -> 
--       let res1 = fill f e1 env (n+1) ft pt 
--           res2 = fill f e2 env (n+1) ft pt
--           res3 = fill f e3 env (n+1) ft pt 
--       in res1 ++ res2 ++ res3
--     Let v e1 e2 -> 
--       let res1 = fill f e1 env (n+1) ft pt 
--           res2 = fill f e2 env (n+1) ft pt
--       in res1 ++ res2
--     LetBang vs v e1 e2 ->
--       let res1 = fill f e1 env (n+1) ft pt 
--           res2 = fill f e2 env (n+1) ft pt
--       in res1 ++ res2
--     Take v1 f' v2 e1 e2 -> 
--       let res1 = fill f e1 env (n+1) ft pt 
--           res2 = fill f e2 env (n+1) ft pt
--       in res1 ++ res2
--     Put e1 f e2 -> fill f e1 env (n+1) ft pt
--     Member e' f' -> fill f e' env (n+1) ft pt
--     Case e1 c v1 e2 v2 e3 -> case split e1 pt of 
--       (False, _, _) -> [] -- means it is irrelevant to our thing?? 
--       (True, x, Nothing) -> [] -- umm, templates should not have ended??
--       (True, x, Just y) -> -- eg Member, Var, etc.
--         -- Try both branches.
--         let res2 = fill f e2 env (n+1) ft y
--             res3 = fill f e3 env (n+1) ft y
--         -- TODO: STICK THEM BACK TOGETHER.
--         in res2 ++ res3
--       -- Split up the partial template.
--     Esac e1 c v e2 -> case split e1 pt of 
--       (False, _, _) -> []
--       (True, x, Nothing) -> []
--       -- TODO: STITCH BACK TGT.
--       (True, x, Just y) -> fill f e2 env (n+1) ft pt
--     _ -> []

-- split :: Expr -> Template -> (Bool, Template, Maybe Template)
-- split exp t = case exp of 
--   PrimOp o (x:xs) -> 
--     let (b, t, mt) = split x t 
--     in
--       case b of 
--         True -> (b, t, mt)
--         False -> case xs of 
--           [y] -> split y t
--           _ -> (b, t, mt) 
--   Literal v ->
--     case t of 
--       PrimitiveAST x -> (True, (PrimitiveAST x), Nothing)
--       _ -> (False, t, Nothing)
--   Var v ->
--     case t of 
--       RecordAST mv fs -> case find (\(f', v', t') -> v == f') fs of 
--         Just (f', v', t') -> (True, RecordAST mv [], Just t')
--         Nothing -> (False, t, Nothing)
--       RecursiveRecordAST r mv fs -> case find (\(f', v', t') -> v == f') fs of 
--         Just (f', v', t') -> (True, RecursiveRecordAST r mv [], Just t')
--         Nothing -> (False, t, Nothing)
--       VariantAST mv fs -> case find (\(f', v', t') -> v == f') fs of 
--         Just (f', v', t') -> (True, VariantAST mv [], Just t')
--         Nothing -> (False, t, Nothing)
--       _ -> (False, t, Nothing)
--   Con c e -> split e t 
--   TypeApp f ts -> (False, t, Nothing)
--   Sig e t' -> split e t
--   Apply e1 e2 -> case split e1 t of 
--     (True, x, y) -> (True, x, y)
--     _ -> split e2 t
--   -- TODO
--   Struct fs -> (False, t, Nothing)
--   If e1 e2 e3 -> case split e1 t of 
--     (True, x, y) -> (True, x, y)
--     _ -> case split e2 t of 
--       (True, x, y) -> (True, x, y)
--       _ -> split e3 t
--   Let v e1 e2 -> case split e1 t of 
--     (True, x, y) -> (True, x, y)
--     _ -> split e2 t 
--   LetBang vs v e1 e2 -> case split e1 t of 
--     (True, x, y) -> (True, x, y)
--     _ -> split e2 t 
--   Take v1 f v2 e1 e2 -> case t of 
--     RecordAST v fs -> case find (\(f', v', t) -> f == f') fs of 
--       Just (f, v', t) -> (True, RecordAST v [], Just t)
--       Nothing -> (False, t, Nothing)
--     RecursiveRecordAST r v fs -> case find (\(f', v', t) -> f == f') fs of 
--       Just (f, v', t) -> (True, RecursiveRecordAST r v [], Just t)
--       Nothing -> (False, t, Nothing)
--     _ -> split e2 t
--   Put e1 f e2 -> case t of
--     RecordAST v fs -> case find (\(f', v', t') -> f == f') fs of 
--       Just (f', v', t') -> (True, RecordAST v [], Just t')
--       Nothing -> (False, t, Nothing)
--     RecursiveRecordAST r v fs -> case find (\(f', v', t') -> f == f') fs of 
--       Just (f', v', t') -> (True, RecursiveRecordAST r v [], Just t')
--       Nothing -> (False, t, Nothing)
--     _ -> split e2 t
--   -- DO WE NEED TO CHECK THE TEMPLATES ATTACHED TO FIELDNAMES FOR THESE?
--   Member e f -> case t of 
--     RecordAST v fs -> case find (\(f', v', t') -> f == f') fs of 
--       Just (f', v', t') -> (True, RecordAST v [], Just t')
--       Nothing -> (False, t, Nothing)
--     RecursiveRecordAST r v fs -> case find (\(f', v', t') -> f == f') fs of 
--       Just (f', v', t') -> (True, RecursiveRecordAST r v [], Just t')
--       Nothing -> (False, t, Nothing)
--     _ -> (False, t, Nothing)
--   Case e1 c v1 e2 v2 e3 -> case split e1 t of 
--     (True, x, y) -> (True, x, y)
--     _ -> case split e2 t of
--       (True, x, y) -> (True, x, y)
--       _ -> split e3 t
--   Esac e1 c v e2 -> case split e1 t of 
--     (True, x, y) -> (True, x, y)
--     _ -> split e2 t 


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

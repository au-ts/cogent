

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

import Control.Arrow (first, second)
import Control.Monad.List
import Control.Monad.State.Strict

import Data.Maybe (maybeToList, catMaybes, fromMaybe)

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

placeHolder = Just "ok"

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
          let (funName, b, matrix, argPairs, templatePairs, sizes, message) = (init' f x e ty)
              measures = buildMeasure ty []
              msg = ("\n\nMatrix\n" ++ (show matrix) 
                  ++ "\n\nMeasures\n" ++ (show measures)
                  ++ "\n\nArgPairs\n" ++ (show argPairs)
                  ++ "\n\nTemplate Pairs\n" ++ (show templatePairs)
                  ++ "\n\nSizes\n" ++ (show sizes)
                  ++ "\n\nMsg\n" ++ message
                  )
              errs' = case b of 
                True -> ((show "Passes termination") ++ msg):errs
                False -> ((show "Fails termination") ++ msg):errs
            in (errs', (funName, b):[])

    init' :: FunName ->
             VarName ->
                Expr ->
                Type ->
             (FunName, Bool, Matrix.Matrix Cmp, [(ArgExpr, ArgExpr)], [(Template, Template)], [[(Siz, Siz)]], String)
    init' funName x e ty =
      let 
        -- generate list of measures
        measures = buildMeasure ty []
        -- generate template
        template = buildTemplate ty
  -- MAIN --
        -- generate argument pairs
        argPairs = genArgPairs funName x M.empty e
        -- list of (inputTemplate, recursiveTemplate, env) tuples
        templateEnvs = map (mapConstructors template) argPairs
        templatePairs = map completeTemplate templateEnvs
        lists = map (genLists measures) templatePairs
        matrix = Matrix.fromLists lists
        result = globalDescent matrix
        message = show (genSizes measures (head templatePairs))
      in (funName, result, matrix, argPairs, templatePairs, [], message)

        ------------
        -- (templateExpr, env, err) = fst $ runFresh unifVars $ fillTemplates funName e template (envAdd (Var "r") emptyEnv) 0
        -- -- convert the expressions into templates
        -- templateExprChar = zip templateExpr ['a'..'z'] -- lol, fix later
        -- (templateTemplate, env1) = fillTemplateExp template templateExprChar env
        -- -- generate assertions
        -- env2 = assertions templateTemplate env1
        -- env3 = resolveEnv env2
        -- -- apply measures 
        -- -- matrix = Matrix.fromLists [[]]
        -- -- generate local descent arrays
        -- -- generate matrix
        -- sizes = generateSize env3 (templateTemplate !! 0) measures
        -- -- row1 = generateRow env3 (templateTemplate !! 0) measures
        -- cmps = generateMatrix env3 templateTemplate measures
        -- matrix = Matrix.fromLists $ cmps
        -- -- matrix = Matrix.fromLists $ generateMatrix env2 templateTemplate measures
        -- -- run global descent
        -- result = globalDescent matrix
        -- result = True

type Info = M.Map FreshVar ArgExpr

type Siz = Maybe (Either Template FreshVar, MeasureOp, Int)
-- Nothing for mismatch, otherwise thing. 

genSizes :: [MeasureOp] -> (Template, Template) -> [(Siz, Siz)]
genSizes [] _ = []
genSizes ms (input, recursive) = 
  map (\m -> ((applyMeasures m input 0), (applyMeasures m recursive 0))) ms

genLists :: [MeasureOp] -> (Template, Template) -> [Cmp]
genLists [] _ = []
genLists ms (input, recursive) = 
  map (\m -> (compareSizes (applyMeasures m input 0) (applyMeasures m recursive 0))) ms

compareSizes :: Siz -> Siz -> Cmp
compareSizes Nothing _ = Unknown
compareSizes _ Nothing = Unknown 
compareSizes (Just (Right v0, m0, i0)) (Just (Right v1, m1, i1)) = 
  if (v0 == v1) then 
    if (i0 > i1) then Le
    else if (i0 == i1) then Eq 
    else Unknown
  else
    Unknown
compareSizes x y = Unknown

-- consider leaving the mOp in? need to or nah?
applyMeasures :: MeasureOp -> Template -> Int -> Siz
applyMeasures m0@(ProjectOp f0 m) t0@(RecordAST mv0 ts) i =
  case find (\(f, mv, t) -> f0 == f) ts of 
    Just (f, mv, t) -> case mv of 
      Just "ok" -> applyMeasures m t i
      Just v ->
        case t of
          RecParAST rp' mv' -> Just (Right v, m0, i+1)
          _ -> Just (Right v, m0, i)
      Nothing -> case mv0 of 
        Just v -> Just (Right v, m0, i)
        Nothing -> Just (Left t0, m0, i)
    -- template doesnt exist: this shouldn't happen
    Nothing -> Nothing
-- check that rps are the same?
applyMeasures m0@(UnfoldOp rp0 f0 m) t0@(RecursiveRecordAST rp mv0 ts) i = 
  case find (\(f, mv, t) -> f0 == f) ts of 
    Just (f, mv, t) -> case mv of 
      Just "ok" -> applyMeasures m t i
      Just v -> 
        case t of
          -- match rps again...?
          RecParAST rp' mv' -> Just (Right v, m0, i+1)
          _ -> Just (Right v, m0, i)
      Nothing -> case mv0 of 
        Just v -> Just (Right v, m0, i)
        Nothing -> Just (Left t0, m0, i) -- no need to keep traversing
    Nothing -> Nothing
-- NOTE: will be confused when there are multiple elements in the VariantAST
applyMeasures m0@(CaseOp cs) t0@(VariantAST mv [(f0, mv0, t)]) i = 
  case find (\(f, m) -> f0 == f) cs of 
    Just (f, m) -> case mv of 
      Just "ok" -> applyMeasures m t i
      Just v -> 
        case t of 
          RecParAST rp' mv' -> Just (Right v, m0, i+1)
          _ -> Just (Right v, m0, i)
      Nothing -> Just (Left t0, m0, i)
    Nothing -> Nothing
applyMeasures m0 t0 i = Just (Left t0, m0, i)

mapConstructors :: Template -> (ArgExpr, ArgExpr) -> (Template, Template, Info)
mapConstructors tem (AEVar v, recursive) = 
  let (recursiveTemplate, recursiveEnv) = removeConstructors recursive tem 1
      alpha = ('a':show 0)
      -- v is the input argument name
      inputTemplate = fillFreshName tem v
      inputEnv = M.insert alpha (AEVar v) M.empty
  in (inputTemplate, recursiveTemplate, M.union inputEnv recursiveEnv)
-- should not happen
mapConstructors tem (ae1, ae2) = (tem, tem, M.empty)

reverseMapLookup :: [(FreshVar, ArgExpr)] -> ArgExpr -> Maybe FreshVar
reverseMapLookup [] _ = Nothing
reverseMapLookup ((f, ae0):xs) ae = if (ae0 == ae) then Just f
                                  else reverseMapLookup xs ae

-- NOTE some elements in the map will be the same, mapped to different 'freshvars'
-- remove constructors from the argExpr, use them to fill in the template initially.
removeConstructors :: ArgExpr -> Template -> Int -> (Template, Info)
removeConstructors (AEStruct ae) (RecordAST mv ts) n =
  -- map each struct element to a freshvar
  let fresh = zip (map (\x -> x:(show n)) ['a'..'z']) ae
    -- match the field names and recurse
      (ts', info) = removeConstructorsList ts fresh 0
    -- wrap the Record up again.
  in case mv of
    Nothing -> (RecordAST placeHolder ts', info)
    fv -> (RecordAST fv ts', info)
-- no constructors
removeConstructors ae tem n = 
  let alpha = ('a':show n)
      tem' = fillFreshName tem alpha 
  in (tem', M.insert alpha ae M.empty)

-- for each element in the struct, fix it up and continue 
removeConstructorsList :: [(FieldName, Maybe FreshVar, Template)] -> [([Char],(FieldName, ArgExpr))] -> Int -> ([(FieldName, Maybe FreshVar, Template)], Info)
-- find the argExpr that fits, and 
removeConstructorsList [] _ i = ([], M.empty)
removeConstructorsList _ [] i = ([], M.empty)
removeConstructorsList ((f0, mv, t):fs) ae0 i =
  let (res, resInfo) = removeConstructorsList fs ae0 i
  in
    case find (\(c, (f, ae)) -> f == f0) ae0 of
      Just (c, (f, ae)) ->
        -- check if ae is already inside the map: if yes, then use the map value
        case reverseMapLookup (M.toList resInfo) ae of 
          Just fv -> 
            let (template, info) = removeConstructors ae t (i+1)
                info' = M.union info resInfo
            in ((f, Just fv, template):res, info')
          Nothing -> 
            let (template, info) = removeConstructors ae t (i+1)
                info' = M.insert c ae (M.union info resInfo)
            -- add to env, set template.
            in ((f, Just c, template):res, info')
      Nothing -> ((f0, mv, t):res, resInfo)

fillFreshName :: Template -> FreshVar -> Template
fillFreshName tem alpha =
  case tem of 
    RecordAST mv xs -> RecordAST (Just alpha) xs
    RecursiveRecordAST rp mv xs -> RecursiveRecordAST rp (Just alpha) xs
    VariantAST mv xs -> VariantAST (Just alpha) xs
    PrimitiveAST mv -> PrimitiveAST (Just alpha)
    RecParAST rp mv -> RecParAST rp (Just alpha)

reverseAE :: FreshVar -> ArgExpr -> TemplateExpr
reverseAE a (AEVar v) = TEVar v (TELeaf (Just a))
reverseAE a (AEFieldProj f ae) = attachTE (reverseAE a ae) (TERecord f (TELeaf (Just a)))
reverseAE a (AEVariantProj f ae) = attachTE (reverseAE a ae) (TEVariant f (TELeaf (Just a)))
reverseAE a (AELit p) = TEPrim p
reverseAE a _ = TEUnknown

-- attach a template exp to the (very) end of another template exp
attachTE :: TemplateExpr -> TemplateExpr -> TemplateExpr 
attachTE (TERecord f t) child = case t of 
  TELeaf a -> TERecord f child
  _ -> TERecord f (attachTE t child)
attachTE (TEVariant f t) child = case t of 
  TELeaf a -> TEVariant f child
  _ -> TERecord f (attachTE t child)
attachTE (TEVar v t) child = case t of 
  TELeaf a -> TEVar v child
  _ -> TEVar v (attachTE t child)
attachTE t _ = t -- the others dont have children

completeTemplate :: (Template, Template, Info) -> (Template, Template)
completeTemplate (inputT, recursiveT, env) =
  -- reverse each element inside the env. use it to 'fill' the template multiple times through on each path. 
  let templateExprs = map (\(x, y) -> (reverseAE x y)) (M.toList env)
      input = completeTemplateList inputT templateExprs 
      recursive = completeTemplateList recursiveT templateExprs 
  in (input, recursive)
  -- for each template exp, 'fill' the template.
  -- check if the current thing is the same.

completeTemplateList :: Template -> [TemplateExpr] -> Template
completeTemplateList tem [] = tem
completeTemplateList tem (t:ts) = completeTemplateList (matchTemplate t tem) ts

matchTemplate :: TemplateExpr -> Template -> Template
matchTemplate te@(TEVar v ae) tem@(RecordAST mv ts) =
  case mv of
    -- pass onto the next function, which will fill in the template.
    Just x -> if x == v then (fill ae tem)
              else RecordAST mv ts -- (map (fill ae) ts)
    -- try to match on each element of xs? 
    Nothing -> RecordAST mv ts -- (map (fill ae) ts)
-- TODO: other cases.
matchTemplate te@(TEVar v ae) tem@(RecursiveRecordAST rp mv ts) =
  case mv of 
    Just x -> if x == v then (fill ae tem)
              else RecursiveRecordAST rp mv ts -- (map (fill ae) ts)
    -- try to match on each element of xs? 
    Nothing -> RecursiveRecordAST rp mv ts -- (map (fill ae) ts)
matchTemplate te tem = tem

fill :: TemplateExpr -> Template -> Template
fill (TERecord f ae) (RecordAST mv ts) = 
  case find (\(f', mv', t') -> f' == f) ts of 
    Just (f', mv', t') -> case mv of
      Nothing -> RecordAST placeHolder (findAndReplace f ts ae)
      _ -> RecordAST mv (findAndReplace f ts ae)
    Nothing -> (RecordAST mv ts)
fill (TERecord f ae) (RecursiveRecordAST rp mv ts) = 
  case find (\(f', mv', t') -> f' == f) ts of 
    Just (f', mv', t') -> case mv of 
      Nothing -> RecursiveRecordAST rp placeHolder (findAndReplace f ts ae)
      _ -> RecursiveRecordAST rp placeHolder (findAndReplace f ts ae)
    Nothing -> (RecursiveRecordAST rp mv ts)
fill (TEVariant f ae) (VariantAST mv ts) = 
  case find (\(f', mv', t') -> f' == f) ts of
    Just (f', mv', t') -> 
      case ae of 
        TELeaf fv -> case mv' of 
          Nothing -> VariantAST placeHolder [(f', fv, (fill ae t'))]
          _ -> VariantAST mv [(f', fv, (fill ae t'))]
        _ -> VariantAST placeHolder [(f', placeHolder, (fill ae t'))]
    Nothing -> (VariantAST mv ts)
-- TODO: other cases?
fill ae template = template

findAndReplace :: FieldName -> [((FieldName, Maybe FreshVar, Template))] -> TemplateExpr -> [(FieldName, Maybe FreshVar, Template)]
findAndReplace f0 ((f, mv, t):fs) ae = 
  if f0 == f then 
    -- fill in and continue. 
    case ae of 
      TELeaf fv -> (f, fv, fill ae t):fs
      _ -> (f, placeHolder, fill ae t):fs
  else (f, mv, t):(findAndReplace f0 fs ae)

data TemplateExpr 
  = TERecord FieldName TemplateExpr -- for both recursive and non-recursive
  | TEVariant FieldName TemplateExpr
  | TEPrim PrimValue
  | TEVar VarName TemplateExpr -- includes recpars...
  | TELeaf (Maybe VarName) -- leaf node. either empty, or contains recursive link
  -- | TFresh VarName -- recursive link (kinda)
  | TEUnknown
  deriving (Show, Eq)

{-
 - The intent of this data structure is to represent a canonical expression
 - which is the argument of a function call.
 - The structure contains a variant projection operation, which projects the
 - variant name from the variant; the application of this variant projection
 - means that the expression _is actually in_ that state.
 -}

data ArgExpr
  = AEVar VarName
  | AEStruct [(FieldName, ArgExpr)]
  | AEFieldProj FieldName ArgExpr
  | AEVariant FieldName ArgExpr
  | AEVariantProj FieldName ArgExpr
  | AELit PrimValue
  | AEUnit
  | AEUnknown
  deriving (Show, Eq)

-- e[u/z]
argExprSubst :: M.Map VarName ArgExpr -> ArgExpr -> ArgExpr
argExprSubst ctxt e@(AEVar x)         = (case M.lookup x ctxt of Just u -> u; Nothing -> e)
argExprSubst ctxt (AEStruct fs)       = AEStruct $ map (second (argExprSubst ctxt)) fs
argExprSubst ctxt (AEFieldProj f e)   = AEFieldProj f (argExprSubst ctxt e)
argExprSubst ctxt (AEVariant v e)     = AEVariant v (argExprSubst ctxt e)
argExprSubst ctxt (AEVariantProj v e) = AEVariantProj v (argExprSubst ctxt e)
argExprSubst ctxt e@AELit{}           = e
argExprSubst ctxt e@AEUnit            = e
argExprSubst ctxt e@AEUnknown         = e

-- secretly a very simple evaluator/rewriter
exprToArgExpr :: Expr -> ArgExpr
exprToArgExpr (PrimOp op es)         = AEUnknown
exprToArgExpr (Literal l)            = AELit l
exprToArgExpr (Var x)                = AEVar x
exprToArgExpr (Con cn e)             = AEVariant cn $ exprToArgExpr e
exprToArgExpr (Apply e0 e1)          = AEUnknown
exprToArgExpr (TypeApp fnName _)     = AEUnknown
exprToArgExpr (Sig e t)              = exprToArgExpr e
exprToArgExpr (Struct fs)            = AEStruct $ map (second exprToArgExpr) fs
exprToArgExpr (If ec ett eff)
  | AELit (BoolV b) <- exprToArgExpr ec =
    if b then exprToArgExpr ett else exprToArgExpr eff
  | otherwise = AEUnknown
exprToArgExpr (Let x e0 e1) =
  argExprSubst (M.insert x (exprToArgExpr e0) M.empty) $ exprToArgExpr e1
exprToArgExpr (LetBang ys x e0 e1) =
  argExprSubst (M.insert x (exprToArgExpr e0) M.empty) $ exprToArgExpr e1
exprToArgExpr (Take x f y e0 e1) =
  argExprSubst (M.insert x AEUnknown -- TODO
               $ M.insert y (exprToArgExpr e0)
               $ M.empty)
               (exprToArgExpr e1)
exprToArgExpr (Put e0 f e1)
  | (AEStruct fs) <- exprToArgExpr e0 =
    let aeField = exprToArgExpr e1
     in AEStruct (updateField f aeField fs)
  | otherwise = AEUnknown
exprToArgExpr (Member e f)           = AEFieldProj f $ exprToArgExpr e
exprToArgExpr (Case e0 cn x e1 y e2) = AEUnknown -- TODO
exprToArgExpr (Esac e0 cn x e1)      = AEUnknown -- TODO

genArgPairs :: FunName -> VarName -> M.Map VarName ArgExpr -> Expr -> [(ArgExpr, ArgExpr)]
genArgPairs n r env (PrimOp op es)    = concatMap (genArgPairs n r env) es
genArgPairs n r _ (Literal l)         = []
genArgPairs n r _ (Var x)             = []
genArgPairs n r env (Con cn e)        = genArgPairs n r env e
genArgPairs n r _ (TypeApp fnName _)  = []
genArgPairs n r env (Apply (TypeApp fnName ts) arg) | (fnName == n) =
  let mainArg = fromMaybe (AEVar r) (M.lookup r env)
      recArg = argExprSubst env $ exprToArgExpr arg
   in [(mainArg, recArg)]
genArgPairs n r env (Apply e0 e1)    =    genArgPairs n r env e0
                                     ++ genArgPairs n r env e1
genArgPairs n r env (Sig e t)        = genArgPairs n r env e
genArgPairs n r env (Struct fs)      = concatMap (genArgPairs n r env . snd) fs
genArgPairs n r env (If ec ett eff)  =    genArgPairs n r env ec
                                     ++ genArgPairs n r env ett
                                     ++ genArgPairs n r env eff
genArgPairs n r env (Let x e0 e1) =
  genArgPairs n r env e0 ++
    (let ae = argExprSubst env $ exprToArgExpr e0
         env' = M.insert x ae env
      in genArgPairs n r env' e1)
genArgPairs n r env (LetBang ys x e0 e1) =
  genArgPairs n r env e0 ++
    (let ae = argExprSubst env $ exprToArgExpr e0
         env' = M.insert x ae env
      in genArgPairs n r env e1)
genArgPairs n r env (Take x f y e0 e1) =
  genArgPairs n r env e0 ++
    (let aeRecord = argExprSubst env $ exprToArgExpr e0
         aeField = AEFieldProj f aeRecord
         env' = M.insert x aeRecord $ M.insert y aeField $ env
      in genArgPairs n r env' e1)
genArgPairs n r env (Put e0 f e1) = genArgPairs n r env e0 ++ genArgPairs n r env e1
genArgPairs n r env (Member e f) = genArgPairs n r env e
genArgPairs n r env (Case e0 cn x e1 y e2) =
  let aeVariant = argExprSubst env $ exprToArgExpr e0
   in    genArgPairs n r env e0
      ++ (let aeVarCase = AEVariantProj cn aeVariant
              env' = M.insert x aeVarCase env
          in genArgPairs n r env' e1)
      ++ (let env' = M.insert y aeVariant env
          in genArgPairs n r env' e2)
genArgPairs n r env (Esac e0 cn x e1) =
  genArgPairs n r env e0 ++
    (let aeVariant = argExprSubst env $ exprToArgExpr e0
         aeVarCase = AEVariantProj cn aeVariant
         env' = M.insert x aeVarCase env
      in genArgPairs n r env' e1)

reduceArgExprHead :: ArgExpr -> Maybe ArgExpr
reduceArgExprHead (AEFieldProj f (AEStruct fs))
  | Just ae <- lookup f fs = Just ae
  | otherwise              = Just AEUnknown
reduceArgExprHead (AEVariantProj v0 (AEVariant v1 ae))
  | v0 == v1  = Just ae
  | otherwise = Just AEUnknown
reduceArgExprHead ae = Nothing

reduceArgExpr :: ArgExpr -> ArgExpr
reduceArgExpr ae0@(AEFieldProj _ ae) =
  case reduceArgExprHead ae0 of
    Just ae1 -> reduceArgExpr ae1
    Nothing -> reduceArgExpr ae
reduceArgExpr ae0@(AEVariantProj _ ae) =
  case reduceArgExprHead ae0 of
    Just ae1 -> reduceArgExpr ae1
    Nothing -> reduceArgExpr ae
reduceArgExpr (AEStruct fs) = AEStruct $ map (second reduceArgExpr) fs
reduceArgExpr (AEVariant f ae) = AEVariant f $ reduceArgExpr ae
reduceArgExpr ae = ae

generateSize :: Env -> (Template, Template) -> [MeasureOp] -> [(Size, Size)]
generateSize env (t1, t2) [] = []
generateSize env (t1, t2) (m:ms) = 
  let s1 = applyMeasure env m t1 m 
      s2 = applyMeasure env m t2 m 
  in (s1, s2):generateSize env (t1, t2) ms

-- for each template + expression, apply the measure
generateRow :: Env -> (Template, Template) -> [MeasureOp] -> [Cmp]
generateRow env _ [] = []
generateRow env (t1, t2) (m:ms) = 
  let s1 = applyMeasure env m t1 m 
      s2 = applyMeasure env m t2 m 
      res = compareMeasure s1 s2 env
  in res:(generateRow env (t1, t2) ms)

generateMatrix :: Env -> [(Template, Template)] -> [MeasureOp] -> [[Cmp]]
generateMatrix env _ [] = [[]]
generateMatrix env [] _ = [[]]
generateMatrix env (t:ts) ms =
  case ts of 
    [] -> [(generateRow env t ms)]
    xs -> [(generateRow env t ms)] ++ (generateMatrix env ts ms)

type Size = (Maybe MeasureOp, Maybe FreshVar, Int)
compareMeasure :: Size -> Size -> Env -> Cmp
-- input, then recursive measure.
compareMeasure (_, _, -1) _ _ = Unknown
compareMeasure _ (_, _, -1) _ = Unknown
compareMeasure (_, e1, n1) (_, e2, n2) env = 
  case e1 of 
    Just x ->
      case e2 of 
        Just y -> 
          if (n1 > n2 && (equivExpr x y env)) then Le 
          else 
            if (n1 == n2 && (equivExpr x y env)) then Eq 
            else Unknown 
        _ -> Unknown
    _ -> Unknown 

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
applyMeasure env mOp (RecordAST (Just alpha) [(f, mv, t)]) (ProjectOp f' m) = 
  if (f == f') then 
    case applyMeasure env mOp t m of 
      -- if it's an error, return the current position.
      (Nothing, Nothing, -1) -> (Just (ProjectOp f' m), Just alpha, 0)
      x -> x
  else (Nothing, Nothing, -1)
applyMeasure env mOp (RecursiveRecordAST rp (Just alpha) [(f, mv, t)]) (UnfoldOp rp' f' m) = 
  if (f == f') then 
    case applyMeasure env mOp t m of -- continue
      -- if error, return the current position.
      (Nothing, Nothing, -1) -> (Just (UnfoldOp rp' f' m), Just alpha, 0)
      x -> x
  else (Nothing, Nothing, -1)
applyMeasure env mOp (VariantAST (Just alpha) [(f, mv, t)]) (CaseOp cs) =
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

-- TODO: from the MissingH library
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

-- env: fresh: expr
--    : fresh: [fresh]
-- -> if a fresh var exists for an exp, can use that instead of creating a new one
-- can drop the eq assertions.

-- remove the int
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


applyMeasureToArg :: MeasureOp -> ArgExpr -> Int -> (MeasureOp, ArgExpr, Int)
applyMeasureToArg m0@(ProjectOp f m) ae0@(AEStruct fs) i =
  case lookup f fs of
    Just ae -> applyMeasureToArg m ae i
    Nothing -> (m0, ae0, i)
applyMeasureToArg m0@(CaseOp vs) ae0@(AEVariant v ae) i =
  case lookup v vs of
    Just m -> applyMeasureToArg m ae i
    Nothing -> (m0, ae0, i)
applyMeasureToArg m0@(UnfoldOp _ f m) ae0@(AEStruct fs) i =
  case lookup f fs of
    Just ae -> applyMeasureToArg m ae (i+1)
    Nothing -> (m0, ae0, i)
applyMeasureToArg m0 ae0 i = (m0, ae0, i)

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
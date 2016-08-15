--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--


{-# LANGUAGE ExistentialQuantification #-}

module Cogent.GraphGen where

-- import Cogent.Compiler (__impossible)
import qualified Cogent.Common.Syntax as CS
import Cogent.Common.Types as CT
import Cogent.Core
import Cogent.Normal
import Cogent.Vec

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif
import Control.Monad
import Data.List
import qualified Data.Map as M

-- import Debug.Trace

type GM a = Either String a

failure :: String -> GM a
failure = Left

abort :: String -> GM a
abort s = error s

type VarEnv = [(String, GExprGroup)]
type GError = String
type GBool = Bool

data NextNode
    = NextNode Int | Ret | Err
    deriving (Show)

data GraphNode
    = GBasic NextNode [(String, GTyp, GExpr)]
    | GCond NextNode NextNode GExpr
    | GCall NextNode CS.FunName [GExpr] [(String, GTyp)]
    deriving (Show)

data FunctionGraph = FunctionGraph CS.FunName [(String, GTyp)] [(String, GTyp)] Graph
                   | FunctionGraphError CS.FunName [(String, GTyp)] [(String, GTyp)] GError
                   | FunctionGraphTypeError CS.FunName GError
    deriving (Show)

data Graph = Graph [(Int,GraphNode)]
    deriving (Show)

data GOp
    = Plus
    | Minus
    | Times
    | DividedBy
    | Modulus
    | Equals
    | SignedLess
    | SignedLessEquals
    | MemUpdate
    | MemAcc
    | WordCast
    | BWXOR
    | Not
    | And
    | Or
    | BWAnd
    | BWOr
    | ShiftLeft
    | ShiftRight
    | BWNot
    deriving (Show)

data GTyp = GBoolT | GWordT Int | GMem
    deriving (Show, Eq)

data GExpr
    = GVariable String GTyp
    | GOp GOp GTyp [GExpr]
    | GBool GBool
    | GNum GTyp Integer
    deriving (Show)

data IsUnboxed = IsUnboxed | NotUnboxed
    deriving (Show, Eq)

data GExprGroup
    = GEGSingle { singleType :: GTyp }
    | GEGUnit
    | GEGTuple GExprGroup GExprGroup
    | GEGStruct [(CS.FieldName, GExprGroup)] IsUnboxed
    | GEGSum [(CS.FieldName, GExprGroup)]
    deriving (Show, Eq)

ptrGTyp = GWordT 32
wordGTyp = GWordT 32
globalMemNm = "mem"
globalMem = GVariable globalMemNm GMem

getExprType :: GExpr -> GTyp
getExprType (GVariable _ typ) = typ
getExprType (GOp _ typ _) = typ
getExprType (GBool _) = GBoolT
getExprType (GNum typ _) = typ

graphGen :: Show a => [Definition TypedExpr a] -> String -> IO ()
graphGen defs log = putStrLn $ (concatMap prettyFunctionGraph d)
      ++ "\n# ==Failed functions==\n" ++ f
      ++ "\n# ==Failed Typed Functions==\n" ++ f2
      ++ report
    where d = graphDefinitions defs
          f = concatMap prettyFailedFunction d
          f2 = concatMap prettyFailedTypeFunction d
          report = prettyFailureReport d

graphDefinitions :: Show a => [Definition TypedExpr a] -> [FunctionGraph]
graphDefinitions = foldr graphDefinition []

graphDefinition :: Show a => Definition TypedExpr a -> [FunctionGraph] -> [FunctionGraph]
graphDefinition te@(FunDef _ fn _ ti to _) gs = fg : gs
    where
        fg = case graphHelper te of
            (Right x) -> x
            (Left err) ->
                case graphTypeHelper ti to of
                    (Right (input,output)) -> FunctionGraphError fn input output err
                    (Left err2) -> FunctionGraphTypeError fn err2

graphDefinition _ gs = gs

graphTypeHelper :: Type t -> Type t -> GM ([(String, GTyp)], [(String, GTyp)])
graphTypeHelper ti to = do
    let v = "a@0"
    gti <- graphType ti
    gto <- graphType to
    input <- getFieldVariables (v, gti)
    output <- getFieldVariables (v, gto)
    return (input, output)

graphHelper :: Show a => Definition TypedExpr a -> GM FunctionGraph
graphHelper (FunDef _ fn ks ti to e) = do
    let v = "a@0"
    gti <- graphType ti
    gto <- graphType to
    (g,_) <- graph (Graph []) e 1 Ret [(v, gti)]
    input <- getFieldVariables(v, gti)
    output <- getFieldVariables("ret", gto)
    return (FunctionGraph fn input output g)
graphHelper _ = undefined

graphType :: Type t -> GM GExprGroup
graphType (TPrim Boolean) = return $ GEGSingle GBoolT
graphType (TPrim U8)      = return $ GEGSingle (GWordT 8)
graphType (TPrim U16)     = return $ GEGSingle (GWordT 16)
graphType (TPrim U32)     = return $ GEGSingle (GWordT 32)
graphType (TPrim U64)     = return $ GEGSingle (GWordT 64)
graphType (TProduct t u)  = do
    gt <- graphType t
    gu <- graphType u
    return $ GEGTuple gt gu
graphType (TRecord e s)   = do
    res <- mapM (\x -> liftM (\y -> (fst x, y)) (graphType $ (fst . snd) x)) e
    return $ GEGStruct res (if s == Unboxed then IsUnboxed else NotUnboxed)
graphType (TUnit)         = return $ GEGUnit
graphType (t @ (TCon _ _ Unboxed))
    = failure ("graphType: no repr known for: " ++ show t)
graphType (TCon _ _ _) = return $ GEGSingle ptrGTyp
graphType (TSum alts) = do
    altGTs <- mapM (graphType . fst . snd) alts  -- FIXME: cogent.1
    return $ GEGSum (Data.List.zip (map fst alts) altGTs)
graphType x = failure ("graphType: couldn't handle: " ++ show x)

mkUpds :: String -> [(String, GTyp)] -> [GExpr] -> GM [(String, GTyp, GExpr)]
mkUpds _ [] [] = return []
mkUpds s ((nm, gTyp) : nms) (x : xs) = do
    mkus <- mkUpds s nms xs
    if getExprType x == gTyp then return $ (nm, gTyp, x) : mkus
    else failure ("mkUpds: type mismatch: " ++ show (nm, gTyp, x))
mkUpds s nms xs = abort ("mkUpds: " ++ s ++ ": length mismatch: " ++ show (nms, xs))

mkBasicVs :: String -> NextNode -> [(String, GExprGroup)] -> [GExpr] -> [(String, GTyp, GExpr)] -> GM GraphNode
mkBasicVs s nn vs xs exUpds = do
    vFlds <- mapM getFieldVariables vs
    mkus <- mkUpds s (concat vFlds) xs
    return $ GBasic nn (mkus ++ exUpds)

mkBasic :: String -> NextNode -> (String, GExprGroup) -> [GExpr] -> [(String, GTyp, GExpr)] -> GM GraphNode
mkBasic s nn v xs exUpds = mkBasicVs s nn [v] xs exUpds

mystery :: String -> Integer
mystery s = 0 -- error ("mystery: " ++ s)

graph :: Show a => Graph -> TypedExpr t v a -> Int -> NextNode -> VarEnv -> GM (Graph, Int)

graph g (TE _ (Let _ (TE appTy (App (TE _ (Fun fn _ _)) arg)) e)) n ret vs = do
    let v = (freshNames !! (Prelude.length vs)) ++ "@" ++ show n
    ty <- graphType appTy
    lhs <- getFieldVariables (v, ty)
    gexprs <- atomNoUpds arg vs
    let gnode = GCall (NextNode (n + 1)) fn (gexprs ++ [globalMem]) (lhs ++ [(globalMemNm, GMem)])
    let g' = addGraphNode g n gnode
    g'' <- graph g' e (n+1) ret ((v, ty) : vs)
    return g''

graph g (TE _ (Let _ e1 e2)) n ret vs = do
    let v = (freshNames !! (Prelude.length vs)) ++ "@" ++ show n
    (gexprs, exUpds) <- atom e1 vs
    ty <- graphType (exprType e1)
    gnode <- mkBasic "Let" (NextNode (n + 1)) (v, ty) gexprs exUpds
    let g' = addGraphNode g n gnode
    g'' <- graph g' e2 (n+1) ret ((v, ty) : vs)
    return g''

graph g (TE _ (If e e1 e2)) n ret vs = do
    (g, n1) <- graph g e1 (n + 1) ret vs
    (g, n2) <- graph g e2 n1 ret vs
    sa <- singleAtom e vs
    let gnode = GCond (NextNode (n + 1)) (NextNode n1) sa
    let g' = addGraphNode g n gnode
    return (g', n2)

graph g (TE tp (Take _ (TE recTy (Variable v)) fld e)) n ret vs = do
    when (finInt (fst v) >= Prelude.length vs) $ abort $ "atom: " ++ show (v, vs)
    let (prevNm', aggTy) = vs !! (finInt $ fst v)
    let newNm = namePrefix prevNm' ++ "_fld" ++ show fld ++ "@" ++ show n
    gtrec <- graphType recTy
    prevNm <- if aggTy == gtrec
                 then return (namePrefix prevNm' ++ "@" ++ show n)
                 else abort ("graph: take: type mismatch: " ++ show (recTy, aggTy))
    newTy <- case recTy of
        TRecord flds _ -> graphType $ fst (snd (flds !! fld))
        otherwise -> failure ("graph: take: not a record")
    prevFlds <- case recTy of
        TRecord _ Unboxed -> do
            gfv <- getFieldVariable (prevNm, aggTy) fld
            res <- fmap (\z -> map (\(x,y) -> GVariable x y) z) (getFieldVariables gfv)
            return res
        TRecord flds _ -> do
            mko <- mkFieldOffset (GVariable prevNm ptrGTyp, aggTy) fld
            res <- getFieldAccesses mko
            return res
        otherwise -> failure ("graph: take: not a record")
    gnode <- mkBasic "Take" (NextNode (n + 1)) (newNm, newTy) prevFlds []
    let g' = addGraphNode g n gnode
    g'' <- graph g' e (n + 1) ret ((newNm, newTy) : (prevNm, aggTy) : vs)
    return g''

graph g (TE _ (Split _ e1@(TE _ (Variable v)) e2)) n ret vs = do
    when (finInt (fst v) >= Prelude.length vs) $ abort $ "atom: " ++ show (v, vs)
    let (prevNm', _) = vs !! (finInt $ fst v)
    let v1 = namePrefix prevNm' ++ "_fst@" ++ show n
    let v2 = namePrefix prevNm' ++ "_snd@" ++ show n
    (gexprs, exUpds) <- atom e1 vs
    (GEGTuple ty1 ty2) <- graphType (exprType e1)
    gnode <- mkBasicVs "Split" (NextNode (n + 1)) [(v1, ty1), (v2, ty2)] gexprs exUpds
    let g' = addGraphNode g n gnode
    g'' <- graph g' e2 (n+1) ret ((v1, ty1): (v2, ty2): vs)
    return g''

graph g te@(TE _ (LetBang _ _ e1 e2)) n ret vs = do
    let g' = addGraphNode g n (GBasic (NextNode (n + 2)) [])
    (g'', n1) <- graph g' e1 (n + 2) (NextNode (n + 1)) vs
    let v = (freshNames !! (Prelude.length vs)) ++ "@" ++ show (n + 1)
    gty <- graphType (exprType e1)
    vars <- getFieldVariables ("ret", gty)
    gnode <- mkBasic "LetB" (NextNode n1) (v, gty) [GVariable n ty | (n, ty) <- vars] []
    let g''' = addGraphNode g'' (n + 1) gnode
    g'''' <- graph g''' e2 n1 ret ((v, gty) : vs)
    return g''''

graph g te@(TE _ (Case x tag (_, _, m) (_, _, nom))) n ret vs = do
    let tagN = mystery tag
    flds <- atomNoUpds x vs
    let tagF = Prelude.head flds
    sumGTy <- graphType (exprType x)
    alts <- case sumGTy of
            GEGSum alts -> return alts
            _ -> abort ("graph: Case: sumGTy " ++ show sumGTy)
    ix <- case findIndex ((== tag) . fst) alts of
        Just ix -> return ix
        Nothing -> abort ("graph: Case: alt miss " ++ tag ++ ": " ++ show alts)
    let cond = GOp Equals GBoolT [tagF, GNum (GWordT 32) tagN]
    let g' = addGraphNode g n (GCond (NextNode (n + 1)) (NextNode (n + 2)) cond)
    let v = tag ++ "@" ++ show (n + 1)
    m_flds <- getFieldsFromConcat (map snd alts) ix (Prelude.tail flds)
    m_node <- mkBasic "Case" (NextNode (n + 3)) (v, snd (alts !! ix)) m_flds []
    let g'' = addGraphNode g' (n + 1) m_node
    (g3, n') <- graph g'' m (n + 3) ret ((v, snd (alts !! ix)) : vs)
    let v2 = tag ++ "_missed@" ++ show (n + 2)
    let smallerGTy = GEGSum (filter ((/= tag) . fst) alts)
    flds' <- sumFieldsMash sumGTy smallerGTy flds
    nom_node <- mkBasic "CaseNM" (NextNode n') (v2, smallerGTy) flds' []
    let g4 = addGraphNode g3 (n + 2) nom_node
    g5 <- graph g4 nom n' ret ((v2, smallerGTy) : vs)
    return g5

graph g te@(TE ty (App fn arg)) n ret vs = graph g (TE ty (Let undefined te (TE ty (Variable (FZero, undefined))))) n ret vs
graph g te@(TE ty (Put rec fld v)) n ret vs = graph g (TE ty (Let undefined te (TE ty (Variable (FZero, undefined))))) n ret vs

graph g te n ret vs = case isAtom (untypeE te) of
    True -> do
        ty <- graphType (exprType te)
        (gexprs, exUpds) <- atomCheck te vs
        gnode <- mkBasic "Ret" ret ("ret", ty) gexprs exUpds
        let g' = addGraphNode g n gnode
        return (g', n + 1)
    False -> failure ("graph: couldn't handle: " ++ show te)

getFieldVariable :: (String, GExprGroup) -> CS.FieldIndex -> GM (String, GExprGroup)
getFieldVariable (nm, GEGStruct fs IsUnboxed) fld = return (nm ++ "." ++ show fld, tp)
    where
        (_, tp) = fs !! fld
getFieldVariable x y = failure ("getFieldVariable: not an unboxed record " ++ show x ++ " -- " ++ show y)

getFieldVariables :: (String, GExprGroup) -> GM [(String, GTyp)]
getFieldVariables (nm, GEGUnit) = return [(nm, wordGTyp)]
getFieldVariables (nm, GEGSingle gTyp) = return [(nm, gTyp)]
getFieldVariables (nm, GEGTuple a b) = do
    ga <- getFieldVariables (nm ++ ".1", a)
    gb <- getFieldVariables (nm ++ ".2", b)
    return $ ga ++ gb
getFieldVariables v@(nm, GEGStruct fs IsUnboxed) = do
    gfv <- mapM (\n -> getFieldVariable v n) [0 .. Prelude.length fs - 1]
    gfvs <- mapM getFieldVariables gfv
    return $ concat gfvs
getFieldVariables (nm, GEGStruct fs NotUnboxed)  = return [(nm, ptrGTyp)]
getFieldVariables (nm, GEGSum alts) = getFieldVariables (nm,
    GEGStruct (("tag", GEGSingle wordGTyp) : alts) IsUnboxed)

getFieldAddresses :: (GExpr, GExprGroup) -> GM [(GExpr, GTyp)]
getFieldAddresses (ptr, GEGUnit)  = return [(ptr, wordGTyp)]
getFieldAddresses (ptr, GEGSingle gTyp) = return [(ptr, gTyp)]
getFieldAddresses (ptr, GEGTuple a b)  = do
    gfaa <- getFieldAddresses (ptr, a)
    mko <- mkOffset ptr a
    gfab <- getFieldAddresses (mko, b)
    return $ gfaa ++ gfab
getFieldAddresses (ptr, GEGStruct [] IsUnboxed) = return []
getFieldAddresses v@(ptr, GEGStruct fs IsUnboxed) = do
    mfo <- mapM (\n -> mkFieldOffset v n) [0 .. Prelude.length fs - 1]
    gfas <- mapM getFieldAddresses mfo
    return $ concat gfas
getFieldAddresses (ptr, GEGStruct _ NotUnboxed) = return [(ptr, ptrGTyp)]
getFieldAddresses (ptr, GEGSum alts) = getFieldAddresses (ptr,
    GEGStruct (("tag", GEGSingle wordGTyp) : alts) IsUnboxed)

getFieldAccesses :: (GExpr, GExprGroup) -> GM [GExpr]
getFieldAccesses (ptr, ggTyp) = do
    gfas <- getFieldAddresses (ptr, ggTyp)
    return $ map (\(ptr2, gTyp) -> (GOp MemAcc gTyp [globalMem, ptr2])) gfas

mkFieldOffset :: (GExpr, GExprGroup) -> CS.FieldIndex -> GM (GExpr, GExprGroup)
mkFieldOffset (ptr, GEGStruct fs _) fld = do
    offs <- mapM (\(_,x) -> gexprGroupTypeWidth fs x) (take fld fs)
    let offsum = sum offs
    let typ = snd (fs !! fld)
    return $ (GOp Plus ptrGTyp [ptr, GNum ptrGTyp offsum], typ)
mkFieldOffset _ _ = failure "mkFieldOffset: not a record"

mkOffset :: GExpr -> GExprGroup -> GM GExpr
mkOffset ptr ggTyp = do
    geg <- gexprGroupTypeWidth [] ggTyp
    return $ GOp Plus ptrGTyp [ptr, GNum ptrGTyp geg]

gexprGroupTypeWidth :: [(String, GExprGroup)] -> GExprGroup -> GM Integer
gexprGroupTypeWidth _ GEGUnit = return 4
gexprGroupTypeWidth _ (GEGSingle (GWordT 32)) = return 4
gexprGroupTypeWidth fs (GEGSingle (GWordT n))
    = failure $ "non-32 bit word in aggregate: " ++ show fs
gexprGroupTypeWidth fs (GEGSingle _)
    = failure $ "non word in aggregate: " ++ show fs
gexprGroupTypeWidth fs (GEGTuple a b) = do
    ga <- gexprGroupTypeWidth fs a
    gb <- gexprGroupTypeWidth fs b
    return $ ga + gb

gexprGroupTypeWidth fs (GEGStruct flds IsUnboxed) = do
    list <- mapM (gexprGroupTypeWidth fs . snd) flds
    return $ sum list
gexprGroupTypeWidth fs (GEGStruct _ NotUnboxed)
    = gexprGroupTypeWidth fs (GEGSingle ptrGTyp)
gexprGroupTypeWidth fs (GEGSum alts) = do
    list <- mapM (gexprGroupTypeWidth fs . snd) alts
    return $ 4 + sum list

getFieldsFromConcat :: [GExprGroup] -> Int -> [GExpr] -> GM [GExpr]
getFieldsFromConcat groups n fields = do
    list <- mapM (\z -> getFieldVariables ("",z)) groups
    let dropN = sum $ map (\z -> Prelude.length z) (take n list)
    when (n >= Prelude.length groups) $ abort $ "getFieldsFromConcat: " ++ show (n, groups)
    list2 <- getFieldVariables ("", groups !! n)
    let takeN = Prelude.length list2
    return (take takeN $ drop dropN fields)

atom :: Show a => TypedExpr t v a -> VarEnv -> GM ([GExpr], [(String, GTyp, GExpr)])
atom (TE ty (Variable v)) vs = do
    when (finInt (fst v) >= Prelude.length vs) $ abort $ "atom: " ++ show (v, vs)
    let (nm, ggTyp) = vs !! (finInt $ fst v)
    xGTyp <- graphType ty
    when (xGTyp /= ggTyp) $ abort $ "atom: types: " ++ show (v, ty) ++ "\n\n" ++ show vs ++ "\n\n" ++ show (xGTyp, ggTyp)
    list <- fmap (\z -> map (\(nm2, gTyp) -> GVariable nm2 gTyp) z) (getFieldVariables (nm, ggTyp))
    return $ (list, [])

atom (TE ty (Op opr es)) vs = case opr of
    CS.Gt -> do
        ares <- atom (TE ty (Op CS.Le es)) vs
        gt <- graphType ty
        return ([GOp Not (singleType gt) (fst ares)],[])
    CS.Ge -> do
        ares <- atom (TE ty (Op CS.Lt es)) vs
        gt <- graphType ty
        return ([GOp Not (singleType gt) (fst ares)],[])
    CS.NEq -> do
        ares <- atom (TE ty (Op CS.Eq es)) vs
        gt <- graphType ty
        return ([GOp Not (singleType gt) (fst ares)],[])
    otherwise -> do
        gt <- graphType ty
        es' <- mapM (flip singleAtom vs) es
        return ([GOp (opConvert opr) (singleType gt) es'], [])

atom (TE ty (ILit i pt)) vs = do
    gt <- graphType ty
    return ([GNum (singleType gt) i],[])

atom (TE (TPrim _) (Promote ty e)) vs = do
    gt <- graphType ty
    atm <- singleAtom e vs
    return ([GOp WordCast (singleType gt) [atm]],[])

atom (TE (ty @ (TSum _)) (Promote _ e)) vs = do
    gTy <- graphType (exprType e)
    gTy2 <- graphType ty
    fields <- atomNoUpds e vs
    new_fields <- sumFieldsMash gTy gTy2 fields
    return (new_fields, [])

atom (TE ty2 (Promote ty e)) _ = abort ("Promote: broken type " ++ show (ty, ty2))

atom (TE _ (Tuple a b)) vs = do
    atomA <- atomNoUpds a vs
    atomB <- atomNoUpds b vs
    return (atomA ++ atomB, [])

atom (TE _ Unit) vs = return (zeroFields GEGUnit, [])

atom (TE _ (Struct flds)) vs = do
    gexprs <- mapM (flip atomNoUpds vs) (map snd flds)
    return (concat gexprs, [])

atom te@(TE _ (Member (rec @ (TE (TRecord flds Unboxed) _)) ix)) vs = do
    recFields <- atomNoUpds rec vs
    tys <- mapM (\(_,(t,_)) -> graphType t) flds
    flds <- getFieldsFromConcat tys ix recFields
    return (flds, [])

atom te@(TE fldTy (Member rec ix)) vs = do
    recPtr <- singleAtom rec vs
    gt <- graphType (exprType rec)
    ptr <- mkFieldOffset (recPtr, gt) ix
    accs <-getFieldAccesses ptr
    return (accs, [])

atom (TE (TRecord flds Unboxed) (Put rec fld v)) vs = do
    recFields <- atomNoUpds rec vs
    vFields <- atomNoUpds v vs
    tys <- mapM (\(_,(t,_)) -> graphType t) (take fld flds)
    list <- mapM (\z -> getFieldVariables ("",z)) tys
    let n = sum $ map (\z -> Prelude.length z) list
    return (take n recFields ++ vFields ++ drop (n + Prelude.length vFields) recFields,[])

atom (TE ty (Con tag x)) vs = do
    let tagN = mystery tag
    let tagX = GNum (GWordT 32) tagN
    altFields <- atomNoUpds x vs
    altTy <- graphType (exprType x)
    gTy <- graphType ty
    fields <- sumFieldsMash (GEGSum [(tag, altTy)]) gTy (tagX : altFields)
    return (fields, [])

atom (TE recTy (Put rec fld v)) vs = do
    recPtr <- singleAtom rec vs
    gt <- graphType recTy
    ptr <- mkFieldOffset (recPtr, gt) fld
    addresses <- getFieldAddresses ptr
    vars <- atomNoUpds v vs
    let updGMem = foldr (\(addr, var) m -> GOp MemUpdate GMem [m, addr, var]) globalMem (Data.List.zip (map fst addresses) vars)
    return ([recPtr], [(globalMemNm, GMem, updGMem)])

atom te@(TE _ (Esac x)) vs = do
    sumFields <- atomNoUpds x vs
    return (Prelude.tail sumFields, [])

atom te@(TE _ (Fun _ _ _)) vs  = failure ("atom Fun")
atom te@(TE _ (App _ _)) vs    = failure ("atom App: " ++ show te)
atom te@(TE _ (SLit _)) vs     = failure ("atom SLit: " ++ show te)

atom (TE _ x) vs = failure ("atom: couldn't handle: " ++ show x)

atomCheck :: Show a => TypedExpr t v a -> VarEnv -> GM ([GExpr], [(String, GTyp, GExpr)])
atomCheck te vs = do
    res <- atom te vs
    gty <- graphType (exprType te)
    vfields <- getFieldVariables ("", gty)
    when (Prelude.length (fst res) /= Prelude.length vfields)
        $ abort $ "atomCheck: " ++ show te ++ ", " ++ show res
    return res

atomNoUpds :: Show a => TypedExpr t v a -> VarEnv -> GM [GExpr]
atomNoUpds te ve = do
    res <- atomCheck te ve
    case res of
        (xs, [])   -> return xs
        (xs, upds) -> failure ("atomNoUpds: got upds: " ++ show upds)

singleAtom :: Show a => TypedExpr t v a -> VarEnv -> GM GExpr
singleAtom te ve = do
    res <- atom te ve
    case res of
        ([x], []) -> return x
        xs        -> failure ("singleAtom: not single " ++ show xs)

zeroField :: GTyp -> GExpr
zeroField GBoolT = (GBool False)
zeroField (GWordT n) = (GNum (GWordT n) 0)
zeroField t = error ("zeroField: " ++ show t)

zeroFields :: GExprGroup -> [GExpr]
zeroFields GEGUnit = [zeroField wordGTyp]
zeroFields (GEGSingle fty) = [zeroField fty]
zeroFields (GEGTuple a b) = zeroFields a ++ zeroFields b
zeroFields (GEGStruct ts IsUnboxed) = concatMap (zeroFields . snd) ts
zeroFields (GEGStruct ts NotUnboxed) = [zeroField ptrGTyp]
zeroFields (GEGSum alts) = zeroField wordGTyp : concatMap (zeroFields . snd) alts

sumFieldsMash :: GExprGroup -> GExprGroup -> [GExpr] -> GM [GExpr]
sumFieldsMash (GEGSum alts) (GEGSum alts2) (tag : fields) = do
    chunks <- forM alts2 $ \(tag, gty) -> do
        case findIndex (== (tag, gty)) alts of
            Just ix -> getFieldsFromConcat (map snd alts) ix fields
            Nothing -> return $ zeroFields gty
    return $ tag : concat chunks
sumFieldsMash t t' _ = abort ("sumFieldsMash: " ++ show (t, t'))

addGraphNode :: Graph -> Int -> GraphNode -> Graph
addGraphNode (Graph g) n gn = Graph ((n, gn) : g)

prettyFailedTypeFunction :: FunctionGraph -> String
prettyFailedTypeFunction (FunctionGraphTypeError fn err) = "# Function: " ++ fn ++ "\n#    >>Error: " ++ err ++ "\n\n"
prettyFailedTypeFunction _ = ""

prettyFunctionGraph :: FunctionGraph -> String
prettyFunctionGraph (FunctionGraph fn input output g)
    = "Function " ++ prettyFName fn ++ " " ++ prettyVars (input ++ [(globalMemNm, GMem)])
                               ++ " " ++ prettyVars (output ++ [(globalMemNm, GMem)]) ++ "\n" ++  prettyGraph g ++ "EntryPoint 1\n\n"
prettyFunctionGraph _ = ""

prettyFailedFunction :: FunctionGraph -> String
prettyFailedFunction (FunctionGraphError fn input output err) = "# Function: " ++ fn
    ++ "\n#    >>Error: " ++ err ++ "\n\n"
    ++ "Function " ++ prettyFName fn ++ " " ++ prettyVars (input ++ [(globalMemNm, GMem)])
                                ++ " " ++ prettyVars (output ++ [(globalMemNm, GMem)]) ++ "\n"
prettyFailedFunction _ = ""

failureCount :: FunctionGraph -> [(String, (Int, Int))]
failureCount (FunctionGraphTypeError _ err) = [(err, (1, 0))]
failureCount (FunctionGraphError _ _ _ err) = [(err, (0, 1))]
failureCount _ = []

prettyFailureReport :: [FunctionGraph] -> String
prettyFailureReport d = (if null fails then []
    else "#== Failure Report ==\n\n" ++ report)
  where
    fails = concatMap failureCount d
    m = M.fromListWith (\(a, b) (c, d) -> (a + c, b + d)) fails
    failCounts = M.toList m
    report = concatMap (\(s, (t, e)) -> "# Error " ++ s ++ "\n(" ++ show t
        ++ " type failures, " ++ show e ++ " body failures)\n") failCounts

prettyGraph :: Graph -> String
prettyGraph (Graph ((index, n):ns)) = show index ++ " " ++ prettyNode n ++ "\n" ++ prettyGraph (Graph ns)
prettyGraph (Graph []) = ""

prettyNode :: GraphNode -> String
prettyNode (GBasic nn es) = "Basic " ++ prettyNN nn ++ " " ++ show(Prelude.length es) ++ " " ++ prettyBindings es
prettyNode (GCond n1 n2 e) = "Cond " ++ prettyNN n1 ++ " " ++ prettyNN n2 ++ " " ++ prettyE e
prettyNode (GCall nn s gs vs) = "Call " ++ prettyNN nn ++ " " ++ prettyFName s ++ " " ++ prettyList prettyE gs ++ "  " ++ prettyVars vs

prettyFName :: CS.FunName -> String
prettyFName s = "Cogent." ++ s

prettyList :: (a -> String) -> [a] -> String
prettyList p xs = show (Prelude.length xs) ++ " " ++ concat (intersperse " " (map p xs))

prettyVars :: [(String, GTyp)] -> String
prettyVars = prettyList prettyVar

prettyVar :: (String, GTyp) -> String
prettyVar (s, ty) = s ++ " " ++ prettyTy ty

prettyNN :: NextNode -> String
prettyNN Ret = "Ret"
prettyNN Err = "Err"
prettyNN (NextNode i) = show i

prettyBindings :: [(String, GTyp, GExpr)] -> String
prettyBindings [] = ""
prettyBindings ((s,t,e):es) = s ++ " " ++ prettyTy t ++ " " ++ prettyE e ++ " " ++ prettyBindings es

prettyTy :: GTyp -> String
prettyTy GBoolT     = "Bool"
prettyTy (GWordT i) = "Word " ++ show i
prettyTy GMem       = "Mem"

prettyE :: GExpr -> String
prettyE (GVariable s t) = "Var " ++ s ++ " " ++ prettyTy t
prettyE (GOp o t es)     = "Op " ++ show o ++ " " ++ prettyTy t ++ " " ++ show (Prelude.length es) ++ " " ++ (concatMap (\x -> prettyE x ++ " ") es)
prettyE (GBool b)       = "Bool " ++ show b
prettyE (GNum t i)      = "Num " ++ show i ++ " " ++ prettyTy t

opConvert :: CS.Op -> GOp
opConvert CS.Plus  = Plus
opConvert CS.Minus = Minus
opConvert CS.Times = Times
opConvert CS.Divide = DividedBy
opConvert CS.Mod = Modulus
opConvert CS.Not = Not
opConvert CS.And = And
opConvert CS.Or = Or
-- opConvert Gt = ">"
opConvert CS.Lt = SignedLess
opConvert CS.Le = SignedLessEquals
-- opConvert Ge = ">="
opConvert CS.Eq = Equals
-- opConvert NEq = "/="
opConvert CS.BitAnd = BWAnd
opConvert CS.BitOr = BWOr
opConvert CS.BitXor = BWXOR
opConvert CS.LShift = ShiftLeft
opConvert CS.RShift = ShiftRight
opConvert CS.Complement = BWNot
opConvert x = error ("opConvert: couldn't handle: " ++ show x)

namePrefix :: String -> String
namePrefix = takeWhile (/= '@')

freshNames :: [String]
freshNames = map pure ['a'..'z'] ++ map ((++) "v" . show) [(1 :: Integer)..]


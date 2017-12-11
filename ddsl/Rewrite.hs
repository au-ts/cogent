--
-- Copyright 2017, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--
{-# LANGUAGE PatternGuards #-}

module Rewrite (rewrite) where

import Prelude as P hiding (mapM_)
import Data.List as L
import Data.Map as M hiding (null)
import Data.Maybe (fromJust, isJust)
import Data.Tuple.Select
import Data.Bits
import Data.Foldable (mapM_)
import Control.Monad.State hiding (mapM_)
import qualified Control.Monad as CM
import Control.Applicative ((<$>), (<*>), pure)
import Text.Printf
import Text.Parsec.Pos (Line)

import Syntax as S
import Pretty
import Kinds
import Util hiding (Def)

-------------------------------------------------------------------------------
-- Environments

type DState = State (DD, Def, Env, VarIdx, TypeIdx)

type Env = (Delta, Gamma, Pi)
type Def = [DataDesc]
type DD  = [DataDesc]
type VarIdx = Integer
type TypeIdx = Integer

getDState :: DState (DD, Def, Env, VarIdx, TypeIdx)
getDState = gets id

putDState :: (DD, Def, Env, VarIdx, TypeIdx) -> DState ()
putDState s = modify (const s)

getEnv :: DState Env
getEnv = sel3 <$> getDState

putEnv :: Env -> DState ()
putEnv env = modify (\(ds, def, _, n, m) -> (ds, def, env, n, m))

getFreshVar :: DState Ident
getFreshVar = do
  (ds, def, env, n, m) <- getDState
  let v = genPrefix ++ "v" ++ show n
  putDState (ds, def, env, n + 1, m)
  return v

getFreshType :: DState Ident
getFreshType = do
  (ds, def, env, n, m) <- getDState
  let t = genPREFIX ++ "T" ++ show m
  putDState (ds, def, env, n, m + 1)
  return t

emptyGamma :: DState ()
emptyGamma = getEnv >>= \(del, _, pii) -> putEnv (del, empty, pii)

resetVar :: DState ()
resetVar = getDState >>= \(ds, def, env, _, m) -> putDState (ds, def, env, 0, m)

-------------------------------------------------------------------------------

-- guarantees it won't add duplicated items to Def
insertDef :: DataDesc -> DState ()
insertDef d = modify (\(ds, def, env, n, m) -> (ds, d:def, env, n, m))

-- IMPORTANT: add new DataDesc at the very end of list
insertDD :: DataDesc -> DState ()
insertDD d = modify (\(ds, def, env, n, m) -> (ds ++ [d], def, env, n, m))

insertDelta :: Ident -> Kind -> DState ()
insertDelta id k = do 
  (del, gam, pii) <- getEnv 
  when (id `member` del) $ error $ progErr "insertDelta"
  putEnv (M.insert id k del, gam, pii)

lookupDelta :: Ident -> DState (Maybe Kind)
lookupDelta id = do
  (del, _, _) <- getEnv
  return (M.lookup id del)

insertGamma :: Ident -> Kind -> DState ()
insertGamma id k = do 
  (del, gam, pii) <- getEnv 
  when (id `member` gam) $ error $ progErr "insertGamma"
  putEnv (del, M.insert id k gam, pii)

lookupGamma :: Ident -> DState Kind
lookupGamma id = do
  (_, gam, pii) <- getEnv
  case M.lookup id gam of
    Nothing -> case M.lookup id pii of
                 Nothing -> error $ progErr "lookupGamma"
                 Just kv -> return $ fst kv
    Just k -> return k

lookupPi :: Ident -> DState (Kind, Value)
lookupPi id = do
  (_, _, pii) <- getEnv
  maybe (error $ progErr "lookupPi") return (M.lookup id pii)

-------------------------------------------------------------------------------

rewrite :: [Module] -> (Delta, Pi) -> ([Module], Delta)
rewrite [] (del, _) = ([], del)
rewrite (Module n h ds : ms) (del, pii) =
  let (ds', del') = rewrite1 ds (del, pii)
      (ms', del'') = rewrite ms (del', pii)
  in (Module n h ds' : ms', del'')

rewrite1 :: [DataDesc] -> (Delta, Pi) -> ([DataDesc], Delta)
rewrite1 ds (del, pii) = (\st -> (sel2 st, sel1 $ sel3 st)) $ 
  execState rewriteDs (ds, [], (del, empty, pii), 0, 0)

rewriteDs :: DState ()
rewriteDs = do
  (ds, _, _, _, _) <- getDState
  case ds of
    [] -> return ()
    d:ds -> do modify (\(d:ds, def, envs, n, m) -> (ds, def, envs, n, m))
               rewriteD d
               rewriteDs

rewriteD :: DataDesc -> DState ()
rewriteD (DStruct id ps fs tc pos) = do
  ps' <- rewriteParams ps
  fs' <- rewriteFields fs
  tc' <- rewriteTypeCons tc (Atom $ KStruct id)
  insertDef (DStruct id ps' fs' tc' pos)
  emptyGamma
  resetVar
rewriteD (DBitfield id ps t bfs tc pos) = do
  ps'  <- rewriteParams ps
  t'   <- rewriteType t
  k    <- infType t
  bfs' <- rewriteBFields bfs k
  tc'  <- rewriteTypeCons tc (Atom $ KBitfield id Nothing)
  insertDef (DBitfield id ps' t' bfs' tc' pos)
  emptyGamma
  resetVar
rewriteD (DTUnion id ps t cs pos) = do
  ps' <- rewriteParams ps
  t'  <- rewriteType t
  k   <- infType t
  cs' <- rewriteCases cs k
  insertDef (DTUnion id ps' t' cs' pos)
  emptyGamma
  resetVar
rewriteD (DBUnion id ps t cs pos) = do 
  ps' <- rewriteParams ps
  t'  <- rewriteType t
  k   <- infType t
  cs' <- rewriteCases cs k
  insertDef (DBUnion id ps' t' cs' pos)
  emptyGamma
  resetVar
rewriteD (DTypeSyn id ps t tc pos) = do
  ps' <- rewriteParams ps
  t'  <- rewriteType_ t
  k   <- infType t
  tc' <- rewriteTypeCons tc k
  insertDef (DTypeSyn id ps' t' tc' pos)
  emptyGamma
  resetVar
rewriteD d@(DEnum id t es pos) = do
  t' <- rewriteType t
  (Atom (KEnum k), _) <- lookupPi id
  es' <- mapM (flip prmtExpr k) es
  insertDef (DEnum id t' es' pos)
  emptyGamma
  resetVar
rewriteD (DConst id t expr pos) = do
  t'     <- rewriteType t
  (k, _) <- lookupPi id
  expr'  <- prmtExpr expr k
  insertDef (DConst id t' expr' pos)
  emptyGamma
  resetVar

-------------------------------------------------------------------------------

rewriteParams :: [Param] -> DState [Param]
rewriteParams [] = return []
rewriteParams (p:ps) = (:) <$> rewriteParam p <*> rewriteParams ps

rewriteParam :: Param -> DState Param
rewriteParam (Nothing, t) = (,) <$> (Just <$> getFreshVar) <*> rewriteType t
rewriteParam (Just id, t) = do
  infType t >>= insertGamma id
  (,) <$> pure (Just id) <*> rewriteType t

rewriteFields :: [Field] -> DState [Field]
rewriteFields [] = return []
rewriteFields (f:fs) = (:) <$> rewriteField f <*> rewriteFields fs

rewriteField :: Field -> DState Field
rewriteField (Field opId t mc pos) = do
  id <- case opId of 
          Nothing -> Just <$> getFreshVar
          Just _  -> return opId
  t' <- rewriteType t
  k  <- infType t
  when (isJust opId) $ insertGamma (fromJust opId) k
  mc' <- rewriteMaybeCons mc
  return (Field id t' mc' pos)
 
rewriteBFields :: [BField] -> Kind -> DState [BField]
rewriteBFields [] _ = return []
rewriteBFields (b:bs) k = (:) <$> rewriteBField b k <*> rewriteBFields bs k

rewriteBField :: BField -> Kind -> DState BField
rewriteBField (BField tag opId e mc pos) k = do
  id <- case opId of
          Nothing -> Just <$> getFreshVar
          Just _  -> return opId
  e' <- prmtExpr_ e
  when (isJust opId) $ insertGamma (fromJust opId) k
  mc' <- rewriteMaybeCons mc
  return (BField tag id e' mc' pos)

rewriteCases :: [Case] -> Kind -> DState [Case]
rewriteCases cs k = mapM (flip rewriteCase k) cs

rewriteCase :: Case -> Kind -> DState Case
rewriteCase (Case e f pos) k = do 
  envs <- getEnv
  e' <- prmtExpr e k
  f' <- rewriteField f
  putEnv envs
  return (Case e' f' pos)

-- rewriteTypeCons :: tyCons -> kind of instance -> return ...
rewriteTypeCons :: TyConstraint -> Kind -> DState TyConstraint
rewriteTypeCons Nothing   _ = return Nothing
rewriteTypeCons (Just (opI, c)) k = do
  when (isJust opI) $ insertGamma (fromJust opI) k
  c' <- prmtExpr_ c
  return $ Just (opI, c')

rewriteMaybeCons :: Maybe Constraint -> DState (Maybe Constraint)
rewriteMaybeCons Nothing = return Nothing
rewriteMaybeCons (Just c) = Just <$> prmtExpr_ c

-- rewrite any Array type to typedef
rewriteType :: Type -> DState Type
rewriteType ty@(Array t e) = do
  let arrDef = DTypeSyn 
      arrId  = toName ty 
  mk <- lookupDelta arrId
  case mk of
    Nothing -> do p <- getFreshVar
                  k <- infExpr e
                  insertDD (DTypeSyn arrId [(Just p, UInt 32 View)] (Array t $ Var p dummyPos) Nothing dummyPos)
                  arrk <- infType ty
                  insertDelta arrId (k `Arrow` arrk)
    Just _ -> return ()
  CompTy arrId <$> sequence [prmtExpr e (Atom $ KUInt 32 View)]
rewriteType (CompTy id args) = do
  (del, _, _) <- getEnv
  case M.lookup id del of
    Nothing -> error $ progErr "rewriteType"
    Just k  -> CompTy id <$> mapKind k args
  where mapKind k [] = return []
        mapKind (k `Arrow` ks) (a:as) = 
          (:) <$> (if isIK k then prmtExpr a k else pure a) 
              <*> (mapKind ks as)
        mapKind k as = error $ progErr "mapKind"
rewriteType t = return t

-- normally rewrite Array type
rewriteType_ :: Type -> DState Type
rewriteType_ (Array t e) = do
  Array <$> rewriteType t <*> prmtExpr_ e
rewriteType_ ty = rewriteType ty

-------------------------------------------------------------------------------

prmtExpr :: Expr -> Kind -> DState Expr
prmtExpr expr k | k == Atom KBool = prmtExpr_ expr
                | otherwise = do
  ke <- infExpr expr
  case expr of
    ILit  n _ -> if k == ke then return expr else upcast expr k
    Var   v _ -> if k == ke then return expr else upcast expr k
    BinExpr op e1 e2 pos -> 
      BinExpr op <$> prmtExpr e1 k <*> prmtExpr e2 k <*> pure pos
    UnExpr op e pos -> UnExpr op <$> prmtExpr e k <*> pure pos
    App    f as pos -> upcast (App f as pos) k
    _ -> error $ progErr "prmtExpr"

prmtExpr_ :: Expr -> DState Expr
prmtExpr_ expr = do
  ke <- infExpr expr
  case expr of
    ILit  _ _ -> return expr
    BLit  _ _ -> return expr
    Var   _ _ -> return expr
    BinExpr op e1 e2 pos -> do 
      k1 <- infExpr e1
      k2 <- infExpr e2
      if isIK k1
        then do let k = maxInt k1 k2
                BinExpr op <$> prmtExpr e1 k <*> prmtExpr e2 k <*> pure pos
        else BinExpr op <$> prmtExpr_ e1 <*> prmtExpr_ e2 <*> pure pos
    UnExpr op e pos -> UnExpr op <$> prmtExpr_ e <*> pure pos
    -- In e enum pos -> do Atom (KEnum k) <- fst <$> lookupPi enum
    --                     In <$> prmtExpr e k <*> pure enum <*> pure pos
    App (Func "in") [e, Var c _] pos -> do
      (_, IEnum evs) <- lookupPi c
      prmtExpr_ $ L.foldl (\acc e' -> BinExpr Or acc (BinExpr Eq e e' pos) pos) 
                          (BinExpr Eq e (fst $ head evs) pos) 
                          (tail $ L.map fst evs)
    App f as  pos -> return $ App f as pos

upcast :: Expr -> Kind -> DState Expr
upcast e k = do
  ke <- infExpr e
  if not (ke `klt` k)
    then return e
    else case () of _ | Atom (KUInt is _) <- toV k, is > 8 -> return $ App (Func ("toU" ++ show is)) [e] dummyPos
                      | otherwise -> error $ progErr "upcast"

-------------------------------------------------------------------------------

infType :: Type -> DState Kind
infType Bool  = return $ Atom KBool
infType (UInt is en) = return $ Atom (KUInt is en)
infType (Array ty _) = Atom <$> KArray <$> infType ty
infType (CompTy id args) = do
  (del, _, _) <- getEnv
  case M.lookup id del of
    Nothing -> error $ progErr "infType"
    Just k  -> return $ toFull k

infExpr :: Expr -> DState Kind
infExpr (ILit  n _) = return $ fromJust $ decInt n 
infExpr (BLit  _ _) = return $ Atom KBool
infExpr (Var   v _) = toV <$> lookupGamma v
infExpr (BinExpr op e1 e2 _) = do
  k1 <- infExpr e1
  k2 <- infExpr e2
  if isIK k1 
    then if op `elem` [AddOp, SubOp, MulOp, DivOp, ModOp, BitOr, BitXor, BitAnd]
           then return $ maxInt k1 k2
           else return $ Atom KBool
    else return $ Atom KBool
infExpr (UnExpr op e _) = do
  k <- infExpr e
  if op `elem` [Plus, Minus, BitComp]
    then return k
    else return $ Atom KBool
infExpr (App f args _) = app <$> mapM infExpr args <*> (infFunc f <$> (infExpr $ head args))

infFunc :: Func -> Kind -> Kind
infFunc (Func "in"    ) _ = Arrow integral (Arrow (Atom $ KEnum integral) (Atom KBool)) 
infFunc (Func "length") _ = Arrow (Atom KAny) (Atom $ KUInt 32 View)
infFunc (Func "crc32" ) _ = Arrow (Atom KAny) (Atom $ KUInt 32 View)
infFunc (Func "toU16" ) k@(Atom (KUInt _ _)) = Arrow k (Atom $ KUInt 16 View)
infFunc (Func "toU24" ) k@(Atom (KUInt _ _)) = Arrow k (Atom $ KUInt 24 View)
infFunc (Func "toU32" ) k@(Atom (KUInt _ _)) = Arrow k (Atom $ KUInt 32 View)
infFunc (Func "toU64" ) k@(Atom (KUInt _ _)) = Arrow k (Atom $ KUInt 64 View)
infFunc f _ = error $ progErr "infFunc"

app :: [Kind] -> Kind -> Kind
app [] k = k
app (_:k) (_ `Arrow` k') = app k k'
app (_:_) (Atom _) = error $ progErr "app"



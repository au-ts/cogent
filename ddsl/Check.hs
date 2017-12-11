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
--
{-# LANGUAGE PatternGuards #-}

module Check (
  check,
  
  Err(..), 
  ErrPhase(..), 
  ErrMsg(..), 
  ErrKind(..), 
  ErrContext(..),

  KindClass(..),
  Value(..)  
) where

import Prelude as P hiding (mapM_)
import Control.Monad.State hiding (mapM_)
import Data.List as L (map, nub, sort, elemIndex, (!!))
import Data.Map as M hiding (null)
import Data.Maybe (isJust, fromJust)
import Data.Tuple.Select
import Data.Bits
import Data.Foldable (mapM_)

import Syntax as S
import Kinds
import Util

-------------------------------------------------------------------------------
-- Environments

type DState = State (Def, Env, [Err], Stack)

getDState :: DState (Def, Env, [Err], Stack)
getDState = gets id

putDState :: (Def, Env, [Err], Stack) -> DState ()
putDState e = modify (const e)

type Env = (Delta, Gamma, Pi)
-- Delta :: Type -> Kind
-- Gamma :: Variable -> Kind
-- Pi    :: Constant -> (Kind, Value)

modDel :: Ident -> Kind -> DState ()
modDel id k = modify (\(def, (del, gam, pii), errs, stack) ->  
                       (def, (adjust (const k) id del, gam, pii), errs, stack))

-------------------------------------------------------------------------------
-- Stack

type Stack = [(Ident, SourcePos)]

pushStack :: (Ident, SourcePos) -> DState ()
pushStack d = do
    (def, env, err, stack) <- getDState
    putDState (def, env, err, d:stack)

popStack :: DState (Ident, SourcePos)
popStack = do
    (def, env, err, stack) <- getDState
    putDState (def, env, err, tail stack)
    return $ head stack

getStackTop :: DState (Ident, SourcePos)
getStackTop = do
    (_, _, _, stack) <- getDState
    return $ head stack

-------------------------------------------------------------------------------
-- Level

getLevel :: Ident -> DState Level
getLevel id = do
    (def, _, _, _) <- getDState
    case M.lookup id def of
      Nothing -> error "ERROR: Undefined indentifier used in `getLevel'"
      Just (_, lv) -> return lv

putLevel :: Ident -> Level -> DState ()
putLevel id lv = do
    (def, envs, errs, stack) <- getDState
    case M.lookup id def of
      Nothing -> error "ERROR: Undefined indentifier used in `putLevel'"
      Just rec -> let def' = adjust (\rec -> (fst rec, lv)) id def
                  in putDState (def', envs, errs, stack)

liftLevel :: Ident -> Level -> DState ()
liftLevel id lv = do lv' <- getLevel id
                     if lv' > lv
                       then return ()
                       else putLevel id (lv + 1)

-------------------------------------------------------------------------------
-- Error handling

data Err = Err ErrPhase Ident ErrMsg ErrContext SourcePos

data ErrPhase = DepErr | WfkErr | ConErr

data ErrMsg = KindMismatch KindExpect KindActual
            | SizeMismatch SizeExpect SizeActual
            | PosMismatch  PosExpect  PosActual 
            | IntOutOfRange Integer
            | NoField
            | NoBField
            | NoCase
            | RedeclTopLevel Ident
            | CyclicType  Ident
            | UndeclType  Ident
            | RedeclVar   Ident
            | UndeclVar   Ident
            | CyclicConst Ident
            | UndeclConst Ident
            | UndeclFunc  Func
            | TooManyArgs (Either Func Type)
            | TooFewArgs  (Either Func Type)
            | NoArg       Func  -- Only applys to Func. FIXME: When type unsaturated, we merely say wrong type.
            | FuncNoStatic Func
            | VarNoStatic  Ident
            | CaseOverlap Case Case
            | TagOverlap  Case Case
            | NoTagInBUnion
            | DupTagInBUnion BField
            | BinOpKind BinOp ErrKind
            | ExprsKindMismatch (Expr, ErrKind) (Expr, ErrKind)
            | OtherErr String

type KindExpect = ErrKind
type KindActual = ErrKind
type SizeExpect = Integer
type SizeActual = Integer
type PosExpect  = Integer
type PosActual  = Integer

data ErrKind = JustKind Kind
             | AtMostKind  Kind
             | AtLeastKind Kind
             | KindClass KindClass
             | KindOfSize Integer
             | MiscKind String

data KindClass = BK  -- Base
               | IK  -- Integral
               | IVK -- Integral view
               | IPK -- Integral physical 
               | PK  -- Physical
               | AK  -- Atomic

data ErrContext = NoErrContext
                | ErrSizeOfBitfield
                | ErrSizeOfArr      Expr Type
                | ErrTypeOfSwitch   Type
                | ErrTypeOfBitfield Type
                | ErrTypeOfBUnion   Type
                | ErrTypeOfTypeSyn  Type
                | ErrTypeOfEnum     Type
                | ErrTypeOfConst    Type
                | ErrTypeOfArrElem  Type Type
                | ErrTypeOfCase     Type Case
                | ErrExpr           Expr
                | ErrParam          Param
                | ErrArg            Arg  (Either Func Type)
                | ErrEnumItem       Expr
                | ErrExprInConst    Expr
                | ErrField          Field
                | ErrBField         BField
                | ErrConstraint     Expr
                | ErrTagInCase      Expr Case
                | ErrSizeOfTag      Case
                | ErrPosOfTag       Case

addErrP_ :: ErrPhase -> ErrMsg -> ErrContext -> SourcePos -> DState ()
addErrP_ ph msg ctx pos = do (def, envs, errs, stack) <- getDState
                             let err = Err ph (fst $ head stack) msg ctx pos
                             putDState (def, envs, errs ++ [err], stack)

addErrP :: ErrPhase -> ErrMsg -> ErrContext -> SourcePos -> DState Kind
addErrP ph msg ctx pos = addErrP_ ph msg ctx pos >> return BadK


addErr_ :: ErrPhase -> ErrMsg -> ErrContext -> DState ()
addErr_ ph msg ctx = do
  (_, _, _, stack) <- getDState
  addErrP_ ph msg ctx (snd $ head stack)
 
addErr :: ErrPhase -> ErrMsg -> ErrContext -> DState Kind
addErr ph msg ctx = addErr_ ph msg ctx >> return BadK

-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------

check :: [Module] -> Either [Err] (Def, Delta, Pi)
check = flip check' (empty, empty, empty)

check' :: [Module] -> (Def, Delta, Pi) -> Either [Err] (Def, Delta, Pi)
check' [] e = Right e
check' (Module m h ds : ms) e = check1 ds e >>= check' ms

check1 :: [DataDesc] -> (Def, Delta, Pi) -> Either [Err] (Def, Delta, Pi)
check1 ds (def, del, pii) = 
  let (def0, err0) = initDef ds
      (def', (del', _, pii'), errs', _) = 
        execState (checkDs ds) (M.union def def0, (del, empty, pii), err0, [])
  in if length errs' == 0
       then Right (def', del', pii')
       else Left errs'

initDef :: [DataDesc] -> (Def, [Err])
initDef [] = (empty, [])
initDef (d:ds) = case M.lookup id def of
                   Nothing -> (insert id (d, -1) def, errs)
                   Just _  -> (def, errs ++ [err])
  where
    id = getIdent d
    (def, errs) = initDef ds
    err = Err DepErr id (RedeclTopLevel id) NoErrContext (getPos d)

-----------------------------------------------------------------------------------

checkDs :: [DataDesc] -> DState ()
checkDs [] = return ()
checkDs (d:ds) = do lv <- getLevel $ getIdent d
                    if lv == -1
                      then do checkD d 0
                              checkDs ds
                      else checkDs ds

checkD :: DataDesc -> Level -> DState ()
checkD d lv = do
  (def, (del, gam, pii), errs, stack) <- getDState
  when (notMember (getIdent d) del) $ do
    putDState (def, (del, empty, pii), errs, (getIdent d, getPos d):stack)  -- Giving a fresh Gamma
    case d of
      DStruct id ps fs tc _ -> do
        putLevel id lv
        ks <- checkParams ps
        checkTypeDecl ks id (Atom $ KStruct id)
        -- when (null fs && not allow_empty_struct_internal) $ 
        --   addErr_ WfkErr NoField NoErrContext  -- checked in Parser
        checkFields fs
        mapM_ (flip checkTypeCons $ Atom $ KStruct id) tc
      DBitfield id ps ty bfs tc _ -> do
        putLevel id lv
        ks <- checkParams ps
        checkTypeDecl ks id (Atom $ KBitfield id Nothing)
        kt <- getKind ty
        when (not $ isIPK kt) $
          addErr_ WfkErr (KindMismatch (KindClass IPK) (JustKind kt)) (ErrTypeOfBitfield ty)
        modDel id (Atom $ KBitfield id (Just kt))
        -- when (null bfs) $ addErr_ WfkErr NoBField NoErrContext
        checkBFields bfs kt
        mapM_ (flip checkTypeCons $ Atom $ KBitfield id Nothing) tc
        v  <- checkBFieldsSize bfs
        let v' = sizeInt kt
        when (v /= v') $
          addErr_ WfkErr (SizeMismatch v' v) ErrSizeOfBitfield
      DTUnion id ps t cs _ -> do
        putLevel id lv
        ks <- checkParams ps
        checkTypeDecl ks id (Atom $ KTUnion id)
        kt <- getKind t
        when (not $ isIPK kt) $
            addErr_ WfkErr (KindMismatch (KindClass IPK) (JustKind kt)) (ErrTypeOfSwitch t)
        -- when (null cs) $ addErr_ WfkErr NoCase NoErrContext
        checkCases cs kt
        return ()
      DBUnion id ps ty cs _ -> do
        putLevel id lv
        ks <- checkParams ps
        checkTypeDecl ks id (Atom $ KBUnion id Nothing Nothing)
        kt <- getKind ty
        when (not $ isIPK kt) $
          addErr_ WfkErr (KindMismatch (KindClass IPK) (JustKind kt)) (ErrTypeOfBUnion ty)
        modDel id (Atom $ KBUnion id (Just kt) Nothing)
        -- when (null cs) $ addErr_ WfkErr NoCase NoErrContext
        checkCases cs kt
        (p, s, k) <- checkTaggedCases cs
        modDel id (Atom $ KBUnion id (Just k) (Just (p, s)))
      DTypeSyn id ps ty tc _ -> do
        putLevel id lv
        ks <- checkParams ps
        kt <- getKind ty
        when (not $ isAK kt) $ 
          addErr_ WfkErr (KindMismatch (KindClass AK) (JustKind kt)) (ErrTypeOfTypeSyn ty)
        checkTypeDecl ks id kt
        mapM_ (flip checkTypeCons kt) tc
      DEnum id ty es _ -> do
        putLevel id lv
        kt <- getKind ty
        when (not $ isIK kt) $
          addErr_ WfkErr (KindMismatch (KindClass IK) (JustKind kt)) (ErrTypeOfEnum ty)
        kvs <- mapM (\e -> do (k, v) <- checkConstExpr e
                              when (not $ isIK k && k `kle` kt) $ 
                                addErr_ WfkErr 
                                        (KindMismatch (AtMostKind kt) (JustKind k))
                                        (ErrEnumItem e)
                              return (k, v)
                    ) es
        checkConstDecl id (Atom $ KEnum kt, toIEnum $ P.zip es $ P.map snd kvs) 
      DConst id ty expr _ -> do
        putLevel id lv
        kt <- getKind ty
        (k, v) <- checkConstExpr expr
        case () of _ | isIK kt && isIK k -> do
                         when (not $ k `kle` kt) $ 
                           addErr_ WfkErr (KindMismatch (AtMostKind kt) (JustKind k)) (ErrExprInConst expr)
                         checkConstDecl id (kt, v)
                     | kt == Atom KBool && k == Atom KBool ->
                         checkConstDecl id (k, v)
                     | otherwise -> do 
                         addErr_ WfkErr (KindMismatch (JustKind kt) (JustKind k)) (ErrTypeOfConst ty)
                         checkConstDecl id (BadK, BadV)
    (def', (del', _, pii'), errs', _) <- getDState
    putDState (def', (del', gam, pii'), errs', stack)
  where err = error $ progErr "checkD"
        toIEnum :: [(Expr, Value)] -> Value   -- Assume all good, do not throw errors
        toIEnum [] = IEnum []
        toIEnum (ev:evs) = case ev of
                           (e, IConst n) -> let IEnum vs = toIEnum evs
                                            in  IEnum ((e, n):vs)
                           otherwise -> toIEnum evs

checkTypeDecl :: [Kind] -> Ident -> Kind -> DState Kind
checkTypeDecl ks id k = do
  let k' = ks `parameteriseTo` k
  (def, (del, gam, pii), errs, stack) <- getDState
  case M.lookup id del of
    Just _  -> error $ progErr "checkTypeDecl"
    Nothing -> do putDState (def, (insert id k' del, gam, pii), errs, stack)
                  return k'

-- Will check unprocessed types
checkTypeUse :: Ident -> Bool -> DState Kind
checkTypeUse id b = do
  (def, (del, _, _), _, stack) <- getDState
  if id `elem` P.map fst stack
    then addErr DepErr (CyclicType id) NoErrContext
    else case M.lookup id del of
           Just k -> do lv <- getLevel id
                        liftLevel (fst $ head stack) lv
                        return k
           Nothing -> case M.lookup id def of
                        Just d -> if b then addErr DepErr (UndeclType id) NoErrContext
                                       else do checkD (fst d) 0
                                               checkTypeUse id True   -- Go to the other branch
                        Nothing -> addErr DepErr (UndeclType id) NoErrContext 

-- Returns kind of input type
getKind :: Type -> DState Kind
getKind Bool  = return $ Atom KBool
getKind (UInt is en) = return $ Atom (KUInt is en)
getKind ty@(Array t expr) = do
  k <- getKind t
  when (not $ isAK k) $
      addErr_ WfkErr (KindMismatch (KindClass AK) (JustKind k)) (ErrTypeOfArrElem t ty) 
  ke <- checkExpr expr
  when (not $ isIK ke) $
      addErr_ WfkErr (KindMismatch (KindClass IK) (JustKind ke)) (ErrSizeOfArr expr ty)
  when (Atom (KUInt 32 View) `klt` ke) $
      addErr_ WfkErr (KindMismatch (AtMostKind $ Atom $ KUInt 32 View) (JustKind ke)) (ErrSizeOfArr expr ty)
  return (Atom $ KArray k)
getKind t@(CompTy id args) = do
  k <- checkTypeUse id False
  ks <- mapM checkExpr args
  checkArgs (Right t) k $ zip args ks

checkVarDecl :: Ident -> Kind -> DState ()
checkVarDecl "_" _ = return ()    -- Seems unreachable
checkVarDecl id k =
  do (def, (del, gam, pii), errs, stack) <- getDState
     case M.lookup id gam of
         Just _  -> addErr_  DepErr (RedeclVar id) NoErrContext
         Nothing -> putDState (def, (del, insert id k gam, pii), errs, stack)

checkVarUse :: Ident -> DState Kind
checkVarUse id = do
  (_, (_, gam, pii), _, _) <- getDState
  case M.lookup id gam of
    Just k  -> return k
    Nothing -> do mkv <- checkConstUse id 
                  case mkv of 
                    Just kv -> return $ fst kv
                    Nothing -> addErr WfkErr (UndeclVar id) NoErrContext

checkConstDecl :: Ident -> (Kind, Value) -> DState ()
checkConstDecl id kv = do
  (def, (del, gam, pii), errs, stack) <- getDState
  case M.lookup id pii of
    Just _  -> error $ progErr "checkConstDecl"
    Nothing -> putDState (def, (del, gam, insert id kv pii), errs, stack)

checkConstUse :: Ident -> DState (Maybe (Kind, Value))
checkConstUse id = do
  (def, (_, _, pii), _, stack) <- getDState
  if id `elem` P.map fst stack
    then do addErr_ DepErr (CyclicConst id) NoErrContext
            return $ Just (BadK, BadV)
    else case M.lookup id pii of
           Just kv -> do lv <- getLevel id
                         liftLevel (fst $ head stack) lv
                         return $ Just kv
           Nothing -> case M.lookup id def of
                        Just d ->  do checkD (fst d) 0
                                      checkConstUse id  -- Go to the other branch
                        Nothing -> return Nothing

checkOpVar :: OpIdent -> Kind -> DState ()
checkOpVar oid k = mapM_ (flip checkVarDecl k) oid

checkFields :: [Field] -> DState ()
checkFields [] = return ()
checkFields (f:fs) = do checkField  f
                        checkFields fs
                        return ()

checkField :: Field -> DState ()
checkField f@(Field opId ty mc pos) = do
  kt <- getKind ty
  when (not $ isPK kt) $
      addErrP_ WfkErr (KindMismatch (KindClass PK) (JustKind kt)) (ErrField f) pos
  checkOpVar opId kt
  mapM_ checkCons mc

checkBFields :: [BField] -> Kind -> DState ()
checkBFields []     k = return ()
checkBFields (b:bs) k = do checkBField  b  k
                           checkBFields bs k

checkBField :: BField -> Kind -> DState ()
checkBField b@(BField t opId nb mc pos) k = do
  (ke, v) <- checkConstExpr nb
  when (not $ isIK ke) $
      addErrP_ WfkErr (KindMismatch (KindClass IK) (JustKind ke)) (ErrBField b) pos
  checkOpVar opId k
  mapM_ checkCons mc

checkCases :: [Case] -> Kind -> DState ([Ident],[Value])
checkCases [] _ = return ([], [])
checkCases (c:cs) kt = do
  (oid, v ) <- checkCase c kt
  (ids, vs) <- checkCases cs kt
  ids' <- if isJust oid
            then case (fromJust oid) `elemIndex` ids of
                   Just idx -> do addErrP_ WfkErr (CaseOverlap c (cs!!idx)) NoErrContext (cPosition c)
                                  return ids
                   Nothing  -> return (fromJust oid : ids)
            else return ids
  case v `elemIndex` vs of
    Just idx -> do addErrP_ WfkErr (TagOverlap c (cs!!idx)) NoErrContext (cPosition c)
                   return (ids', v:vs)
    Nothing  -> return (ids', v:vs)

checkCase :: Case -> Kind -> DState (OpIdent, Value)
checkCase c@(Case e f@(Field opId _ _ _) pos) kt = do
  (k, v) <- checkConstExpr e
  when (not $ isIK k) $ 
    addErrP_ WfkErr (KindMismatch (KindClass IK) (JustKind k)) (ErrTagInCase e c) pos
  when (not $ k `kle` kt) $ 
    addErrP_ WfkErr
      (KindMismatch (AtMostKind kt) (JustKind k)) 
      (ErrTagInCase e c) pos
  (_, (_, gam, _), _, _) <- getDState
  checkField f
  -- BE CAREFUL: don't add case identifier to Gamma
  modify (\(def, (del, _, pii), errs, s) -> (def, (del, gam, pii), errs, s))  
  return (opId, v)

checkTypeCons :: (Maybe Instance, Constraint) -> Kind -> DState ()
checkTypeCons (mi, c) k = do mapM_ (flip checkVarDecl k) mi
                             checkCons c

checkCons :: Constraint -> DState ()
checkCons expr = do ke <- checkExpr expr
                    when (ke /= Atom KBool) $
                      addErr_ WfkErr (KindMismatch (JustKind (Atom KBool)) (JustKind ke)) (ErrConstraint expr)

checkParams :: [Param] -> DState [Kind]
checkParams [] = return []
checkParams (p:ps) = do k <- checkParam p
                        ks <- checkParams ps
                        return (k:ks)

checkParam :: Param -> DState Kind
checkParam p@(opId, ty) = do
  k <- getKind ty
  when (not $ isAK k) $
    addErr_ WfkErr (KindMismatch (KindClass AK) (JustKind k)) (ErrParam p)
  mapM_ (flip checkVarDecl k) opId
  return $ toV k

{- Ident: Type/function name, for error message
   Kind : Kind of function
   [(Arg, Kind)]: Argument kind list
   Returns: Kind after application
-}
checkArgs :: Either Func Type -> Kind -> [(Arg, Kind)] -> DState Kind
checkArgs id k@(Atom _) [] = return k
checkArgs id (k `Arrow` ks) [] = addErr WfkErr (TooFewArgs  id) NoErrContext
checkArgs id (Atom _) (ak:aks) = addErr WfkErr (TooManyArgs id) NoErrContext
checkArgs id (k `Arrow` ks) (ak:aks) = if not $ (snd ak) `kcomp` k 
                                       then addErr WfkErr 
                                                   (KindMismatch (AtMostKind k) 
                                                                 (JustKind $ snd ak)) 
                                                   (ErrArg (fst ak) id)  
                                       else checkArgs id ks aks
checkArgs _ _ _ = return BadK

checkExpr :: Expr -> DState Kind
checkExpr (ILit n pos) = maybe (addErrP WfkErr (IntOutOfRange n) NoErrContext pos) return (decInt n) 
checkExpr (BLit _ _) = return $ Atom KBool
checkExpr (Var v _) = checkVarUse v >>= \k -> return $ toV k
checkExpr expr@(BinExpr op e1 e2 pos) = do
  k1 <- checkExpr e1
  k2 <- checkExpr e2
  case () of _ | isIK k1 && isIK k2 -> 
                   case () of _ | op `elem` [AddOp, SubOp, MulOp, DivOp, ModOp, BitOr, BitXor, BitAnd] ->
                                    return $ maxInt k1 k2
                                | op `elem` [Gt, Ge, Lt, Le, Eq, Ne] ->
                                    return $ Atom KBool
                                | otherwise -> 
                                    addErrP WfkErr 
                                            (BinOpKind op (MiscKind 
                                               "(Integral t0, Integral t1) => t0 -> t1 -> t")) 
                                            (ErrExpr expr) pos
               | (k1 == Atom KBool) && (k2 == Atom KBool) ->
                   if op `elem` [And, Or, Eq, Ne]
                     then return $ Atom KBool
                     else addErrP WfkErr 
                                  (BinOpKind op 
                                             (JustKind $ 
                                             (Atom KBool) `Arrow` (Atom KBool) `Arrow` (Atom KBool))) 
                                  (ErrExpr expr) pos
               | otherwise -> addErrP WfkErr (ExprsKindMismatch (e1, JustKind k1) (e2, JustKind k2))
                                             (ErrExpr expr) pos
checkExpr expr@(UnExpr op e pos) = do
  k <- checkExpr e
  case () of _ | op `elem` [Plus, Minus, BitComp] ->
                   if isIK k
                     then return k
                     else addErrP WfkErr (KindMismatch (KindClass IK) (JustKind k)) 
                                  (ErrExpr expr) pos
               | op `elem` [Not] ->
                   if k == Atom KBool
                     then return $ Atom KBool
                     else addErrP WfkErr (KindMismatch (JustKind $ Atom KBool) (JustKind k)) 
                                  (ErrExpr expr) pos
               | otherwise -> error $ progErr "checkExpr"
-- checkExpr expr@(In e enum pos) = do
--   (k, _) <- checkConstUse enum False
--   ke <- checkExpr e
--   when (not $ isIK ke) $ 
--     addErrP_ WfkErr (KindMismatch (KindClass IK) (JustKind ke)) (ErrInArg1 expr) pos
--   case k of 
--     Atom (KEnum k') | ke `kle` k' -> return $ Atom KBool
--                     | otherwise   -> addErrP WfkErr (KindMismatch (AtMostKind k') (JustKind ke)) (ErrInArg1 expr) pos
--     otherwise -> addErrP WfkErr (KindMismatch (MiscKind "Integral t => {t}") (JustKind k)) (ErrInArg2 expr) pos
checkExpr (App f args _) = checkFunc f args
checkExpr (Member v ms _) = undefined -- TODO


checkConstExpr :: Expr -> DState (Kind, Value)
checkConstExpr expr = do
  k <- checkExpr expr
  case expr of
    ILit  n _ -> return (k, IConst n)
    BLit  b _ -> return (k, BConst b)
    Var v pos -> do mkv <- checkConstUse v 
                    case mkv of
                      Nothing -> do addErrP_ ConErr (VarNoStatic v) (ErrExpr expr) pos
                                    return (BadK, BadV)
                      Just kv -> return kv
    BinExpr op e1 e2 _ -> do
      (_, v1) <- checkConstExpr e1
      (_, v2) <- checkConstExpr e2
      case op of
        Or     -> return (k, appValueBBB v1 v2 (||))
        And    -> return (k, appValueBBB v1 v2 (&&))
        Eq     -> return (k, BConst $ v1 == v2)
        Ne     -> return (k, BConst $ v1 /= v2)
        Gt     -> return (k, appValueIIB v1 v2 (>))
        Ge     -> return (k, appValueIIB v1 v2 (>=))
        Lt     -> return (k, appValueIIB v1 v2 (<))
        Le     -> return (k, appValueIIB v1 v2 (<=))
        BitOr  -> return (k, appValueIII v1 v2 (.|.))
        BitXor -> return (k, appValueIII v1 v2 (xor))
        BitAnd -> return (k, appValueIII v1 v2 (.&.))
        AddOp  -> return (k, appValueIII v1 v2 (+))
        SubOp  -> return (k, appValueIII v1 v2 (-))
        MulOp  -> return (k, appValueIII v1 v2 (*))
        DivOp  -> return (k, appValueIII v1 v2 div)
        ModOp  -> return (k, appValueIII v1 v2 mod)
    UnExpr op e _ -> do 
      (_, v) <- checkConstExpr e
      case op of
        Not     -> case v of
                     BConst b  -> return (k, BConst (not b))
                     otherwise -> error err
        Plus    -> return (k, appValueI v (0 +))
        Minus   -> return (k, appValueI v (0 -))
        BitComp -> return (k, appValueI v complement)
    -- In e enum _ -> do (_, v ) <- checkConstExpr e
    --                   (_, v') <- checkConstExpr (Const enum dummyPos)
    --                   case v' of 
    --                     (IEnum cvs) -> return (k, BConst $ v `elem` P.map (IConst . snd) cvs)
    --                     _ -> return (k, BadV)
    App f@(Func fn) args pos -> do 
      args' <- mapM checkConstExpr args
      if not $ BadK `elem` L.map fst args'
        then if fn `elem` ["length", "crc32"]  -- FIXME: might be constantable in the future
               then do addErrP_ ConErr (FuncNoStatic f) (ErrExpr expr) pos
                       return (BadK, BadV)
               else return (k, evalFunc f $ L.map snd args')
        else return (BadK, BadV)
  where err = progErr "checkExpr"

-- Returns the return type of function application
checkFunc :: Func -> [Arg] -> DState Kind
checkFunc f [] = addErr WfkErr (NoArg f) NoErrContext -- FIXME if partially applied expression is allowed
checkFunc f as@(a:_) = do (k:ks) <- mapM checkExpr as
                          fk <- funcKind f k
                          checkArgs (Left f) fk $ zip as (k:ks)

-- Works like a dictionary: looks up particular function kind given a key 
funcKind :: Func -> Kind -> DState Kind
funcKind (Func "in") _ = return $ Arrow integral (Arrow (Atom $ KEnum integral) (Atom KBool)) 
funcKind (Func "length") _ = return $ Arrow (Atom KAny) (Atom $ KUInt 32 View)
funcKind (Func "crc32" ) _ = return $ Arrow (Atom KAny) (Atom $ KUInt 32 View)
funcKind (Func "toU16" ) k@(Atom (KUInt _ _)) = return $ Arrow k (Atom $ KUInt 16 View)
funcKind f@(Func "toU24" ) k@(Atom (KUInt _ _)) = 
  if allow_u24_internal then return $ Arrow k (Atom $ KUInt 24 View)
                        else addErr WfkErr (UndeclFunc f) NoErrContext
funcKind (Func "toU32" ) k@(Atom (KUInt _ _)) = return $ Arrow k (Atom $ KUInt 32 View)
funcKind (Func "toU64" ) k@(Atom (KUInt _ _)) = return $ Arrow k (Atom $ KUInt 64 View)
funcKind f _ = addErr WfkErr (UndeclFunc f) NoErrContext

-----------------------------------------------------------------------------------

checkBFieldsSize :: [BField] -> DState Integer
checkBFieldsSize [] = return 0
checkBFieldsSize (b:bs) = do v  <- checkBFieldSize b
                             vs <- checkBFieldsSize bs
                             return (v + vs)

checkBFieldSize :: BField -> DState Integer
checkBFieldSize (BField _ _ expr _ _) = do
  (_, v) <- checkConstExpr expr
  let IConst n = v
  return n

checkTaggedCases :: [Case] -> DState (Position, Size, Kind)
checkTaggedCases [] = return (0, 0, BadK)
checkTaggedCases (c:cs) = do (p, s, k) <- checkTaggedCase c
                             checkTaggedCases' cs (p, s, k)

checkTaggedCases' :: [Case] -> (Position, Size, Kind) -> DState (Position, Size, Kind)
checkTaggedCases' [] psk = return psk
checkTaggedCases' (c:cs) (p, s, k) = do
  (p', s', k') <- checkTaggedCase c
  when (p /= p') $
    addErrP_ WfkErr (PosMismatch p p') (ErrPosOfTag c) pos
  when (s /= s') $
    addErrP_ WfkErr (SizeMismatch s s') (ErrSizeOfTag c) pos
  when (k /= k') $
    addErrP_ WfkErr (KindMismatch (JustKind k) (JustKind k')) (ErrTypeOfCase ty c) pos
  checkTaggedCases' cs (p, s, k)
  where (Case _ (Field _ ty _ _) pos) = c

checkTaggedCase :: Case -> DState (Position, Size, Kind)
checkTaggedCase (Case e f _) = do 
  ke <- checkExpr e
  (p, s, k) <- checkTaggedField f
  return (p, s, k)

checkTaggedField :: Field -> DState (Position, Size, Kind)
checkTaggedField f@(Field _ ty _ pos) = do
  (def, _, _, _) <- getDState
  k <- getKind ty
  case k of
    Atom (KBitfield id _) -> do
        case M.lookup id def of  -- CAUTION: lookup Def
          Nothing  -> error $ progErr "checkTaggedField"
          Just rec -> checkTaggedBitfield (sel1 rec)
    k -> do addErrP_ WfkErr (KindMismatch (JustKind (Atom (KBitfield "_" Nothing))) (JustKind k))
                    (ErrField f) pos
            return (0, 0, BadK)

checkTaggedBitfield :: DataDesc -> DState (Position, Size, Kind)
checkTaggedBitfield d@(DBitfield id _ t bs _ pos) = do
  pushStack (id, pos)
  (p, s) <- checkBFieldsTaggedness bs
  popStack
  k <- getKind t
  modDel id $ Atom (KBitfield id (Just k))
  return (p, s, k)
checkTaggedBitfield _ = error $ progErr "checkTaggedBitfield"

checkBFieldsTaggedness :: [BField] -> DState (Position, Size)
checkBFieldsTaggedness [] = error $ progErr "checkBFieldsTaggedness"
checkBFieldsTaggedness bs = do
  let (bs1, bs2) = break (\b -> tag (bfTag b)) bs
  p <- checkUntaggedBFields1 bs1 0
  if null bs2
    then do addErr_ WfkErr NoTagInBUnion NoErrContext
            return (p, 0)
    else do let (BField _ _ expr _ _) = head bs2
            (_, IConst s) <- checkConstExpr expr
            checkUntaggedBFields2 $ tail bs2
            return (p, s)

checkUntaggedBFields1 :: [BField] -> Position -> DState Position
checkUntaggedBFields1 [] n = return n
checkUntaggedBFields1 ((BField _ _ expr _ _):bs) n = do
  (_, IConst v) <- checkConstExpr expr
  checkUntaggedBFields1 bs (n + v)

checkUntaggedBFields2 :: [BField] -> DState ()
checkUntaggedBFields2 [] = return ()
checkUntaggedBFields2 (b@(BField t opId expr _ pos):bs) | Tag t' <- t = do
  when t' $ addErrP_ WfkErr (DupTagInBUnion b) NoErrContext pos
  checkUntaggedBFields2 bs


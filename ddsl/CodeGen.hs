{-# LANGUAGE DeriveDataTypeable, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}

module CodeGen (gen) where

import Prelude as P hiding (foldr) 
import Syntax as DS
import Check
import Pretty
import Kinds
import Util
import COGENT.Syntax  as CS
import COGENT.Types   as CT
import COGENT.PrettyPrint

import Data.Bits
import Data.Char as C
import Data.Digits (unDigits, digits)
import Data.Foldable as F (toList)
import Data.List as L
import Data.Maybe
import Data.Map as M
import qualified Data.Traversable as T (mapM)
import Data.Tuple.Select
import Control.Applicative ((<$>), (<*>), pure)
import Control.Monad 
import Control.Monad.State 
import Text.PrettyPrint.ANSI.Leijen (pretty, plain)
import System.FilePath (replaceExtension)


type DState = State (Delta, Theta, Pi)
type Theta = Map Ident (VarSource, DS.Type)  -- local var -> (source of decl, type)
data VarSource = FromPara | FromField | FromCase | FromInst | FromBField Position Size | FromConst

getDState :: DState (Delta, Theta, Pi)
getDState = gets id

putDState :: (Delta, Theta, Pi) -> DState ()
putDState e = modify (const e)

lookupDel :: Ident -> DState Kind
lookupDel id = do
  (del, _, _) <- getDState
  case M.lookup id del of
    Nothing -> error $ progErr "lookupDel"
    Just k -> return k

insertTheta :: Ident -> (VarSource, DS.Type) -> DState ()
insertTheta id (s, t) = do
  (del, the, pii) <- getDState
  putDState (del, M.insert id (s, t) the, pii)

lookupTheta :: Ident -> DState (VarSource, DS.Type)
lookupTheta id = do
  (_, the, pii) <- getDState
  case M.lookup id the of
    Nothing -> case M.lookup id pii of
                 Nothing -> error $ progErr "lookupTheta"
                 Just kv -> return (FromConst, lowerKind $ fst kv)
    Just v  -> return v

lookupPi :: Ident -> DState (Maybe (Kind, Value))
lookupPi id = do
  (_, _, pii) <- getDState
  case M.lookup id pii of
    Nothing -> return Nothing
    Just kv -> return $ Just kv

-------------------------------------------------------------------------------

isPrim :: DS.Type -> DState Bool
isPrim (DS.Array _ _) = return False
isPrim (CompTy id _) = do
  (del, _, _) <- getDState
  case M.lookup id del of
    Nothing -> error $ progErr "isPrim"
    Just k  -> return $ isPrimK $ toFull k
isPrim _ = return True

infType :: DS.Type -> DState Kind
infType DS.Bool  = return $ Atom KBool
infType (UInt is en) = return $ Atom (KUInt is en)
infType (DS.Array ty _) = Atom <$> KArray <$> infType ty
infType (CompTy id args) = do  -- lookupDelta
  (del, _, _) <- getDState
  case M.lookup id del of
    Nothing -> error $ progErr "infType"
    Just k  -> return $ toFull k

{-
bkToType :: Kind -> CS.BaseType
bkToType k@(Atom s) | isBK k = PrimType (s2t s)
  where s2t :: Singleton -> PrimType
        s2t KBool = CS.Bool
        s2t s     = Unsigned $ fromIntegral $ sizeInt (Atom s) 
bkToType _ = error $ progErr "bkToType"
-}

-------------------------------------------------------------------------------
-- Main Generation Procedure

-- FIXME: zilinc: fix malloc functions

type RD = CS.Definition RawStmt RawExpr

gen :: [DataDesc] -> (Delta, Pi) -> [RD]
gen ds (del, pii) = 
  (Include lib_dir) :  -- It asks the user to change to correct path. Default is .
  (fst $ runState (concat <$> mapM genD ds) (del, M.empty, pii))

genD :: DataDesc -> DState [RD]
-- Struct
genD d@(DStruct id ps fs tc _) = do 
  envs    <- getDState
  thetaD d
  typedef <- genRecord id fs
  malloc  <- genStructMalloc id ps fs
  free    <- return $ genFree id
  serFunc <- genStructSer d
  desFunc <- genStructDes d
  putDState envs
  return [typedef, malloc, free, serFunc, desFunc]

-- Bitfield
genD d@(DBitfield id ps ty bfs tc _) = do
  envs <- getDState
  thetaD d
  typedef <- genTypeDef id ty
  malloc  <- genTypeSynMalloc id ps ty
  free    <- genTypeSynFree id ty
  unbox   <- genTypeSynUnbox id ty
  serFunc <- genBitfieldSer d
  desFunc <- genBitfieldDes d
  putDState envs
  return $ [typedef] ++ maybeToList malloc ++ [free] ++ 
           maybeToList unbox ++ [serFunc, desFunc]

-- TUnion
genD d@(DTUnion id ps ty cs _) = do
  envs    <- getDState
  thetaD d
  typedef <- genVariant id cs
  free    <- return $ genFree id
  serFunc <- genTUnionSer d
  desFunc <- genTUnionDes d
  putDState envs
  return $ [typedef, free, serFunc, desFunc]

-- BUnion
genD d@(DBUnion id ps ty cs _) = do
  envs <- getDState
  thetaD d
  typedef <- genTypeDef id ty
  malloc  <- genTypeSynMalloc id ps ty
  free    <- genTypeSynFree id ty
  unbox   <- genTypeSynUnbox id ty
  serFunc <- genBUnionSer d
  desFunc <- genBUnionDes d
  putDState envs
  return $ [typedef] ++ maybeToList malloc ++ [free] ++ 
           maybeToList unbox ++ [serFunc, desFunc]

-- Typedef
genD d@(DTypeSyn id ps ty@(DS.Array t e) tc _) = do
  envs <- getDState
  thetaD d
  typedef <- genTypeDef id ty
  free    <- return $ genFree id
  serFunc <- genArrSer d
  desFunc <- genArrDes d
  putDState envs
  return [typedef, free, serFunc, desFunc]

genD d@(DTypeSyn id ps ty tc _) = do
  envs <- getDState
  thetaD d
  typedef <- genTypeDef id ty
  malloc  <- genTypeSynMalloc id ps ty  -- CHECK: seems only primitive types need malloc
  free    <- genTypeSynFree id ty       -- CHECK: seems always need to free
  unbox   <- genTypeSynUnbox id ty      -- CHECK: only primitive types need unbox
  serFunc <- genTypeSynSer d
  desFunc <- genTypeSynDes d
  putDState envs
  return $ [typedef] ++ maybeToList malloc ++ [free] ++
           maybeToList unbox ++ [serFunc, desFunc]

-- Const
genD d@(DConst id ty e _) = do
  e' <- genExprSer e
  ty' <- genRWType ty
  return [CS.Constant (toConst $ toName id) ty' e']

genD d@(DEnum id ty es _) = return []

-------------------------------------------------------------------------------
-- Collect Theta

thetaD :: DataDesc -> DState ()
thetaD (DStruct id ps fs tc _) = do
  thetaParams ps
  thetaFields fs
  thetaTyCons tc id
thetaD (DBitfield id ps ty bfs tc _) = do
  thetaParams ps
  thetaBFields ty bfs 0
  thetaTyCons tc id
thetaD (DTUnion id ps ty cs _) = do
  thetaParams ps
  thetaCases  cs
thetaD (DBUnion id ps ty cs _) = do
  thetaParams ps
  thetaCases  cs
thetaD (DTypeSyn id ps ty tc _) = do
  thetaParams ps
  thetaTyCons tc id
thetaD _ = return ()

thetaParams :: [Param] -> DState ()
thetaParams [] = return ()
thetaParams (p:ps) = thetaParam p >> thetaParams ps

thetaParam :: Param -> DState ()
thetaParam (Nothing, _ ) = return ()  -- FIXME: can be dropped
thetaParam (Just id, ty) = insertTheta id (FromPara, ty)

thetaFields :: [Field] -> DState ()
thetaFields [] = return ()
thetaFields (f:fs) = thetaField f >> thetaFields fs

thetaField :: Field -> DState ()
thetaField (Field (Just id) ty _ _) = insertTheta id (FromField, ty)

thetaBFields :: DS.Type -> [BField] -> Position -> DState ()
thetaBFields _ [] _ = return ()
thetaBFields ty (bf:bfs) p = 
  thetaBField  ty bf  p >>= \p' ->
  thetaBFields ty bfs p'

thetaBField :: DS.Type -> BField -> Position -> DState Position
thetaBField ty (BField _ (Just id) s _ _) p = do
  IConst s' <- evalConst s
  insertTheta id (FromBField p s', ty)
  return (p + s')

thetaCases :: [Case] -> DState ()
thetaCases cs = mapM_ thetaCase cs

thetaCase :: Case -> DState ()
thetaCase (DS.Case t (Field (Just id) ty _ _) _) = do
  insertTheta id (FromCase, ty)

thetaTyCons :: TyConstraint -> Ident -> DState ()
thetaTyCons (Just (Just ins, _)) ty = insertTheta ins (FromInst, CompTy ty [])
thetaTyCons _ _ = return ()

-------------------------------------------------------------------------------
-- Struct

genRecord :: Ident -> [Field] -> DState RD
genRecord id fs = TypeDef (toName id) <$> (Record <$>
                    (mapM (\(Field id ty _ _) -> (,) <$> pure (toName id) 
                                                     <*> ((,) <$> genRWType ty <*> pure False)) fs))

genStructMalloc :: Ident -> [Param] -> [Field] -> DState RD
genStructMalloc id ps fs = do
  ps' <- mapM (\(_, ty) -> genRWType ty) ps
  fs' <- mapM (\(Field _ ty _ _) -> genRWType ty) fs
  return $ AbstractProto (genFuncName (CompTy id []) FuncMalloc) (fs' ++ ps')  
                         (CanFail [Linear $ UserDefined (toName id)] [])

genStructSer :: DataDesc -> DState RD
genStructSer (DStruct id ps fs tc _) = do
  vt  <- genROType (CompTy id [])
  ps' <- (++) <$> pure [(varVal, vt),
                        (varBuf, Linear  $ UserDefined typeBuf),
                        (varIdx, Unboxed $ UserDefined typeIdx)] 
              <*> genParams ps
  tc' <- genTyConsSer tc
  fs' <- mapM genFieldSer fs
  let stmtsSer = tc' ++ concat fs'
  return $ Binding (genFuncName (CompTy id []) FuncSerialise) ps'
                   (CanFail [Linear $ UserDefined typeBuf, Unboxed $ UserDefined typeIdx]
                            [Linear $ UserDefined typeBuf])
                   (foldDoStmtsR stmtsSer $ returnR [varR varBuf, varR varIdx]) 

genStructDes :: DataDesc -> DState RD
genStructDes (DStruct id ps fs tc _) = do
  ps' <- (++) <$> pure [(varBuf, Shareable $ UserDefined typeBuf),
                        (varIdx, Unboxed   $ UserDefined typeIdx)] 
              <*> genParams ps
  tc' <- genTyConsDes id tc
  fs' <- concat <$> zipWithM genFieldDes fs (inits fs)
  let stmtsDes = fs' ++ [genStructMallocApp id ps fs] ++ tc'
  return $ Binding (genFuncName (CompTy id []) FuncDeserialise) ps'
                   (CanFail [Linear $ UserDefined $ toName id, Unboxed $ UserDefined $ typeIdx] [])
                   (foldDoStmtsR stmtsDes $ returnR [varR varVal, varR varIdx]) 

genFieldSer :: Field -> DState [RawStmt]
genFieldSer (Field id ty cons _) = do
  cons' <- genMConsSer cons
  id'   <- genExprSer (DS.Var (toName id) dummyPos)
  as    <- genArgsSer ty
  return $ maybeToList cons' ++ 
    [bindErrR (appR (genFuncName ty FuncSerialise) $
                    [id', varR varBuf, varR varIdx] ++ as) 
              ([varBuf, varIdx], undefined)
              ([varBuf], failR [varR varBuf])]

-- genFieldDes :: the field to des -> earlier fields -> return type
genFieldDes :: Field -> [Field] -> DState [RawStmt]
genFieldDes f@(Field id ty cons _) fs = do
  id'   <- genExprDes (DS.Var (toName id) dummyPos)
  as    <- genArgsDes ty
  frees <- foldDoStmtsR 
           <$> (concat <$> mapM genFieldFree fs)
           <*> pure (failR [])
  frees' <- foldDoStmtsR 
            <$> (concat <$> mapM genFieldFree (fs ++ [f]))
            <*> pure (failR [])
  cons' <- genMConsDes_ cons frees'
  return $ [bindErrR (appR (genFuncName ty FuncDeserialise) $
                           [varR varBuf, varR varIdx] ++ as)
                     ([toName id, varIdx], undefined)
                     ([], frees)] ++ maybeToList cons'

genFieldFree :: Field -> DState [RawStmt]
genFieldFree (Field id ty _ _) =
  isPrim ty >>= \b -> case b of
    True  -> return []
    False -> return $ bindSucR (appR (genFuncName ty FuncFree) [varR $ toName id])
                               ([], undefined) : []

genStructMallocApp :: Ident -> [Param] -> [Field] -> RawStmt
genStructMallocApp id ps fs = 
  let fs' = L.map (\(Field fid _ _ _) -> varR $ toName fid) fs
      ps' = L.map (\(pid, _) -> varR $ toName pid) ps
  in bindErrR (appR (genFuncName (CompTy id []) FuncMalloc) (fs' ++ ps'))
              ([varVal], undefined)
              ([], failR []) 

---------------------------------------
-- Bitfield

genBitfieldSer :: DataDesc -> DState RD
genBitfieldSer (DBitfield id ps ty bfs tc _) = do 
  let vt = Unboxed $ UserDefined (toName id)
  ps' <- (++) <$> pure [(varVal, vt),
                        (varBuf, Linear  $ UserDefined typeBuf),
                        (varIdx, Unboxed $ UserDefined typeIdx)] 
              <*> genParams ps
  bfcs <- concat <$> mapM (return . F.toList <=< genMConsSer . bfConstraint) bfs
  tc' <- genTyConsSer tc
  inSer <- genTypeSer ty
  let stmtsSer = bfcs ++ tc'
  return $ Binding (genFuncName (CompTy id []) FuncSerialise) ps'
                   (CanFail [Linear $ UserDefined typeBuf, Unboxed $ UserDefined typeIdx] 
                            [Linear $ UserDefined typeBuf]) 
                   (foldDoStmtsR stmtsSer inSer)

genBitfieldDes :: DataDesc -> DState RD
genBitfieldDes (DBitfield id ps ty bfs tc _) = do
  ps' <- (++) <$> pure [(varBuf, Shareable $ UserDefined typeBuf),
                        (varIdx, Unboxed   $ UserDefined typeIdx)]
              <*> genParams ps
  inDes <- genTypeDes ty
  bfcs <- concat <$> mapM (return . F.toList <=< genMConsDes . bfConstraint) bfs
  tc' <- genTyConsDes id tc
  let stmtsDes = inDes : bfcs ++ tc'
  return $ Binding (genFuncName (CompTy id []) FuncDeserialise) ps'
                   (CanFail [Unboxed $ UserDefined (toName id), Unboxed $ UserDefined typeIdx] [])
                   (foldDoStmtsR stmtsDes $ returnR [varR varVal, varR varIdx]) 

---------------------------------------
-- TUnion

genVariant :: Ident -> [Case] -> DState RD
genVariant id cs = return $ 
  TypeDef (toName id) (Variant $ genVariantBranches cs) 

genVariantBranches :: [Case] -> [(TagName, BaseType)]
genVariantBranches cs = 
  L.map (\(DS.Case _ (Field id ty _ _) _) -> (toTag id, genType ty)) cs

{- Variants are unboxed so no need to malloc
genVariantMalloc :: Ident -> [Param] -> [Case] -> DState [RD]
genVariantMalloc id ps cs = do
  mapM (\c -> genCaseMalloc id ps c) cs
  where genCaseMalloc :: Ident -> [Param] -> Case -> DState RD
        genCaseMalloc id ps (e, (Just cid, ty, _)) = do
          ps' <- L.map snd <$> genParams ps
          return $ AbstractProto (genFuncName (CompTy (toName (id, cid)) []) FuncMalloc)
                                 (Linear (genType ty) : ps')
                                 (CanFail [Linear $ UserDefined (toName id)] [])

genVariantFree :: Ident -> DState RD
genVariantFree id = return $ 
  AbstractProto (genFuncName (CompTy id []) FuncFree)
                [Linear $ UserDefined (toName id)] 
                (CannotFail [])
-}

genTUnionSer :: DataDesc -> DState RD
genTUnionSer (DTUnion id ps t cs _) = do
  vt  <- genROType (CompTy id [])
  ps' <- (++) <$> pure [(varVal, vt),
                        (varBuf, Linear  $ UserDefined typeBuf),
                        (varIdx, Unboxed $ UserDefined typeIdx)] 
              <*> genParams ps
  Binding (genFuncName (CompTy id []) FuncSerialise) ps'
          (CanFail [Linear $ UserDefined typeBuf, Unboxed $ UserDefined typeIdx]
                   [Linear $ UserDefined typeBuf]) <$>
          (caseR (varR varVal) <$>
                 (mapM (\c@(DS.Case e (Field cid _ _ _) _) -> do 
                          stmts <- genCaseStmtsSer t c
                          return (toTag cid, toName cid, stmts)) cs))

genTUnionDes :: DataDesc -> DState RD
genTUnionDes (DTUnion id ps t cs _) = do
  ps' <- (++) <$> pure [(varBuf, Shareable $ UserDefined typeBuf),
                        (varIdx, Unboxed   $ UserDefined typeIdx)]
              <*> genParams ps
  as <- genArgsDes t
  let tagDes = bindErrR (appR (genFuncName t FuncDeserialise) $
                              [varR varBuf, varR varIdx] ++ as) 
                        ([varTag, varIdx], undefined)
                        ([varIdx], failR [])
  cases <- mapM (\c -> do tagExpr <- genExprDes $ cCase c
                          ifR (opR "==" [varR varTag, tagExpr]) 
                              <$> (genCaseStmtsDes id ps t c) 
                              <*> pure undefined 
                ) cs
  return $ Binding (genFuncName (CompTy id []) FuncDeserialise) ps'
                   (CanFail [Linear $ UserDefined $ toName id, Unboxed $ UserDefined typeIdx] [])
                   (foldDoStmtsR [tagDes] $ 
                      foldIfStmtsR cases (RS $ Fail (constR unhandled_tag) [varR varIdx]))

genCaseStmtsSer :: DS.Type -> Case -> DState RawStmt
genCaseStmtsSer ts (DS.Case e (Field id ty mc _) _) = do
  tagExpr <- genExprSer e
  ats <- genArgsSer ts
  assert <- genMConsSer mc
  let tagSer = bindErrR (appR (genFuncName ts FuncSerialise) $ 
                              [tagExpr, varR varBuf, varR varIdx] ++ ats)
                        ([varBuf, varIdx], undefined)
                        ([varBuf], failR [varR varBuf])
  valSer <- genArgsSer ty >>= \as ->
            isPrim ty >>= \b -> return $
            if b then [bindSucR (appR (genFuncName (genType ty) FuncUnbox) [varR (toName id)])
                                ([toName id], undefined)] ++ maybeToList assert ++
                      [bindErrR (appR (genFuncName ty FuncSerialise) $
                                      [varR (toName id), varR varBuf, varR varIdx] ++ as)
                                ([varBuf, varIdx], undefined)
                                ([varBuf], failR [varR varBuf])]
                 else [bindErrR (appR (genFuncName ty FuncSerialise) $
                                      [varR (toName id), varR varBuf, varR varIdx] ++ as)
                                ([varBuf, varIdx], undefined)
                                ([varBuf], failR [varR varBuf])]
  return $ foldDoStmtsR (tagSer : valSer) 
                        (returnR [varR varBuf, varR varIdx]) 

genCaseStmtsDes :: Ident -> [Param] -> DS.Type -> Case -> DState RawStmt
genCaseStmtsDes id ps ts (DS.Case e (Field cid ty mc _) _) = do
  ats <- genArgsDes ty  -- arguments for value malloc
  let valDes = bindErrR (appR (genFuncName ty FuncDeserialise) $ [varR varBuf, varR varIdx] ++ ats) 
                        ([toName cid, varIdx], undefined) 
                        ([], failR [])
  assert <- genMConsDes mc
  b <- isPrim ty
  let as = L.map (\(id, _) -> varR $ toName id) ps 
  if b then genArgsDes ty >>= \atys -> return $
            foldDoStmtsR (valDes : maybeToList assert ++
                          [bindErrR (appR (genFuncName (genType ty) FuncMalloc) $ 
                                          [varR $ toName cid] ++ atys)
                                    ([prime $ toName cid], undefined) 
                                    ([], failR [])])
                         (returnR [vlitR (UserDefined $ toName id) 
                                         (toTag cid) (varR $ prime $ toName cid), 
                                   varR varIdx])
       else let free = bindSucR (appR (genFuncName (genType ty) FuncFree) 
                                      [varR $ toName cid])
                                ([], failR [])
                assert' = fmap (\(RS (Bind s (HandleError next (v, vs, _)))) -> 
                                  RS (Bind s (HandleError next (v, vs, free)))) assert
            in return $ foldDoStmtsR (valDes : maybeToList assert')
                                     (returnR [vlitR (UserDefined $ toName id) 
                                                     (toTag cid) (varR $ toName cid), 
                                               varR varIdx])

---------------------------------------
-- BUnion

genBUnionSer :: DataDesc -> DState RD
genBUnionSer (DBUnion id ps ty cs _) = do
  ps' <- (++) <$> pure [(varVal, Unboxed $ UserDefined $ toName id),
                        (varBuf, Linear  $ UserDefined typeBuf  ),
                        (varIdx, Unboxed $ UserDefined typeIdx  )]
              <*> genParams ps
  Atom (KBUnion _ _ (Just (p, s))) <- lookupDel id
  ts <- mapM (genExprSer . cCase) cs
  let e    = opR (bitmask ++ toName (genType ty))
                 [varR varVal, ilitR $ psToDec (p, s) (genType ty)]
      cdtn = L.foldl (\acc t -> opR (toName Or) [acc, opR (toName Eq) [e, t]]) 
                     (opR (toName Eq) [e, head ts]) 
                     (tail ts)
  return $ Binding (genFuncName (CompTy id []) FuncSerialise) ps'
                   (CanFail [Linear $ UserDefined typeBuf, Unboxed $ UserDefined typeIdx]
                            [Linear $ UserDefined typeBuf])
                   (ifR cdtn 
                        (appR (genFuncName ty FuncSerialise) [varR varVal, varR varBuf, varR varIdx])
                        (failR_ (constR unhandled_tag) [varR varBuf]))

genBUnionDes :: DataDesc -> DState RD
genBUnionDes (DBUnion id ps ty cs _) = do 
  ps' <- (++) <$> pure [(varBuf, Shareable $ UserDefined typeBuf),
                        (varIdx, Unboxed   $ UserDefined typeIdx)]
              <*> genParams ps
  Atom (KBUnion _ _ (Just (p, s))) <- lookupDel id
  ts <- mapM (genExprDes . cCase) cs
  let e    = opR (bitmask ++ toName (genType ty))
                 [varR varVal, ilitR $ psToDec (p, s) (genType ty)]
      cdtn = L.foldl (\acc t -> opR (toName Or) [acc, opR (toName Eq) [e, t]]) 
                     (opR (toName Eq) [e, head ts]) 
                     (tail ts)
      ser = bindErrR (appR (genFuncName ty FuncDeserialise) [varR varBuf, varR varIdx])
                     ([varVal, varIdx], undefined)
                     ([varIdx], failR [])
      chk = ifR cdtn (returnR [varR varVal, varR varIdx])
                     (failR_ (constR unhandled_tag) [])
  return $ Binding (genFuncName (CompTy id []) FuncDeserialise) ps'
                   (CanFail [Unboxed $ UserDefined $ toName id, Unboxed $ UserDefined typeIdx] [])
                   (foldDoStmtsR [ser] chk)

---------------------------------------
-- Array

genArrSer :: DataDesc -> DState RD
genArrSer (DTypeSyn id ps ty@(DS.Array t e) Nothing _) = do
  ps' <- (++) <$> pure [(varVal, Shareable $ Bang $ UserDefined $ toName id),
                        (varBuf, Linear  $ UserDefined typeBuf),
                        (varIdx, Unboxed $ UserDefined typeIdx)]
              <*> genParams ps
  let serElems = bindErrR (appR (genFuncName t FuncSerialise) [varR varItr, varR varBuf, varR varIdx])
                          ([varBuf, varIdx], returnR [varR varBuf, varR varIdx])
                          ([varBuf], failR [varR varBuf, varR varIdx])
      for = (forR [varItr, varBuf, varIdx] 
                  (foldWithR (varR varVal) [varR varBuf, varR varIdx])
                  serElems)
      ser = bindErrR for ([varBuf, varIdx], returnR [varR varBuf, varR varIdx])
                         ([varBuf, varIdx], failR [varR varBuf])
  return $ Binding (genFuncName (CompTy id []) FuncSerialise) ps'
                   (CanFail [Linear $ UserDefined typeBuf, Unboxed $ UserDefined typeIdx] 
                            [Linear $ UserDefined typeBuf]) ser
genArrSer _ = error $ progErr "genArrSer"

genArrDes :: DataDesc -> DState RD
genArrDes (DTypeSyn id ps ty@(DS.Array t e) Nothing _) = do
  ps' <- (++) <$> pure [(varBuf, Shareable $ UserDefined typeBuf),
                        (varIdx, Unboxed   $ UserDefined typeIdx)]
              <*> genParams ps
  -- TODO: zilinc: malloc inside
  let desElems = bindErrR (appR (genFuncName t FuncDeserialise) [varR varItr, varR varBuf, varR varIdx])
                          ([varBuf, varIdx], returnR [varR varBuf, varR varIdx])
                          ([varBuf], failR [varR varBuf, varR varIdx])
      for = (forR [varItr, varBuf, varIdx]
                  (foldWithR (varR varVal) [varR varBuf, varR varIdx])
                  desElems)
      des = bindErrR for ([varVal, varIdx], returnR [varR varVal, varR varIdx])
                         ([varVal, varIdx], failR [])
  return $ Binding (genFuncName (CompTy id []) FuncDeserialise) ps'
                   (CanFail [Linear $ UserDefined $ toName id, Unboxed $ UserDefined typeIdx] []) des
genArrDes _ = error $ progErr "genArrDes"

----------------------------------------
-- Type Synonym

genTypeDef :: Ident -> DS.Type -> DState RD
genTypeDef id ty = do
  ty' <- genType_ ty
  return $ TypeDef (toName id) ty'

genTypeSynUnbox :: Ident -> DS.Type -> DState (Maybe RD)
genTypeSynUnbox id ty = do
  b <- isPrim ty
  if b then return $ Just $ 
              Binding (genFuncName (CompTy id []) FuncUnbox)
                      [(varVal, Shareable $ Bang $ UserDefined $ toName id)]
                      (CannotFail [Unboxed $ UserDefined $ toName id])
                      (appR (genFuncName (genType ty) FuncUnbox) [varR varVal])           
       else return Nothing

genTypeSynMalloc :: Ident -> [Param] -> DS.Type -> DState (Maybe RD)
genTypeSynMalloc id ps ty = do
  b <- isPrim ty
  ps' <- (++) <$> pure [(varVal, Unboxed $ genType ty)] <*> genParams ps
  as  <- (:) <$> pure (varR varVal) <*> genArgsSer ty
  if b then return $ Just $ Binding (genFuncName (CompTy id []) FuncMalloc) ps'
                                    (CanFail [Linear $ UserDefined $ toName id] [])
                                    (appR (genFuncName (genType ty) FuncMalloc) as)
       else return Nothing

genTypeSynFree :: Ident -> DS.Type -> DState RD
genTypeSynFree id ty = return $
  Binding (genFuncName (CompTy id []) FuncFree) 
          [(varVal, Linear $ UserDefined $ toName id)]
          (CannotFail [])
          (appR (genFuncName (genType ty) FuncFree) [varR varVal])

genTypeSynSer :: DataDesc -> DState RD
genTypeSynSer (DTypeSyn id ps ty tc _) = do
  vt  <- isPrim ty >>= \b -> 
         if b then return $ Unboxed $ UserDefined (toName id)
              else return $ Shareable $ Bang $ UserDefined (toName id)
  ps' <- (++) <$> pure [(varVal, vt),
                        (varBuf, Linear  $ UserDefined typeBuf),
                        (varIdx, Unboxed $ UserDefined typeIdx)] 
              <*> genParams ps
  tc' <- genTyConsSer tc
  inSer <- genTypeSer ty
  return $ Binding (genFuncName (CompTy id []) FuncSerialise) ps'
                   (CanFail [Linear $ UserDefined typeBuf, Unboxed $ UserDefined typeIdx] 
                            [Linear $ UserDefined typeBuf]) 
                   (foldDoStmtsR tc' inSer)

genTypeSynDes :: DataDesc -> DState RD
genTypeSynDes (DTypeSyn id ps ty tc _) = do
  ps' <- (++) <$> pure [(varBuf, Shareable $ UserDefined typeBuf),
                        (varIdx, Unboxed   $ UserDefined typeIdx)]
              <*> genParams ps
  inDes <- genTypeDes ty
  tc' <- genTyConsDes id tc
  let stmtsDes = inDes : tc'
  vt  <- isPrim ty >>= \b -> 
         if b then return $ Unboxed $ UserDefined (toName id)
              else return $ Linear  $ UserDefined (toName id) 
  return $ Binding (genFuncName (CompTy id []) FuncDeserialise) ps'
                   (CanFail [vt, Unboxed $ UserDefined typeIdx] [])
                   (foldDoStmtsR stmtsDes $ returnR [varR varVal, varR varIdx])

-------------------------------------------------------------------------------
-- Components

genParams :: [Param] -> DState [(VarName, CS.Type)]
genParams [] = return []
genParams (p:ps) = (:) <$> genParam p <*> genParams ps

genParam :: Param -> DState (VarName, CS.Type)
genParam (id, ty) = (,) <$> pure (toName id) <*> genROType ty

genArgsSer :: DS.Type -> DState [RawExpr]
genArgsSer ty = case ty of
  DS.Array t e -> sequence [genExprSer e]
  CompTy id as -> mapM genExprSer as
  otherwise    -> return []

genArgsDes :: DS.Type -> DState [RawExpr]
genArgsDes ty = case ty of
  DS.Array t e -> sequence [genExprDes e]
  CompTy id as -> mapM genExprDes as
  otherwise    -> return []

genTyConsSer :: TyConstraint -> DState [RawStmt]
genTyConsSer Nothing = return []
genTyConsSer (Just (_, cons)) = 
  genAssertSer cons >>= \a -> 
  return [bindErrR a 
         ([], undefined)
         ([], failR [varR varBuf])] 

genTyConsDes :: Ident -> TyConstraint -> DState [RawStmt]
genTyConsDes id Nothing = return []
genTyConsDes id (Just (inst, cons)) = do
  a <- genAssertDes cons 
  b <- isPrim (CompTy id [])
  if b then return [bindErrR a ([], undefined) 
                      ([], failR [])]
       else if isJust inst
              then return [letbangErrR [varVal] a ([], undefined) 
                             ([], h)]
              else return [bindErrR a ([], undefined)
                             ([], h)]
  where h = bindSucR (appR (genFuncName (CompTy id []) FuncFree) [varR varVal])
                     ([], failR [])
 
genMConsSer :: Maybe Constraint -> DState (Maybe RawStmt)
genMConsSer = T.mapM (\mc -> genAssertSer mc >>= \cons' -> return $ 
                      bindErrR cons' ([], undefined)
                        ([], failR [varR varBuf]))

-- genMConsDes_ :: mc -> handler -> check_stmts
genMConsDes_ :: Maybe Constraint -> RawStmt -> DState (Maybe RawStmt)
genMConsDes_ mc h = T.mapM (\mc -> genAssertDes mc >>= \cons' -> return $
                            bindErrR cons' ([], undefined) ([], h)) mc

genMConsDes :: Maybe Constraint -> DState (Maybe RawStmt)
genMConsDes = flip genMConsDes_ (failR [])

genAssertSer :: Constraint -> DState RawStmt
genAssertSer cons = appR funcAssert <$> sequence [genExprSer cons]

genAssertDes :: Constraint -> DState RawStmt
genAssertDes cons = appR funcAssert <$> sequence [genExprDes cons]

genTypeSer :: DS.Type -> DState RawStmt
genTypeSer ty = do
  as <- genArgsSer ty
  -- return [bindErrR (appR (genFuncName ty FuncSerialise) $
  --                        [varR varVal, varR varBuf, varR varIdx] ++ as)
  --                  ([varBuf, varIdx], undefined)
  --                  ([varBuf, varIdx], failR [varR varBuf, varR varIdx])]
  return (appR (genFuncName ty FuncSerialise) $
               [varR varVal, varR varBuf, varR varIdx] ++ as)

genTypeDes :: DS.Type -> DState RawStmt
genTypeDes ty = do
  as <- genArgsDes ty
  return $ bindErrR (appR (genFuncName ty FuncDeserialise) $
                          [varR varBuf, varR varIdx] ++ as)
                    ([varVal, varIdx], undefined) 
                    ([], failR [])

genExprSer :: DS.Expr -> DState RawExpr
genExprSer (DS.ILit  n _) = return $ RE $ CS.ILit n
genExprSer (DS.BLit  b _) = return $ RE $ CS.BLit b
-- genExprSer (DS.Const c _) = return $ varR $ toName c
genExprSer (DS.Var   v _) = do
  (s, t) <- lookupTheta v
  case s of
    FromConst -> return $ varR $ toConst $ toName v
    FromInst  -> return $ varR varVal
    FromPara  -> return $ varR (toName v)
    FromField -> return $ memberR (varR varVal) [toName v]
    FromCase  -> return $ varR (toName v)
    FromBField p s -> return $ opR (bitmask ++ toName (genType t)) 
                                     [varR varVal, ilitR $ psToDec (p, s) $ genType t]
genExprSer (DS.BinExpr op e1 e2 _) = 
  RE <$> Op (toName op) <$> sequence [genExprSer e1, genExprSer e2]
genExprSer (DS.UnExpr  op e     _) = 
  RE <$> Op (toName op) <$> sequence [genExprSer e]
-- genExprSer (DS.In e c _) = do
--   (_, IEnum cvs) <- lookupPi c
--   genExprSer (L.foldl (\acc c -> BinExpr Or acc (BinExpr Eq e c dummyPos) dummyPos) 
--                       (BinExpr Eq e (DS.Const (fst $ head cvs) dummyPos) dummyPos) 
--                       (tail $ L.map (flip DS.Const dummyPos . fst) cvs))
genExprSer (DS.App f as _) = 
  RE <$> Op (toName f) <$> mapM genExprSer as

genExprDes :: DS.Expr -> DState RawExpr
genExprDes (DS.ILit  n _) = return $ RE $ CS.ILit n
genExprDes (DS.BLit  b _) = return $ RE $ CS.BLit b
-- genExprDes (DS.Const c _) = return $ varR $ toName c
genExprDes (DS.Var   v _) = do
  (s, t) <- lookupTheta v
  case s of
    FromConst -> return $ varR $ toConst $ toName v
    FromInst  -> return $ varR varVal
    FromPara  -> return $ varR (toName v)
    FromField -> return $ varR (toName v)
    FromCase  -> return $ varR (toName v)
    FromBField p s -> return $ opR (bitmask ++ toName (genType t)) 
                                     [varR varVal, ilitR $ psToDec (p, s) $ genType t]
genExprDes (DS.BinExpr op e1 e2 _) = 
  RE <$> Op (toName op) <$> sequence [genExprDes e1, genExprDes e2]
genExprDes (DS.UnExpr  op e     _) = 
  RE <$> Op (toName op) <$> sequence [genExprDes e]
-- genExprDes (DS.In e c _) = do
--   (_, IEnum cvs) <- lookupPi c
--   genExprDes (L.foldl (\acc c -> BinExpr Or acc (BinExpr Eq e c dummyPos) dummyPos) 
--                       (BinExpr Eq e (DS.Const (fst $ head cvs) dummyPos) dummyPos) 
--                       (tail $ L.map (flip DS.Const dummyPos . fst) cvs))
genExprDes (DS.App f as _) = 
  RE <$> Op (toName f) <$> mapM genExprDes as

genFree :: Ident -> RD
genFree id = 
  AbstractProto (genFuncName (CompTy id []) FuncFree)
                [Linear $ UserDefined (toName id)] 
                (CannotFail [])

genType :: DS.Type -> BaseType
genType DS.Bool = PrimType CT.Bool
genType (UInt is _) = PrimType $ Unsigned $ fromIntegral is
genType (CompTy id _) = UserDefined id
genType _ = error $ progErr "genType"

-- impure version, deals with Arrays
genType_ :: DS.Type -> DState BaseType
genType_ (DS.Array t _) = CS.Array <$> genRWType t
genType_ ty = return $ genType ty

genROType :: DS.Type -> DState CT.Type
genROType t = isPrim t >>= \b -> case b of
  True  -> return $ Unboxed $ genType t
  False -> return $ Shareable $ Bang $ genType t

genRWType :: DS.Type -> DState CT.Type
genRWType t = isPrim t >>= \b -> case b of
  True  -> return $ Unboxed $ genType t
  False -> return $ Linear $ genType t

evalConst :: DS.Expr -> DState Value
evalConst e = case e of
    DS.ILit  n _ -> return (IConst n)
    DS.BLit  b _ -> return (BConst b)
    -- DS.Const c _ -> snd <$> lookupPi c
    DS.Var   v _ -> snd <$> fromJust <$> lookupPi v -- error $ progErr "evalConst"
    BinExpr op e1 e2 _ -> do
      v1 <- evalConst e1
      v2 <- evalConst e2
      case op of
        Or     -> return (appValueBBB v1 v2 (||))
        And    -> return (appValueBBB v1 v2 (&&))
        Eq     -> return (BConst $ v1 == v2)
        Ne     -> return (BConst $ v1 /= v2)
        Gt     -> return (appValueIIB v1 v2 (>))
        Ge     -> return (appValueIIB v1 v2 (>=))
        Lt     -> return (appValueIIB v1 v2 (<))
        Le     -> return (appValueIIB v1 v2 (<=))
        BitOr  -> return (appValueIII v1 v2 (.|.))
        BitXor -> return (appValueIII v1 v2 (xor))
        BitAnd -> return (appValueIII v1 v2 (.&.))
        AddOp  -> return (appValueIII v1 v2 (+))
        SubOp  -> return (appValueIII v1 v2 (-))
        MulOp  -> return (appValueIII v1 v2 (*))
        DivOp  -> return (appValueIII v1 v2 div)
        ModOp  -> return (appValueIII v1 v2 mod)
    UnExpr op e _ -> do 
      v <- evalConst e
      case op of
        Not     -> case v of
                     BConst b  -> return (BConst (not b))
                     otherwise -> error err
        Plus    -> return (appValueI v (0 +))
        Minus   -> return (appValueI v (0 -))
        BitComp -> return (appValueI v complement)
    -- In e enum _ -> do 
    --   v  <- evalConst e
    --   v' <- evalConst (DS.Const enum dummyPos)
    --   case v' of 
    --     (IEnum cvs) -> return (BConst $ v `elem` P.map (IConst . snd) cvs)
    --     _ -> error err
    DS.App f args _ -> mapM evalConst args >>= return . evalFunc f
  where err = progErr "evalConst"

psToDec :: (Position, Size) -> CS.BaseType -> Integer
psToDec (p, s) (PrimType (Unsigned n)) =
  unDigits 2 $ take n ((replicate (fromIntegral p) 0) ++ (replicate (fromIntegral s) 1) ++ repeat 0)
psToDec _ _ = error $ progErr "psToDec"

-------------------------------------------------------------------------------
-- Smart constructors

-- RawExpr

opR :: OpName -> [RawExpr] -> RawExpr
opR op es = RE $ Op op es

ilitR :: Integer -> RawExpr
ilitR = RE . CS.ILit

blitR :: Bool -> RawExpr
blitR = RE . CS.BLit

varR :: FieldName -> RawExpr
varR = RE . Variable

constR :: ConstName -> RawExpr
constR = RE . CS.Const

memberR :: RawExpr -> [FieldName] -> RawExpr
memberR e fs = RE $ CS.Member e fs

vlitR :: BaseType -> TagName -> RawExpr -> RawExpr
vlitR ty tag e = RE $ VariantLit ty tag e

-- RawIter

foldWithR :: RawExpr -> [RawExpr] -> RawIter
foldWithR e es = RI $ With (RI $ ArrayFold e) es

pushWithR :: RawExpr -> [RawExpr] -> RawIter
pushWithR e es = RI $ With (RI $ ArrayPush e) es

-- RawStmt

appR :: FuncName -> [RawExpr] -> RawStmt
appR f es = RS $ CS.App f es

-- FIXME: zilinc
takeR :: RawExpr -> FieldName -> RawStmt
-- takeR e f = RS $ Take e f
takeR _ _ = RS (Return [])

-- FIXME: zilinc
putR :: RawExpr -> FieldName -> RawExpr -> RawStmt
-- putR e f v = RS $ Put e f v
putR _ _ _ = RS (Return [])

bindR :: RawStmt -> ErrCont RawStmt -> RawStmt
bindR s err = RS $ Bind s err

bindSucR :: RawStmt -> ([VarName], RawStmt) -> RawStmt
bindSucR s suc = bindR s (OnlySuccess (fst suc) (snd suc))

bindErrR :: RawStmt -> ([VarName], RawStmt) -> ([VarName], RawStmt) -> RawStmt
bindErrR s next err = bindR s (HandleError next (varErr, fst err, snd err))

letbangErrR :: [VarName] -> RawStmt -> ([VarName], RawStmt) -> ([VarName], RawStmt) -> RawStmt
letbangErrR v s next err = RS $ LetBang v s (HandleError next (varErr, fst err, snd err))

returnR :: [RawExpr] -> RawStmt
returnR es = RS $ Return es

failR :: [RawExpr] -> RawStmt
failR = failR_ (varR varErr)

failR_ :: RawExpr -> [RawExpr] -> RawStmt
failR_ e es = RS $ Fail e es

ifR :: RawExpr -> RawStmt -> RawStmt -> RawStmt
ifR c t e = RS $ If c t e

foldIfStmtsR :: [RawStmt] -> RawStmt -> RawStmt
foldIfStmtsR ss bot = 
  L.foldr (\(RS (If e t _)) acc -> RS $ If e t acc) bot ss

forR :: [VarName] -> RawIter -> RawStmt -> RawStmt
forR v i s = RS $ For v i s

-- FIXME: zilinc
caseR :: RawExpr -> [(TagName, VarName, RawStmt)] -> RawStmt
-- caseR e cs = RS $ CS.Case e cs
caseR _ _ = RS (Return [])

foldDoStmtsR :: [RawStmt] -> RawStmt -> RawStmt
foldDoStmtsR ss bot = 
  L.foldr (\s0 acc -> case s0 of
             RS (Bind s (HandleError (vs, _) err)) -> 
               RS (Bind s (HandleError (vs, acc) err))
             RS (Bind s (OnlySuccess vs _)) -> 
               RS (Bind s (OnlySuccess vs acc))
             RS (LetBang vs s (HandleError (vs', _) err)) ->
               RS (LetBang vs s (HandleError (vs', acc) err))
             RS (LetBang vs s (OnlySuccess vs' _)) ->
               RS (LetBang vs s (OnlySuccess vs' acc))
          ) bot ss

-------------------------------------------------------------------------------
-- Name Generation

unhandled_tag = "UNHANDLED_TAG"
constraint_voilation = "CONSTRAINT_VOILATION"

lib_dir = "lib.cogent"

data FuncTag = FuncSerialise 
             | FuncDeserialise 
             | FuncMalloc
             | FuncFree
             | FuncUnbox
             | FuncOthers String

genFuncName :: (Nameable t) => t -> FuncTag -> FuncName
genFuncName t FuncSerialise   = "serialise_"   ++ toName t
genFuncName t FuncDeserialise = "deserialise_" ++ toName t
genFuncName t FuncMalloc = "malloc_" ++ toName t
genFuncName t FuncFree = "free_" ++ toName t
genFuncName t FuncUnbox = "unbox_" ++ toName t
genFuncName _ _ = error "TODO: genFuncName"

typeIdx = "Index"
typeBuf = "Buf"

bitmask = "bitmask"

varVal  = genPrefix ++ "val"
varBuf  = genPrefix ++ "buf"
varIdx  = genPrefix ++ "idx"
varItr  = genPrefix ++ "itr"
varErr  = genPrefix ++ "err"
varTag  = genPrefix ++ "tag"

funcAssert = "check"
opIn = "in"

prime :: String -> String
prime x = genPrefix ++ x ++ "'"

toConst :: String -> String
toConst = L.map toUpper

instance Nameable BaseType where
  toName t@(PrimType _) = pShow t
  toName (UserDefined t) = toName t
  -- toName (CT.Array t) = arrayPrefix ++ toName t  -- FIXME
  toName _ = error $ progErr "toName (BaseType)"

instance Nameable Func where
  toName (Func f) = f

class Tagable c where
  toTag :: c -> TagName

instance Tagable Ident where
  toTag id = genPrefix ++ id ++ "_tag"

instance Tagable OpIdent where
  toTag (Just id) = toTag id
  toTag _ = error $ progErr "toTag (OpIdent)" 

tagVarName = "tag"

--
-- Copyright 2019, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{- LANGUAGE AllowAmbiguousTypes -}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
--{-# LANGUAGE ImpredicativeTypes #-B
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
#if __GLASGOW_HASKELL__ < 709
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans -Wwarn #-}

module Cogent.C.Type where

import           Cogent.C.Monad
import           Cogent.C.Syntax       as C   hiding (BinOp (..), UnOp (..))
import qualified Cogent.C.Syntax       as C   (BinOp (..), UnOp (..))
import           Cogent.Compiler
import           Cogent.Common.Syntax  as Syn
import           Cogent.Common.Types   as Typ
import           Cogent.Core           as CC
import           Cogent.Inference             (kindcheck_)
import           Cogent.Isabelle.Deep
import           Cogent.Mono                  (Instance)
import           Cogent.Normal                (isAtom)
import           Cogent.Surface               (noPos)
import           Cogent.Util                  (behead, decap, extTup2l, extTup3r, first3, secondM, toCName, whenM, flip3)
import qualified Data.DList          as DList
import           Data.Nat            as Nat
import qualified Data.OMap           as OMap
import           Data.Vec            as Vec   hiding (at, repeat, zipWith)

import           Control.Applicative          hiding (empty)
import           Control.Arrow                       ((***), (&&&), first, second)
import           Control.Monad.Identity       (runIdentity)
import           Control.Monad.RWS.Strict     hiding (mapM, mapM_, Dual, (<>), Product, Sum)
import           Data.Binary
import           Data.Char                    (isAlphaNum, toUpper)
#if __GLASGOW_HASKELL__ < 709
import           Data.Foldable                (mapM_)
#endif
import           Data.Function                (on)
import           Data.Functor.Compose
import           Data.IntMap         as IM    (delete, mapKeys)
import qualified Data.List           as L
import           Data.Loc                     (noLoc)  -- FIXME: remove
import qualified Data.Map            as M
import           Data.Maybe                   (catMaybes, fromJust)
import           Data.Monoid                  ((<>))
-- import           Data.Semigroup.Monad
-- import           Data.Semigroup.Reducer       (foldReduce)
import qualified Data.Set            as S
import           Data.String
import           Data.Traversable             (mapM)
import           Data.Tuple                   (swap)
import           Lens.Micro
import           Lens.Micro.Mtl               hiding (assign)
import           Lens.Micro.TH
#if __GLASGOW_HASKELL__ < 709
import           Prelude             as P     hiding (mapM, mapM_)
#else
import           Prelude             as P     hiding (mapM)
#endif
import           System.IO (Handle, hPutChar)
import qualified Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>), (<>))

import Debug.Trace
-- import Unsafe.Coerce (unsafeCoerce)


-- * Type generation

genTyDecl :: (StrlType, CId) -> [TypeName] -> ([CExtDecl], [CExtDecl])
genTyDecl (Record x, n) _ = ([CDecl $ CStructDecl n (map (second Just . swap) x)], [genTySynDecl (n, CStruct n)])
genTyDecl (RecordL layout, n) _ =
  let bitsize   = hiDataLayout layout
      size      = trace ("**** n = " ++ n ++ ": " ++ show (PP.pretty layout) ++ "\n bit size =" ++ show bitsize) $ dataLayoutSizeInWords layout
      arrayType = trace ("**** size = " ++ show size ++ "\n--------------------------------") $ CArray (CInt False CIntT) (CArraySize $ CConst $ CNumConst size (CInt False CIntT) DEC)
  in
    if size == 0
      then ([],[])
      else ([CDecl $ CStructDecl n [(arrayType, Just "data")]], [genTySynDecl (n, CStruct n)])
genTyDecl (Product t1 t2, n) _ = ([CDecl $ CStructDecl n [(t1, Just p1), (t2, Just p2)]], [])
genTyDecl (Variant x, n) _ = case __cogent_funion_for_variants of
  False -> ([CDecl $ CStructDecl n ((CIdent tagsT, Just fieldTag) : map (second Just . swap) (M.toList x))],
            [genTySynDecl (n, CStruct n)])
  True  -> ([CDecl $ CStructDecl n [(CIdent tagsT, Just fieldTag), (CUnion Nothing $ Just (map swap (M.toList x)), Nothing)]],
            [genTySynDecl (n, CStruct n)])
genTyDecl (Function t1 t2, n) tns =
  if n `elem` tns then ([],[])
                  else ([], [genTySynDecl (n, CIdent fty)])
  where fty = if __cogent_funtyped_func_enum then untypedFuncEnum else unitT
#ifdef BUILTIN_ARRAYS
genTyDecl (Array t Nothing , n) _ = ([], [genTySynDecl (n, CArray t CPtrToArray   )])
genTyDecl (Array t (Just e), n) _ = ([], [genTySynDecl (n, CArray t (CArraySize e))])
genTyDecl (ArrayL layout, n) _ =
  let elemSize = dataLayoutSizeInWords layout
      dataType = CPtr $ CInt False CIntT
   in if elemSize == 0
         then ([],[])
         else ([], [genTySynDecl (n, dataType)])
#endif
genTyDecl (AbsType x, n) _ = ([CMacro $ "#include <abstract/" ++ x ++ ".h>"], [])

genTySynDecl :: (TypeName, CType) -> CExtDecl
genTySynDecl (n,t) = CDecl $ CTypeDecl t [n]

lookupStrlTypeCId :: StrlType -> Gen v (Maybe CId)
lookupStrlTypeCId st = M.lookup st <$> use cTypeDefMap

genNewCId :: CId -> StrlType -> Gen v CId
genNewCId t st = do 
  cTypeDefs %= ((st,t):)  -- NOTE: add a new entry at the front
  cTypeDefMap %= M.insert st t
  return t

-- Lookup a structure and return its name, or create a new entry.
getStrlTypeCId :: StrlType -> Gen v CId
getStrlTypeCId st = do lookupStrlTypeCId st >>= \case
                         Nothing -> do
                           t <- freshGlobalCId 't'
                           genNewCId t st
                         Just t  -> return t

getStrlTypeWithCId :: CId -> StrlType -> Gen v CId
getStrlTypeWithCId t st = do lookupStrlTypeCId st >>= \case
                                Nothing -> genNewCId t st
                                Just t  -> return t

{-# RULES
"monad-left-id" [~] forall x k. return x >>= k = k x
"monad-right-id" [~] forall k. k >>= return = k
"monad-assoc" [~] forall j k l. (j >>= k) >>= l = j >>= (\x -> k x >>= l)
  #-}

-- FIXME: prove it! / zilinc
instance Monad (Compose (Gen v) Maybe) where
  return = Compose . return . return
  (Compose ma) >>= f = Compose (ma >>= \case Nothing -> return Nothing
                                             Just a  -> getCompose (f a))

lookupTypeCId :: CC.Type 'Zero VarName -> Gen v (Maybe CId)
lookupTypeCId (TVar     {}) = __impossible "lookupTypeCId"
lookupTypeCId (TVarBang {}) = __impossible "lookupTypeCId"
lookupTypeCId (TCon tn [] _) = fmap (const tn) . M.lookup tn <$> use absTypes
lookupTypeCId (TCon tn ts _) = getCompose (forM ts (\t -> (if isUnboxed t then ('u':) else id) <$> (Compose . lookupTypeCId) t) >>= \ts' ->
                                           Compose (M.lookup tn <$> use absTypes) >>= \tss ->
                                           Compose $ return (if ts' `S.member` tss
                                                               then return $ tn ++ "_" ++ L.intercalate "_" ts'
                                                               else Nothing))
lookupTypeCId (TProduct t1 t2) =
  getCompose (Compose . lookupStrlTypeCId =<<
    Record <$> (P.zip [p1,p2] <$> mapM (Compose . lookupType) [t1,t2]))
lookupTypeCId (TSum fs) = getCompose (Compose . lookupStrlTypeCId =<< Variant . M.fromList <$> mapM (secondM (Compose . lookupType) . second fst) fs)
lookupTypeCId (TFun t1 t2) = getCompose (Compose . lookupStrlTypeCId =<< Function <$> (Compose . lookupType) t1 <*> (Compose . lookupType) t2)  -- Use the enum type for function dispatching
lookupTypeCId (TRecord _ fs Unboxed) =
  getCompose (Compose . lookupStrlTypeCId =<<
    Record <$> (mapM (\(a,(b,_)) -> (a,) <$> (Compose . lookupType) b) fs))
lookupTypeCId (TRecord _ _  (Boxed _ l@(Layout RecordLayout {}))) = lookupStrlTypeCId (RecordL l)
lookupTypeCId (TRecord _ fs (Boxed _ CLayout)) =
  getCompose (Compose . lookupStrlTypeCId =<<
    Record <$> (mapM (\(a,(b,_)) -> (a,) <$> (Compose . lookupType) b) fs))
lookupTypeCId cogentType@(TRecord _ _ (Boxed _ _)) = __impossible "lookupTypeCId: record with non-record layout"
#ifdef BUILTIN_ARRAYS
lookupTypeCId (TArray t n Unboxed _) = do
  n' <- CArraySize <$> genLExpr n
  tarr <- getCompose (CArray <$> Compose (lookupType t) <*> Compose (pure $ Just n'))
  getCompose (Compose . lookupStrlTypeCId =<< (Record . (:[]) . (arrField,)) <$> Compose (pure tarr))
lookupTypeCId (TArray t n (Boxed _ l) _) = lookupStrlTypeCId (ArrayL l)
#endif
lookupTypeCId t = Just <$> typeCId t

-- XXX | -- NOTE: (Monad (Gen v), Reducer (Maybe a) (First a)) => Reducer (Gen v (Maybe a)) (Mon (Gen v) (First a)) / zilinc
-- XXX | -- If none of a type's parts are used, then getFirst -> None; otherwise getFirst -> Just cid
-- XXX | typeCIdUsage :: forall v. CC.Type Zero -> Gen v (First CId)
-- XXX | typeCIdUsage (TVar     {}) = __impossible "typeCIdUsage"
-- XXX | typeCIdUsage (TVarBang {}) = __impossible "typeCIdUsage"
-- XXX | typeCIdUsage (TCon tn [] _) = fmap (const tn) <$> (First . M.lookup tn <$> use absTypes)
-- XXX | typeCIdUsage (TCon tn ts _) = getMon $ foldReduce (map ((getFirst <$>) . typeCIdUsage) ts :: [Gen v (Maybe CId)])
-- XXX | typeCIdUsage (TProduct t1 t2) = getMon $ foldReduce [getFirst <$> typeCIdUsage t1 :: Gen v (Maybe CId), getFirst <$> typeCIdUsage t2]
-- XXX | typeCIdUsage (TSum fs) = getMon $ foldReduce (map ((getFirst <$>) . typeCIdUsage . snd) fs :: [Gen v (Maybe CId)])
-- XXX | typeCIdUsage (TFun t1 t2) = getMon $ foldReduce [getFirst <$> typeCIdUsage t1 :: Gen v (Maybe CId), getFirst <$> typeCIdUsage t2]
-- XXX | typeCIdUsage (TRecord fs s) = getMon $ foldReduce (map ((getFirst <$>) . typeCIdUsage . fst . snd) fs :: [Gen v (Maybe CId)])
-- XXX | typeCIdUsage t = return $ First Nothing  -- base types

typeCId :: CC.Type 'Zero VarName -> Gen v CId
typeCId t = use custTypeGen >>= \ctg ->
            case M.lookup t ctg of
              Just (n,_) -> return n
              Nothing -> do
                n <- t & if __cogent_fflatten_nestings then typeCIdFlat else typeCId'
                when (isUnstable t) $ do
                  typeCorres  %= DList.cons (toCName n, t)
                  typeCorres' %= OMap.alter addToTypeCorres (toCName n)
                return n
  where
    addToTypeCorres :: Maybe Sort -> Maybe Sort
    addToTypeCorres Nothing  = Just (typeToSort t  )
    addToTypeCorres (Just s) = Just (extendSort t s)

    typeCId' :: CC.Type 'Zero VarName -> Gen v CId
    typeCId' (TVar     {}) = __impossible "typeCId' (in typeCId)"
    typeCId' (TVarBang {}) = __impossible "typeCId' (in typeCId)"
    typeCId' (TPrim pt) | pt == Boolean = return boolT
                        | otherwise = primCId <$> pure pt
    typeCId' (TString) = return "char"
    typeCId' (TCon tn [] _) = do
      absTypes %= M.insert tn (S.singleton []) -- NOTE: Since it's non-parametric, it can have only one entry which is always the same / zilinc
      -- getStrlTypeCId (AbsType tn)  -- NOTE: Monomorphic abstract types will remain undefined! / zilinc
      return tn
    typeCId' (TCon tn ts _) = do  -- mapM typeCId ts >>= \ts' -> return (tn ++ "_" ++ L.intercalate "_" ts')
      ts' <- forM ts $ \t -> (if isUnboxed t then ('u':) else id) <$> typeCId t
      absTypes %= M.insertWith S.union tn (S.singleton ts')
      let tn' = tn ++ "_" ++ L.intercalate "_" ts'
          ins Nothing  = Just $ S.singleton ts'
          ins (Just s) = Just $ S.insert ts' s
      absTypes %= M.alter ins tn
      lookupStrlTypeCId (AbsType tn') >>= \case
        Nothing -> do cTypeDefs %= ((AbsType tn', tn'):)  -- This tn' should never be used!
                      cTypeDefMap %= M.insert (AbsType tn') tn'
        Just _  -> return ()
      return tn'
    typeCId' (TProduct t1 t2) = getStrlTypeCId =<< Record <$> (P.zip [p1,p2] <$> mapM genType [t1,t2])
    typeCId' (TSum fs) = getStrlTypeCId =<< Variant . M.fromList <$> mapM (secondM genType . second fst) fs
    typeCId' (TFun t1 t2) = getStrlTypeCId =<< Function <$> genType t1 <*> genType t2  -- Use the enum type for function dispatching
    typeCId' (TRecord NonRec fs Unboxed) = getStrlTypeCId =<< Record <$> (mapM (\(a,(b,_)) -> (a,) <$> genType b) fs)
    typeCId' (TRecord NonRec fs (Boxed _ l)) = do
      strlty <- Record <$> (mapM (\(a,(b,_)) -> (a,) <$> genType b) fs)
      -- \ ^ NOTE: Recursively call 'genType' anyways, trying to construct the C types
      -- in the order of its dependency.
      -- In the typeCorres table, we want the entries in dependency order. When it comes
      -- to types that use Dargent layouts, their C type definitions no longer depend on
      -- the C type definitions of their components, as they will just be defined as
      -- a singleton array type. However, their getters/setters (the function definitions)
      -- will rely on the C types of the components they access. For verification reasons,
      -- we want this function-type dependency be reflected in the table as well, even
      -- though it's not needed for C code generation. But since type generation and
      -- function definition generation are totally independent of each other, we have
      -- to use this hack to force the registration of C types in the typeCorres table.
      -- / zilinc
      case l of
        Layout RecordLayout {} -> getStrlTypeCId (RecordL l)
        CLayout -> getStrlTypeCId strlty
        _ -> __impossible "Tried to get the c-type of a record with a non-record layout"
    typeCId' (TRecord (Rec v) fs (Boxed _ l)) = do
      case l of
        Layout RecordLayout {} ->
          getStrlTypeCId (RecordL l)
        CLayout -> do
          -- Map a in-scope recursive parameter back to the ID of the 
          -- Record we're about to generate
          newId <- freshGlobalCId 't'
          -- NOTE: Here we temporarily add @v@ to the store. The following two lines
          -- of code have to be here. / zilinc
          recParRecordIds %= M.insert v newId
          strlType <- Record <$> (mapM (\(a,(b,_)) -> (a,) <$> genType b) fs)
          res      <- lookupStrlTypeCId strlType
          recParRecordIds %= M.delete v  -- @v@ gets removed!
          case res of
            Nothing -> do
              getStrlTypeWithCId newId strlType
            Just x ->  do 
              -- HACK
              globalOracle -= 1
              return x
    typeCId' t@(TRPar v (Just m)) = do
      recId <- M.lookup (simplifyType $ m M.! v) <$> use recParCIds
      case recId of 
        Nothing -> do
          Just res <- M.lookup v <$> use recParRecordIds  -- FIXME! What about Nothing?
          recParCIds %= M.insert (simplifyType $ m M.! v) res
          return res 
        Just x ->
          return x
    typeCId' (TRParBang v (Just m)) = typeCId' (TRPar v (Just m))

    typeCId' (TUnit) = return unitT
#ifdef BUILTIN_ARRAYS
    -- When the unboxed array has size 0, it's a flexible array member!
    typeCId' (TArray t (LILit 0 _) Unboxed _) = do
      t' <- genType t
      getStrlTypeCId (Array t' (Just $ sint 0))

    typeCId' (TArray t l Unboxed _) = do
      tarr <- CArray <$> genType t <*> (CArraySize <$> genLExpr l)
      getStrlTypeCId $ Record [(arrField, tarr)]

    typeCId' (TArray t l (Boxed _ al) _) =
      case al of
        Layout ArrayLayout {} -> getStrlTypeCId (ArrayL al)
        CLayout -> getStrlTypeCId =<< Array <$> genType t <*> pure Nothing
        _ -> __impossible "Tried to get the c-type of an array with a non-array record"
#endif

    typeCIdFlat :: CC.Type 'Zero VarName -> Gen v CId
    typeCIdFlat (TProduct t1 t2) = do
      ts' <- mapM genType [t1,t2]
      fss <- forM (P.zip3 [p1,p2] [t1,t2] ts') $ \(f,t,t') -> case t' of
        CPtr _ -> return [(f,t')]
        _      -> collFields f t
      getStrlTypeCId $ Record (concat fss)
    -- typeCIdFlat (TSum fs) = __todo  -- Don't flatten variants for now. It's not clear how to incorporate with --funion-for-variants
    typeCIdFlat (TRecord _ fs Unboxed) = do
      let (fns,ts) = P.unzip $ P.map (second fst) fs
      ts' <- mapM genType ts
      fss <- forM (P.zip3 fns ts ts') $ \(f,t,t') -> case t' of
        CPtr _ -> return [(f,t')]
        _      -> collFields f t
      getStrlTypeCId $ Record (concat fss)
    typeCIdFlat t = typeCId' t

    collFields :: FieldName -> CC.Type 'Zero VarName -> Gen v [(CId, CType)]
    collFields fn (TProduct t1 t2) = concat <$> zipWithM collFields (P.map ((fn ++ "_") ++) [p1,p2]) [t1,t2]
    collFields fn (TRecord _ fs _) = let (fns,ts) = P.unzip (P.map (second fst) fs) in concat <$> zipWithM collFields (P.map ((fn ++ "_") ++) fns) ts
    collFields fn t = (:[]) . (fn,) <$> genType t

    isUnstable :: CC.Type 'Zero VarName -> Bool
    isUnstable (TCon {}) = True  -- NOTE: we relax the rule here to generate all abstract types in the table / zilinc (28/5/15)
    -- XXX | isUnstable (TCon _ (_:_) _) = True
    isUnstable (TProduct {}) = True
    isUnstable (TSum _) = True
    isUnstable (TRecord {}) = True
#ifdef BUILTIN_ARRAYS
    isUnstable (TArray {}) = True
#endif
    isUnstable _ = False

-- Made for Glue
absTypeCId :: CC.Type 'Zero VarName -> Gen v CId
absTypeCId (TCon tn [] _) = return tn
absTypeCId (TCon tn ts _) = do
  ts' <- forM ts $ \t -> (if isUnboxed t then ('u':) else id) <$> typeCId t
  return (tn ++ "_" ++ L.intercalate "_" ts')
absTypeCId _ = __impossible "absTypeCId"

-- Returns the right C type
genType :: CC.Type 'Zero VarName -> Gen v CType
genType t@(TRecord _ _ s)  | s /= Unboxed = do
  when __cogent_funused_dargent_accessors $ registerGS t
  CPtr . CIdent <$> typeCId t
  -- c.f. genTypeA
  -- This puts the pointer around boxed cogent-types
genType t@(TString)                     = CPtr . CIdent <$> typeCId t
genType t@(TCon _ _ s)   | s /= Unboxed = CPtr . CIdent <$> typeCId t
genType t@(TRPar _ _)                   = CPtr . CIdent <$> typeCId t
genType t@(TRParBang _ _)               = CPtr . CIdent <$> typeCId t
#ifdef BUILTIN_ARRAYS
genType t@(TArray elt l s _)
  | (Boxed _ CLayout) <- s = CPtr <$> genType elt  -- If it's heap-allocated without layout specified
  -- we get rid of unused info here, e.g. array length, hole location
  | (Boxed _ al)      <- s = CIdent <$> typeCId (simplifyType t) -- we are going to declare it as a type
  | Unboxed <- s, LILit 0 _ <- l = CArray <$> genType elt <*> pure (CArraySize $ sint 0)
  | otherwise                    = CIdent <$> typeCId t  -- if the array is unboxed, it's wrapped in a struct
#endif
genType t                        = CIdent <$> typeCId t

registerGS :: CC.Type 'Zero VarName -> Gen v ()
registerGS t@(TRecord _ _ (Boxed _ (Layout {}))) = do
  g <- use (boxedRecordGetters . at (StrlCogentType t))
  s <- use (boxedRecordSetters . at (StrlCogentType t))
  case g of
    Nothing -> (boxedRecordGetters . at (StrlCogentType t)) ?= M.empty
    Just _  -> return ()
  case s of
    Nothing -> (boxedRecordSetters . at (StrlCogentType t)) ?= M.empty
    Just _  -> return ()
registerGS _ = return ()

-- Helper function for remove unnecessary info for cogent types
simplifyType :: CC.Type 'Zero VarName -> CC.Type 'Zero VarName
#ifdef BUILTIN_ARRAYS
simplifyType (TArray elt _ (Boxed rw (Layout l@(ArrayLayout {}))) _) =
    TArray elt (LILit 0 U32) (Boxed rw (Layout l)) Nothing
#endif
-- In the C code, we don't care whether records are readonly or not (at least for recursive types). Thus, we only generate one type of record /emmetm
simplifyType (TRecord rp fs s) =
    TRecord rp fs (Boxed False CLayout)
simplifyType x = x


-- The following two functions have different behaviours than the `genType' function
-- in certain scenarios

-- Used when generating a type for an argument to a function
genTypeA :: CC.Type 'Zero VarName -> Gen v CType
genTypeA t@(TRecord _ _ Unboxed) | __cogent_funboxed_arg_by_ref = CPtr . CIdent <$> typeCId t  -- TODO: sizeof
genTypeA t = genType t


-- TODO(dagent): this seems wrong with respect to Dargent
lookupType :: CC.Type 'Zero VarName -> Gen v (Maybe CType)
lookupType t@(TRecord _ _ s)  | s /= Unboxed = getCompose (CPtr . CIdent <$> Compose (lookupTypeCId t))
lookupType t@(TString)                       = getCompose (CPtr . CIdent <$> Compose (lookupTypeCId t))
lookupType t@(TCon _ _ s)     | s /= Unboxed = getCompose (CPtr . CIdent <$> Compose (lookupTypeCId t))
#ifdef BUILTIN_ARRAYS
lookupType t@(TArray _ _ s _) | s /= Unboxed = getCompose (CPtr . CIdent <$> Compose (lookupTypeCId t))
                              | otherwise    = getCompose (CPtr . CIdent <$> Compose (lookupTypeCId t))
#endif
lookupType t                                 = getCompose (       CIdent <$> Compose (lookupTypeCId t))



-- *****************************************************************************
-- * LExpr generation

genLExpr :: CC.LExpr 'Zero VarName -> Gen v CExpr
genLExpr (LVariable var        ) = __todo "genLExpr"
genLExpr (LFun      fn [] ls   ) = __todo "genLExpr"
genLExpr (LFun      fn ts ls   ) = __todo "genLExpr"
genLExpr (LOp       opr es     ) = genOp opr (CC.TPrim U32) <$> mapM genLExpr es  -- FIXME: we assume it's U32 for now / zilinc
genLExpr (LApp      e1 e2      ) = __todo "genLExpr"
genLExpr (LCon      tag e t    ) = __todo "genLExpr"
genLExpr (LUnit                ) = __todo "genLExpr"
genLExpr (LILit     n   pt     ) = pure $ mkConst pt n
genLExpr (LSLit     s          ) = __todo "genLExpr"
genLExpr (LLet      a e1 e2    ) = __todo "genLExpr"
genLExpr (LLetBang  vs a e1 e2 ) = __todo "genLExpr"
genLExpr (LTuple    e1 e2      ) = __todo "genLExpr"
genLExpr (LStruct   fs         ) = __todo "genLExpr"
genLExpr (LIf       c e1 e2    ) = __todo "genLExpr"
genLExpr (LCase     c tag (a1,e1) (a2,e2)) = __todo "genLExpr"
genLExpr (LEsac     e          ) = __todo "genLExpr"
genLExpr (LSplit    a tp e     ) = __todo "genLExpr"
genLExpr (LMember   rec fld    ) = __todo "genLExpr"
genLExpr (LTake     a rec fld e) = __todo "genLExpr"
genLExpr (LPut      rec fld e  ) = __todo "genLExpr"
genLExpr (LPromote  ty e       ) = __todo "genLExpr"
genLExpr (LCast     ty e       ) = __todo "genLExpr"



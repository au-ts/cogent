--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--


{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
--{-# LANGUAGE ImpredicativeTypes #-}
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


module Cogent.C.GenState where

import           Cogent.C.Syntax       as C hiding (BinOp (..), UnOp (..))
import qualified Cogent.C.Syntax       as C (BinOp (..), UnOp (..))
import           Cogent.Compiler
import           Cogent.Common.Syntax  as Syn
import           Cogent.Common.Types   as Typ
import           Cogent.Core           as CC
import           Cogent.Inference             (kindcheck_)
import           Cogent.Isabelle.Deep
import           Cogent.Mono                  (Instance)
import           Cogent.Normal                (isAtom)
import           Cogent.Util           (decap, extTup2l, extTup3r, first3, secondM, toCName, whenM)
import qualified Data.DList          as DList
import           Data.Nat            as Nat
import           Data.Vec            as Vec hiding (repeat, zipWith)

import           Control.Applicative          hiding (empty)
import           Control.Arrow                       ((***), (&&&), second)
import           Control.Lens                 hiding (at, assign)
import           Control.Monad.RWS.Strict     hiding (mapM, mapM_, Dual, (<>), Product, Sum)
import           Data.Char                    (isAlphaNum, toUpper)
#if __GLASGOW_HASKELL__ < 709
import           Data.Foldable                (mapM_)
#endif
import           Data.Functor.Compose
import           Data.Function.Flippers       (flip3)
import qualified Data.List           as L
import           Data.Loc                     (noLoc)  -- FIXME: remove
import qualified Data.Map            as M
import           Data.Maybe                   (catMaybes, fromJust)
import           Data.Monoid                  ((<>))
import           Data.Semigroup.Monad
-- import           Data.Semigroup.Reducer       (foldReduce)
import qualified Data.Set            as S
import           Data.String
import           Data.Traversable             (mapM)
import           Data.Tuple                   (swap)
#if __GLASGOW_HASKELL__ < 709
import           Prelude             as P    hiding (mapM, mapM_)
#else
import           Prelude             as P    hiding (mapM)
#endif
import           System.IO (Handle, hPutChar)
import qualified Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>), (<>))

-- import Debug.Trace
import Unsafe.Coerce (unsafeCoerce)

-- *****************************************************************************
-- * The state for code-generation

-- | A FunClass is a map from the structural types of functions to a set of all names
--   of declared functions with that structural type. It is used to generate the
--   dispatch functions needed to implement higher order functions in C.
type FunClass  = M.Map StrlType (S.Set (FunName, Attr))  -- ^ @c_strl_type &#x21A6; funnames@
type VarPool   = M.Map CType [CId]  -- ^ vars available @(ty_id &#x21A6; [var_id])@

-- | The 'i'th element of the vector is the C expression bound to the variable in scope
--   with DeBruijn index 'i'. The type parameter 'v' is the number of variables in scope.
type GenRead v = Vec v CExpr

data GenState  = GenState
  { _cTypeDefs    :: [(StrlType, CId)]
  , _cTypeDefMap  :: M.Map StrlType CId
    -- ^ Maps structural types we've seen so far to the
    --   C identifiers corresponding to the structural type.
    --
    --   We keep both a Map and a List because the list remembers the order,
    --   but the map gives performant reads.

  , _typeSynonyms :: M.Map TypeName CType
  , _typeCorres   :: DList.DList (CId, CC.Type 'Zero)
    -- ^ C type names corresponding to Cogent types
    
  , _absTypes     :: M.Map TypeName (S.Set [CId])
    -- ^ Maps TypeNames of abstract Cogent types to
    --   the Set of all monomorphised type argument lists
    --   which the abstract type is applied to in the program.

  , _custTypeGen  :: M.Map (CC.Type 'Zero) (CId, CustTyGenInfo)
  , _funClasses   :: FunClass
  , _localOracle  :: Integer
  , _globalOracle :: Integer
  , _varPool      :: VarPool
  , _ffiFuncs     :: M.Map FunName (CType, CType)
    -- ^ A map containing functions that need to generate C FFI functions. 
    --   The map is from the original function names (before prefixing with @\"ffi_\"@ to a pair of @(marshallable_arg_type, marshallable_ret_type)@.
    --   This map is needed when we generate the Haskell side of the FFI.
  
  , _boxedRecordSetters :: M.Map (CC.Type 'Zero, FieldName) CExpr
  , _boxedRecordGetters :: M.Map (CC.Type 'Zero, FieldName) CExpr
    -- ^ The expressions to call the generated setter and getter functions for the fields of boxed cogent records.

  , _boxedSettersAndGetters :: [CExtDecl]
    -- ^ A list of the implementations of all generated setter and getter functions
  }

makeLenses ''GenState

newtype Gen v a = Gen { runGen :: RWS (GenRead v) () GenState a }
                deriving (Functor, Applicative, Monad,
                          MonadReader (GenRead v),
                          MonadState  GenState)





-- *****************************************************************************
-- * Type generation


genTyDecl :: (StrlType, CId) -> [TypeName] -> [CExtDecl]
genTyDecl (Record x, n) _ = [CDecl $ CStructDecl n (map (second Just . swap) x), genTySynDecl (n, CStruct n)]
genTyDecl (BoxedRecord _, n) _ = [CDecl $ CStructDecl n [(CPtr (CInt False CIntT), Just "data")], genTySynDecl (n, CStruct n)]
genTyDecl (Product t1 t2, n) _ = [CDecl $ CStructDecl n [(t1, Just p1), (t2, Just p2)]]
genTyDecl (Variant x, n) _ = case __cogent_funion_for_variants of
  False -> [CDecl $ CStructDecl n ((CIdent tagsT, Just fieldTag) : map (second Just . swap) (M.toList x)),
            genTySynDecl (n, CStruct n)]
  True  -> [CDecl $ CStructDecl n [(CIdent tagsT, Just fieldTag), (CUnion Nothing $ Just (map swap (M.toList x)), Nothing)],
            genTySynDecl (n, CStruct n)]
genTyDecl (Function t1 t2, n) tns =
  if n `elem` tns then []
                  else [CDecl $ CTypeDecl (CIdent fty) [n]]
  where fty = if __cogent_funtyped_func_enum then untypedFuncEnum else unitT
genTyDecl (Array t ms, n) _ = [CDecl $ CVarDecl t n True Nothing]
genTyDecl (AbsType x, n) _ = [CMacro $ "#include <abstract/" ++ x ++ ".h>"]

genTySynDecl :: (TypeName, CType) -> CExtDecl
genTySynDecl (n,t) = CDecl $ CTypeDecl t [n]

freshLocalCId :: Char -> Gen v CId
freshLocalCId c = do (localOracle += 1); (c:) . show <$> use localOracle

freshGlobalCId :: Char -> Gen v CId
freshGlobalCId c = do (globalOracle += 1); (c:) . show <$> use globalOracle

lookupStrlTypeCId :: StrlType -> Gen v (Maybe CId)
lookupStrlTypeCId st = M.lookup st <$> use cTypeDefMap

-- Lookup a structure and return its name, or create a new entry.
getStrlTypeCId :: StrlType -> Gen v CId
getStrlTypeCId st = do lookupStrlTypeCId st >>= \case
                         Nothing -> do t <- freshGlobalCId 't'
                                       cTypeDefs %= ((st,t):)  -- NOTE: add a new entry at the front
                                       cTypeDefMap %= M.insert st t
                                       return t
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

lookupTypeCId :: CC.Type 'Zero -> Gen v (Maybe CId)
lookupTypeCId (TVar     {}) = __impossible "lookupTypeCId"
lookupTypeCId (TVarBang {}) = __impossible "lookupTypeCId"
lookupTypeCId (TCon tn [] _) = fmap (const tn) . M.lookup tn <$> use absTypes
lookupTypeCId (TCon tn ts _) = getCompose (forM ts (\t -> (if isUnboxed t then ('u':) else id) <$> (Compose . lookupTypeCId) t) >>= \ts' ->
                                           Compose (M.lookup tn <$> use absTypes) >>= \tss ->
                                           Compose $ return (if ts' `S.member` tss
                                                               then return $ tn ++ "_" ++ L.intercalate "_" ts'
                                                               else Nothing))
lookupTypeCId (TProduct t1 t2) = getCompose (Compose . lookupStrlTypeCId =<< Record <$> (P.zip [p1,p2] <$> mapM (Compose . lookupType) [t1,t2]))
lookupTypeCId (TSum fs) = getCompose (Compose . lookupStrlTypeCId =<< Variant . M.fromList <$> mapM (secondM (Compose . lookupType) . second fst) fs)
lookupTypeCId (TFun t1 t2) = getCompose (Compose . lookupStrlTypeCId =<< Function <$> (Compose . lookupType) t1 <*> (Compose . lookupType) t2)  -- Use the enum type for function dispatching
lookupTypeCId (TRecord fs Unboxed) = getCompose (Compose . lookupStrlTypeCId =<< Record <$> (mapM (\(a,(b,_)) -> (a,) <$> (Compose . lookupType) b) fs))
lookupTypeCId cogentType@(TRecord _ (Boxed _ _)) = lookupStrlTypeCId (BoxedRecord (StrlCogentType cogentType))
lookupTypeCId (TArray t l) = getCompose (Compose . lookupStrlTypeCId =<< Array <$> (Compose . lookupType) t <*> pure (Just $ fromIntegral l))
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

typeCId :: CC.Type 'Zero -> Gen v CId
typeCId t = use custTypeGen >>= \ctg ->
            case M.lookup t ctg of
              Just (n,_) -> return n
              Nothing ->
                (if __cogent_fflatten_nestings then typeCIdFlat else typeCId') t >>= \n ->
                when (isUnstable t) (typeCorres %= DList.cons (toCName n, t)) >>
                return n
  where
    typeCId' :: CC.Type 'Zero -> Gen v CId
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
    typeCId' (TRecord fs Unboxed) = getStrlTypeCId =<< Record <$> (mapM (\(a,(b,_)) -> (a,) <$> genType b) fs)
    typeCId' cogentType@(TRecord _ (Boxed _ _)) = getStrlTypeCId (BoxedRecord (StrlCogentType cogentType))
    typeCId' (TUnit) = return unitT
    typeCId' (TArray t l) = getStrlTypeCId =<< Array <$> genType t <*> pure (Just $ fromIntegral l)

    typeCIdFlat :: CC.Type 'Zero -> Gen v CId
    typeCIdFlat (TProduct t1 t2) = do
      ts' <- mapM genType [t1,t2]
      fss <- forM (P.zip3 [p1,p2] [t1,t2] ts') $ \(f,t,t') -> case t' of
        CPtr _ -> return [(f,t')]
        _      -> collFields f t
      getStrlTypeCId $ Record (concat fss)
    -- typeCIdFlat (TSum fs) = __todo  -- Don't flatten variants for now. It's not clear how to incorporate with --funion-for-variants
    typeCIdFlat (TRecord fs Unboxed) = do
      let (fns,ts) = P.unzip $ P.map (second fst) fs
      ts' <- mapM genType ts
      fss <- forM (P.zip3 fns ts ts') $ \(f,t,t') -> case t' of
        CPtr _ -> return [(f,t')]
        _      -> collFields f t
      getStrlTypeCId $ Record (concat fss)
    typeCIdFlat t = typeCId' t

    collFields :: FieldName -> CC.Type 'Zero -> Gen v [(CId, CType)]
    collFields fn (TProduct t1 t2) = concat <$> zipWithM collFields (P.map ((fn ++ "_") ++) [p1,p2]) [t1,t2]
    collFields fn (TRecord fs _) = let (fns,ts) = P.unzip (P.map (second fst) fs) in concat <$> zipWithM collFields (P.map ((fn ++ "_") ++) fns) ts
    collFields fn t = (:[]) . (fn,) <$> genType t

    isUnstable :: CC.Type 'Zero -> Bool
    isUnstable (TCon {}) = True  -- NOTE: we relax the rule here to generate all abstract types in the table / zilinc (28/5/15)
    -- XXX | isUnstable (TCon _ (_:_) _) = True
    isUnstable (TProduct {}) = True
    isUnstable (TSum _) = True
    isUnstable (TRecord {}) = True
    isUnstable (TArray {}) = True
    isUnstable _ = False

-- Made for Glue
absTypeCId :: CC.Type 'Zero -> Gen v CId
absTypeCId (TCon tn [] _) = return tn
absTypeCId (TCon tn ts _) = do
  ts' <- forM ts $ \t -> (if isUnboxed t then ('u':) else id) <$> typeCId t
  return (tn ++ "_" ++ L.intercalate "_" ts')
absTypeCId _ = __impossible "absTypeCId"

-- Returns the right C type
genType :: CC.Type 'Zero -> Gen v CType
genType t@(TString)                    = CPtr . CIdent <$> typeCId t
genType t@(TCon _ _ s)  | s /= Unboxed = CPtr . CIdent <$> typeCId t
genType   (TArray t l)                 = CArray <$> genType t <*> pure (CArraySize (mkConst U32 l))  -- c.f. genTypeP
genType t                              = CIdent <$> typeCId t

-- The following two functions have different behaviours than the `genType' function
-- in certain scenarios

-- Used when generating a type for an argument to a function
genTypeA :: CC.Type 'Zero -> Gen v CType
genTypeA t@(TRecord _ Unboxed) | __cogent_funboxed_arg_by_ref = CPtr . CIdent <$> typeCId t  -- TODO: sizeof
genTypeA t = genType t

-- It will generate a pointer type for an array, instead of the static-sized array type
genTypeP :: CC.Type 'Zero -> Gen v CType
genTypeP (TArray telm l) = CPtr <$> genTypeP telm
genTypeP t = genType t

genTypeALit :: CC.Type 'Zero -> Gen v CType
genTypeALit (TArray t l) = CArray <$> (genType t) <*> pure (CArraySize (mkConst U32 l))
genTypeALit t = genType t

lookupType :: CC.Type 'Zero -> Gen v (Maybe CType)
lookupType t@(TRecord _ s) | s /= Unboxed = getCompose (CPtr . CIdent <$> Compose (lookupTypeCId t))
lookupType t@(TString)                    = getCompose (CPtr . CIdent <$> Compose (lookupTypeCId t))
lookupType t@(TCon _ _ s)  | s /= Unboxed = getCompose (CPtr . CIdent <$> Compose (lookupTypeCId t))
lookupType t@(TArray _ _)                 = getCompose (CPtr . CIdent <$> Compose (lookupTypeCId t))
lookupType t                              = getCompose (       CIdent <$> Compose (lookupTypeCId t))

-- *****************************************************************************
-- * Helper functions to build C syntax

u32 :: CType
u32 = CogentPrim U32

-- FIXME: more might be true / zilinc
-- isAddressableCExpr :: CExpr -> Bool
-- isAddressableCExpr (CVar {}) = True
-- isAddressableCExpr (CDeref e) = isAddressableCExpr e
-- isAddressableCExpr (CTypeCast _ e) = isAddressableCExpr e
-- isAddressableCExpr _ = False

primCId :: PrimInt -> String
primCId Boolean = "Bool"
primCId U8  = "u8"
primCId U16 = "u16"
primCId U32 = "u32"
primCId U64 = "u64"

likely :: CExpr -> CExpr
likely e = CEFnCall (CVar "likely" (Just $ CFunction CBool CBool)) [e]

unlikely :: CExpr -> CExpr
unlikely e = CEFnCall (CVar "unlikely" (Just $ CFunction CBool CBool)) [e]

variable :: CId -> CExpr
variable = flip CVar Nothing

mkBoolLit :: CExpr -> CExpr
mkBoolLit e = CCompLit (CIdent boolT) [([CDesignFld boolField], CInitE e)]

true :: CExpr
true = mkConst Boolean 1

mkConst :: (Integral t) => PrimInt -> t -> CExpr
mkConst pt (fromIntegral -> n)
  | pt == Boolean = mkBoolLit (mkConst U8 n)
  | otherwise = CConst $ CNumConst n (CogentPrim pt) DEC

-- str.fld
strDot' :: CId -> CId -> CExpr
strDot' str fld = strDot (variable str) fld

-- str->fld
strArrow' :: CId -> CId -> CExpr
strArrow' str fld = strArrow (variable str) fld

strDot :: CExpr -> CId -> CExpr
strDot rec fld = CStructDot rec fld

strArrow :: CExpr -> CId -> CExpr
strArrow rec fld = CStructDot (CDeref rec) fld

mkArrIdx :: Integral t => CExpr -> t -> CExpr
mkArrIdx arr idx = CArrayDeref arr (mkConst U32 idx)

isTrivialCExpr :: CExpr -> Bool
isTrivialCExpr (CBinOp {}) = False
isTrivialCExpr (CUnOp {}) = False
isTrivialCExpr (CCondExpr {}) = False
isTrivialCExpr (CConst {}) = True
isTrivialCExpr (CVar {}) = True
isTrivialCExpr (CStructDot (CDeref e) _) = False  -- NOTE: Not sure why but we cannot do `isTrivialCExpr e && not __cogent_fintermediate_vars' / zilinc
isTrivialCExpr (CArrayDeref e idx) = __fixme $ isTrivialCExpr e && isTrivialCExpr idx
isTrivialCExpr (CStructDot e _) = isTrivialCExpr e && not __cogent_fintermediate_vars
isTrivialCExpr (CDeref e) = isTrivialCExpr e && not __cogent_fintermediate_vars
isTrivialCExpr (CAddrOf e) = isTrivialCExpr e && not __cogent_fintermediate_vars
isTrivialCExpr (CTypeCast _ e) = isTrivialCExpr e
isTrivialCExpr (CSizeof   e) = isTrivialCExpr e
isTrivialCExpr (CSizeofTy _) = True
isTrivialCExpr (CEFnCall {}) = False
isTrivialCExpr (CCompLit _ dis) = and (map (\(ds,i) -> and (map isTrivialCDesignator ds) && isTrivialCInitializer i) dis) && __cogent_fuse_compound_literals
isTrivialCExpr (CMKBOOL e) = isTrivialCExpr e

isTrivialCInitializer :: CInitializer -> Bool
isTrivialCInitializer (CInitE e) = isTrivialCExpr e
isTrivialCInitializer (CInitList dis) = and $ map (\(ds,i) -> and (map isTrivialCDesignator ds) && isTrivialCInitializer i) dis

isTrivialCDesignator :: CDesignator -> Bool
isTrivialCDesignator (CDesignE e) = isTrivialCExpr e
isTrivialCDesignator (CDesignFld _) = True

-- *****************************************************************************
-- ** Naming convensions

-- NOTE: Reserved names; users should NOT use them in Cogent programs!
--       Prefixing underscores are disliked by C-parser / zilinc


tagsT, fieldTag :: CId
tagsT         = "tag_t"
fieldTag      = "tag"
tagEnum tag   = "TAG_ENUM_" ++ tag

variantT :: CId
variantT = "variant_t"

-- NOTE: assume ty is given by function `genType'
mkVariantTT :: TagName -> CType -> CId
mkVariantTT tag (CIdent tn) = tag ++ "_" ++ tn
mkVariantTT tag (CPtr (CIdent tn)) = tag ++ "_p" ++ tn  -- FIXME: may need to distinguish * and non-* / zilinc
mkVariantTT _ _ = __impossible "mkVariantTT"

argOf fn = fn ++ "_arg"
retOf fn = fn ++ "_ret"

unitT, dummyField :: CId
unitT         = "unit_t"
dummyField    = "dummy"

boolT, boolField :: CId
boolT     = "bool_t"
boolField = "boolean"

funEnum fn = "FUN_ENUM_" ++ fn
untypedFuncEnum = "untyped_func_enum" :: CId
funDispatch tn = "dispatch_" ++ tn  -- tn is the typename of the Enum
funMacro f = "FUN_MACRO_" ++ f
funDispMacro f = "FUN_DISP_MACRO_" ++ f

-- FIXME: we can probably merge these
letbangTrue = "LETBANG_TRUE"
letTrue = "LET_TRUE"

p1, p2 :: CId
p1 = "p1"
p2 = "p2"

-- NOTE: use actual names instead
-- XXX | field n = 'f':show n
-- XXX | fields = map (('f':) . show) [0 :: Int ..]

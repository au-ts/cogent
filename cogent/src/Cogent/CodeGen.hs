--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{- LANGUAGE AllowAmbiguousTypes -}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
--{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
#if __GLASGOW_HASKELL__ < 709
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PackageImports #-}
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

module Cogent.CodeGen where

import           Cogent.Compiler
import           Cogent.Common.Syntax  as Syn
import           Cogent.Common.Types   as Typ
import           Cogent.Deep
import qualified Cogent.DList          as DList
import           Cogent.Mono                  (Instance)
import           Cogent.Normal                (isAtom)
import           Cogent.PrettyCore            (displayOneLine)
import           Cogent.PrettyCore            ()
-- import           Cogent.PrettyPrint           ()
import           Cogent.Sugarfree      as SF  hiding (kindcheck, withBindings)
import           Cogent.Util                  (extTup3, first3, secondM, toCName, whenM)
import           Cogent.Vec            as Vec hiding (repeat, zipWith)

import           Control.Applicative         hiding (empty)
import           Control.Arrow                      ((***), (&&&), second)
import           Control.Lens                hiding (at)
import           Control.Monad.RWS.Strict    hiding (mapM, mapM_, Dual, (<>), Product, Sum)
import           Data.Char                   (isAlphaNum, toUpper)
#if __GLASGOW_HASKELL__ < 709
import           Data.Foldable               (mapM_)
#endif
import           Data.Functor.Compose
import           Data.Function.Flippers      (flip3)
import qualified Data.List           as L
import           Data.Loc                    (noLoc)
import qualified Data.Map            as M
import           Data.Maybe                  (fromJust)
import           Data.Monoid                 ((<>))
import           Data.Semigroup.Monad
-- import           Data.Semigroup.Reducer      (foldReduce)
import qualified Data.Set            as S
import           Data.String
import           Data.Traversable            (mapM)
import           Data.Tuple                  (swap)
import qualified "language-c-quote" Language.C as C
import           Language.C.Quote.C
import           "language-c-quote" Language.C.Syntax ()
#if __GLASGOW_HASKELL__ < 709
import           Prelude             as P    hiding (mapM, mapM_)
#else
import           Prelude             as P    hiding (mapM)
#endif
import           System.IO (Handle)
import qualified Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>), (<>))
import qualified Text.PrettyPrint.Mainland as ML
#if MIN_VERSION_mainland_pretty(0,6,0)
import qualified Text.PrettyPrint.Mainland.Class as ML
#endif

-- import Debug.Trace
import Unsafe.Coerce (unsafeCoerce)

-- ****************************************************************************
-- AST

-- Most of the abstract syntax is derived from Absyn.ML in c-parser
-- Currently we just implement the smallest set used in our CG

type CId = String

data CIntType = CCharT | CShortT | CIntT | CLongT | CLongLongT
              deriving (Eq, Ord, Show)

-- XXX | -- This is copied from language-c-quote
-- XXX | data CArraySize = CArraySize CExpr
-- XXX |                 | CVariableArraySize
-- XXX |                 | CNoArraySize
-- XXX |                 deriving (Eq, Ord, Show)

-- The type parameter has been striped off
data CType = CInt Bool CIntType    -- true is signed
           | CogentPrim  PrimInt     -- add Cogent primitive types
           | CBool  -- NOTE: this should be the same as Cogent boolean (could be used interchangeably)
           | CChar
           | CStruct CId
           | CUnion (Maybe CId) (Maybe [(CType, CId)])  -- Made specifically for --funion-for-variants
           | CEnum CId
           | CPtr CType
           -- | CArray CType CArraySize
           -- | CBitfield Bool c  -- True for signed field
           | CIdent CId
           | CFunction CType CType
           | CVoid
           deriving (Eq, Ord, Show)

u32 :: CType
u32 = CogentPrim U32

primCId :: PrimInt -> String
primCId Boolean = "Bool"
primCId U8  = "u8"
primCId U16 = "u16"
primCId U32 = "u32"
primCId U64 = "u64"

data Radix = BIN | OCT | DEC | HEX
              deriving (Eq, Ord, Show)

data CLitConst = CNumConst Integer CType Radix
               | CCharConst Char
               | CStringConst String
               deriving (Eq, Ord, Show)

data CExpr = CBinOp CBinOp CExpr CExpr
           | CUnOp  CUnOp CExpr
           | CCondExpr CExpr CExpr CExpr
           | CConst CLitConst
           | CVar CId (Maybe CType)
           | CStructDot CExpr CId
           -- | CArrayDeref CExpr CExpr
           | CDeref CExpr
           | CAddrOf CExpr
           | CTypeCast CType CExpr
           | CSizeof   CExpr
           | CSizeofTy CType
           | CEFnCall CExpr [CExpr]
           | CCompLit CType [([CDesignator], CInitializer)]
           -- | CArbitrary (CType CExpr)
           | CMKBOOL CExpr
           deriving (Eq, Ord, Show)

isTrivialCExpr :: CExpr -> Bool
isTrivialCExpr (CBinOp {}) = False
isTrivialCExpr (CUnOp {}) = False
isTrivialCExpr (CCondExpr {}) = False
isTrivialCExpr (CConst {}) = True
isTrivialCExpr (CVar {}) = True
isTrivialCExpr (CStructDot (CDeref e) _) = False  -- NOTE: Not sure why but we cannot do `isTrivialCExpr e && not __cogent_fintermediate_vars' / zilinc
isTrivialCExpr (CStructDot e _) = isTrivialCExpr e && not __cogent_fintermediate_vars
isTrivialCExpr (CDeref e) = isTrivialCExpr e && not __cogent_fintermediate_vars
isTrivialCExpr (CAddrOf e) = isTrivialCExpr e && not __cogent_fintermediate_vars
isTrivialCExpr (CTypeCast _ e) = isTrivialCExpr e
isTrivialCExpr (CSizeof   e) = isTrivialCExpr e
isTrivialCExpr (CSizeofTy _) = True
isTrivialCExpr (CEFnCall {}) = False
isTrivialCExpr (CCompLit _ dis) = and (map (\(ds,i) -> and (map isTrivialCDesignator ds) && isTrivialCInitializer i) dis) && __cogent_fuse_compound_literals
isTrivialCExpr (CMKBOOL e) = isTrivialCExpr e

-- FIXME: more might be true / zilinc
isAddressableCExpr :: CExpr -> Bool
isAddressableCExpr (CVar {}) = True
isAddressableCExpr (CDeref e) = isAddressableCExpr e
isAddressableCExpr (CTypeCast _ e) = isAddressableCExpr e
isAddressableCExpr _ = False

likely :: CExpr -> CExpr
likely e = CEFnCall (CVar "likely" (Just $ CFunction CBool CBool)) [e]

unlikely :: CExpr -> CExpr
unlikely e = CEFnCall (CVar "unlikely" (Just $ CFunction CBool CBool)) [e]

variable :: CId -> CExpr
variable = flip CVar Nothing

-- str.fld
mkStr1 :: CId -> FieldName -> CExpr
mkStr1 str fld = mkStr2 str fld

-- str->fld
mkStr1' :: CId -> FieldName -> CExpr
mkStr1' str fld = mkStr2' str fld

mkStr2 :: CId -> CId -> CExpr
mkStr2 str fld = mkStr3 (variable str) fld

mkStr2' :: CId -> CId -> CExpr
mkStr2' str fld = mkStr3' (variable str) fld

mkStr3 :: CExpr -> CId -> CExpr
mkStr3 rec fld = CStructDot rec fld

mkStr3' :: CExpr -> CId -> CExpr
mkStr3' rec fld = CStructDot (CDeref rec) fld

data CInitializer = CInitE CExpr
                  | CInitList [([CDesignator], CInitializer)]
                  deriving (Eq, Ord, Show)

isTrivialCInitializer :: CInitializer -> Bool
isTrivialCInitializer (CInitE e) = isTrivialCExpr e
isTrivialCInitializer (CInitList dis) = and $ map (\(ds,i) -> and (map isTrivialCDesignator ds) && isTrivialCInitializer i) dis

data CDesignator = CDesignE CExpr
                 | CDesignFld CId
                 deriving (Eq, Ord, Show)

isTrivialCDesignator :: CDesignator -> Bool
isTrivialCDesignator (CDesignE e) = isTrivialCExpr e
isTrivialCDesignator (CDesignFld _) = True

type CBinOp    = C.BinOp
type CUnOp     = C.UnOp

-- data CTrappable = CBreakT | CContinueT

data CStmt = CAssign CExpr CExpr
           | CAssignFnCall (Maybe CExpr) CExpr [CExpr]  -- lval, fn, args
           -- | CChaos     CExpr
           -- | CEmbFnCall CExpr CExpr [CExpr] -- lval, fn, args
           | CBlock [CBlockItem]
           | CWhile CExpr CStmt  -- elide `string wrap option'
           -- | CTrap CTrappable CStmt
           | CReturn (Maybe CExpr)
           | CReturnFnCall CExpr [CExpr]
           | CBreak
           | CContinue
           | CIfStmt CExpr CStmt CStmt
           | CSwitch CExpr [(Maybe CExpr, CStmt)]  -- simplified
           | CEmptyStmt
           -- elide `Auxupd' `Ghostupd' `Spec' and `AsmStmt'
           -- | CLocalInit CExpr
           deriving (Show)

data CBlockItem = CBIStmt CStmt
                | CBIDecl (CDeclaration IND)
                deriving (Show)

data FnSpec = FnSpec [Storage] [TypeQual] [GccAttrs] deriving (Eq, Show)

noFnSpec = FnSpec [] [] []
staticInlineFnSpec = FnSpec [STStatic] [TQInline] []

data Storage  = STStatic | STRegister | STAuto   | STExtern   deriving (Eq, Show)
data TypeQual = TQConst  | TQVolatile | TQInline | TQRestrict deriving (Eq, Show)
data GccAttrs = GccAttrs [GccAttr] deriving (Eq, Show)
data GccAttr  = GccAttr String [CExpr] deriving (Eq, Show)

data IND  -- internal decl
data EXD  -- external decl

data CDeclaration d where
  CVarDecl    :: CType -> CId -> Bool -> Maybe CInitializer -> CDeclaration d -- elide `gcc_attribute list'. true if NOT extern
  CStructDecl :: CId -> [(CType, Maybe CId)] -> CDeclaration EXD  -- add Maybe for --funion-for-variants
  CTypeDecl   :: CType -> [CId] -> CDeclaration EXD  -- change [(t, v)] -> ... to t -> [v] -> ...
  CExtFnDecl  :: { retType :: CType,
                   name    :: CId,
                   params  :: [(CType, Maybe CId)] ,
                   specs   :: FnSpec } -> CDeclaration EXD
  CEnumDecl   :: Maybe CId -> [(CId, Maybe CExpr)] -> CDeclaration EXD
deriving instance Show (CDeclaration d)

data CExtDecl = CFnDefn (CType, CId) [(CType, CId)] [CBlockItem] FnSpec
              | CDecl (CDeclaration EXD)
              | CMacro String
              | CFnMacro CId [CId] [CBlockItem]
              deriving (Show)

-- ****************************************************************************
-- The front-end: -> Dual-AST


data StrlType = Record  [(CId, CType)] Bool  -- fieldname |-> fieldtype * is_unboxed
              | Product CType CType         -- pair
              | Variant (M.Map CId CType)   -- one tag field, and fields for all possibilities
              | Function CType CType
              | AbsType CId
              deriving (Eq, Ord, Show)

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

type FunClass  = M.Map StrlType (S.Set (FunName, Attr))  -- c_strl_type |-> funnames
type VarPool   = M.Map CType [CId]  -- vars available (ty_id |-> [var_id])
type GenRead v = Vec v CExpr

data GenState  = GenState { _cTypeDefs    :: [(StrlType, CId)]
                          , _cTypeDefMap  :: M.Map StrlType CId
                          , _typeSynonyms :: M.Map TypeName CType
                          , _typeCorres   :: DList.DList (CId, SF.Type 'Zero)  -- C type names corresponding to Cogent types
                          , _absTypes     :: M.Map TypeName (S.Set [CId])
                          , _custTypeGen  :: M.Map (SF.Type 'Zero) (CId, CustTyGenInfo)
                          , _funClasses   :: FunClass
                          , _localOracle  :: Integer
                          , _globalOracle :: Integer
                          , _varPool      :: VarPool
                          }

makeLenses ''GenState

recycleVars :: VarPool -> Gen v ()
recycleVars pool =
  use varPool >>= \pool' ->
  -- varPool .= M.unionWith (\vs1 vs2 -> L.nub (vs1 ++ vs2)) pool' pool
  varPool .= M.unionWith (\vs1 vs2 -> __assert (L.null $ L.intersect vs1 vs2) "recycleVars: found duplicates" >>
                                      (vs1 ++ vs2)) pool' pool

mergePools :: [VarPool] -> VarPool
mergePools = M.unionsWith (\vs1 vs2 -> L.nub (vs1 ++ vs2))

intersectPools :: VarPool -> VarPool -> VarPool
intersectPools = M.intersectionWith L.intersect

newtype Gen v a = Gen { runGen :: RWS (GenRead v) () GenState a }
                deriving (Functor, Applicative, Monad,
                          MonadReader (GenRead v),
                          MonadState  GenState)

-- Generates `enum tag_t' and `tag_t'
genEnum :: Gen v [CExtDecl]
genEnum = do
  tdefs <- use cTypeDefs
  let enums = L.filter (\tdef -> case fst tdef of Variant _ -> True ; _ -> False) tdefs  -- get all variant types
  if null enums
    then return []
    else let tags = S.unions $ P.map ((\(Variant alts) -> S.map tagEnum $ M.keysSet alts) . fst) enums
             enumMembers = P.map (,Nothing) $ S.toList tags
         in return $ [CDecl $ CEnumDecl (Just tagsT) enumMembers, CDecl $ CTypeDecl (CEnum tagsT) [tagsT]]

-- NOTE: It's not used becuase it's defined in cogent-defns.h / zilinc
genBool :: Gen v [CExtDecl]
genBool = pure [ CDecl $ CStructDecl boolT [(CogentPrim U8, Just boolField)]
               , CDecl $ CTypeDecl (CStruct boolT) [boolT]]

-- NOTE: It's not used becuase it's defined in cogent-defns.h / zilinc
genUnit :: Gen v [CExtDecl]
genUnit = pure [ CDecl $ CStructDecl unitT [(CInt True CIntT, Just dummyField)]  -- NOTE: now the dummy field is an int for verification / zilinc
               , CDecl $ CTypeDecl (CStruct unitT) [unitT]]

genLetTrueEnum :: Gen v [CExtDecl]
genLetTrueEnum = getMon $
  (whenM __cogent_flet_in_if $ pure $ [CDecl $ CEnumDecl Nothing [(letTrue, Just (CConst $ CNumConst 1 (CInt True CIntT) DEC))]]) <>
  (whenM __cogent_fletbang_in_if $ pure $ [CDecl $ CEnumDecl Nothing [(letbangTrue, Just (CConst $ CNumConst 1 (CInt True CIntT) DEC))]])

genFunClasses :: Gen v ([CExtDecl], [TypeName])  -- NOTE: also returns a list of c-typenames that represents function types (for #63) / zilinc
genFunClasses = do funclasses <- use funClasses
                   let fas = S.unions $ M.elems funclasses
                       ufe = if __cogent_funtyped_func_enum && not (S.null fas) then genFunEnum untypedFuncEnum fas else []
                   fcls_tns <- forM (M.toList funclasses) $ \(t,fns) -> do
                                 tn <- getStrlTypeCId t
                                 let enum = if not __cogent_funtyped_func_enum
                                              then genFunEnum tn fns
                                              else [CDecl $ CTypeDecl (CIdent untypedFuncEnum) [tn]]
                                     Function ti to = t
                                 disp <- genFunDispatch tn (ti,to) fns
                                 return (enum ++ disp, tn)
                   return (ufe ++ concat (map fst fcls_tns), map snd fcls_tns)
  where genFunEnum :: CId -> S.Set (FunName, Attr) -> [CExtDecl]
        genFunEnum tn (S.toList -> s) =
          let fes = map (funEnum . fst) s
          in [CDecl $ CEnumDecl (Just tn) (map ((,Nothing)) fes), CDecl $ CTypeDecl (CEnum tn) [tn]]

genFunDispatch :: CId -> (CType, CType) -> S.Set (FunName, Attr) -> Gen v [CExtDecl]
genFunDispatch tn (ti, to) (S.toList -> fs) = do
  let tn' = if __cogent_funtyped_func_enum then untypedFuncEnum else tn
      disp = funDispatch tn
  localOracle .= 0
  r' <- freshLocalCId 'a'  -- return
  f' <- freshLocalCId 'a'  -- function
  x' <- freshLocalCId 'a'  -- arg
  let body fm = case fs of
                  []  -> __impossible "genFunDispatch"
                  [(f,a)] -> [CBIStmt $ genInnerFnCall fm a f r' x']
                  _   -> let alts' = flip map (init fs) $ \(f,a) ->
                                       let fncall = genInnerFnCall fm a f r' x'
                                        in (Just (variable $ funEnum f), genBreakWithFnCall fm fncall)
                             deft' = let (f,a) = last fs
                                         fncall = genInnerFnCall fm a f r' x'
                                      in (Nothing, genBreakWithFnCall fm fncall)  -- the last alt will be the `default' case
                          in [CBIStmt $ CSwitch (variable f') (alts'++[deft'])]
  return [CFnMacro (funDispMacro disp) [r',f',x'] [CBIStmt $ CBlock (body True)],  -- macro version
          CFnDefn (to,disp) [(CIdent tn',f'), (ti,x')] (body False) staticInlineFnSpec]  -- funct version
  where
    genInnerFnCall :: Bool -> Attr -> CId -> CId -> CId -> CStmt
    genInnerFnCall fm a f r x = if not fm
      then CReturnFnCall (variable f) [variable x]
      else if fnMacro a
        then CAssignFnCall Nothing (variable $ funMacro f) [variable r, variable x]
        else CAssignFnCall (Just $ variable r) (variable f) [variable x]
    genBreakWithFnCall :: Bool -> CStmt -> CStmt
    genBreakWithFnCall fm s = if fm then CBlock [CBIStmt s, CBIStmt CBreak] else s

genTyDecl :: (StrlType, CId) -> [TypeName] -> [CExtDecl]
genTyDecl (Record x _, n) _ = [CDecl $ CStructDecl n (map (second Just . swap) x), genTySynDecl (n, CStruct n)]
genTyDecl (Product t1 t2, n) _ = [CDecl $ CStructDecl n [(t1, Just p1), (t2, Just p2)]]
genTyDecl (Variant x, n) _ = case __cogent_funion_for_variants of
  False -> [CDecl $ CStructDecl n ((CIdent $ tagsT, Just fieldTag) : map (second Just . swap) (M.toList x)),
            genTySynDecl (n, CStruct n)]
  True  -> [CDecl $ CStructDecl n [(CIdent tagsT, Just fieldTag), (CUnion Nothing $ Just (map swap (M.toList x)), Nothing)],
            genTySynDecl (n, CStruct n)]
genTyDecl (Function t1 t2, n) tns =
  if n `elem` tns then []
                  else [CDecl $ CTypeDecl (CIdent fty) [n]]
  where fty = if __cogent_funtyped_func_enum then untypedFuncEnum else unitT
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

lookupTypeCId :: SF.Type 'Zero -> Gen v (Maybe CId)
lookupTypeCId (TVar     {}) = __impossible "lookupTypeCId"
lookupTypeCId (TVarBang {}) = __impossible "lookupTypeCId"
lookupTypeCId (TCon tn [] _) = fmap (const tn) . M.lookup tn <$> use absTypes
lookupTypeCId (TCon tn ts _) = getCompose (forM ts (\t -> (if isUnboxed t then ('u':) else id) <$> (Compose . lookupTypeCId) t) >>= \ts' ->
                                           Compose (M.lookup tn <$> use absTypes) >>= \tss ->
                                           Compose $ return (if ts' `S.member` tss
                                                               then return $ tn ++ "_" ++ L.intercalate "_" ts'
                                                               else Nothing))
lookupTypeCId (TProduct t1 t2) = getCompose (Compose . lookupStrlTypeCId =<< Record <$> (P.zip [p1,p2] <$> mapM (Compose . lookupType) [t1,t2]) <*> pure True)
lookupTypeCId (TSum fs) = getCompose (Compose . lookupStrlTypeCId =<< Variant . M.fromList <$> mapM (secondM (Compose . lookupType) . second fst) fs)
lookupTypeCId (TFun t1 t2) = getCompose (Compose . lookupStrlTypeCId =<< Function <$> (Compose . lookupType) t1 <*> (Compose . lookupType) t2)  -- Use the enum type for function dispatching
lookupTypeCId (TRecord fs s) = getCompose (Compose . lookupStrlTypeCId =<< Record <$> (mapM (\(a,(b,_)) -> (a,) <$> (Compose . lookupType) b) fs) <*> pure True)
lookupTypeCId t = Just <$> typeCId t

-- XXX | -- NOTE: (Monad (Gen v), Reducer (Maybe a) (First a)) => Reducer (Gen v (Maybe a)) (Mon (Gen v) (First a)) / zilinc
-- XXX | -- If none of a type's parts are used, then getFirst -> None; otherwise getFirst -> Just cid
-- XXX | typeCIdUsage :: forall v. SF.Type Zero -> Gen v (First CId)
-- XXX | typeCIdUsage (TVar     {}) = __impossible "typeCIdUsage"
-- XXX | typeCIdUsage (TVarBang {}) = __impossible "typeCIdUsage"
-- XXX | typeCIdUsage (TCon tn [] _) = fmap (const tn) <$> (First . M.lookup tn <$> use absTypes)
-- XXX | typeCIdUsage (TCon tn ts _) = getMon $ foldReduce (map ((getFirst <$>) . typeCIdUsage) ts :: [Gen v (Maybe CId)])
-- XXX | typeCIdUsage (TProduct t1 t2) = getMon $ foldReduce [getFirst <$> typeCIdUsage t1 :: Gen v (Maybe CId), getFirst <$> typeCIdUsage t2]
-- XXX | typeCIdUsage (TSum fs) = getMon $ foldReduce (map ((getFirst <$>) . typeCIdUsage . snd) fs :: [Gen v (Maybe CId)])
-- XXX | typeCIdUsage (TFun t1 t2) = getMon $ foldReduce [getFirst <$> typeCIdUsage t1 :: Gen v (Maybe CId), getFirst <$> typeCIdUsage t2]
-- XXX | typeCIdUsage (TRecord fs s) = getMon $ foldReduce (map ((getFirst <$>) . typeCIdUsage . fst . snd) fs :: [Gen v (Maybe CId)])
-- XXX | typeCIdUsage t = return $ First Nothing  -- base types

typeCId :: SF.Type 'Zero -> Gen v CId
typeCId t = use custTypeGen >>= \ctg ->
            case M.lookup t ctg of
              Just (n,_) -> return n
              Nothing -> 
                (if __cogent_fflatten_nestings then typeCIdFlat else typeCId') t >>= \n ->
                when (isUnstable t) (typeCorres %= DList.cons (toCName n, t)) >>
                return n
  where
    typeCId' :: SF.Type 'Zero -> Gen v CId
    typeCId' (TVar     {}) = __impossible "typeCId' (in typeCId)"
    typeCId' (TVarBang {}) = __impossible "typeCId' (in typeCId)"
    typeCId' (TPrim pt) | pt == Boolean = return boolT
                        | otherwise = primCId <$> pure pt
    typeCId' (TString) = return "char"
    typeCId' (TCon tn [] s) = do
      absTypes %= M.insert tn (S.singleton []) -- NOTE: Since it's non-parametric, it can have only one entry which is always the same / zilinc
      -- getStrlTypeCId (AbsType tn)  -- NOTE: Monomorphic abstract types will remain undefined! / zilinc
      return tn
    typeCId' (TCon tn ts s) = do  -- mapM typeCId ts >>= \ts' -> return (tn ++ "_" ++ L.intercalate "_" ts')
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
    typeCId' (TProduct t1 t2) = getStrlTypeCId =<< Record <$> (P.zip [p1,p2] <$> mapM genType [t1,t2]) <*> pure True
    typeCId' (TSum fs) = getStrlTypeCId =<< Variant . M.fromList <$> mapM (secondM genType . second fst) fs
    typeCId' (TFun t1 t2) = getStrlTypeCId =<< Function <$> genType t1 <*> genType t2  -- Use the enum type for function dispatching
    typeCId' (TRecord fs s) = getStrlTypeCId =<< Record <$> (mapM (\(a,(b,_)) -> (a,) <$> genType b) fs) <*> pure True
    typeCId' (TUnit) = return unitT

    typeCIdFlat :: SF.Type 'Zero -> Gen v CId
    typeCIdFlat (TProduct t1 t2) = do
      ts' <- mapM genType [t1,t2]
      fss <- forM (P.zip3 [p1,p2] [t1,t2] ts') $ \(f,t,t') -> case t' of
        CPtr _ -> return [(f,t')]
        _      -> collFields f t
      getStrlTypeCId $ Record (concat fss) True
    -- typeCIdFlat (TSum fs) = __todo  -- Don't flatten variants for now. It's not clear how to incorporate with --funion-for-variants
    typeCIdFlat (TRecord fs s) = do
      let (fns,ts) = P.unzip $ P.map (second fst) fs
      ts' <- mapM genType ts
      fss <- forM (P.zip3 fns ts ts') $ \(f,t,t') -> case t' of
        CPtr _ -> return [(f,t')]
        _      -> collFields f t
      getStrlTypeCId $ Record (concat fss) True
    typeCIdFlat t = typeCId' t

    collFields :: FieldName -> SF.Type 'Zero -> Gen v [(CId, CType)]
    collFields fn (TProduct t1 t2) = concat <$> zipWithM collFields (P.map ((fn ++ "_") ++) [p1,p2]) [t1,t2]
    collFields fn (TRecord fs s) = let (fns,ts) = P.unzip (P.map (second fst) fs) in concat <$> zipWithM collFields (P.map ((fn ++ "_") ++) fns) ts
    collFields fn t = (:[]) . (fn,) <$> genType t

    isUnstable :: SF.Type 'Zero -> Bool
    isUnstable (TCon _ _ _) = True  -- NOTE: we relax the rule here to generate all abstract types in the table / zilinc (28/5/15)
    -- XXX | isUnstable (TCon _ (_:_) _) = True
    isUnstable (TProduct {}) = True
    isUnstable (TSum _) = True
    isUnstable (TRecord {}) = True
    isUnstable _ = False

-- Made for Glue
absTypeCId :: SF.Type 'Zero -> Gen v CId
absTypeCId (TCon tn [] s) = return tn
absTypeCId (TCon tn ts s) = do
  ts' <- forM ts $ \t -> (if isUnboxed t then ('u':) else id) <$> typeCId t
  return (tn ++ "_" ++ L.intercalate "_" ts')
absTypeCId _ = __impossible "absTypeCId"

-- Returns the right C type
genType :: SF.Type 'Zero -> Gen v CType
genType t@(TRecord _ s) | s /= Unboxed = CPtr . CIdent <$> typeCId t
genType t@(TString)                    = CPtr . CIdent <$> typeCId t
genType t@(TCon _ _ s)  | s /= Unboxed = CPtr . CIdent <$> typeCId t
genType t                              =        CIdent <$> typeCId t

genTypeA :: Bool -> SF.Type 'Zero -> Gen v CType
genTypeA is_arg t@(TRecord _ Unboxed) | is_arg && __cogent_funboxed_arg_by_ref = CPtr . CIdent <$> typeCId t  -- TODO: sizeof
genTypeA _ t = genType t

lookupType :: SF.Type 'Zero -> Gen v (Maybe CType)
lookupType t@(TRecord _ s) | s /= Unboxed = getCompose (CPtr . CIdent <$> Compose (lookupTypeCId t))
lookupType t@(TString)                    = getCompose (CPtr . CIdent <$> Compose (lookupTypeCId t))
lookupType t@(TCon _ _ s)  | s /= Unboxed = getCompose (CPtr . CIdent <$> Compose (lookupTypeCId t))
lookupType t                              = getCompose (       CIdent <$> Compose (lookupTypeCId t))

-- Add a type synonym
genType' :: SF.Type 'Zero -> TypeName -> Gen v CType
genType' = genTypeA' False

genTypeA' :: Bool -> SF.Type 'Zero -> TypeName -> Gen v CType
genTypeA' is_arg ty n = do ty' <- genTypeA is_arg ty
                           typeSynonyms %= M.insert n ty'
                           return ty'

-- XXX | assign :: CId -> Char -> [CExpr] -> [CBlockItem]
-- XXX | assign rv c = map ((\(x,y) -> CBIStmt $ CAssign (CStructDot (variable rv) x) y) .
-- XXX |                    first ((c:) . show)) . P.zip [(1 :: Int)..]

-- (assignee, assigner)
assign1 :: CExpr -> CExpr -> CBlockItem
assign1 a e = CBIStmt $ CAssign a e

-- Given a C type, returns a fresh local variable e
declare :: CType -> Gen v (CId, [CBlockItem], [CBlockItem])
declare ty = declareG ty Nothing

-- XXX | Same as `declare', but don't reuse any vars
-- XXX | declareNoReuse :: CType -> Gen v (CId, [CBlockItem], [CBlockItem])
-- XXX | declareNoReuse ty = do
-- XXX |   v <- freshLocalCId 'r'
-- XXX |   let decl = CBIDecl $ CVarDecl ty v True Nothing
-- XXX |   return $ (v,[decl],[])

-- XXX | A var_id given
-- XXX | declare' :: CType -> CId -> Gen v CBlockItem
-- XXX | declare' ty var = declareG' ty var Nothing

-- declareInit ty e: declares a new var, initialises it to e, and recycle variables
-- associated with e
declareInit :: CType -> CExpr -> VarPool -> Gen v (CId, [CBlockItem], [CBlockItem])
declareInit ty e p = declareG ty (Just $ CInitE e) <* recycleVars p

-- XXX | declareInit' :: CType -> CId -> CExpr -> Gen v CBlockItem
-- XXX | declareInit' ty v e = declareG' ty v $ Just $ CInitE e

-- declareG ty minit: (optionally) initialises a freshvar of type ty
declareG :: CType -> Maybe CInitializer -> Gen v (CId, [CBlockItem], [CBlockItem])
declareG ty minit | __cogent_fshare_linear_vars = do
  pool <- use varPool
  case M.lookup ty pool of
    Nothing -> do
      v <- freshLocalCId 'r'
      let decl = [CBIDecl $ CVarDecl ty v True Nothing]
          ass = case minit of
                  Nothing -> []
                  Just (CInitE e) -> [assign1 (variable v) e]
                  Just (CInitList il) -> [assign1 (variable v) (CCompLit ty il)]
      return (v,decl,ass)
    Just []     -> do varPool .= M.delete ty pool; declareG ty minit
    Just (v:vs) -> do
      varPool .= M.update (const $ Just vs) ty pool
      case minit of
        Nothing -> return (v, [], [CBIStmt CEmptyStmt])  -- FIXME: shouldn't have anything in p though / zilinc
        Just (CInitE e) -> return (v, [], [assign1 (variable v) e])
        Just (CInitList il) -> return (v, [], [assign1 (variable v) (CCompLit ty il)])
declareG ty minit = do
  v <- freshLocalCId 'r'
  let decl = CBIDecl $ CVarDecl ty v True minit
  return (v,[],[decl])

-- similar to declareG, with a given name
-- declareG' :: CType -> CId -> Maybe CInitializer -> Gen v CBlockItem
-- declareG' ty v minit = return (CBIDecl $ CVarDecl ty v True minit)

-- If assigned to a var, then recycle
maybeAssign :: Maybe CId -> CExpr -> VarPool -> Gen v (CExpr, [CBlockItem], VarPool)
maybeAssign Nothing  e p = return (e,[],p)
maybeAssign (Just v) e p | __cogent_fintermediate_vars = maybeAssign Nothing e p
                         | otherwise = recycleVars p >> return (variable v, [assign1 (variable v) e], M.empty)

forceDecl :: Maybe CId -> CType -> Gen v (CId, [CBlockItem], [CBlockItem])
forceDecl Nothing  t = declare t
forceDecl (Just v) t = return (v,[],[])

-- If assigned to a new var, then recycle
aNewVar :: CType -> CExpr -> VarPool -> Gen v (CExpr, [CBlockItem], [CBlockItem], VarPool)
aNewVar t e p | __cogent_simpl_cg && not (isTrivialCExpr e) = (extTup3 M.empty) . (first3 variable) <$> declareInit t e p
              | otherwise = return (e,[],[],p)

-- only used for compound literals
maybeInitCL :: Maybe CId -> CType -> CExpr -> VarPool -> Gen v (CExpr, [CBlockItem], [CBlockItem], VarPool)
maybeInitCL Nothing  t e p | __cogent_fuse_compound_literals = return (e,[],[],p)
                           | otherwise = (extTup3 M.empty) . (first3 variable) <$> declareInit t e p
maybeInitCL (Just v) t e p = noDecls <$> maybeAssign (Just v) e p

withBindings :: Vec v' CExpr -> Gen (v :+: v') a -> Gen v a
withBindings vec = Gen . withRWS (\r s -> (r <++> vec, s)) . runGen

genLit :: Integer -> PrimInt -> CExpr
genLit n pt | pt == Boolean = mkBoolLit $ mkConst U8 n
            | otherwise = CConst $ CNumConst n (CogentPrim pt) DEC

likelihood :: Likelihood -> (CExpr -> CExpr)
likelihood l = case l of Likely   -> likely
                         Regular  -> id
                         Unlikely -> unlikely

mkBoolLit :: CExpr -> CExpr
mkBoolLit e = CCompLit (CIdent boolT) [([CDesignFld boolField], CInitE e)]

true :: CExpr
true = mkConst Boolean 1

mkConst :: PrimInt -> Integer -> CExpr
mkConst pt n | pt == Boolean = mkBoolLit (mkConst U8 n)
             | otherwise = CConst $ CNumConst n (CogentPrim pt) DEC

genOp :: Syn.Op -> SF.Type 'Zero -> [CExpr] -> Gen v CExpr
genOp opr (SF.TPrim pt) es =
  let oprf = case opr of
               -- binary
               Plus        -> (\[e1,e2] -> downcast pt $ CBinOp C.Add  (upcast pt e1) (upcast pt e2))
               Minus       -> (\[e1,e2] -> downcast pt $ CBinOp C.Sub  (upcast pt e1) (upcast pt e2))
               Divide      -> (\[e1,e2] -> (if __cogent_fcheck_undefined then flip (CCondExpr e2) (mkConst pt 0) else id)
                                              (downcast pt $ CBinOp C.Div (upcast pt e1) (upcast pt e2)))
               Times       -> (\[e1,e2] -> downcast pt $ CBinOp C.Mul  (upcast pt e1) (upcast pt e2))
               Mod         -> (\[e1,e2] -> (if __cogent_fcheck_undefined then flip (CCondExpr e2) (mkConst pt 0) else id)
                                              (downcast pt $ CBinOp C.Mod (upcast pt e1) (upcast pt e2)))
               And         -> (\[e1,e2] -> mkBoolLit (CBinOp C.Land (mkStr3 e1 boolField) (mkStr3 e2 boolField)))
               Or          -> (\[e1,e2] -> mkBoolLit (CBinOp C.Lor  (mkStr3 e1 boolField) (mkStr3 e2 boolField)))
               BitAnd      -> (\[e1,e2] -> downcast pt $ CBinOp C.And  (upcast pt e1) (upcast pt e2))
               BitXor      -> (\[e1,e2] -> downcast pt $ CBinOp C.Xor  (upcast pt e1) (upcast pt e2))
               BitOr       -> (\[e1,e2] -> downcast pt $ CBinOp C.Or   (upcast pt e1) (upcast pt e2))
               LShift      -> (\[e1,e2] -> (if __cogent_fcheck_undefined
                                              then CCondExpr (CBinOp C.Ge e2 (mkConst pt $ width pt)) (mkConst pt 0) else id)
                                             (downcast pt $ CBinOp C.Lsh (upcast pt e1) (upcast pt e2)))
               RShift      -> (\[e1,e2] -> (if __cogent_fcheck_undefined
                                              then CCondExpr (CBinOp C.Ge e2 (mkConst pt $ width pt)) (mkConst pt 0) else id)
                                             (downcast pt $ CBinOp C.Rsh (upcast pt e1) (upcast pt e2)))
               Gt          -> (\[e1,e2] -> mkBoolLit $ CBinOp C.Gt e1 e2)
               Lt          -> (\[e1,e2] -> mkBoolLit $ CBinOp C.Lt e1 e2)
               Ge          -> (\[e1,e2] -> mkBoolLit $ CBinOp C.Ge e1 e2)
               Le          -> (\[e1,e2] -> mkBoolLit $ CBinOp C.Le e1 e2)
               Syn.Eq      -> (\[e1,e2] -> case pt of
                                Boolean -> mkBoolLit (CBinOp C.Eq (mkStr3 e1 boolField) (mkStr3 e2 boolField))
                                _       -> mkBoolLit (CBinOp C.Eq e1 e2))
               Syn.NEq     -> (\[e1,e2] -> case pt of
                                Boolean -> mkBoolLit (CBinOp C.Ne (mkStr3 e1 boolField) (mkStr3 e2 boolField))
                                _       -> mkBoolLit (CBinOp C.Ne e1 e2))
               -- unary
               Syn.Not        -> (\[e1] -> mkBoolLit (CUnOp C.Lnot (mkStr3 e1 boolField)))
               Syn.Complement -> (\[e1] -> downcast pt $ CUnOp C.Not (upcast pt e1))
   in return $ oprf es
  where width = \case U8 -> 8; U16 -> 16; U32 -> 32; U64 -> 64; Boolean -> 8
        upcast, downcast :: PrimInt -> CExpr -> CExpr
        upcast   pt e = if pt `elem` [U8, U16] then CTypeCast u32 e else e
        downcast pt e = if pt `elem` [U8, U16] then CTypeCast (CogentPrim pt) e else e
genOp _ _ _ = __impossible "genOp"

genExpr_ :: TypedExpr 'Zero v VarName -> Gen v (CExpr, [CBlockItem], [CBlockItem], VarPool)
genExpr_ = genExpr Nothing

noDecls :: (CExpr, [CBlockItem], VarPool) -> (CExpr, [CBlockItem], [CBlockItem], VarPool)
noDecls (e,s,p) = (e,[],s,p)

-- The first argument is the return value on one level up
-- Returns: (expr, decls, stmts, reusable_var_pool)
genExpr :: Maybe CId -> TypedExpr 'Zero v VarName -> Gen v (CExpr, [CBlockItem], [CBlockItem], VarPool)
genExpr _ (TE t (Op opr [])) = __impossible "genExpr"
genExpr mv (TE t (Op opr es@(e1:_))) = do
  (es',decls,stms,ps) <- L.unzip4 <$> mapM genExpr_ es
  e' <- genOp opr (exprType e1) es'
  (v,ass,vp) <- maybeAssign mv e' (mergePools ps)
  return (v, concat decls, concat stms ++ ass, vp)
genExpr mv (TE t (ILit n pt)) =
  noDecls <$> maybeAssign mv (genLit n pt) M.empty
genExpr mv (TE t (SLit s)) =
  noDecls <$> maybeAssign mv (CConst $ CStringConst s) M.empty
genExpr mv (TE t (Unit)) = do
  t' <- genType t
  let e' = CCompLit t' [([CDesignFld dummyField], CInitE (CConst $ CNumConst 0 (CInt True CIntT) DEC))]
  noDecls <$> maybeAssign mv e' M.empty
genExpr mv (TE t (Variable v)) = do  -- NOTE: this `v' could be a higher-order function
  e' <- ((`at` fst v) <$> ask)
  -- --------------------------------------------------------------------------
  -- XXX | NOTE: We need to establish C scope in order to determine the life time of linear C variables.
  -- XXX |       Thus --fshare-linear-vars is not working due to it. It now does a weaker modification,
  -- XXX |       which moves all variable declarations to the beginning of a function / zilinc
  p <- whenM __cogent_fshare_linear_vars $ do
    t' <- genType t
    whenM (isTypeLinear t) $ case e' of
      CVar v _ -> return $ M.singleton t' [v]
      _ -> return mempty
  -- --------------------------------------------------------------------------
  noDecls <$> maybeAssign mv e' p
genExpr mv (TE t (Fun f _ _)) =  -- it is a function identifier
  noDecls <$> maybeAssign mv (variable $ funEnum f) M.empty
genExpr mv (TE t (App e1@(TE _ (Fun f _ MacroCall)) e2)) | __cogent_ffncall_as_macro = do  -- first-order function application
  (e2',e2decl,e2stm,e2p) <- genExpr_ e2
  t' <- genType t
  (v,vdecl,vstm) <- forceDecl mv t'
  let call = [CBIStmt $ CAssignFnCall Nothing (variable $ funMacro f) [variable v, e2']]
  recycleVars e2p
  return (variable v, e2decl ++ vdecl, e2stm ++ vstm ++ call, M.empty)
genExpr mv (TE t (App e1@(TE _ (Fun f _ _)) e2)) = do  -- first-order function application
  (e2',e2decl,e2stm,e2p) <- genExpr_ e2
  (v,ass,vp) <- maybeAssign mv (CEFnCall (variable f) [e2']) e2p
  return (v, e2decl, e2stm ++ ass, vp)
genExpr mv (TE t (App e1 e2)) | __cogent_ffncall_as_macro = do
  enumt <- typeCId $ exprType e1
  (e1',e1decl,e1stm,e1p) <- genExpr_ e1
  (e2',e2decl,e2stm,e2p) <- genExpr_ e2
  let fname = funDispatch enumt
  t' <- genType t
  (v,vdecl,vstm) <- forceDecl mv t'
  let call = [CBIStmt $ CAssignFnCall Nothing (variable $ funDispMacro fname) [variable v, e1', e2']]
  recycleVars (mergePools [e1p,e2p])
  return (variable v, e1decl ++ e2decl ++ vdecl, e1stm ++ e2stm ++ vstm ++ call, M.empty)
genExpr mv (TE t (App e1 e2)) = do   -- change `e1' to its dispatch function, with `e' being the first argument
  enumt <- typeCId $ exprType e1
  (e1',e1decl,e1stm,e1p) <- genExpr_ e1
  (e2',e2decl,e2stm,e2p) <- genExpr_ e2
  let fname = variable $ funDispatch enumt
  (v',ass,vp) <- maybeAssign mv (CEFnCall fname [e1', e2']) (mergePools [e1p,e2p])
  return (v', e1decl ++ e2decl, e1stm ++ e2stm ++ ass, vp)
genExpr mv (TE t (Take _ rec fld e)) = do
  -- NOTE: New `rec' and old `rec' CAN be the same at this point, as long as they get copied while being
  --       updated. Similarly, the field can be `rec.f' instead of a new one / zilinc
  (rec',recdecl,recstm,recp) <- genExpr_ rec
  let rect@(TRecord fs s) = exprType rec
  (rec'',recdecl',recstm',recp') <- flip3 aNewVar recp rec' =<< genType rect
  ft <- genType . fst . snd $ fs!!fld
  (f',fdecl,fstm,fp) <- (case __cogent_fintermediate_vars of
    True  -> return . (extTup3 M.empty) . (first3 variable) <=< flip (declareInit ft) M.empty
    False -> return . (,[],[],M.empty)) $ (if s == Unboxed then mkStr3 else mkStr3') rec'' (fst $ fs!!fld)
  (f'',fdecl',fstm',fp') <- aNewVar ft f' fp
  (e',edecl,estm,ep) <- withBindings (Cons f'' (Cons rec'' Nil)) $ genExpr mv e
  return (e', recdecl ++ recdecl' ++ fdecl ++ fdecl' ++ edecl, recstm ++ recstm' ++ fstm ++ fstm' ++ estm, mergePools [fp',recp',ep])
genExpr mv (TE t (Put rec fld val)) = do
  t' <- genType t
  -- NOTE: always copy a new record and leave rec unchanged. This prevents the following problem:
  -- > let x' = x {f = fv}  -- x is an unboxed record
  -- >  in (x', x)
  -- >  -- x shouldn't change its field f to fv
  let TRecord fs s = exprType rec
  (rec',recdecl,recstm,recp) <- genExpr_ rec
  (rec'',recdecl',recstm') <- declareInit t' rec' recp
  (val',valdecl,valstm,valp) <- genExpr_ val
  let put = assign1 ((if s == Unboxed then mkStr3 else mkStr3') (variable rec'') (fst $ fs!!fld)) val'
  recycleVars valp
  (v,ass,vp) <- maybeAssign mv (variable rec'') M.empty
  return (v, recdecl ++ recdecl' ++ valdecl, recstm ++ recstm' ++ valstm ++ put : ass, vp)
genExpr mv (TE t (Let _ e1 e2))
  | not __cogent_flet_in_if || isAtom (untypeE e1) = do
    t1' <- genType $ exprType e1
    (e1',e1decl,e1stm,e1p) <- genExpr_ e1
    (v,vdecl,vstm) <- declareInit t1' e1' e1p
    (e2',e2decl,e2stm,e2p) <- withBindings (Cons (variable v) Nil) $ genExpr mv e2
    return (e2', e1decl ++ vdecl ++ e2decl, e1stm ++ vstm ++ e2stm, e2p)
  | otherwise = do
    t1' <- genType $ exprType e1
    (v,vdecl,vstm) <- declare t1'
    (e1',e1decl,e1stm,e1p) <- genExpr_ e1
    let ass = assign1 (variable v) e1'
        binding = [CBIStmt $ CIfStmt (variable letTrue) (CBlock $ e1stm ++ [ass]) CEmptyStmt]
    recycleVars e1p
    (e2',e2decl,e2stm,e2p) <- withBindings (Cons (variable v) Nil) $ genExpr mv e2
    return (e2', vdecl ++ e1decl ++ e2decl, vstm ++ binding ++ e2stm, e2p)
genExpr mv (TE t (LetBang vs v e1 e2)) | not __cogent_fletbang_in_if = genExpr mv (TE t (Let v e1 e2))
                                       | otherwise = do
    t1' <- genType $ exprType e1
    (v,vdecl,vstm) <- declare t1'
    (e1',e1decl,e1stm,e1p) <- genExpr_ e1
    let ass = assign1 (variable v) e1'
        binding = [CBIStmt $ CIfStmt (variable letbangTrue) (CBlock $ e1stm ++ [ass]) CEmptyStmt]
    recycleVars e1p
    (e2',e2decl,e2stm,e2p) <- withBindings (Cons (variable v) Nil) $ genExpr mv e2
    return (e2', vdecl ++ e1decl ++ e2decl, vstm ++ binding ++ e2stm, e2p)
genExpr mv (TE t (Tuple e1 e2)) = do
  (e1',e1decl,e1stm,e1p) <- genExpr_ e1
  (e2',e2decl,e2stm,e2p) <- genExpr_ e2
  t' <- genType t
  (v,vdecl,ass,vp) <- flip (maybeInitCL mv t') (mergePools [e1p,e2p]) $ CCompLit t' $
                        P.zip (map ((:[]) . CDesignFld) [p1,p2]) (map CInitE [e1',e2'])
  return (v, e1decl ++ e2decl ++ vdecl, e1stm ++ e2stm ++ ass, vp)
genExpr mv (TE t (Struct fs)) = do
  let (ns,es) = P.unzip fs
  (es',decls,stms,eps) <- L.unzip4 <$> mapM genExpr_ es
  t' <- genType t
  (v,vdecl,ass,vp) <- flip (maybeInitCL mv t') (mergePools eps) $ CCompLit t' $
                        P.zip (map ((:[]) . CDesignFld) ns) (map CInitE es')
  return (v, concat decls ++ vdecl, concat stms ++ ass, vp)
genExpr mv (TE t (Con tag e)) = do
  (e',edecl,estm,ep) <- genExpr_ e
  t' <- genType t
  (v,vdecl,ass,vp) <- flip (maybeInitCL mv t') ep $ CCompLit t' $ map (map CDesignFld *** CInitE)
                        [([fieldTag], variable $ tagEnum tag), ([tag], e')]
  return (v, edecl ++ vdecl, estm ++ ass, vp)
genExpr mv (TE t (Member rec fld)) = do
  let TRecord fs s = exprType rec
  (rec',recdecl,recstm,recp) <- genExpr_ rec
  let e' = (if s == Unboxed then mkStr3 else mkStr3') rec' (fst $ fs!!fld)
  (v',ass,vp) <- maybeAssign mv e' recp
  return (v', recdecl, recstm ++ ass, vp)
genExpr mv (TE t (If c e1 e2)) = do
  (v,vdecl,vstm) <- case mv of
    Nothing -> declare =<< genType t
    Just v  -> return (v,[],[])
  (c',cdecl,cstm,cp) <- genExpr_ c
  pool0 <- use varPool
  (e1',e1decl,e1stm,e1p) <- genExpr (if __cogent_fintermediate_vars then Nothing else Just v) e1
  pool1 <- use varPool
  varPool .= pool0
  (e2',e2decl,e2stm,e2p) <- genExpr (if __cogent_fintermediate_vars then Nothing else Just v) e2
  pool2 <- use varPool
  varPool .= intersectPools pool1 pool2  -- it seems that pool_final = (e1p & e2p) + (pool1 & pool2)
  let ifstm = if __cogent_fintermediate_vars
                then CBIStmt $ CIfStmt (mkStr3 c' boolField) (CBlock $ e1stm ++ [assign1 (variable v) e1'])
                                                             (CBlock $ e2stm ++ [assign1 (variable v) e2'])
                else CBIStmt $ CIfStmt (mkStr3 c' boolField) (CBlock e1stm) (CBlock e2stm)
  recycleVars (mergePools [cp, intersectPools e1p e2p])
  return (variable v, vdecl ++ cdecl ++ e1decl ++ e2decl, vstm ++ cstm ++ [ifstm], M.empty)
genExpr mv (TE t (Case e tag (l1,_,e1) (l2,_,e2))) = do  -- NOTE: likelihood `l2' unused because it has become binary / zilinc
  (v,vdecl,vstm) <- case mv of
    Nothing -> (declare =<< genType t)
    Just v  -> return (v,[],[])
  (e',edecl,estm,ep) <- genExpr_ e
  let et@(TSum altys) = exprType e
  (e'',edecl',estm',ep') <- flip3 aNewVar ep e' =<< genType et
  let tags = filter (/= tag) $ map fst altys
      cnd = CBinOp C.Eq (mkStr3 e'' fieldTag) (variable $ tagEnum tag)
      (alty1,False) = fromJust $ L.lookup tag altys
  pool0 <- use varPool
  (v1,v1decl,v1stm,v1p) <- flip3 aNewVar M.empty (mkStr3 e'' tag) =<< genType alty1
  (e1',e1decl,e1stm,e1p) <- withBindings (Cons v1 Nil) $ genExpr (if __cogent_fintermediate_vars then Nothing else Just v) e1
  pool1 <- use varPool
  varPool .= pool0
  -- NOTE: create a smaller Enum, copy over everything / zilinc
  restt <- genType $ TSum $ filter (\al -> fst al /= tag) altys
  (rest',restdecl,reststm) <- case __cogent_fshare_variants of
     False -> (first3 variable) <$> (declareG restt $ Just $ CInitList $ map ((:[]) . CDesignFld &&& CInitE . mkStr3 e'') (fieldTag:tags))
     True  -> return (e'',[],[])
  (rest'',restdecl',reststm',restp') <- aNewVar restt rest' M.empty
  (e2',e2decl,e2stm,e2p) <- withBindings (Cons rest'' Nil) $ genExpr (if __cogent_fintermediate_vars then Nothing else Just v) e2
  pool2 <- use varPool
  varPool .= intersectPools pool1 pool2
  let macro1 = likelihood l1
      -- XXX | macro2 = likelihood l2
      ifstm = if __cogent_fintermediate_vars
                then CBIStmt $ CIfStmt (macro1 cnd) (CBlock $ v1stm ++ e1stm ++ [assign1 (variable v) e1'])
                                                    (CBlock $ reststm ++ reststm' ++ e2stm ++ [assign1 (variable v) e2'])
                else CBIStmt $ CIfStmt (macro1 cnd) (CBlock $ v1stm ++ e1stm) (CBlock $ reststm ++ reststm' ++ e2stm)
  recycleVars (mergePools [ep', intersectPools (mergePools [v1p,e1p]) (mergePools [restp',e2p])])
  return (variable v, vdecl ++ edecl ++ edecl' ++ v1decl ++ e1decl ++ restdecl ++ restdecl' ++ e2decl, vstm ++ estm ++ estm' ++ [ifstm], M.empty)
genExpr mv (TE _ (Esac e)) | not __cogent_fnew_subtyping = do
  (e',edecl,estm,ep) <- genExpr_ e
  let TSum [(tag,(ty,False))] = exprType e
  ct <- genType ty  -- FIXME: is it useful? / zilinc
  (v,ass,vp) <- flip (maybeAssign mv) ep $ mkStr3 e' tag
  return (v, edecl, estm ++ ass, vp)
genExpr mv (TE _ (Esac e)) = do  -- | __cogent_fnew_subtyping
  (e',edecl,estm,ep) <- genExpr_ e
  let TSum alts = exprType e
      [(tag,(_,_))] = filter (not . snd . snd) alts
  (v,ass,vp) <- flip (maybeAssign mv) ep $ mkStr3 e' tag
  return (v, edecl, estm ++ ass, vp)
genExpr mv (TE t (Split _ e1 e2)) = do
  (e1',e1decl,e1stm,e1p) <- genExpr_ e1
  let e1t@(TProduct t1 t2) = exprType e1
  (e1'',e1decl',e1stm',e1p') <- flip3 aNewVar e1p e1' =<< genType e1t
  t1' <- genType t1
  t2' <- genType t2
  (v1,v1decl,v1stm) <- declareInit t1' (mkStr3 e1'' p1) M.empty
  (v2,v2decl,v2stm) <- declareInit t2' (mkStr3 e1'' p2) M.empty
  recycleVars e1p'
  (e2',e2decl,e2stm,e2p) <- withBindings (fromJust $ cvtFromList (SSuc $ SSuc SZero) [variable v1, variable v2]) $ genExpr mv e2
  return (e2', e1decl ++ e1decl' ++ v1decl ++ v2decl ++ e2decl, e1stm ++ e1stm' ++ v1stm ++ v2stm ++ e2stm, e2p)
  -- NOTE: It's commented out because split shoule behave like let / zilinc
  -- XXX | NOTE: It's an optimisation here, we no more generate new variables / zilinc
  -- XXX | (e2',e2stm) <- withBindings (fromJust $ cvtFromList (SSuc $ SSuc SZero) [mkStr3 e1' p1, mkStr3 e1' p2]) $ genExpr mv e2
  -- XXX | return (e2', e1stm ++ e2stm)
genExpr mv (TE t (Promote _ (TE _ (Con tag e)))) = do  -- a special case
  (e',e1decl,estm,ep) <- genExpr_ e
  t' <- genType t
  (v,vdecl,ass,vp) <- flip (maybeInitCL mv t') ep $ CCompLit t' $
                        [([CDesignFld fieldTag], CInitE $ variable (tagEnum tag)), ([CDesignFld tag], CInitE e')]
  return (v, e1decl ++ vdecl, estm ++ ass, vp)
genExpr mv (TE t (Promote _ e))
  | et@(TSum alts) <- exprType e = do  -- width subtyping
      let tags = L.map fst alts
      (e',edecl,estm,ep) <- genExpr_ e
      (e'',edecl',estm',ep') <- flip3 aNewVar ep e' =<< genType et
      t' <- genType t
      (v,vdecl,ass,vp) <- flip (maybeInitCL mv t') ep' $ CCompLit t' $ map ((:[]) . CDesignFld &&& CInitE . mkStr3 e'') (fieldTag:tags)
      return (v, edecl ++ edecl' ++ vdecl, estm ++ estm' ++ ass, vp)
  | otherwise = do             -- int promotion
      (e',edecl,estm,ep) <- genExpr_ e
      t' <- genType t
      (v,ass,vp) <- flip (maybeAssign mv) ep $ CTypeCast t' e'
      return (v, edecl, estm ++ ass, vp)

insertSetMap :: Ord a => a -> Maybe (S.Set a) -> Maybe (S.Set a)
insertSetMap x Nothing  = Just $ S.singleton x
insertSetMap x (Just y) = Just $ S.insert x y

fnSpecStaticInline (FnSpec st tq ats) = FnSpec (STStatic:st) (TQInline:tq) ats
fnSpecAttr attr = (if __cogent_fstatic_inline || inlineDef attr then fnSpecStaticInline else id)
fnSpecKind ti to = (if | isTypeHasKind ti k2 && isTypeHasKind to k2 -> fnSpecAttrConst
                       | isTypeInKinds ti [k0,k2] && isTypeInKinds to [k0,k2] -> fnSpecAttrPure
                       | otherwise -> id)
fnSpecAttrConst (FnSpec st tq ats) = FnSpec st tq (GccAttrs [GccAttr "const" []]:ats)
fnSpecAttrPure  (FnSpec st tq ats) = FnSpec st tq (GccAttrs [GccAttr "pure"  []]:ats)

 -- NOTE: This function excessively uses `unsafeCoerce' because of existentials / zilinc
genDefinition :: Definition TypedExpr VarName -> Gen 'Zero [CExtDecl]
genDefinition (FunDef attr fn Nil t rt e) = do
  localOracle .= 0
  varPool .= M.empty
  arg <- freshLocalCId 'a'
  t' <- genTypeA' True (unsafeCoerce t :: SF.Type 'Zero) (argOf fn)
  (e',edecl,estm,_) <- withBindings (Cons (CVar arg Nothing & if __cogent_funboxed_arg_by_ref then CDeref else id) Nil)
                         (genExpr Nothing (unsafeCoerce e :: TypedExpr 'Zero ('Suc 'Zero) VarName))
  rt' <- genType' (unsafeCoerce rt :: SF.Type 'Zero) (retOf fn)
  funClasses %= M.alter (insertSetMap (fn,attr)) (Function t' rt')
  body <- case __cogent_fintermediate_vars of
    True  -> do (rv,rvdecl,rvstm) <- declareInit rt' e' M.empty
                return $ edecl ++ rvdecl ++ estm ++ rvstm ++ [CBIStmt $ CReturn $ Just (variable rv)]
    False -> return $ edecl ++ estm ++ [CBIStmt $ CReturn $ Just e']
  return [CDecl $ CExtFnDecl rt' fn [(t', Nothing)] ((if __cogent_ffunc_purity_attr then fnSpecKind t rt else id) $ fnSpecAttr attr noFnSpec),
          CFnDefn (rt', fn) [(t', arg)] body ((if __cogent_ffunc_purity_attr then fnSpecKind t rt else id) $ fnSpecAttr attr noFnSpec)]
genDefinition (AbsDecl attr fn Nil t rt)
  = do t'  <- genType' (unsafeCoerce t  :: SF.Type 'Zero) (argOf fn)
       rt' <- genType' (unsafeCoerce rt :: SF.Type 'Zero) (retOf fn)
       funClasses %= M.alter (insertSetMap (fn,attr)) (Function t' rt')
       return [CDecl $ CExtFnDecl rt' fn [(t',Nothing)] (fnSpecAttr attr noFnSpec)]
-- NOTE: An ad hoc treatment to concreate non-parametric type synonyms / zilinc
genDefinition (TypeDef tn ins (Just (unsafeCoerce -> ty :: SF.Type 'Zero)))
  -- NOTE: We need to make sure that ty doesn't consist of any function type with no function members / zilinc
  -- NOTE: If the RHS of this (the structural definition) is used at all, we generate the synonym / zilinc (26/08/15)
  | not (isTFun ty) = lookupTypeCId ty >>= mapM_ (const $ genRealSyn ty tn) >> return []
  where
    -- This function generates a type synonym to a datatype, not to a pointer
    genRealSyn :: SF.Type 'Zero -> TypeName -> Gen v ()
    genRealSyn ty n = typeCId ty >>= \t -> typeSynonyms %= M.insert n (CIdent t)
genDefinition _ = return []
-- genDefinition (TypeDef tn ins _) = __impossible "genDefinition"

-- ----------------------------------------------------------------------------
-- These function are not in the front-end, they directly go to target code from extra info given by earlier phase

-- XXX | cFunMacro :: (FunName, M.Map Instance Int) -> [C.Definition]
-- XXX | cFunMacro (fn, m) = concat $ flip map (M.toList m) $ \(ts, idx) ->
-- XXX |                       let stableName = fn ++ "_" ++ L.intercalate "_" (map mangleName ts)
-- XXX |                           unstableName = fn ++ "_" ++ show idx
-- XXX |                       in [ C.EscDef ("#define " ++ stableName ++ "() " ++ unstableName ++ "()") noLoc
-- XXX |                          , C.EscDef ("#define " ++ funEnum stableName ++ " " ++ funEnum unstableName) noLoc ]
-- XXX |
-- XXX | cDispatchMacro :: (SF.Type Zero, CId) -> Maybe C.Definition
-- XXX | cDispatchMacro (t@(TFun t1 t2), cname) = Just $ C.EscDef ("#define " ++ funDispatch (mangleName t) ++ " " ++ funDispatch cname) noLoc
-- XXX | cDispatchMacro _ = Nothing

-- ----------------------------------------------------------------------------
-- Table of Abstract types

printATM :: [(TypeName, S.Set [CId])] -> String
printATM = L.concat . L.map (\(tn,S.toList -> ls) -> tn ++ "\n" ++
             if ls == [[]] then "    *\n" else unlines (L.map (\l -> "    " ++ unwords l) ls))

-- ----------------------------------------------------------------------------

-- Returns a tuple (.h file, .c file, abstract types and their c names, table-c-type, state for Glue)
gen :: FilePath
    -> [Definition TypedExpr VarName]
    -> [(Type 'Zero, String)]
    -> M.Map FunName (M.Map Instance Int)
    -> String
    -> ([C.Definition], [C.Definition], [(TypeName, S.Set [CId])], [TableCTypes], GenState)
gen hfn defs ctygen insts log =
  let (tdefs, fdefs) = L.partition isTypeDef defs
      (extDecls, st, ()) = runRWS (runGen $
        concat <$> mapM genDefinition (fdefs ++ tdefs)  -- `fdefs' will collect the types that are used in the program, and `tdefs' can generate synonyms
        ) Nil (GenState { _cTypeDefs    = []
                        , _cTypeDefMap  = M.empty
                        , _typeSynonyms = M.empty
                        , _typeCorres   = DList.empty
                        , _absTypes     = M.empty
                        , _custTypeGen  = M.fromList $ P.map (second $ (,CTGI)) ctygen
                        , _funClasses   = M.empty
                        , _localOracle  = 0
                        , _globalOracle = 0
                        , _varPool      = M.empty
                        })
      (enum, st', _) = runRWS (runGen . getMon $ Mon genLetTrueEnum <> Mon genEnum) Nil st  -- `LET_TRUE', `LETBANG_TRUE' & `_tag' enums
      ((funclasses,tns), st'', _) = runRWS (runGen genFunClasses) Nil st'  -- fun_enums & dispatch functions
      (dispfs, fenums) = L.partition isFnDefn funclasses where isFnDefn (CFnDefn {}) = True; isFnDefn _ = False
      (fndefns,fndecls) = L.partition isFnDefn extDecls where isFnDefn (CFnDefn {}) = True; isFnDefn _ = False  -- there are no types
      -- (hf,ht) = L.partition isFnDecl h where isFnDecl (CDecl (CExtFnDecl {})) = True; isFnDecl _ = False
      tdefs' = reverse $ st ^. cTypeDefs
      tsyns' = M.toList $ st ^. typeSynonyms
      absts' = M.toList $ st ^. absTypes
      tycorr = reverse $ DList.toList $ st ^. typeCorres
      gn = L.map (\c -> if not (isAlphaNum c) then '_' else toUpper c) hfn ++ "__"
  in (L.map (\l -> C.EscDef ("// " ++ l) noLoc) (lines log) ++
      C.EscDef "" noLoc :
      C.EscDef ("#ifndef " ++ gn) noLoc :
      C.EscDef ("#define " ++ gn ++ "\n") noLoc :
      C.EscDef ("#include <cogent-defns.h>\n") noLoc :
      -- NOTE: These two lines are not useful because AlexH has the Python program to resolve names / zilinc
      -- concat (map cFunMacro (M.toList insts)) ++  -- macros for function names
      -- catMaybes (map cDispatchMacro stbns') ++    -- macros for dispatch functions
      map cExtDecl (
        -- Type synonyms shouldn't be referenced to by gen'ed C code;
        -- Gen'ed C only uses machine gen'ed type names and abstract type names
        enum ++ fenums ++
        concat (map (flip genTyDecl tns) tdefs') ++  -- type definitions
        fndecls ++  -- Ext function decl's (generated by CodeGen monad)
        dispfs ++
        map genTySynDecl tsyns'  -- type synonyms
        -- NOTE: Stable names are not used / zilinc
        -- XXX | map genStableName stbns'  -- stable names
        ) ++
      [C.EscDef ("#endif") noLoc],
      L.map (\l -> C.EscDef ("// " ++ l) noLoc) (lines log) ++
      C.EscDef "" noLoc :
      C.EscDef ("#include \"" ++ hfn ++ "\"\n") noLoc :
      map cExtDecl fndefns,
      absts',  -- table of abstract types
      map TableCTypes tycorr,  -- table of Cogent types |-> C types
      st''
     )


-- ****************************************************************************
-- The back-end: pretty-printers

-- C generator
--

#if MIN_VERSION_language_c_quote(0,11,2)
#else
instance IsString C.Id where
  fromString = flip C.Id noLoc
#endif

cId :: CId -> C.Id
cId v = toIdent (toCName v) noLoc

cType :: CType -> C.Type
cType ty = let (dcsp, decl) = splitCType ty in C.Type dcsp decl noLoc

cFieldGroup :: CType -> C.FieldGroup
cFieldGroup (CUnion Nothing (Just flds)) =
  C.FieldGroup (C.DeclSpec [] [] (C.Tunion Nothing (Just $ cFieldGroups $ map (second Just) flds) [] noLoc) noLoc) [] noLoc
cFieldGroup _ = __impossible "cFieldGroup"

cInitializer :: CInitializer -> C.Initializer
cInitializer (CInitE e) = [cinit| $(cExpr e) |]
cInitializer (CInitList dis) = C.CompoundInitializer (map cDesignatedInitr dis) noLoc

cFieldGroups :: [(CType, Maybe CId)] -> [C.FieldGroup]
cFieldGroups = map (\(ty, mf) -> case mf of
                      Just f  -> [csdecl| $ty:(cType ty) $id:(cId f); |]
                      Nothing -> cFieldGroup ty)

isCTypeSigned :: CType -> Bool
isCTypeSigned (CInt s _) = s
isCTypeSigned (CogentPrim _) = False
isCTypeSigned _ = True  -- FIXME

cLitConst :: CLitConst -> C.Exp
cLitConst (CNumConst n (isCTypeSigned -> False) DEC) | n < 65536 = [cexp| $uint:n |]
                                                     | n < 4294967296 = [cexp| $ulint:n |]
                                                     | otherwise = [cexp| $ullint:n |]
cLitConst (CNumConst n s DEC) | n < 65536 = [cexp| $int:n |]
                              | n < 4294967296 = [cexp| $lint:n |]
                              | otherwise = [cexp| $llint:n |]
cLitConst (CNumConst {}) = __impossible "cLitConst"  -- NOTE: currently we parse everything to its decimal form / zilinc
cLitConst (CCharConst c) = [cexp| $char:c |]
cLitConst (CStringConst s) = [cexp| $string:s |]

cDesignator :: CDesignator -> C.Designator
cDesignator (CDesignE e) = C.IndexDesignator (cExpr e) noLoc
cDesignator (CDesignFld fn) = C.MemberDesignator (cId fn) noLoc

cDesignators :: [CDesignator] -> Maybe C.Designation
cDesignators [] = Nothing
cDesignators ds = Just $ C.Designation (map cDesignator ds) noLoc

cDesignatedInitr :: ([CDesignator], CInitializer) -> (Maybe C.Designation, C.Initializer)
cDesignatedInitr = cDesignators *** cInitializer

cExpr :: CExpr -> C.Exp
cExpr (CBinOp opr e1 e2) = C.BinOp opr (cExpr e1) (cExpr e2) noLoc
cExpr (CUnOp opr e) = C.UnOp opr (cExpr e) noLoc
cExpr (CCondExpr c e1 e2) = [cexp| $(cExpr c) ? $(cExpr e1) : $(cExpr e2) |]
cExpr (CConst lit) = cLitConst lit
cExpr (CVar v _) = [cexp| $id:(cId v) |]
cExpr (CStructDot e f) = [cexp| $(cExpr e).$id:(cId f) |]
cExpr (CDeref e) = [cexp| (* $(cExpr e)) |]
cExpr (CAddrOf e) = [cexp| (& $(cExpr e)) |]
cExpr (CTypeCast ty e) = [cexp| ($ty:(cType ty)) $(cExpr e) |]
cExpr (CSizeof e) = [cexp| sizeof ($(cExpr e)) |]
cExpr (CSizeofTy ty) = [cexp| sizeof ($ty:(cType ty)) |]
cExpr (CEFnCall fn args) = [cexp| $(cExpr fn) ($args:(map cExpr args)) |]
cExpr (CCompLit ty dis) = C.CompoundLit (cType ty) (map cDesignatedInitr dis) noLoc  -- cannot add another pair of parens
cExpr (CMKBOOL e) = [cexp| $(cExpr e) != 0 |]

mkDeclSpec :: C.TypeSpec -> C.DeclSpec
mkDeclSpec tysp = C.DeclSpec [] [] tysp noLoc

cSign :: Bool -> C.Sign
cSign True  = C.Tsigned   noLoc
cSign False = C.Tunsigned noLoc

splitCType :: CType -> (C.DeclSpec, C.Decl)
splitCType (CInt signed intTy) = (,) (case intTy of
  CCharT     -> mkDeclSpec $ C.Tchar      (Just $ cSign signed) noLoc;
  CShortT    -> mkDeclSpec $ C.Tshort     (Just $ cSign signed) noLoc;
  CIntT      -> mkDeclSpec $ C.Tint       (Just $ cSign signed) noLoc;
  CLongT     -> mkDeclSpec $ C.Tlong      (Just $ cSign signed) noLoc;
  CLongLongT -> mkDeclSpec $ C.Tlong_long (Just $ cSign signed) noLoc) (C.DeclRoot noLoc)
splitCType (CogentPrim pt) = (mkDeclSpec $ C.Tnamed (C.Id (primCId pt) noLoc) [] noLoc, C.DeclRoot noLoc)
splitCType CBool = (mkDeclSpec $ C.Tnamed "Bool" [] noLoc, C.DeclRoot noLoc)
splitCType CChar = (mkDeclSpec $ C.Tchar Nothing noLoc, C.DeclRoot noLoc)
splitCType (CStruct tid) = (mkDeclSpec $ C.Tstruct (Just $ cId tid) Nothing [] noLoc, C.DeclRoot noLoc)
splitCType (CUnion {}) = __impossible "splitCType"
splitCType (CEnum tid) = (mkDeclSpec $ C.Tenum (Just $ cId tid) [] [] noLoc, C.DeclRoot noLoc)
splitCType (CPtr ty) = let (tysp, decl) = splitCType ty in (tysp, C.Ptr [] decl noLoc)
splitCType (CIdent tn) = (mkDeclSpec $ C.Tnamed (cId tn) [] noLoc, C.DeclRoot noLoc)
splitCType (CFunction t1 t2) = __fixme $ splitCType t2  -- FIXME: this type is rarely used and is never tested / zilinc
splitCType CVoid = (mkDeclSpec $ C.Tvoid noLoc, C.DeclRoot noLoc)

cFnSpecOnDeclSpec :: FnSpec -> C.DeclSpec -> C.DeclSpec
cFnSpecOnDeclSpec (FnSpec stg qual attr) (C.DeclSpec stg' qual' tysp loc) =
  C.DeclSpec (stg' ++ L.map cStorage stg) (qual' ++ L.map cTypeQual qual ++ L.concatMap cAttrs attr) tysp loc
cFnSpecOnDeclSpec _ decl = decl  -- NOTE: doesn't work for C.AntiDeclSpec / zilinc

cFnSpecOnType :: FnSpec -> C.Type -> C.Type
cFnSpecOnType fnsp (C.Type dcsp decl loc) = C.Type (cFnSpecOnDeclSpec fnsp dcsp) decl loc
cFnSpecOnType _ t = t  -- NOTE: doesn't work for C.AntiType / zilinc

cStorage :: Storage -> C.Storage
cStorage STAuto = C.Tauto noLoc
cStorage STRegister = C.Tregister noLoc
cStorage STStatic = C.Tstatic noLoc
cStorage STExtern = C.Textern Nothing noLoc  -- FIXME: can be extended to support Linkage / zilinc

cTypeQual :: TypeQual -> C.TypeQual
cTypeQual TQConst = C.Tconst noLoc
cTypeQual TQVolatile = C.Tvolatile noLoc
cTypeQual TQInline = C.Tinline noLoc
cTypeQual TQRestrict = C.Trestrict noLoc

cAttrs :: GccAttrs -> [C.TypeQual]
cAttrs (GccAttrs attrs) = L.map cAttr attrs

cAttr :: GccAttr -> C.TypeQual
cAttr (GccAttr n es) = C.TAttr (C.Attr (C.Id n noLoc) (L.map cExpr es) noLoc)

cDeclaration :: CDeclaration d -> C.InitGroup
cDeclaration (CVarDecl ty v ext (Just initr)) = [cdecl| $ty:(cType ty) $id:(cId v) = $init:(cInitializer initr); |]
cDeclaration (CVarDecl ty v ext Nothing) = [cdecl| $ty:(cType ty) $id:(cId v); |]
cDeclaration (CStructDecl tid flds) = [cdecl| struct $id:(cId tid) { $sdecls:(cFieldGroups flds) }; |]
cDeclaration (CTypeDecl ty vs) = let (dcsp, decl) = splitCType ty
                                 in C.TypedefGroup dcsp [] (map (\v -> C.Typedef (cId v) decl [] noLoc) vs) noLoc
cDeclaration (CExtFnDecl rt fn params fnsp) = [cdecl| $ty:(cFnSpecOnType fnsp $ cType rt) $id:(cId fn) ($params:(map cParam' params)); |]
cDeclaration (CEnumDecl mtid eis) =
  C.InitGroup (mkDeclSpec $ C.Tenum (fmap cId mtid) (map (\(ei, me) -> C.CEnum (cId ei) (fmap cExpr me) noLoc) eis) [] noLoc) [] [] noLoc

cParam :: (CType, CId) -> C.Param
cParam (ty, v) = [cparam| $ty:(cType ty) $id:(cId v) |]

cParam' :: (CType, Maybe CId) -> C.Param
cParam' (ty, Nothing) = [cparam| $ty:(cType ty) |]
cParam' (ty, Just v) = cParam (ty, v)

cStmt :: CStmt -> C.Stm
cStmt (CAssign el er) = [cstm| $(cExpr el) = $(cExpr er); |]
cStmt (CAssignFnCall mel er args) = case mel of Nothing -> [cstm| $(cExpr er) ($args:(map cExpr args)); |]
                                                Just el -> [cstm| $(cExpr el) = $(cExpr er) ($args:(map cExpr args)); |]
cStmt (CReturnFnCall f args) = [cstm| return $(cExpr f) ($args:(map cExpr args)); |]
cStmt (CBlock bis) = [cstm| { $items:(map cBlockItem bis) } |]
cStmt (CWhile e s) = [cstm| while ($(cExpr e)) $stm:(cStmt s) |]
cStmt (CReturn me) = case me of Nothing -> [cstm| return; |]; Just e -> [cstm| return $(cExpr e); |]
cStmt CBreak = [cstm| break; |]
cStmt CContinue = [cstm| continue; |]
cStmt (CIfStmt c th el) = [cstm| if ($(cExpr c)) $stm:(cStmt th) else $stm:(cStmt el) |]
cStmt (CSwitch e alts) = [cstm| switch ($(cExpr e)) { $items:(map cAlt alts) } |]
cStmt CEmptyStmt = [cstm| ; |]

cAlt :: (Maybe CExpr, CStmt) -> C.BlockItem
cAlt (Nothing, s) = [citem| default: $stm:(cStmt s) |]
cAlt (Just e , s) = [citem| case $(cExpr e): $stm:(cStmt s) |]

cBlockItem :: CBlockItem -> C.BlockItem
cBlockItem (CBIStmt stmt) = [citem| $stm:(cStmt stmt) |]
cBlockItem (CBIDecl decl) = [citem| $decl:(cDeclaration decl); |]

cExtDecl :: CExtDecl -> C.Definition
cExtDecl (CFnDefn (ty, fn) params bis fnsp) =
  [cedecl| $ty:(cFnSpecOnType fnsp $ cType ty) $id:(cId fn) ($params:(map cParam params)) { $items:(map cBlockItem bis) }|]
cExtDecl (CDecl decl) = [cedecl| $decl:(cDeclaration decl); |]
cExtDecl (CMacro s) = C.EscDef s noLoc
cExtDecl (CFnMacro fn as body) = C.EscDef (string1 ++ "\\\n" ++ string2) noLoc
  where macro1, macro2 :: ML.Doc
        macro1 = ML.string "#define" ML.<+> ML.string fn ML.<> ML.parens (ML.commasep $ L.map ML.string as)
        macro2 = ML.ppr [citems| $items:(L.map cBlockItem body) |]
        string1, string2 :: String
        string1 = L.filter (/= '\n') $ ML.pretty 100 macro1
        string2 = concat $ map (\c -> if c == '\n' then "\\\n" else [c]) $ ML.pretty 100 macro2

-- ----------------------------------------------------------------------------
-- Table generator

newtype TableCTypes = TableCTypes (CId, SF.Type 'Zero)

table :: TableCTypes -> PP.Doc
table (TableCTypes entry) = PP.pretty entry

printCTable :: Handle -> (PP.Doc -> PP.Doc) -> [TableCTypes] -> String -> IO ()
printCTable h m ts log = mapM_ (displayOneLine h . PP.renderPretty 0 80 . m) $
                           L.map (PP.string . ("-- " ++)) (lines log) ++ PP.line : L.map table ts

#if __GLASGOW_HASKELL__ < 709
instance PP.Pretty (CId, SF.Type 'Zero) where
#else
instance {-# OVERLAPPING #-} PP.Pretty (CId, SF.Type 'Zero) where
#endif
  pretty (n,t) = PP.pretty (deepType id (M.empty, 0) t) PP.<+> PP.string ":=:" PP.<+> PP.pretty n


-- ////////////////////////////////////////////////////////////////////////////
-- misc.

kindcheck :: Type 'Zero -> Kind
kindcheck (TVar v)         = __impossible "kindcheck"
kindcheck (TVarBang v)     = __impossible "kindcheck"
kindcheck (TUnit)          = mempty
kindcheck (TProduct t1 t2) = kindcheck t1 <> kindcheck t2
kindcheck (TSum ts)        = mconcat $ L.map (kindcheck . fst . snd) ts
kindcheck (TFun ti to)     = mempty
kindcheck (TRecord ts s)   = mappend (sigilKind s) $ mconcat $ (L.map (kindcheck . fst . snd) (filter (not . snd .snd) ts))
kindcheck (TPrim i)        = mempty
kindcheck (TString)        = mempty
kindcheck (TCon n vs s)    = sigilKind s

isTypeLinear :: Type 'Zero -> Bool
isTypeLinear = flip isTypeHasKind k1

isTypeInKinds :: Type 'Zero -> [Kind] -> Bool
isTypeInKinds t ks = kindcheck t `elem` ks

isTypeHasKind :: Type 'Zero -> Kind -> Bool
isTypeHasKind t k = isTypeInKinds t [k]

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
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{- OPTIONS_HADDOCK ignore-exports #-}  -- See: https://github.com/haskell/haddock/issues/861


-- | __NOTE:__
-- This module assumes:
--
--   1. No tag duplication in Cogent source file
--
--   2. Constants and field names share the same namespace, so no duplicates allowed
--
--   3. No reserved names (or Prelude definitions) in this module are present in source files
--
--   4. No unused constants which have types which are otherwise absent in the code

module Cogent.Haskell.Shallow (
  shallow
  -- * Contexts
, SG (..)
, ReaderGen (..)
, typeStrs, typeVars, recoverTuples, localBindings
, typarUpd, pushScope, addBindings
, WriterGen (..)
, StateGen  (..)
, freshInt, nominalTypes
  -- * Top-level definition generation
, shallowDefinitions, shallowDefinition
, shallowTypeDef
, shallowConst
  -- * Type generation
  -- $containment
, typeStr
, isRecOrVar
, typeComponents, typeStrFields
, nominalType, nominalTypeStr
, shallowTypeNominal
  -- $type_gen
, shallowType, shallowPrimType, shallowRecTupleType
, decTypeStr
  -- * Expression generation
, shallowExpr
, shallowGetter, shallowGetter'
, shallowSetter
, shallowLet
, shallowILit
, getRecordFieldName
  -- * Naming convensions
, keywords
, snm
, tagName
, recTypeName, varTypeName
, typeParam
, mkName
, mkQName
, mkDeclHead
, mkForallT
, mkTyConT
, mkVarT
, mkConT
, mkAppT
, mkTupleT
, mkListT
, mkQVarE
, mkConE
, mkLetE
, tyVars
, shallowTypesFromTable
, internalVar
) where


import Cogent.Common.Syntax as CS
import Cogent.Common.Types hiding (Boxed)
import Cogent.Compiler
import qualified Cogent.Core as CC
import Cogent.Core (TypedExpr(..))
import Cogent.Desugar as D (freshVarPrefix)
import Cogent.Isabelle.Shallow (isRecTuple)
import Cogent.Isabelle.ShallowTable (TypeStr(..), st)
import Cogent.PrettyPrint ()
import qualified Cogent.Surface as S
import Cogent.Util (Stage(..), delimiter, secondM, toHsTypeName, concatMapM, (<<+=))
import Data.Fin
import Data.Nat as Nat
import Data.Vec as Vec hiding (sym)

import Control.Arrow (second, (***))
import Control.Applicative
import Lens.Micro
import Lens.Micro.TH
import Lens.Micro.Mtl
import Control.Monad.RWS hiding (Product, Sum, mapM)
import Data.Char (isUpper)
import Data.Foldable (toList)
import Data.Function (on)
import Data.Generics.Aliases (mkQ)
import Data.Generics.Schemes (everything)
import Data.List as L
import qualified Data.Map as M
import Data.Maybe (maybe)
import Data.Set as Set (empty, fromList, insert, isSubsetOf)
-- import GHC.LanguageExtensions.Type
import Language.Haskell.Exts.Build
import Language.Haskell.Exts.Pretty
import Language.Haskell.Exts.Syntax as HS
-- import Language.Haskell.HS.LanguageExtensions
-- import Language.Haskell.HS.Syntax as TH
-- import Language.Haskell.HS.Ppr    as PP
-- import Language.Haskell.HS.PprLib as PP
import Prelude as P


import Debug.Trace (trace)
import Text.Show.Pretty (ppShow)


-- * Contexts

data ReaderGen = ReaderGen
  { _typeStrs :: [TypeStr]    -- ^ type structures, as in the Isabelle shallow embedding generator
  , _typeVars :: [TyVarName]  -- ^ type variables in scope
  , _recoverTuples :: Bool    -- ^ whether we use unboxed records for tuples
  , _localBindings :: [M.Map VarName VarName]  -- ^ a stack of (Cogent var &#x21A6; Haskell var)
  }

makeLenses ''ReaderGen

-- | update in-scope type variables
typarUpd :: [TyVarName] -> ReaderGen -> ReaderGen
typarUpd typars = set typeVars typars

pushScope :: ReaderGen -> ReaderGen
pushScope = localBindings %~ (M.empty:)

-- | add a list of @(cogent_var, haskell_var)@ to the context
addBindings :: [(VarName, VarName)] -> ReaderGen -> ReaderGen
addBindings vs = localBindings %~ (\(h:t) -> (M.fromList vs `M.union` h):t)  -- left-biased union for shadowing

data WriterGen = WriterGen
  { datatypes :: [HS.Decl ()]  -- ^ Haskell datatypes defined
  }

data StateGen = StateGen
  { _freshInt :: Int
  , _nominalTypes :: M.Map TypeStr TypeName         -- ^ how a structural type maps to a nominal type
  }

makeLenses ''StateGen

#if __GLASGOW_HASKELL__ < 803
instance Monoid WriterGen where
  mempty = WriterGen mempty
  WriterGen ds1 `mappend` WriterGen ds2 = WriterGen (ds1 `mappend` ds2)
#else
instance Semigroup WriterGen where
  WriterGen ds1 <> WriterGen ds2 = WriterGen (ds1 <> ds2)
instance Monoid WriterGen where
  mempty = WriterGen mempty
#endif

newtype SG a = SG { runSG :: RWS ReaderGen WriterGen StateGen a }
             deriving (Functor, Applicative, Monad,
                       MonadReader ReaderGen,
                       MonadWriter WriterGen,
                       MonadState  StateGen )


-- ----------------------------------------------------------------------------
-- * Haskell shallow embedding generation
--

shallow :: Bool    -- ^ Whether we recover the tuple syntax for tuple types.
                   --   If 'False', we will use unboxed records for tuples.
        -> String  -- ^ The name of the Cogent module
        -> Stage   -- ^ The 'Stage' of the compilatation
        -> [CC.Definition TypedExpr VarName b]  -- ^ A list of Cogent definitions
        -> [CC.CoreConst TypedExpr]             -- ^ A list of Cogent constants
        -> String                               -- ^ The log header to be included in the generated code
        -> String
shallow tuples name stg defs consts log =
  let (decls,w) = evalRWS (runSG $ do shallowTypesFromTable
                                      cs <- concatMapM shallowConst consts
                                      ds <- shallowDefinitions defs
                                      return $ cs ++ ds
                          )
                          (ReaderGen (st defs) [] tuples [])
                          (StateGen 0 M.empty)
      tds = datatypes w
      header = (("{-\n" ++ log ++ "\n-}\n") ++)
      moduleHead = ModuleHead () (ModuleName () name) Nothing Nothing
      exts = P.map (\s -> LanguagePragma () [Ident () s])
                   [ "DisambiguateRecordFields"
                   , "DuplicateRecordFields"
                   , "NamedFieldPuns"
                   , "NoImplicitPrelude"
                   , "PartialTypeSignatures"
                   ]
      importVar s = IVar () $ Ident  () s
      importSym s = IVar () $ Symbol () s
      importAbs s = IAbs () (NoNamespace ()) $ Ident () s
      import_bits = P.map importSym [".&.", ".|."] ++
                    P.map importVar ["complement", "xor", "shiftL", "shiftR"]
      import_word = P.map importAbs ["Word8", "Word16", "Word32", "Word64"]
      import_prelude = P.map importVar ["not", "div", "mod", "fromIntegral", "undefined"] ++
                       P.map importSym ["+", "-", "*", "&&", "||", ">", ">=", "<", "<=", "==", "/="] ++
                       P.map importAbs ["Char", "String", "Int", "Show"] ++
                       [IThingAll () $ Ident () "Bool"]
      imps = [ ImportDecl () (ModuleName () "Data.Bits") False False False Nothing Nothing (Just $ ImportSpecList () False import_bits)
             , ImportDecl () (ModuleName () "Data.Tuple.Select") True False False Nothing (Just $ ModuleName () "Tup") Nothing
             , ImportDecl () (ModuleName () "Data.Tuple.Update") True False False Nothing (Just $ ModuleName () "Tup") Nothing
             , ImportDecl () (ModuleName () "Data.Word") False False False Nothing Nothing (Just $ ImportSpecList () False import_word)
             , ImportDecl () (ModuleName () "Prelude"  ) False False False Nothing Nothing (Just $ ImportSpecList () False import_prelude)
             ]
      hsModule = Module () (Just moduleHead) exts imps $ tds ++ decls
      in (hsModule & header .
           prettyPrintStyleMode
             (style {lineLength = 220, ribbonsPerLine = 0.1})
             -- \ ^ if using https://github.com/zilinc/haskell-src-exts, no need for very long lines
             (defaultMode {caseIndent = 2}))

-- ----------------------------------------------------------------------------
-- * Top-level definition generation

-- | create a type synonym
shallowTypeDef :: TypeName -> [TyVarName] -> CC.Type t b -> SG (Decl ())
shallowTypeDef tn tvs t = do
  t' <- shallowType t
  pure $ TypeDecl () (mkDeclHead (mkName tn) (P.map (mkName . snm) tvs)) t'

shallowDefinition :: CC.Definition TypedExpr VarName b -> SG [Decl ()]
shallowDefinition (CC.FunDef _ fn ps _ ti to e) = __fixme $  -- FIXME: dlvars ignored here
  local (typarUpd typar) $ do
    ti' <- shallowType ti
    to' <- shallowType to
    e' <- local pushScope $ shallowExpr e
    ty <- shallowType $ CC.TFun ti to
    let tiname = toHsTypeName fn' ++ "_ArgT"
        toname = toHsTypeName fn' ++ "_RetT"
        tyvars = tyVars ty
        ti'' = mkAppT (TyCon () (mkQName tiname)) (map (TyVar ()) tyvars)
        to'' = mkAppT (TyCon () (mkQName toname)) (map (TyVar ()) tyvars)
        sig = TypeSig () [mkName fn'] (TyFun () ti'' to'')
        dec = FunBind () [Match () (mkName fn') [PVar () arg0] (UnGuardedRhs () e') Nothing]
        tidef = TypeDecl () (mkDeclHead (mkName tiname) tyvars) ti'
        todef = TypeDecl () (mkDeclHead (mkName toname) tyvars) to'
    pure [tidef,todef,sig,dec]
  where fn'   = snm fn
        arg0  = mkName $ snm $ D.freshVarPrefix ++ "0"
        typar = map fst $ Vec.cvtToList ps
shallowDefinition (CC.AbsDecl _ fn ps _ ti to) = __fixme $  -- FIXME: dlvars ignored here
  local (typarUpd typar) $ do
    ti' <- shallowType ti
    to' <- shallowType to
    ty <- shallowType $ CC.TFun ti to
    let tiname = toHsTypeName fn' ++ "_ArgT"
        toname = toHsTypeName fn' ++ "_RetT"
        tyvars = tyVars ty
        ti'' = mkAppT (TyCon () (mkQName tiname)) (map (TyVar ()) tyvars)
        to'' = mkAppT (TyCon () (mkQName toname)) (map (TyVar ()) tyvars)
        sig = TypeSig () [mkName fn'] (TyFun () ti'' to'')
        dec = FunBind () [Match () (mkName fn') [] (UnGuardedRhs () $ var $ mkName "undefined") Nothing]
        tidef = TypeDecl () (mkDeclHead (mkName tiname) tyvars) ti'
        todef = TypeDecl () (mkDeclHead (mkName toname) tyvars) to'
    pure [tidef,todef,sig,dec]
  where fn' = snm fn
        typar = map fst $ Vec.cvtToList ps
shallowDefinition (CC.TypeDef tn ps Nothing) =
    let dec = DataDecl () (DataType ()) Nothing (mkDeclHead (mkName tn) (P.map (mkName . snm) typar)) []
#if MIN_VERSION_haskell_src_exts(1,20,0)
                []
#else
                Nothing
#endif
     in local (typarUpd typar) $ pure [dec]
  where typar = Vec.cvtToList ps
shallowDefinition (CC.TypeDef tn ps (Just t)) = do
    local (typarUpd typar) $ (:[]) <$> shallowTypeDef tn typar t
  where typar = Vec.cvtToList ps


shallowDefinitions :: [CC.Definition TypedExpr VarName b] -> SG [Decl ()]
shallowDefinitions = (concat <$>) . mapM shallowDefinition

shallowConst :: CC.CoreConst TypedExpr -> SG [HS.Decl ()]
shallowConst (n, te@(TE t _)) = do
  e' <- shallowExpr te
  t' <- shallowType t
  let n' = mkName $ snm n
  pure $ [TypeSig () [n'] t', FunBind () [Match () n' [] (UnGuardedRhs () e') Nothing]]

-- | From the list of type structures (which is acquired from module "ShallowTable",
--   it registers all of them in the 'nomimalTypes' context.
--
--   __NOTE:__ Types in the table are not complete, some types of constants are missing.
shallowTypesFromTable :: SG ()
shallowTypesFromTable = do
  ts <- view typeStrs
  forM_ ts $ \t -> do n <- decTypeStr t
                      nominalTypes %= M.insert t n


-- ----------------------------------------------------------------------------
-- * Naming conventions
--

-- | a list of Haskell keywords
--
--   __FIXME:__ there're more / zilinc
keywords :: [String]
keywords = ["data", "type", "newtype", "if", "then", "else", "case", "of", "where"]

-- | name modifier --- map Cogent namespace to Haskell namespace
--
--   __FIXME:__ it's not very robust / zilinc
snm :: String -> String
snm s | s `elem` keywords = s ++ "_"
snm s = s

-- | Constructs a Haskell data constructor name according to the
--   type constructor name and the tag name. (See NOTE [How to deal with variant
--   types]: "Cogent.ShallowHaskell#containment")
tagName :: String -> String -> String
tagName tn tag = tn ++ '_':tag

-- | prefix for records
recTypeName = "R"
-- | prefix for variants
varTypeName = "V"
-- | prefix for type parameters
typeParam   = "t"

-- ----------------------------------------------------------------------------
-- * Type generators
--

-- $containment #containment#
-- __NOTE:__ [How to deal with variant types] / zilinc
--
-- Containment doesn\'t mean Cogent subtyping relations. Instead, they refer to a relation mainly
-- for variant types that /doesn\'t/ form a subtyping relation. For example, @\<A a | B b\>@ is
-- /contained/ in a larger type @\<A a | B b | C c\>@. We need to keep track of these relations as
-- in Haskell, data constructors can not duplicate. Two different solutions will work:
--
--   1. Generate different names for duplicate constructors;
--
--   2. When a smaller type is used, we use a larger type instead and leave some of the alternatives
--      impossible to happen.
--
-- As of now, I prefer 1 over 2, as it will not create partial functions which might complicate
-- Isabelle verification. The downside, however, is that names look ugly.


-- | generate a type structure
--
--   __ASSUME:__ @'isRecOrVar' input == 'True'@
typeStr :: CC.Type t b -> TypeStr
typeStr (CC.TRecord _ fs _) = RecordStr $ P.map fst fs
typeStr (CC.TSum alts) = VariantStr $ sort $ P.map fst alts
typeStr _ = __impossible "Precondition failed: isRecOrVar input == True"

-- | check if a type is a record or a variant
isRecOrVar :: CC.Type t b -> Bool
isRecOrVar (CC.TRecord {}) = True
isRecOrVar (CC.TSum {}) = True
isRecOrVar _ = False

-- | 'typeComponents' takes a record or variant and returns a list of its components in the right order
--
--   __ASSUME:__ @'isRecOrVar' input == 'True'@
typeComponents :: CC.Type t b -> [(String, CC.Type t b)]
typeComponents (CC.TRecord rp fs _) = P.map (second fst) fs  -- FIXME: deal with @rp@ / zilinc
typeComponents (CC.TSum alts) = P.map (second fst) $ sortBy (compare `on` fst) alts
  -- \ ^^^ NOTE: this sorting must stay in-sync with the algorithm `toTypeStr` in ShallowTable.hs / zilinc
typeComponents _ = __impossible "Precondition failed: isRecOrVar input == True"

-- | get field/tag names of a type structure
typeStrFields :: TypeStr -> [String]
typeStrFields (RecordStr fs) = fs
typeStrFields (VariantStr alts) = alts

-- | Given a Cogent type, it returns a nominal type @(type_name, [field/tag_name])@
--
--   __ASSUME:__ @'isRecOrVar' input == 'True'@
nominalType :: CC.Type t b -> SG (TypeName, [String])
nominalType = nominalTypeStr . typeStr

-- | It takes a type structure and returns a nominal type @(type_name, [field/tag_name])@
nominalTypeStr :: TypeStr -> SG (TypeName, [String])
nominalTypeStr st = do
  map <- use nominalTypes
  case M.lookup st map of
    Nothing -> __impossible "nominalTypeStr: please check all the assumptions at the top of this file are met."
    Just tn -> pure (tn, typeStrFields st)


-- $type_gen
-- For examples, if we have @type X a b = {f1:a, f2:{g1:b, g2:T}}@ defined in Cogent,
-- and we know from the env that @S t1 t2 = {f1:t1, f2:t2}@ and @P t3 t3 = {g1:t3, g2:t4}@,
-- we have:
--
--   prop> type X a b = S t1 t2
--   prop>            = S a {g1:b, g2:T}
--   prop>            = S a (P t3 t4)
--   prop>            = S a (P b T)
--
-- This is essentially what the following function (and helpers) is doing.
--

-- | convert a Cogent composite type to a Haskell datatype
--
--   __ASSUME:__ @'isRecOrVar' input == 'True'@
shallowTypeNominal :: CC.Type t b -> SG (HS.Type ())
shallowTypeNominal t = do
  (tn,fs) <- nominalType t
  nts <- forM (typeComponents t) (secondM shallowType)  -- generate a type for each component
  pure $ mkConT (mkName tn) $ P.map (\f -> maybe (TyWildCard () Nothing) id (L.lookup f nts)) fs

-- | Given a type structure, create a Hasekell type declaration and add it to the store.
--   It returns the name of the created type.
decTypeStr :: TypeStr -> SG TypeName
decTypeStr (RecordStr fs) = do
  vn <- freshInt <<+= 1
  let tn = recTypeName ++ show vn
      tvns = P.zipWith (\_ n -> mkName $ typeParam ++ show n) fs [1::Int ..]
      rfs = P.zipWith (\f n -> FieldDecl () [mkName $ "_"++(snm f)] (mkVarT n)) fs tvns
      irule = IRule () Nothing Nothing (IHCon () (UnQual () (mkName "Show")))
      dec = DataDecl () (DataType ()) Nothing (mkDeclHead (mkName tn) tvns)
              [QualConDecl () Nothing Nothing $ RecDecl () (mkName tn) rfs]
#if MIN_VERSION_haskell_src_exts(1,20,0)
              [Deriving () Nothing [irule]]
#else
              (Just (Deriving () [irule]))
#endif
  tell $ WriterGen [dec]
  return tn
decTypeStr (VariantStr tags) = do
  vn <- freshInt <<+= 1
  let tn = varTypeName ++ show vn
      tvns = P.zipWith (\_ n -> mkName $ typeParam ++ show n) tags [1::Int ..]
      cs = P.zipWith (\tag n -> QualConDecl () Nothing Nothing $ ConDecl () (mkName (tagName tn tag)) [mkVarT n]) tags tvns
      irule = IRule () Nothing Nothing (IHCon () (UnQual () (mkName "Show")))
      dec = DataDecl () (DataType ()) Nothing (mkDeclHead (mkName tn) tvns) cs
#if MIN_VERSION_haskell_src_exts(1,20,0)
              [Deriving () Nothing [irule]]
#else
              (Just (Deriving () [irule]))
#endif
  tell $ WriterGen [dec]
  return tn

-- | generate a record type as a tuple type
shallowRecTupleType :: [(FieldName, (CC.Type t b, Bool))] -> SG (HS.Type ())
shallowRecTupleType fs = mkTupleT <$> mapM shallowType (map (fst . snd) fs)

-- | generate a Haskell shallow embedding of a Cogent type
shallowType :: CC.Type t b -> SG (HS.Type ())
shallowType (CC.TVar v) = mkVarT . mkName . snm <$> ((!!) <$> view typeVars <*> pure (finInt v))
shallowType (CC.TVarBang v) = shallowType (CC.TVar v)
shallowType (CC.TCon tn ts _) = mkConT (mkName tn) <$> mapM shallowType ts
shallowType (CC.TFun t1 t2) = TyFun () <$> shallowType t1 <*> shallowType t2
shallowType (CC.TPrim pt) = pure $ shallowPrimType pt
shallowType (CC.TString) = pure . mkTyConT $ mkName "String"
shallowType (CC.TSum alts) = shallowTypeNominal (CC.TSum alts)
shallowType (CC.TProduct t1 t2) = mkTupleT <$> sequence [shallowType t1, shallowType t2]
shallowType (CC.TRecord rp fs s) = do  -- FIXME: @rp@ / zilinc
  tuples <- view recoverTuples
  if tuples && isRecTuple (map fst fs) then
    shallowRecTupleType fs
  else
    shallowTypeNominal (CC.TRecord rp fs s)
shallowType (CC.TUnit) = pure $ TyCon () $ Special () $ UnitCon ()
#ifdef BUILTIN_ARRAYS
shallowType (CC.TArray t _ _ _) = mkListT <$> shallowType t
#endif

-- | generate a Haskell shallow embedding of a primitive Cogent type
shallowPrimType :: PrimInt -> HS.Type ()
shallowPrimType U8  = mkTyConT $ mkName "Word8"
shallowPrimType U16 = mkTyConT $ mkName "Word16"
shallowPrimType U32 = mkTyConT $ mkName "Word32"
shallowPrimType U64 = mkTyConT $ mkName "Word64"
shallowPrimType Boolean = mkTyConT $ mkName "Bool"

-- ----------------------------------------------------------------------------
-- * Expression generators
--

shallowExpr :: TypedExpr t v VarName b -> SG (Exp ())
shallowExpr (TE _ (CC.Variable (_,v))) = do
  bs <- view localBindings
  let v' = case M.lookup v (M.unions bs) of  -- also heap-top-biased unions
             Nothing -> v
             Just v' -> v'
  pure . var . mkName $ snm v'

shallowExpr (TE _ (CC.Fun fn _ _ _)) = pure $ var $ mkName $ snm $  unCoreFunName fn  -- only prints the fun name

shallowExpr (TE _ (CC.Op opr es)) = shallowPrimOp <$> pure opr <*> (mapM shallowExpr es)

shallowExpr (TE _ (CC.App f arg)) = appFun <$> shallowExpr f <*> (mapM shallowExpr [arg])

shallowExpr (TE t (CC.Con cn e _))  = do
  e' <- shallowExpr e
  (tn,_) <- nominalType t
  pure $ appFun (mkConE $ mkName (tagName tn cn)) [e']

shallowExpr (TE _ (CC.Unit)) = pure $ HS.Con () $ Special () $ UnitCon ()
shallowExpr (TE _ (CC.ILit n pt)) = pure $ shallowILit n pt
shallowExpr (TE _ (CC.SLit s)) = pure $ Lit () $ String () s s

#ifdef BUILTIN_ARRAYS
shallowExpr (TE _ (CC.ALit es)) = listE <$> mapM shallowExpr es
shallowExpr (TE _ (CC.ArrayIndex arr idx)) = infixApp <$> shallowExpr arr <*> pure (op $ sym "!!") <*> shallowExpr idx
shallowExpr (TE _ (CC.Pop {})) = __todo "shallowExpr: array pop"
shallowExpr (TE _ (CC.Singleton {})) = __todo "shallowExpr: array singleton"
shallowExpr (TE _ (CC.ArrayMap2 ((v1,v2),fbody) (arr1,arr2))) = do
  fbody' <- shallowExpr fbody
  arr1'  <- shallowExpr arr1
  arr2'  <- shallowExpr arr2
  let f = lamE (map (pvar . name) [v1,v2]) fbody'
  return $ appFun (var $ name "map2") [f, tuple [arr1',arr2']]
shallowExpr (TE _ (CC.ArrayTake {})) = __todo "shallowExpr: array take"
shallowExpr (TE _ (CC.ArrayPut {})) = __todo "shallowExpr: array put"
#endif

shallowExpr (TE _ (CC.Let       nm e1 e2)) = do
  nm' <- getSafeBinder nm
  shallowLet s1 [(nm,nm')] (pvar $ mkName $ snm nm') e1 e2

shallowExpr (TE t (CC.LetBang _ nm e1 e2)) = shallowExpr (TE t $ CC.Let nm e1 e2)

shallowExpr (TE _ (CC.Tuple e1 e2)) = HS.Tuple () Boxed <$> mapM shallowExpr [e1,e2]

shallowExpr (TE t (CC.Struct fs)) = do
  (tn,_) <- nominalType t
  tuple <- view recoverTuples
  let fnms = map fst fs
  if tuple && isRecTuple fnms then
    HS.Tuple () Boxed <$> mapM shallowExpr (map snd fs)
  else
    RecConstr () (UnQual () $ mkName tn) <$>
      mapM (\(f,e) -> FieldUpdate () (UnQual () . mkName . (\x -> "_"++snm x) $ f) <$> shallowExpr e) fs

shallowExpr (TE _ (CC.If c th el)) = do
  c'  <- shallowExpr c
  th' <- local pushScope $ shallowExpr th
  el' <- local pushScope $ shallowExpr el
  pure $ HS.If () c' th' el'

shallowExpr (TE t (CC.Case e tag (_,n1,e1) (_,n2,e2))) = do
  e'  <- shallowExpr e
  n1' <- getSafeBinder n1
  n2' <- getSafeBinder n2
  e1' <- local (addBindings [(n1,n1')] . pushScope) $ shallowExpr e1
  e2' <- local (addBindings [(n2,n2')] . pushScope) $ shallowExpr e2
  (tn,_) <- nominalType (exprType e)
  let c1 = HS.Alt () (PApp () (UnQual () $ mkName (tagName tn tag)) [pvar $ mkName $ snm n1']) (UnGuardedRhs () e1') Nothing
      c2 = HS.Alt () (pvar . mkName $ snm n2') (UnGuardedRhs () e2') Nothing
  pure $ HS.Case () e' [c1,c2]

shallowExpr (TE t (CC.Esac e)) = do
  let te@(CC.TSum alts) = exprType e
      [(tag,_)] = filter (not . snd . snd) alts
  (tn,_) <- nominalType te
  vn <- freshInt <<+= 1
  let v = mkName $ internalVar ++ show vn
  appFun (Lambda () [PApp () (UnQual () . mkName $ snm (tagName tn tag)) [pvar v]] (var v)) <$>
    ((:[]) <$> shallowExpr e)

shallowExpr (TE _ (CC.Split (n1,n2) e1 e2)) = do
  n1' <- getSafeBinder n1
  n2' <- getSafeBinder n2
  let p1 = pvar . mkName $ snm n1'
      p2 = pvar . mkName $ snm n2'
  shallowLet s2 [(n1,n1'),(n2,n2')] (PTuple () Boxed [p1,p2]) e1 e2

shallowExpr (TE _ (CC.Member rec fld)) = do
  let (CC.TRecord _ fs _) = exprType rec
  shallowGetter' rec (map fst fs) fld =<< shallowExpr rec

shallowExpr (TE _ (CC.Take (n1,n2) rec fld e)) = do
  rec' <- shallowExpr rec
  n1' <- getSafeBinder n1
  n2' <- getSafeBinder n2
  let pf = pvar . mkName $ snm n1'  -- taken field
      pr = pvar . mkName $ snm n2'  -- new record
      rect@(CC.TRecord _ fs _) = exprType rec
  f' <- shallowGetter' rec (map fst fs) fld rec'
  e' <- local (addBindings [(n1,n1'),(n2,n2')]) $ shallowExpr e
  pure $ trace ("here "++ppShow f') $ mkLetE [(pr,rec'), (pf,f')] e'

shallowExpr (TE _ (CC.Put rec fld e)) = do
  rec' <- shallowExpr rec
  let rect@(CC.TRecord _ fs _) = exprType rec
  rect' <- shallowType rect
  e' <- shallowExpr e
  a <- shallowSetter rec (map fst fs) fld rec' rect' e'
  return $ trace ("here "++ppShow a) $ a

shallowExpr (TE _ (CC.Promote _ e)) = shallowExpr e
-- \ ^^^ NOTE: We guarantee that `Promote' doesn't change the underlying presentation, thus
-- we don't care what type we promote to here. / zilinc

shallowExpr (TE _ (CC.Cast    t e)) = do
  e' <- shallowExpr e
  t' <- shallowType t
  pure $ ExpTypeSig () (appFun (var $ mkName "fromIntegral") [e']) t'


-- | __NOTE:__ add parens because the precendence is different from Haskell's
shallowPrimOp :: CS.Op -> [Exp ()] -> Exp ()
shallowPrimOp CS.Plus   [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName "+"     ) e2
shallowPrimOp CS.Minus  [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName "-"     ) e2
shallowPrimOp CS.Times  [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName "*"     ) e2
shallowPrimOp CS.Divide [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName "div"   ) e2
shallowPrimOp CS.Mod    [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName "mod"   ) e2
shallowPrimOp CS.And    [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName "&&"    ) e2
shallowPrimOp CS.Or     [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName "||"    ) e2
shallowPrimOp CS.Gt     [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName ">"     ) e2
shallowPrimOp CS.Lt     [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName "<"     ) e2
shallowPrimOp CS.Le     [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName "<="    ) e2
shallowPrimOp CS.Ge     [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName ">="    ) e2
shallowPrimOp CS.Eq     [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName "=="    ) e2
shallowPrimOp CS.NEq    [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName "/="    ) e2
shallowPrimOp CS.BitAnd [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName ".&."   ) e2
shallowPrimOp CS.BitOr  [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName ".|."   ) e2
shallowPrimOp CS.BitXor [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName "xor"   ) e2
shallowPrimOp CS.LShift [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName "shiftL") (appFun (var $ mkName "fromIntegral") [e2])
shallowPrimOp CS.RShift [e1,e2] = Paren () $ InfixApp () e1 (op $ mkName "shiftR") (appFun (var $ mkName "fromIntegral") [e2])
shallowPrimOp CS.Not        [e] = HS.App () (var $ mkName "not"       ) e
shallowPrimOp CS.Complement [e] = HS.App () (var $ mkName "complement") e
shallowPrimOp _ _ = __impossible "PrimOP arity wrong"

shallowILit :: Integer -> PrimInt -> Exp ()
shallowILit n Boolean = HS.Con () . UnQual () . mkName $ if n > 0 then "True" else "False"
shallowILit n v = Paren () $ ExpTypeSig () (Lit () $ Int () n $ show n) (shallowPrimType v)

-- | makes @let p = e1 in e2@
shallowLet :: SNat n                           -- ^ a proof for @'SNat' n@
           -> [(VarName, VarName)]             -- ^ Haskell variable bindings for Cogent variables
           -> Pat ()                           -- ^ pattern @p@
           -> TypedExpr t v VarName b          -- ^ binding @e1@
           -> TypedExpr t (v :+: n) VarName b  -- ^ body @e2@
           -> SG (Exp ())
shallowLet n vs p e1 e2 = do
  __assert (toInt n == P.length vs) "n == |vs|"
  e1' <- shallowExpr e1
  e2' <- local (addBindings vs) $ shallowExpr e2
  pure $ mkLetE [(p,e1')] e2'


-- | Returns a fresh variable name; it tries to keep the original Cogent name.
getSafeBinder :: VarName -> SG VarName
getSafeBinder v = do
  bs <- view localBindings
  if v `elem` concat (P.map M.keys bs)
    then getSafeBinder =<< (((v ++) . show) <$> (freshInt <<+= 1))
    else return v

getRecordFieldName :: TypedExpr t v VarName b -> FieldIndex -> FieldName
getRecordFieldName rec idx | CC.TRecord _ fs _ <- exprType rec = P.map fst fs !! idx
getRecordFieldName _ _ = __impossible "input should be of record type"

-- | @'shallowGetter' rec idx rec\'@:
--
--   [@rec@]: the Cogent record we take from
--
--   [@idx@]: the field index
--
--   [@rec\'@]: the Haskell embedding of @rec@
--
--   For example: @rec { f = x } = ...@ becomes @f rec@
shallowGetter :: TypedExpr t v VarName b -> [FieldName] -> FieldIndex -> Exp () -> SG (Exp ())
shallowGetter rec fnms idx rec' = do
  tuples <- view recoverTuples
  return $ if | tuples, isRecTuple fnms -> appFun (mkQVarE "Tup" . mkName $ "sel" ++ show (idx+1)) [rec']
              | otherwise -> appFun (var . mkName . (\x -> "_"++ snm x) $ getRecordFieldName rec idx) [rec']

-- | Another way to extract a field from a record. E.g.:
--
-- @rec {f = x} = ...@ becomes
--
-- @
--   let R {f, g, h, ...} = rec  -- field puns are used
--    in f
-- @
shallowGetter' :: TypedExpr t v VarName b -> [FieldName] -> FieldIndex -> Exp () -> SG (Exp ())  -- use puns
shallowGetter' rec fnms idx rec' = do
  tuples <- view recoverTuples
  if | tuples, isRecTuple fnms -> shallowGetter rec fnms idx rec'
     | otherwise -> do
         let t@(CC.TRecord _ fs _) = exprType rec
         vs <- mapM (\_ -> freshInt <<+= 1) fs
         (tn,_) <- nominalType t
         let bs = P.map (\v -> mkName $ internalVar ++ show v) vs
             p' = PRec () (UnQual () $ mkName tn)
                       (P.zipWith (\(f,_) b -> PFieldPat () (UnQual () . mkName $ "_"++snm f) (pvar b)) fs bs)
         pure $ mkLetE [(p',rec')] $ var (bs !! idx)

-- | @'shallowSetter' rec idx rec\' rect\' e\'@:
--
--   [@rec@]: the Cogent record we put to
--
--   [@idx@]: the field index
--
--   [@rec\'@]: the Haskell record we put to
--
--   [@rect\'@]: the Haskell type of @rec\'@
--
--   [@e\'@]: the value we want to put in
--
--    __NOTE:__ the type signature is required due to
--   [GHC T11343](https://ghc.haskell.org/trac/ghc/ticket/11343)
shallowSetter :: TypedExpr t v VarName b -> [FieldName] -> FieldIndex -> Exp () -> HS.Type () -> Exp () -> SG (Exp ())
shallowSetter rec fnms idx rec' rect' e' = do
  tuples <- view recoverTuples
  return $ if | tuples, isRecTuple fnms -> appFun (mkQVarE "Tup" . mkName $ "upd" ++ show (idx+1)) [e', rec']
              | otherwise -> RecUpdate () (Paren () $ ExpTypeSig () rec' rect')
                                        [FieldUpdate () (UnQual () (mkName . (\x -> "_"++snm x) $ getRecordFieldName rec idx)) e']


-- | prefix for internally introduced variables
internalVar = "x__shallow_v"


-- ----------------------------------------------------------------------------
-- * Below are smart constructors for "Language.Haskell.Exts.Syntax"
--

mkName :: String -> Name ()
mkName s | P.head s `elem` ":!#$%&*+./<=>?@\\^|-~" = sym s  -- roughly
mkName s = name s

mkQName :: String -> QName ()
mkQName = UnQual () . mkName

mkDeclHead :: Name () -> [Name ()] -> DeclHead ()
mkDeclHead n [] = DHead () n
mkDeclHead n vs = foldl' (\acc v -> DHApp () acc (UnkindedVar () v)) (mkDeclHead n []) vs

mkForallT :: [Name ()] -> Type () -> Type ()
mkForallT ts t = TyForall () (Just (map (UnkindedVar ()) ts)) Nothing t

mkTyConT :: Name () -> HS.Type ()
mkTyConT = TyCon () . UnQual ()

mkVarT :: Name () -> HS.Type ()
mkVarT = TyVar ()

mkConT :: Name () -> [HS.Type ()] -> HS.Type ()
mkConT n ts = mkAppT (mkTyConT n) ts

mkAppT :: HS.Type () -> [HS.Type ()] -> HS.Type ()
mkAppT t ts = foldl' (TyApp ()) t ts

mkTupleT :: [HS.Type ()] -> HS.Type ()
mkTupleT ts = TyTuple () Boxed ts

mkListT :: HS.Type () -> HS.Type ()
mkListT t = TyList () t

mkQVarE :: String -> Name () -> Exp ()
mkQVarE mod v = Var () (Qual () (ModuleName () mod) v)

mkConE :: Name () -> Exp ()
mkConE = HS.Con () . UnQual ()

mkLetE :: [(Pat (), Exp ())] -> Exp () -> Exp ()
mkLetE bs e =
  let decls = P.map (uncurry patBind) bs
   in letE decls e


-- -----------------------------------------------------------------------------
-- misc. helpers

tyVars :: Type () -> [Name ()]
tyVars = nub . everything (++) ([] `mkQ` go)
  where
    go (TyVar () n) = [n]
    go t = []


--
-- Copyright 2017, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
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


module Cogent.ShallowHaskell where

import Cogent.Common.Syntax as CS
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Desugar as D (freshVarPrefix)
import Cogent.Shallow (isRecTuple)
import Cogent.ShallowTable (TypeStr(..), st)
import Cogent.Sugarfree as S
import Cogent.Util (Stage(..), secondM)
import Cogent.Vec as Vec

import Control.Arrow (second)
import Control.Applicative
import Control.Lens hiding (Context, (<*=))
import Control.Monad.RWS hiding (Product, Sum, mapM)
-- import Data.Char (ord, chr)
import Data.Foldable (toList)
import Data.Function (on)
import Data.List as L
import qualified Data.Map as M
import Data.Maybe (maybe)
import Data.Set as Set (empty, fromList, insert, isSubsetOf)
-- import GHC.LanguageExtensions.Type
import Language.Haskell.Exts.Pretty
import Language.Haskell.Exts.Syntax as HS
-- import Language.Haskell.HS.LanguageExtensions
-- import Language.Haskell.HS.Syntax as TH
-- import Language.Haskell.HS.Ppr    as PP
-- import Language.Haskell.HS.PprLib as PP
import Prelude as P

-- import Debug.Trace

-- NOTE:
-- This module assumes:
--   *) No tag duplication in Cogent source file
--   *) No reserved names in this module are present in source file



data ReaderGen = ReaderGen { typeStrs :: [TypeStr]
                           , typeVars :: [TyVarName]
                           , recoverTuples :: Bool
                           }

-- update in-scope type variables
typarUpd typar v = v {typeVars = typar}

data WriterGen = WriterGen { datatypes :: [HS.Decl ()]
                           }

data StateGen = StateGen { _freshInt :: Int
                         , _nominalTypes :: M.Map TypeStr TypeName
                         , _subtypes :: M.Map TypeStr (TypeStr, [String])  -- a map from subtypes to their supertypes and a list of fields that correspond to typevars.
                         }

makeLenses ''StateGen

instance Monoid WriterGen where
  mempty = WriterGen mempty
  (WriterGen ds1) `mappend` (WriterGen ds2) = WriterGen (ds1 `mappend` ds2)

newtype SG a = SG { runSG :: RWS ReaderGen WriterGen StateGen a }
             deriving (Functor, Applicative, Monad,
                       MonadReader ReaderGen,
                       MonadWriter WriterGen,
                       MonadState  StateGen )

needless = __impossible "shouldn't need this"

keywords = ["data", "type", "newtype", "if", "then", "else", "case", "of", "where"]  -- FIXME: more / zilinc

-- FIXME! / zilinc
snm :: String -> String
snm s | s `elem` keywords = s ++ "_"
snm s = s


-- ----------------------------------------------------------------------------
-- type generators
--

recTypeName = "R"
varTypeName = "V"
typeparam   = "t"

isSubtypeOfAny :: Foldable t => TypeStr -> t TypeStr -> Bool
isSubtypeOfAny t ts = or $ P.map (t `isSubtypeStr`) $ toList ts

isSubtypeStr :: TypeStr -> TypeStr -> Bool
isSubtypeStr (VariantStr alts1) (VariantStr alts2) = let s1 = Set.fromList alts1 
                                                         s2 = Set.fromList alts2
                                                      in s1 /= s2 && s1 `isSubsetOf` s2
isSubtypeStr _ _ = False

-- ASSUME: isRecOrVar input == True
typeSkel :: S.Type t -> TypeStr
typeSkel (TRecord fs _) = RecordStr $ P.map fst fs
typeSkel (TSum alts) = VariantStr $ sort $ P.map fst alts
typeSkel _ = __impossible "Precondition failed: isRecOrVar input == True"

isRecOrVar :: S.Type t -> Bool
isRecOrVar (TRecord {}) = True
isRecOrVar (TSum {}) = True
isRecOrVar _ = False

-- ASSUME: isRecOrVar input == True
compTypes :: S.Type t -> [(String, S.Type t)]
compTypes (TRecord fs _) = P.map (second fst) fs
compTypes (TSum alts) = P.map (second fst) $ sortBy (compare `on` fst) alts  -- NOTE: this sorting must stay in-sync with the algorithm `toTypeStr` in ShallowTable.hs / zilinc
compTypes _ = __impossible "Precondition failed: isRecOrVar input == True"

typeStrFields :: TypeStr -> [String]
typeStrFields (RecordStr fs) = fs
typeStrFields (VariantStr alts) = alts

-- ASSUME: isRecOrVar input == True
findShortType :: S.Type t -> SG (TypeName, [String])
findShortType = findShortTypeStr . typeSkel

findShortTypeStr :: TypeStr -> SG (TypeName, [String])
findShortTypeStr st = do
  map <- use nominalTypes
  case M.lookup st map of
    Nothing -> do subs <- use subtypes
                  case M.lookup st subs of
                    Nothing -> __impossible "should find a type"
                    Just (t',vts) -> do (t'',vts') <- findShortTypeStr t'
                                        __assert (P.length vts == P.length vts') "|vts| == |vts'|"
                                        pure $ (t'',vts)
    Just tn -> pure (tn, typeStrFields st)

-- For examples, if we have `type X a b = {f1:a, f2:{g1:b, g2:T}}` defined in Cogent,
-- and we know from the env that `S t1 t2 = {f1:t1, f2:t2}` and `P t3 t3 = {g1:t3, g2:t4}`,
-- we have:
--   > type X a b = S t1 t2
--   >            = S a {g1:b, g2:T}
--   >            = S a (P t3 t4)
--   >            = S a (P b T)
-- This is essentially what the following function (and helpers) is doing.
-- 

-- ASSUME: isRecOrVar input == True
shallowTypeWithName :: S.Type t -> SG (HS.Type ())
shallowTypeWithName t = do
  (tn,fs) <- findShortType t
  nts <- forM (compTypes t) (secondM shallowType)
  pure $ mkConT (mkName tn) $ P.map (\f -> maybe (TyWildCard () Nothing) id (L.lookup f nts)) fs

decTypeStr :: TypeStr -> SG TypeName
decTypeStr (RecordStr fs) = do
  vn <- freshInt <<+= 1
  let tn = recTypeName ++ show vn
      tvns = P.zipWith (\_ n -> mkName $ typeparam ++ show n) fs [1::Int ..]
      rfs = P.zipWith (\f n -> FieldDecl () [mkName $ snm f] (mkVarT n)) fs tvns
      dec = DataDecl () (DataType ()) Nothing (mkDeclHead (mkName tn) tvns) 
              [QualConDecl () Nothing Nothing $ RecDecl () (mkName tn) rfs] Nothing
  tell $ WriterGen [dec]
  return tn
decTypeStr (VariantStr tags) = do
  vn <- freshInt <<+= 1
  let tn = varTypeName ++ show vn
      tvns = P.zipWith (\_ n -> mkName $ typeparam ++ show n) tags [1::Int ..]
      cs = P.zipWith (\tag n -> QualConDecl () Nothing Nothing $ ConDecl () (mkName tag) [mkVarT n]) tags tvns
      dec = DataDecl () (DataType ()) Nothing (mkDeclHead (mkName tn) tvns)
              cs Nothing
  tell $ WriterGen [dec]
  return tn

shallowTypesFromTable :: SG ()
shallowTypesFromTable = do
  ts <- asks typeStrs
  -- partition (supertypes, subtypes)
  let (_,sups,subs) = 
        foldl' (\(all,sups,subs) t -> 
                  case all of
                    [] -> if not (t `isSubtypeOfAny` sups)  -- last iteration
                            then ([],t `Set.insert` sups,subs)
                            else ([],sups,t `Set.insert` subs)
                    (hd:tl) -> if not (t `isSubtypeOfAny` all) && not (t `isSubtypeOfAny` sups)
                                 then (tl,t `Set.insert` sups,subs)
                                 else (tl,sups,t `Set.insert` subs)) (ts, Set.empty, Set.empty) ts
  forM_ sups $ \t -> do  -- generate decs for all supertypes
    decTypeStr t >>= \n -> (nominalTypes %= M.insert t n)
  forM_ subs $ \t -> do  -- find supertypes
    case find (t `isSubtypeStr`) sups of
      Nothing  -> __impossible "should find a supertype"
      Just sup -> subtypes %= (M.insert t (sup, typeStrFields sup))

shallowRecTupleType :: [(FieldName, (S.Type t, Bool))] -> SG (HS.Type ())
shallowRecTupleType fs = shallowTupleType <$> mapM shallowType (map (fst . snd) fs)

shallowTupleType :: [HS.Type ()] -> HS.Type ()
shallowTupleType [] = error "Record should have at least 2 fields"
shallowTupleType ts = mkTupleT ts

shallowType :: S.Type t -> SG (HS.Type ())
shallowType (TVar v) = mkVarT . mkName . snm <$> ((!!) <$> asks typeVars <*> pure (finInt v))
shallowType (TVarBang v) = shallowType (TVar v)
shallowType (TCon tn ts _) = mkConT (mkName tn) <$> mapM shallowType ts
shallowType (TFun t1 t2) = TyFun () <$> shallowType t1 <*> shallowType t2
shallowType (TPrim pt) = pure $ shallowPrimType pt
shallowType (TString) = pure . mkTyConT $ mkName "String"
shallowType (TSum alts) = shallowTypeWithName (TSum alts)
shallowType (TProduct t1 t2) = mkTupleT <$> sequence [shallowType t1, shallowType t2]
shallowType (TRecord fs s) = do
  tuples <- asks recoverTuples
  if tuples && isRecTuple (map fst fs) then
    shallowRecTupleType fs
  else
    shallowTypeWithName (TRecord fs s)
shallowType (TUnit) = pure $ TyCon () $ Special () $ UnitCon ()

shallowPrimType :: PrimInt -> HS.Type ()
shallowPrimType U8  = mkTyConT $ mkName "Int"  -- I.TyDatatype "word" [I.AntiType "8"]
shallowPrimType U16 = mkTyConT $ mkName "Int"  -- I.TyDatatype "word" [I.AntiType "16"]
shallowPrimType U32 = mkTyConT $ mkName "Int"  -- I.TyDatatype "word" [I.AntiType "32"]
shallowPrimType U64 = mkTyConT $ mkName "Int"  -- I.TyDatatype "word" [I.AntiType "64"]
shallowPrimType Boolean = mkTyConT $ mkName "Bool"

-- ----------------------------------------------------------------------------
-- expression generators
--

internalVar = "__shallow_v"

shallowPrimOp :: CS.Op -> [Exp ()] -> Exp ()
-- add parens because the precendence is different from Haskell's
shallowPrimOp CS.Plus   [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName "+"     ) e2 
shallowPrimOp CS.Minus  [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName "-"     ) e2 
shallowPrimOp CS.Times  [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName "*"     ) e2 
shallowPrimOp CS.Divide [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName "div"   ) e2 
shallowPrimOp CS.Mod    [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName "mod"   ) e2 
shallowPrimOp CS.And    [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName "&&"    ) e2  
shallowPrimOp CS.Or     [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName "||"    ) e2  
shallowPrimOp CS.Gt     [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName ">"     ) e2 
shallowPrimOp CS.Lt     [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName "<"     ) e2 
shallowPrimOp CS.Le     [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName "<="    ) e2 
shallowPrimOp CS.Ge     [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName ">="    ) e2 
shallowPrimOp CS.Eq     [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName "=="    ) e2 
shallowPrimOp CS.NEq    [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName "/="    ) e2 
shallowPrimOp CS.BitAnd [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName ".&."   ) e2 
shallowPrimOp CS.BitOr  [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName ".|."   ) e2 
shallowPrimOp CS.BitXor [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName "xor"   ) e2 
shallowPrimOp CS.LShift [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName "shiftL") e2 
shallowPrimOp CS.RShift [e1,e2] = Paren () $ InfixApp () e1 (mkVarOp $ mkName "shiftR") e2 
shallowPrimOp CS.Not        [e] = HS.App () (mkVarE $ mkName "not"       ) e
shallowPrimOp CS.Complement [e] = HS.App () (mkVarE $ mkName "complement") e
shallowPrimOp _ _ = __impossible "PrimOP arity wrong"

shallowILit :: Integer -> PrimInt -> Exp ()
shallowILit n Boolean = HS.Con () . UnQual () . mkName $ if n > 0 then "True" else "False"
shallowILit n v = Paren () $ ExpTypeSig () (Lit () $ Int () n $ show n) (shallowPrimType v)

-- makes `let p = e1 in e2'
shallowLet :: SNat n -> Pat () -> TypedExpr t v VarName -> TypedExpr t (v :+: n) VarName -> SG (Exp ())
shallowLet _ p e1 e2 = do
  e1' <- shallowExpr e1
  e2' <- shallowExpr e2
  pure $ mkLetE [(p,e1')] e2'

getRecordFieldName :: TypedExpr t v VarName -> FieldIndex -> FieldName
getRecordFieldName rec idx | TRecord fs _ <- exprType rec = P.map fst fs !! idx
getRecordFieldName _ _ = __impossible "input should be of record type"

shallowGetter :: TypedExpr t v VarName -> FieldIndex -> Exp () -> Exp ()
shallowGetter rec idx rec' = mkAppE (mkVarE . mkName . snm $ getRecordFieldName rec idx) [rec']

shallowGetter' :: TypedExpr t v VarName -> FieldIndex -> Exp () -> SG (Exp ())  -- use puns
shallowGetter' rec idx rec' = do
  let t@(TRecord fs _) = exprType rec
  vs <- mapM (\_ -> freshInt <<+= 1) fs
  (tn,_) <- findShortType t
  let bs = P.map (\v -> mkName $ internalVar ++ show v) vs
      p' = PRec () (UnQual () $ mkName tn) (P.zipWith (\(f,_) b -> PFieldPat () (UnQual () . mkName $ snm f) (mkVarP b)) fs bs)
  pure $ mkLetE [(p',rec')] $ mkVarE (bs !! idx)

shallowSetter :: TypedExpr t v VarName -> FieldIndex -> Exp () -> Exp () -> Exp ()
shallowSetter rec idx rec' e' = RecUpdate () rec' [FieldUpdate () (UnQual () . mkName . snm $ getRecordFieldName rec idx) e']

shallowPromote :: TypedExpr t v VarName -> S.Type t -> SG (Exp ())
shallowPromote e (TSum _) = shallowExpr e
shallowPromote e t = do
  e' <- shallowExpr e
  t' <- shallowType t
  pure $ ExpTypeSig () e' t'

shallowExpr :: TypedExpr t v VarName -> SG (Exp ())
shallowExpr (TE _ (Variable (_,v))) = pure $ mkVarE $ mkName (snm v)
shallowExpr (TE _ (Fun fn ts _)) = pure $ mkVarE $ mkName (snm fn)  -- only prints the fun name
shallowExpr (TE _ (Op opr es)) = shallowPrimOp <$> pure opr <*> (mapM shallowExpr es)
shallowExpr (TE _ (S.App f arg)) = mkAppE <$> shallowExpr f <*> (mapM shallowExpr [arg])
shallowExpr (TE _ (S.Con cn e))  = do
  e' <- shallowExpr e
  pure $ mkAppE (mkConE $ mkName cn) [e']
shallowExpr (TE _ (S.Promote ty e)) = shallowPromote e ty
shallowExpr (TE t (S.Struct fs)) = do 
  (tn,_) <- findShortType t
  RecConstr () (UnQual () $ mkName tn) <$> mapM (\(f,e) -> FieldUpdate () (UnQual () . mkName $ snm f) <$> shallowExpr e) fs
shallowExpr (TE _ (S.Member rec fld)) = shallowGetter' rec fld =<< shallowExpr rec
shallowExpr (TE _ (S.Unit)) = pure $ HS.Con () $ Special () $ UnitCon ()
shallowExpr (TE _ (S.ILit n pt)) = pure $ shallowILit n pt
shallowExpr (TE _ (S.SLit s)) = pure $ Lit () $ String () s s
shallowExpr (TE _ (S.Tuple e1 e2)) = HS.Tuple () Boxed <$> mapM shallowExpr [e1,e2]
shallowExpr (TE _ (S.Put rec fld e)) = shallowSetter rec fld <$> shallowExpr rec <*> shallowExpr e
shallowExpr (TE _ (S.Let nm e1 e2)) = shallowLet s1 (mkVarP $ mkName $ snm nm) e1 e2
shallowExpr (TE _ (S.LetBang vs nm e1 e2)) = shallowLet s1 (mkVarP $ mkName $ snm nm) e1 e2
shallowExpr (TE t (S.Case e tag (_,n1,e1) (_,n2,e2))) = do
  e'  <- shallowExpr e
  e1' <- shallowExpr e1
  e2' <- shallowExpr e2
  let c1 = HS.Alt () (PApp () (UnQual () $ mkName tag) [mkVarP $ mkName $ snm n1]) (UnGuardedRhs () e1') Nothing
      c2 = HS.Alt () (mkVarP . mkName $ snm n2) (UnGuardedRhs () e2') Nothing
  pure $ HS.Case () e' [c1,c2]
shallowExpr (TE t (Esac e)) = do
  let (TSum [(f,_)]) = exprType e
  vn <- freshInt <<+= 1
  let v = mkName $ internalVar ++ show vn
  mkAppE (Lambda () [PApp () (UnQual () . mkName $ snm f) [mkVarP v]] (mkVarE v)) <$> ((:[]) <$> shallowExpr e)
shallowExpr (TE _ (S.If c th el)) = do
  [c',th',el'] <- mapM shallowExpr [c, th, el]
  pure $ HS.If () c' th' el'
shallowExpr (TE _ (S.Take (n1,n2) rec fld e)) = do
  rec' <- shallowExpr rec
  e' <- shallowExpr e
  let pf = mkVarP . mkName $ snm n1  -- taken field
      pr = mkVarP . mkName $ snm n2  -- new record
  f' <- shallowGetter' rec fld rec'
  pure $ mkLetE [(pr,rec'), (pf,f')] e'
shallowExpr (TE _ (S.Split (n1,n2) e1 e2)) = 
  let p1 = mkVarP . mkName $ snm n1
      p2 = mkVarP . mkName $ snm n2
   in shallowLet s2 (PTuple () Boxed [p1,p2]) e1 e2

-- ----------------------------------------------------------------------------
-- top-level generators
--


shallowTypeDef :: TypeName -> [TyVarName] -> S.Type t -> SG (Decl ())
shallowTypeDef tn tvs t = do
  t' <- shallowType t
  pure $ TypeDecl () (mkDeclHead (mkName tn) (P.map (mkName . snm) tvs)) t'

shallowDefinition :: Definition TypedExpr VarName -> SG [Decl ()]
shallowDefinition (FunDef _ fn ps ti to e) =
    local (typarUpd typar) $ do
    e' <- shallowExpr e
    ty <- shallowType $ TFun ti to
    let sig = TypeSig () [fn'] ty
        dec = FunBind () [Match () fn' [PVar () arg0] (UnGuardedRhs () e') Nothing]
    pure [sig,dec]
  where fn'   = mkName $ snm fn
        arg0  = mkName $ snm $ D.freshVarPrefix ++ "0"
        typar = map fst $ Vec.cvtToList ps
shallowDefinition (AbsDecl _ fn ps ti to) =
    local (typarUpd typar) $ do
      ty <- shallowType $ TFun ti to
      let sig = TypeSig () [fn'] ty
          dec = FunBind () [Match () fn' [] (UnGuardedRhs () $ mkVarE $ mkName "undefined") Nothing]
      pure [sig,dec]
  where fn' = mkName $ snm fn
        typar = map fst $ Vec.cvtToList ps
shallowDefinition (TypeDef tn ps Nothing) =
    let dec = DataDecl () (DataType ()) Nothing (mkDeclHead (mkName tn) (P.map (mkName . snm) typar)) [] Nothing
     in local (typarUpd typar) $ pure [dec]
  where typar = Vec.cvtToList ps
shallowDefinition (TypeDef tn ps (Just t)) = do
    local (typarUpd typar) $ ((:[]) <$> shallowTypeDef tn typar t)
  where typar = Vec.cvtToList ps

shallowDefinitions :: [Definition TypedExpr VarName] -> SG [Decl ()]
shallowDefinitions = (concat <$>) . mapM shallowDefinition

shallow :: Bool -> String -> Stage -> [Definition TypedExpr VarName] -> String -> String
shallow tuples name stg defs log =
  let (decs,w) = evalRWS (runSG (shallowTypesFromTable >> shallowDefinitions defs))
                                (ReaderGen (st defs) [] tuples)
                                (StateGen 0 M.empty M.empty)
      tds = datatypes w
      header = (("{-\n" ++ log ++ "\n-}\n") ++)
      shhs = name ++ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage stg ++ (if tuples then __cogent_suffix_of_recover_tuples else [])
      mh = ModuleHead () (ModuleName () shhs) Nothing Nothing
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
      import_prelude = P.map importVar ["not", "div", "mod", "undefined"] ++
                       P.map importSym ["+", "-", "*", "&&", "||", ">", ">=", "<", "<=", "==", "/="] ++
                       P.map importAbs ["Char", "String", "Int"] ++
                       [IThingAll () $ Ident () "Bool"]
      imps = [ ImportDecl () (ModuleName () "Data.Bits") False False False Nothing Nothing (Just $ ImportSpecList () False import_bits)
             , ImportDecl () (ModuleName () "Prelude"  ) False False False Nothing Nothing (Just $ ImportSpecList () False import_prelude)
             ]
      in header $ prettyPrintStyleMode
                    (style {lineLength = 1000000, ribbonsPerLine = 0.1})  -- nearly infinitely long lines
                    (defaultMode {caseIndent = 2})
                    (Module () (Just mh) exts imps $ decs ++ tds)

-- ----------------------------------------------------------------------------
-- Below are smart constructors for Language.Haskell.Exts.Syntax
--

mkName :: String -> Name ()
mkName s | P.head s `elem` ":!#$%&*+./<=>?@\\^|-~" = Symbol () s  -- roughly
mkName s = Ident () s

mkDeclHead :: Name () -> [Name ()] -> DeclHead ()
mkDeclHead n [] = DHead () n
mkDeclHead n vs = foldl' (\acc v -> DHApp () acc (UnkindedVar () v)) (mkDeclHead n []) vs

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

mkVarE :: Name () -> Exp ()
mkVarE n = Var () (UnQual () n)

mkConE :: Name () -> Exp ()
mkConE = HS.Con () . UnQual ()

mkVarP :: Name () -> Pat ()
mkVarP = PVar ()

mkVarOp :: Name () -> QOp ()
mkVarOp = QVarOp () . UnQual ()

mkAppE :: Exp () -> [Exp ()] -> Exp ()
mkAppE e es = foldl' (HS.App ()) e es

mkLetE :: [(Pat (), Exp ())] -> Exp () -> Exp ()
mkLetE bs e = 
  let decls = P.map (\(p,r) -> PatBind () p (UnGuardedRhs () r) Nothing) bs
   in HS.Let () (BDecls () decls) e



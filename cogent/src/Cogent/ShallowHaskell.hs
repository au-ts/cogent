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
import Cogent.Util (Stage(..), (***^^), secondM)
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
import Data.Set as Set (empty, fromList, insert, isSubsetOf)
-- import GHC.LanguageExtensions.Type
-- import Language.Haskell.TH.LanguageExtensions
import Language.Haskell.TH.Syntax as TH
import Language.Haskell.TH.Ppr    as PP
import Language.Haskell.TH.PprLib as PP
import Prelude as P

import Debug.Trace

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

data WriterGen = WriterGen { datatypes :: [TH.Dec]
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

mkConT :: Name -> [TH.Type] -> TH.Type
mkConT n ts = foldl' AppT (ConT n) ts

mkTupleT :: [TH.Type] -> TH.Type
mkTupleT ts = foldl' AppT (TupleT $ P.length ts) ts

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


defaultBang = TH.Bang NoSourceUnpackedness NoSourceStrictness  -- NOTE: this requires template-haskell >= 2.11 / zilinc


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
shallowTypeWithName :: S.Type t -> SG TH.Type
shallowTypeWithName t = do
  (tn,fs) <- findShortType t
  nts <- forM (compTypes t) (secondM shallowType)
  pure $ mkConT (mkName tn) $ P.map (\f -> case L.lookup f nts of Nothing -> WildCardT; Just t -> t) fs

decTypeStr :: TypeStr -> SG TypeName
decTypeStr (RecordStr fs) = do
  vn <- freshInt <<+= 1
  let tn = recTypeName ++ show vn
      tvns = P.zipWith (\_ n -> mkName $ typeparam ++ show n) fs [1::Int ..]
      tvs = P.map PlainTV tvns
      rfs = P.zipWith (\f n -> (mkName $ snm f, defaultBang, VarT n)) fs tvns
      dec = DataD [] (mkName tn) tvs Nothing [RecC (mkName tn) rfs] []
  tell $ WriterGen [dec]
  return tn
decTypeStr (VariantStr tags) = do
  vn <- freshInt <<+= 1
  let tn = varTypeName ++ show vn
      tvns = P.zipWith (\_ n -> mkName $ typeparam ++ show n) tags [1::Int ..]
      tvs = P.map PlainTV tvns
      cs = P.zipWith (\tag n -> NormalC (mkName tag) [(defaultBang, VarT n)]) tags tvns
      dec = DataD [] (mkName tn) tvs Nothing cs []
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
      Just sup -> subtypes %= (M.insert t (sup, compareTypeStrFields t sup))

compareTypeStrFields :: TypeStr -> TypeStr -> [String]
compareTypeStrFields (VariantStr subs) (VariantStr sups) = sups
compareTypeStrFields _ _ = __impossible "it is not a subtype of anything"

shallowRecTupleType :: [(FieldName, (S.Type t, Bool))] -> SG TH.Type
shallowRecTupleType fs = shallowTupleType <$> mapM shallowType (map (fst . snd) fs)

shallowTupleType :: [TH.Type] -> TH.Type
shallowTupleType [] = error "Record should have at least 2 fields"
shallowTupleType ts = mkTupleT ts

shallowType :: S.Type t -> SG TH.Type
shallowType (TVar v) = VarT . mkName . snm <$> ((!!) <$> asks typeVars <*> pure (finInt v))
shallowType (TVarBang v) = shallowType (TVar v)
shallowType (TCon tn ts _) = mkConT (mkName tn) <$> mapM shallowType ts
shallowType (TFun t1 t2) = AppT <$> (AppT ArrowT <$> shallowType t1) <*> shallowType t2
shallowType (TPrim pt) = pure $ shallowPrimType pt
shallowType (TString) = pure $ ConT $ mkName "String"
shallowType (TSum alts) = shallowTypeWithName (TSum alts)
shallowType (TProduct t1 t2) = mkTupleT <$> sequence [shallowType t1, shallowType t2]
shallowType (TRecord fs s) = do
  tuples <- asks recoverTuples
  if tuples && isRecTuple (map fst fs) then
    shallowRecTupleType fs
  else
    shallowTypeWithName (TRecord fs s)
shallowType (TUnit) = pure $ TupleT 0

shallowPrimType :: PrimInt -> TH.Type
shallowPrimType U8  = ConT $ mkName "Int"  -- I.TyDatatype "word" [I.AntiType "8"]
shallowPrimType U16 = ConT $ mkName "Int"  -- I.TyDatatype "word" [I.AntiType "16"]
shallowPrimType U32 = ConT $ mkName "Int"  -- I.TyDatatype "word" [I.AntiType "32"]
shallowPrimType U64 = ConT $ mkName "Int"  -- I.TyDatatype "word" [I.AntiType "64"]
shallowPrimType Boolean = ConT $ mkName "Bool"

-- ----------------------------------------------------------------------------
-- expression generators
--

internalVar = "__shallow_v"

mkApp :: Exp -> [Exp] -> Exp
mkApp e es = foldl' AppE e es

mkLet :: [(Pat, Exp)] -> Exp -> Exp
mkLet bs e = 
  let bs' = P.map (\(p,b) -> ValD p (NormalB b) []) bs
   in LetE bs' e

shallowPrimOp :: Op -> [Exp] -> Exp
shallowPrimOp CS.Plus   [e1,e2] = InfixE (Just e1) (VarE $ mkName "+"     ) (Just e2) 
shallowPrimOp CS.Minus  [e1,e2] = InfixE (Just e1) (VarE $ mkName "-"     ) (Just e2) 
shallowPrimOp CS.Times  [e1,e2] = InfixE (Just e1) (VarE $ mkName "*"     ) (Just e2) 
shallowPrimOp CS.Divide [e1,e2] = InfixE (Just e1) (VarE $ mkName "div"   ) (Just e2) 
shallowPrimOp CS.Mod    [e1,e2] = InfixE (Just e1) (VarE $ mkName "mod"   ) (Just e2) 
shallowPrimOp CS.And    [e1,e2] = InfixE (Just e1) (VarE $ mkName "&&"    ) (Just e2)  
shallowPrimOp CS.Or     [e1,e2] = InfixE (Just e1) (VarE $ mkName "||"    ) (Just e2)  
shallowPrimOp CS.Gt     [e1,e2] = InfixE (Just e1) (VarE $ mkName ">"     ) (Just e2) 
shallowPrimOp CS.Lt     [e1,e2] = InfixE (Just e1) (VarE $ mkName "<"     ) (Just e2) 
shallowPrimOp CS.Le     [e1,e2] = InfixE (Just e1) (VarE $ mkName "<="    ) (Just e2) 
shallowPrimOp CS.Ge     [e1,e2] = InfixE (Just e1) (VarE $ mkName ">="    ) (Just e2) 
shallowPrimOp CS.Eq     [e1,e2] = InfixE (Just e1) (VarE $ mkName "=="    ) (Just e2) 
shallowPrimOp CS.NEq    [e1,e2] = InfixE (Just e1) (VarE $ mkName "/="    ) (Just e2) 
shallowPrimOp CS.BitAnd [e1,e2] = InfixE (Just e1) (VarE $ mkName ".&."   ) (Just e2) 
shallowPrimOp CS.BitOr  [e1,e2] = InfixE (Just e1) (VarE $ mkName ".|."   ) (Just e2) 
shallowPrimOp CS.BitXor [e1,e2] = InfixE (Just e1) (VarE $ mkName "xor"   ) (Just e2) 
shallowPrimOp CS.LShift [e1,e2] = InfixE (Just e1) (VarE $ mkName "shiftL") (Just e2) 
shallowPrimOp CS.RShift [e1,e2] = InfixE (Just e1) (VarE $ mkName "shiftR") (Just e2) 
shallowPrimOp CS.Not        [e] = mkApp (VarE $ mkName "not"       ) [e]
shallowPrimOp CS.Complement [e] = mkApp (VarE $ mkName "complement") [e]
shallowPrimOp _ _ = __impossible "PrimOP arity wrong"

shallowILit :: Integer -> PrimInt -> Exp
shallowILit n Boolean = ConE . mkName $ if n > 0 then "True" else "False"
shallowILit n v = ParensE $ SigE (LitE $ IntegerL n) (shallowPrimType v)

-- makes `let p = e1 in e2'
shallowLet :: SNat n -> Pat -> TypedExpr t v VarName -> TypedExpr t (v :+: n) VarName -> SG Exp
shallowLet _ p e1 e2 = do
  e1' <- shallowExpr e1
  e2' <- shallowExpr e2
  pure $ mkLet [(p,e1')] e2'

getRecordFieldName :: TypedExpr t v VarName -> FieldIndex -> FieldName
getRecordFieldName rec idx | TRecord fs _ <- exprType rec = P.map fst fs !! idx
getRecordFieldName _ _ = __impossible "input should be of record type"

shallowGetter :: TypedExpr t v VarName -> FieldIndex -> Exp -> Exp
shallowGetter rec idx rec' = mkApp (VarE . mkName . snm $ getRecordFieldName rec idx) [rec']

shallowGetter' :: TypedExpr t v VarName -> FieldIndex -> Exp -> SG Exp  -- use puns
shallowGetter' rec idx rec' = do
  let t@(TRecord fs _) = exprType rec
  vs <- mapM (\_ -> freshInt <<+= 1) fs
  (tn,_) <- findShortType t
  let bs = P.map (\v -> mkName $ internalVar ++ show v) vs
      p' = RecP (mkName tn) (P.zipWith (\(f,_) b -> (mkName $ snm f, VarP b)) fs bs)
  pure $ mkLet [(p',rec')] $ VarE (bs !! idx)
shallowSetter :: TypedExpr t v VarName -> FieldIndex -> Exp -> Exp -> Exp
shallowSetter rec idx rec' e' = RecUpdE rec' [(mkName . snm $ getRecordFieldName rec idx, e')]

shallowPromote :: TypedExpr t v VarName -> S.Type t -> SG Exp
shallowPromote e (TSum _) = shallowExpr e
shallowPromote e t = do
  e' <- shallowExpr e
  t' <- shallowType t
  pure $ SigE e' t'

shallowExpr :: TypedExpr t v VarName -> SG Exp
shallowExpr (TE _ (Variable (_,v))) = pure $ VarE $ mkName (snm v)
shallowExpr (TE _ (Fun fn ts _)) = pure $ VarE $ mkName (snm fn)  -- only prints the fun name
shallowExpr (TE _ (Op opr es)) = shallowPrimOp <$> pure opr <*> (mapM shallowExpr es)
shallowExpr (TE _ (App f arg)) = mkApp <$> shallowExpr f <*> (mapM shallowExpr [arg])
shallowExpr (TE _ (Con cn e))  = do
  e' <- shallowExpr e
  pure $ AppE (ConE $ mkName cn) e'
shallowExpr (TE _ (Promote ty e)) = shallowPromote e ty
shallowExpr (TE t (Struct fs)) = do 
  (tn,_) <- findShortType t
  RecConE (mkName tn) <$> mapM (pure . mkName . snm ***^^ shallowExpr) fs
shallowExpr (TE _ (Member rec fld)) = shallowGetter' rec fld =<< shallowExpr rec
shallowExpr (TE _ (Unit)) = pure $ ConE $ mkName "()"
shallowExpr (TE _ (ILit n pt)) = pure $ shallowILit n pt
shallowExpr (TE _ (SLit s)) = pure $ LitE $ StringL s
shallowExpr (TE _ (Tuple e1 e2)) = TupE <$> mapM shallowExpr [e1,e2]
shallowExpr (TE _ (Put rec fld e)) = shallowSetter rec fld <$> shallowExpr rec <*> shallowExpr e
shallowExpr (TE _ (Let nm e1 e2)) = shallowLet s1 (VarP $ mkName $ snm nm) e1 e2
shallowExpr (TE _ (LetBang vs nm e1 e2)) = shallowLet s1 (VarP $ mkName $ snm nm) e1 e2
shallowExpr (TE t (Case e tag (_,n1,e1) (_,n2,e2))) = do
  e'  <- shallowExpr e
  e1' <- shallowExpr e1
  e2' <- shallowExpr e2
  let c1 = Match (ConP (mkName tag) [VarP $ mkName $ snm n1]) (NormalB e1') []
      c2 = Match (VarP $ mkName $ snm n2) (NormalB e2') []
  pure $ CaseE e' [c1,c2]
shallowExpr (TE t (Esac e)) = do
  let (TSum [(f,_)]) = exprType e
  vn <- freshInt <<+= 1
  let v = mkName $ internalVar ++ show vn
  mkApp (LamE [ConP (mkName $ snm f) [VarP v]] (VarE v)) <$> ((:[]) <$> shallowExpr e)
shallowExpr (TE _ (If c th el)) = do
  [c',th',el'] <- mapM shallowExpr [c, th, el]
  pure $ CondE c' th' el'
shallowExpr (TE _ (Take (n1,n2) rec fld e)) = do
  rec' <- shallowExpr rec
  e' <- shallowExpr e
  let pf = VarP $ mkName $ snm n1  -- taken field
      pr = VarP $ mkName $ snm n2  -- new record
  f' <- shallowGetter' rec fld rec'
  pure $ mkLet [(pr,rec'), (pf,f')] e'
shallowExpr (TE _ (Split (n1,n2) e1 e2)) = 
  let p1 = VarP $ mkName $ snm n1
      p2 = VarP $ mkName $ snm n2
   in shallowLet s2 (TupP [p1,p2]) e1 e2

-- ----------------------------------------------------------------------------
-- top-level generators
--


shallowTypeDef :: TypeName -> [TyVarName] -> S.Type t -> SG [Dec]
shallowTypeDef tn tvs t = do
  t' <- shallowType t
  pure $ [TySynD (mkName tn) (P.map (PlainTV . mkName . snm) tvs) t']

shallowDefinition :: Definition TypedExpr VarName -> SG [[Dec]]
shallowDefinition (FunDef _ fn ps ti to e) =
    local (typarUpd typar) $ do
    e' <- shallowExpr e
    ty <- shallowType $ TFun ti to
    let sig = SigD fn' ty
        dec = FunD fn' [Clause [VarP arg0] (NormalB e') []]
    pure [[sig,dec]]
  where fn'   = mkName $ snm fn
        arg0  = mkName $ snm $ D.freshVarPrefix ++ "0"
        typar = map fst $ Vec.cvtToList ps
shallowDefinition (AbsDecl _ fn ps ti to) =
    local (typarUpd typar) $ do
      ty <- shallowType $ TFun ti to
      let sig = SigD fn' ty
          dec = FunD fn' [Clause [] (NormalB $ VarE $ mkName "undefined") []]
      pure [[sig,dec]]
  where fn' = mkName $ snm fn
        typar = map fst $ Vec.cvtToList ps
shallowDefinition (TypeDef tn ps Nothing) =
    let dec = DataD [] (mkName tn) (P.map (PlainTV . mkName . snm) typar) Nothing [] []
     in local (typarUpd typar) $ pure [[dec]]
  where typar = Vec.cvtToList ps
shallowDefinition (TypeDef tn ps (Just t)) = do
    local (typarUpd typar) $ ((:[]) <$> shallowTypeDef tn typar t)
  where typar = Vec.cvtToList ps

shallowDefinitions :: [Definition TypedExpr VarName] -> SG [[Dec]]
shallowDefinitions = (concat <$>) . mapM shallowDefinition


data HaskellModule = HM LanguageExtensions ModName [ImportedModule] [[Dec]]

pprModule :: ModName -> Doc
pprModule (ModName s) = text "module" <+> text s <+> text "where\n"

-- module-name, qualified name, imported ids
data ImportedModule = ImportedModule String (Maybe (Bool, String)) (Maybe [String])  -- a bit hacky but works

pprImports :: [ImportedModule] -> Doc
pprImports [] = PP.empty
pprImports ms = PP.vcat (P.map pprImport ms) PP.<> text "\n"

pprImport :: ImportedModule -> Doc
pprImport (ImportedModule n qn fs) = 
  let (qualified, alias) = case qn of
        Nothing -> ((PP.empty PP.<>), (PP.empty PP.<>)) 
        Just (q,s) -> (if q then (text "qualified" <+>) else (PP.empty PP.<>), (text "as" <+> text s <+>))
      fs' = case fs of
              Nothing -> PP.empty
              Just fs -> parens (sepBy comma $ P.map text fs)
   in text "import" <+> qualified (text n) <+> alias fs'
  where sepBy d [] = PP.empty
        sepBy d [f] = f
        sepBy d (f:fs) = f PP.<> hcat (P.map (d <+>) fs)

instance Ppr HaskellModule where
  ppr (HM exts mn info decs) = ppr exts
                           $+$ pprModule mn
                           $+$ pprImports info
                           $+$ vcat (P.map ((PP.<> text "\n") . ppr) decs)

data LanguageExtensions = LanguageExtensions [String]  -- NOTE: not using `LanguageExtension's from template-haskell
                                                       -- because they're not consistent with GHC / zilinc

instance Ppr LanguageExtensions where
  ppr (LanguageExtensions []) = PP.empty
  ppr (LanguageExtensions es) = PP.vcat (P.map (\e -> text $ "{-# LANGUAGE " ++ e ++ " #-}") es) PP.<> text "\n"

-- removeSubtypes :: [TypeStr] -> [TypeStr]
-- removeSubtypes ts = filter (\t -> not $ or $ P.map (t `isSubtypeStr`) ts) ts

isSubtypeOfAny :: Foldable t => TypeStr -> t TypeStr -> Bool
isSubtypeOfAny t ts = or $ P.map (t `isSubtypeStr`) $ toList ts

isSubtypeStr :: TypeStr -> TypeStr -> Bool
isSubtypeStr (VariantStr alts1) (VariantStr alts2) = let s1 = Set.fromList alts1 
                                                         s2 = Set.fromList alts2
                                                      in s1 /= s2 && s1 `isSubsetOf` s2
isSubtypeStr _ _ = False

shallow :: Bool -> String -> Stage -> [Definition TypedExpr VarName] -> String -> Doc
shallow tuples name stg defs log =
  let (decs,w) = evalRWS (runSG (shallowTypesFromTable >> shallowDefinitions defs))
                                (ReaderGen (st defs) [] tuples)
                                (StateGen 0 M.empty M.empty)
      tds = P.map (:[]) (datatypes w)
      header = (PP.text ("{-\n" ++ log ++ "\n-}\n") PP.$+$)
      shhs = name ++ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage stg ++ (if tuples then __cogent_suffix_of_recover_tuples else [])
      imps = [ ImportedModule "Data.Bits" Nothing Nothing
             , ImportedModule "Prelude"   Nothing (Just ["(+)", "(-)", "(*)", "div", "(&&)", "(||)", "not", "(>)", "(>=)", "(<)", "(<=)", "(==)", "(/=)", "Bool(..)", "Char", "String", "Int", "undefined"])
             ]
      exts = ["DisambiguateRecordFields", "DuplicateRecordFields", "NamedFieldPuns", "NoImplicitPrelude", "PartialTypeSignatures"]
   in header . ppr $ HM (LanguageExtensions exts) (ModName shhs) imps $ decs ++ tds


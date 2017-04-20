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


module Cogent.ShallowHaskell where

import Cogent.Common.Syntax as CS
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Desugar as D (freshVarPrefix)
import Cogent.Shallow 
  (SG(..), SGTables(..), StateGen(..), 
   typarUpd, varNameGen, isRecTuple, findShortType)
import Cogent.Sugarfree as S
import Cogent.Util (Stage(..), Warning)
import Cogent.Vec as Vec

import Control.Applicative
import Control.Arrow ((***))
import Control.Lens hiding (Context)
import Control.Monad.RWS hiding (Product, Sum, mapM)
import Data.Char (ord, chr, intToDigit, isDigit)
import Data.Either (lefts, rights)
import Data.Foldable (foldr')
import Data.List as L
import Data.Maybe (catMaybes)
-- import Language.Haskell.TH.Quote  as TH
import Language.Haskell.TH.Syntax as TH
import Prelude as P

data HaskellModule = HM Module ModuleInfo [Dec]
                   deriving (Show)

-- package name, module names
pkg  = mkPkgName "TODO"
shmn = mkModName "TODO"
ssmn = mkModName "TODO"

shhm :: Module
shhm = Module pkg shmn

sshm :: Module
sshm = Module pkg ssmn

snm :: String -> String
snm = id


-- ----------------------------------------------------------------------------
-- type generator
--

mkTCon :: Name -> [TH.Type] -> TH.Type
mkTCon n ts = foldr' (flip AppT) (ConT n) ts

mkTuple :: [TH.Type] -> TH.Type
mkTuple ts = foldl' AppT (TupleT $ P.length ts) ts

shallowTVar :: Int -> String
shallowTVar v = [chr $ ord 'a' + fromIntegral v]

shallowTypeWithName :: S.Type t -> SG TH.Type
shallowTypeWithName t = shallowType =<< findShortType t

shallowRecTupleType :: [(FieldName, (S.Type t, Bool))] -> SG TH.Type
shallowRecTupleType fs = shallowTupleType <$> mapM shallowType (map (fst . snd) fs)

shallowTupleType :: [TH.Type] -> TH.Type
shallowTupleType [] = error "Record should have at least 2 fields"
shallowTupleType ts = mkTuple ts

shallowType :: S.Type t -> SG TH.Type
shallowType (TVar v) = VarT . mkName <$> ((!!) <$> asks typeVars <*> pure (finInt v))
shallowType (TVarBang v) = shallowType (TVar v)
shallowType (TCon tn ts _) = mkTCon (mkName tn) <$> mapM shallowType ts
shallowType (TFun t1 t2) = AppT <$> (AppT ArrowT <$> shallowType t1) <*> shallowType t2
shallowType (TPrim pt) = pure $ shallowPrimType pt
shallowType (TString) = pure $ ConT $ mkName "String"
shallowType (TSum alts) = shallowTypeWithName (TSum alts)
shallowType (TProduct t1 t2) = mkTuple <$> sequence [shallowType t1, shallowType t2]
shallowType (TRecord fs s) = do
  tuples <- asks recoverTuples
  if tuples && isRecTuple (map fst fs)then
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
-- expression generator
--

mkApp :: Exp -> [Exp] -> Exp
mkApp e es = foldl' AppE e es


mkShallowOpApp :: Exp -> [Exp] -> Exp
mkShallowOpApp o es = mkApp o es

shallowPrimOp :: Op -> [Exp] -> Exp
shallowPrimOp CS.Plus   es = mkShallowOpApp (VarE $ mkName "GHC.Num.+") es
shallowPrimOp CS.Minus  es = mkShallowOpApp (VarE $ mkName "GHC.Num.-") es
shallowPrimOp CS.Times  es = mkShallowOpApp (VarE $ mkName "GHC.Num.*") es
shallowPrimOp CS.Divide es = mkApp (VarE $ mkName "GHC.Real.div") es
shallowPrimOp CS.Mod    es = mkApp (VarE $ mkName "GHC.Real.mod") es
shallowPrimOp CS.Not    es = mkApp (VarE $ mkName "GHC.Classes.not") es
shallowPrimOp CS.And    es = mkApp (VarE $ mkName "GHC.Classes.&&") es 
shallowPrimOp CS.Or     es = mkApp (VarE $ mkName "GHC.Classes.||") es 
shallowPrimOp CS.Gt     es = mkShallowOpApp (VarE $ mkName "GHC.Classes.>" ) es
shallowPrimOp CS.Lt     es = mkShallowOpApp (VarE $ mkName "GHC.Classes.<" ) es
shallowPrimOp CS.Le     es = mkShallowOpApp (VarE $ mkName "GHC.Classes.<=") es
shallowPrimOp CS.Ge     es = mkShallowOpApp (VarE $ mkName "GHC.Classes.>=") es
shallowPrimOp CS.Eq     es = mkShallowOpApp (VarE $ mkName "GHC.Classes.=" ) es
shallowPrimOp CS.NEq    es = mkShallowOpApp (VarE $ mkName "GHC.Classes./=") es
shallowPrimOp CS.BitAnd es = mkShallowOpApp (VarE $ mkName "Data.Bits..&.") es
shallowPrimOp CS.BitOr  es = mkShallowOpApp (VarE $ mkName "Data.Bits..|.") es
shallowPrimOp CS.BitXor es = mkShallowOpApp (VarE $ mkName "Data.Bits.xor") es
shallowPrimOp CS.LShift [e1,e2] = mkApp (VarE $ mkName "Data.Bits.shiftL") [e1,e2]
shallowPrimOp CS.RShift [e1,e2] = mkApp (VarE $ mkName "Data.Bits.shiftR") [e1,e2]
shallowPrimOp CS.LShift _ = __impossible "shallowPrimOp"
shallowPrimOp CS.RShift _ = __impossible "shallowPrimOp"
shallowPrimOp CS.Complement [e] = mkApp (VarE $ mkName "Data.Bits.complement") [e]
shallowPrimOp CS.Complement _ = __impossible "shallowPrimOp"


shallowExpr :: TypedExpr t v VarName -> SG Exp
shallowExpr (TE _ (Variable (_,v))) = pure $ VarE $ mkName (snm v)
shallowExpr (TE _ (Fun fn ts _)) = pure $ VarE $ mkName (snm fn)  -- only prints the fun name
shallowExpr (TE _ (Op opr es)) = shallowPrimOp <$> pure opr <*> (mapM shallowExpr es)
shallowExpr (TE _ (App f arg)) = mkApp <$> shallowExpr f <*> (mapM shallowExpr [arg])
-- shallowExpr (TE t (Con cn e))  = do
--   tn <- findTypeSyn t
--   econ <- mkApp <$> pure (mkStr [tn,".",cn]) <*> (mapM shallowExpr [e])
--   TermWithType econ <$> shallowType t
-- shallowExpr (TE t (Promote ty (TE _ (Con cn e)))) = shallowExpr (TE t (Con cn e))
-- shallowExpr (TE _ (Promote ty@(TPrim _) e)) = shallowPromote (__impossible "shallowExpr") ty e
-- shallowExpr (TE _ (Promote ty e)) = findTypeSyn ty >>= \tn -> shallowPromote tn ty e
-- shallowExpr (TE t (Struct fs)) = shallowMaker t fs
-- shallowExpr (TE _ (Member rec fld)) = shallowExpr rec >>= \e -> shallowGetter rec fld e
-- shallowExpr (TE _ (Unit)) = pure $ mkId "()"
-- shallowExpr (TE _ (ILit n pt)) = pure $ shallowILit n pt
-- shallowExpr (TE _ (SLit s)) = pure $ mkString s
-- shallowExpr (TE _ (Tuple e1 e2)) = mkApp <$> (pure $ mkId "Pair") <*> (mapM shallowExpr [e1, e2])
-- shallowExpr (TE _ (Put rec fld e)) = shallowSetter rec fld e
-- shallowExpr (TE _ (Let nm e1 e2)) = shallowLet nm e1 e2
-- shallowExpr (TE _ (LetBang vs nm e1 e2)) = shallowLet nm e1 e2
-- shallowExpr (TE t (Case e tag (_,n1,e1) (_,n2,e2))) = do
--   ecase <- shallowExpr e
--   tn <- findTypeSyn $ exprType e
--   let TSum alts = exprType e
--       falts = (filter ((/=) tag . fst) alts)
--       tags = map fst alts
--       types = map (fst . snd) falts  -- FIXME: cogent.1
--   tnto <- findTypeSyn $ TSum falts
--   -- Types of the shrinked variant type so that we can generate a
--   -- TermWithType and prevent Isabelle from complaining about not knowing the type
--   stypes <- shallowType $ TCon tnto types (__impossible "shallowExpr")
--   e1' <- mkLambdaE [snm n1] e1
--   e2' <- mkLambdaE [snm n2] e2
--   -- Increment the variable generator, we need to generate a variable
--   -- for emulating Cogent case, the shrinked variant requires asserting
--   -- its type
--   vn <- use varNameGen
--   varNameGen .= vn + 1
--   -- vn2 is used to give a name to e2' as in large case pattern matching
--   -- it is referenced many, many times.
--   vn2 <- use varNameGen
--   varNameGen .= vn + 1
--   let vgn = "v" ++ (subSymStr $ "G" ++ show vn)
--       vgn2 = "v" ++ (subSymStr $ "G" ++ show vn2)
--       es = map (\tag' -> if tag == tag' then e1' else
--                    let cons = mkApp (mkStr [tnto,".",tag']) [mkId vgn]
--                        typedCons = TermWithType cons stypes
--                    in mkLambda [vgn] $ mkApp (mkId vgn2) [typedCons]) tags
--       rcase = mkApp (mkStr ["case_",tn]) $ es ++ [ecase]
--       e2named = mkL vgn2 e2' rcase
--   pure $ e2named
-- shallowExpr (TE t (Esac e)) = do
--   tn <- findTypeSyn $ exprType e
--   e' <- shallowExpr e
--   pure $ mkApp (mkStr ["case_",tn]) [mkId "Fun.id", e']
-- shallowExpr (TE _ (If c th el)) = mkApp <$> (pure $ mkId "HOL.If") <*> mapM shallowExpr [c, th, el]
-- shallowExpr (TE _ (Take (n1,n2) rec fld e)) = do
--   erec <- shallowExpr rec
--   efield <- mkId <$> getRecordFieldName (exprType rec) fld
--   take <- pure $ mkApp (mkId $ "take" ++ subSymStr "cogent") [erec, efield]
--   let pp = mkPrettyPair n1 n2
--   mkLet pp take <$> shallowExpr e
-- shallowExpr (TE _ (Split (n1,n2) e1 e2)) = mkApp <$> mkLambdaE [mkPrettyPair n1 n2] e2 <*> mapM shallowExpr [e1]


-- ----------------------------------------------------------------------------
-- ??
--

shallowTypeDef = undefined

shallowDefinition :: Definition TypedExpr VarName
                  -> SG ([Either [Dec] [Dec]], Maybe FunName)
shallowDefinition (FunDef _ fn ps ti to e) =
    local (typarUpd typar) $ do
    e' <- shallowExpr e
    ty <- shallowType $ TFun ti to
    let sig = SigD fn' ty
        dec = FunD fn' [Clause [VarP arg0] (NormalB e') []]
    pure ([Left [sig,dec]], Just $ snm fn)
  where fn'   = mkName $ snm fn
        arg0  = mkName $ snm $ D.freshVarPrefix ++ "0"
        typar = map fst $ Vec.cvtToList ps
shallowDefinition (AbsDecl _ fn ps ti to) =
    local (typarUpd typar) $ do
      ty <- shallowType $ TFun ti to
      let sig = SigD fn' ty
          dec = FunD fn' [Clause [] (NormalB $ VarE $ mkName "undefined") []]
      pure ([Right [sig,dec]], Nothing)
  where fn' = mkName $ snm fn
        typar = map fst $ Vec.cvtToList ps
shallowDefinition (TypeDef tn ps Nothing) =
    let dec = DataD [] (mkName tn) (P.map (PlainTV . mkName) typar) Nothing [] []
     in local (typarUpd typar) $ pure ([Right [dec]], Nothing)
  where typar = Vec.cvtToList ps
shallowDefinition (TypeDef tn ps (Just t)) =
    local (typarUpd typar) $ (, Nothing) <$> (shallowTypeDef tn typar t >>= return . map Right)
  where typar = Vec.cvtToList ps


shallowDefinitions :: [Definition TypedExpr VarName] 
                    -> SG ([Either [Dec] [Dec]], [FunName])
shallowDefinitions = (((concat *** catMaybes) . P.unzip) <$>) . mapM ((varNameGen .= 0 >>) . shallowDefinition)

shallowTypeFromTable = undefined

shallowFile :: String -> Stage -> [Definition TypedExpr VarName]
            -> SG (HaskellModule, HaskellModule)
shallowFile name stg defs = do
  let (typedecls,defs') = L.partition isAbsTyp defs
  (htdecls,_) <- shallowDefinitions typedecls
  (htypes,_,_) <- shallowTypeFromTable
  (hdefs,_) <- shallowDefinitions defs'
  return ( HM shhm (ModuleInfo []) $ concat $ lefts hdefs
         , HM sshm (ModuleInfo []) $ concat (rights htdecls) ++ htypes ++ concat (rights hdefs)
         )




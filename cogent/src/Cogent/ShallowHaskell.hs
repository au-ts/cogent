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
import Cogent.Shallow 
  ( SG(..), SGTables(..), StateGen(..)
  , MapTypeName
  , typarUpd, varNameGen, isRecTuple, findShortType
  , stsyn
  )
import Cogent.ShallowTable (TypeStr(..), st, getStrlType, toTypeStr)
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
import qualified Data.Map as M
import Data.Maybe (catMaybes)
-- import Language.Haskell.TH.Quote  as TH
import Language.Haskell.TH.Syntax as TH
import Language.Haskell.TH.Ppr    as PP
import Language.Haskell.TH.PprLib as PP
import Prelude as P

-- package name, module names
shmn = mkModName "TODO"
ssmn = mkModName "TODO"

snm :: String -> String
snm = id


-- ----------------------------------------------------------------------------
-- type generators
--

mkConT :: Name -> [TH.Type] -> TH.Type
mkConT n ts = foldr' (flip AppT) (ConT n) ts

mkTupleT :: [TH.Type] -> TH.Type
mkTupleT ts = foldl' AppT (TupleT $ P.length ts) ts

shallowTVar :: Int -> String
shallowTVar v = [chr $ ord 'a' + fromIntegral v]

shallowTypeWithName :: S.Type t -> SG TH.Type
shallowTypeWithName t = shallowType =<< findShortType t

shallowRecTupleType :: [(FieldName, (S.Type t, Bool))] -> SG TH.Type
shallowRecTupleType fs = shallowTupleType <$> mapM shallowType (map (fst . snd) fs)

shallowTupleType :: [TH.Type] -> TH.Type
shallowTupleType [] = error "Record should have at least 2 fields"
shallowTupleType ts = mkTupleT ts

shallowType :: S.Type t -> SG TH.Type
shallowType (TVar v) = VarT . mkName <$> ((!!) <$> asks typeVars <*> pure (finInt v))
shallowType (TVarBang v) = shallowType (TVar v)
shallowType (TCon tn ts _) = mkConT (mkName tn) <$> mapM shallowType ts
shallowType (TFun t1 t2) = AppT <$> (AppT ArrowT <$> shallowType t1) <*> shallowType t2
shallowType (TPrim pt) = pure $ shallowPrimType pt
shallowType (TString) = pure $ ConT $ mkName "String"
shallowType (TSum alts) = shallowTypeWithName (TSum alts)
shallowType (TProduct t1 t2) = mkTupleT <$> sequence [shallowType t1, shallowType t2]
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
-- expression generators
--

mkApp :: Exp -> [Exp] -> Exp
mkApp e es = foldl' AppE e es

shallowPrimOp :: Op -> [Exp] -> Exp
shallowPrimOp CS.Plus   es = mkApp (VarE $ mkName "GHC.Num.+") es
shallowPrimOp CS.Minus  es = mkApp (VarE $ mkName "GHC.Num.-") es
shallowPrimOp CS.Times  es = mkApp (VarE $ mkName "GHC.Num.*") es
shallowPrimOp CS.Divide es = mkApp (VarE $ mkName "GHC.Real.div") es
shallowPrimOp CS.Mod    es = mkApp (VarE $ mkName "GHC.Real.mod") es
shallowPrimOp CS.Not    es = mkApp (VarE $ mkName "GHC.Classes.not") es
shallowPrimOp CS.And    es = mkApp (VarE $ mkName "GHC.Classes.&&") es 
shallowPrimOp CS.Or     es = mkApp (VarE $ mkName "GHC.Classes.||") es 
shallowPrimOp CS.Gt     es = mkApp (VarE $ mkName "GHC.Classes.>" ) es
shallowPrimOp CS.Lt     es = mkApp (VarE $ mkName "GHC.Classes.<" ) es
shallowPrimOp CS.Le     es = mkApp (VarE $ mkName "GHC.Classes.<=") es
shallowPrimOp CS.Ge     es = mkApp (VarE $ mkName "GHC.Classes.>=") es
shallowPrimOp CS.Eq     es = mkApp (VarE $ mkName "GHC.Classes.=" ) es
shallowPrimOp CS.NEq    es = mkApp (VarE $ mkName "GHC.Classes./=") es
shallowPrimOp CS.BitAnd es = mkApp (VarE $ mkName "Data.Bits..&.") es
shallowPrimOp CS.BitOr  es = mkApp (VarE $ mkName "Data.Bits..|.") es
shallowPrimOp CS.BitXor es = mkApp (VarE $ mkName "Data.Bits.xor") es
shallowPrimOp CS.LShift [e1,e2] = mkApp (VarE $ mkName "Data.Bits.shiftL") [e1,e2]
shallowPrimOp CS.RShift [e1,e2] = mkApp (VarE $ mkName "Data.Bits.shiftR") [e1,e2]
shallowPrimOp CS.LShift _ = __impossible "shallowPrimOp"
shallowPrimOp CS.RShift _ = __impossible "shallowPrimOp"
shallowPrimOp CS.Complement [e] = mkApp (VarE $ mkName "Data.Bits.complement") [e]
shallowPrimOp CS.Complement _ = __impossible "shallowPrimOp"

shallowILit :: Integer -> PrimInt -> Exp
shallowILit n Boolean = ConE . mkName $ if n > 0 then "True" else "False"
shallowILit n v = SigE (LitE $ IntegerL n) (shallowPrimType v)  -- FIXME: IntegerL or IntPrimL? / zilinc

-- makes `let p = e1 in e2'
shallowLet :: SNat n -> Pat -> TypedExpr t v VarName -> TypedExpr t (v :+: n) VarName -> SG Exp
shallowLet _ p e1 e2 = do
  e1' <- shallowExpr e1
  e2' <- shallowExpr e2
  pure $ LetE [ValD p (NormalB e1') []] e2'

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
shallowExpr (TE _ (Unit)) = pure $ ConE $ mkName "GHC.Tuple.()"
shallowExpr (TE _ (ILit n pt)) = pure $ shallowILit n pt
shallowExpr (TE _ (SLit s)) = pure $ LitE $ StringL s
shallowExpr (TE _ (Tuple e1 e2)) = TupE <$> mapM shallowExpr [e1,e2]
-- shallowExpr (TE _ (Put rec fld e)) = shallowSetter rec fld e
shallowExpr (TE _ (Let nm e1 e2)) = shallowLet s1 (VarP $ mkName nm) e1 e2
shallowExpr (TE _ (LetBang vs nm e1 e2)) = shallowLet s1 (VarP $ mkName nm) e1 e2
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
shallowExpr (TE _ (If c th el)) = do
  [c',th',el'] <- mapM shallowExpr [c, th, el]
  pure $ CondE c' th' el'
-- shallowExpr (TE _ (Take (n1,n2) rec fld e)) = do
--   erec <- shallowExpr rec
--   efield <- mkId <$> getRecordFieldName (exprType rec) fld
--   take <- pure $ mkApp (mkId $ "take" ++ subSymStr "cogent") [erec, efield]
--   let pp = mkPrettyPair n1 n2
--   mkLet pp take <$> shallowExpr e
shallowExpr (TE _ (Split (n1,n2) e1 e2)) = shallowLet s2 (TupP [VarP $ mkName n1, VarP $ mkName n2]) e1 e2


-- ----------------------------------------------------------------------------
-- top-level generators
--

shallowTypeDef :: TypeName -> [TyVarName] -> S.Type t -> SG [Dec]
shallowTypeDef _ _ _ = __fixme $ pure []

shallowTypeFromTable :: SG ([Dec], [Dec], MapTypeName)
shallowTypeFromTable = __fixme $ pure ([], [], undefined)


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
    local (typarUpd typar) $ (, Nothing) <$> ((:[]) . Right <$> shallowTypeDef tn typar t)
  where typar = Vec.cvtToList ps


shallowDefinitions :: [Definition TypedExpr VarName] 
                    -> SG ([Either [Dec] [Dec]], [FunName])
shallowDefinitions = (((concat *** catMaybes) . P.unzip) <$>) . mapM ((varNameGen .= 0 >>) . shallowDefinition)


data HaskellModule = HM ModName ModuleInfo [[Dec]] deriving (Show)

pprModule :: ModName -> Doc
pprModule (ModName s) = text "module" <+> text s <+> text "where\n"

pprImports :: ModuleInfo -> Doc
pprImports (ModuleInfo []) = PP.empty
pprImports (ModuleInfo ms) = PP.vcat (P.map pprImport ms) PP.<> text "\n"

pprImport :: Module -> Doc
pprImport (Module _ (ModName s)) = text "import" <+> text s

instance Ppr HaskellModule where
  ppr (HM mn info decs) = pprModule mn
                      $+$ pprImports info
                      $+$ vcat (P.map ((PP.<> text "\n") . ppr) decs)

shallowFile :: String -> Stage -> [Definition TypedExpr VarName]
            -> SG (HaskellModule, HaskellModule)
shallowFile name stg defs = do
  let (typedecls,defs') = L.partition isAbsTyp defs
  (htdecls,_) <- shallowDefinitions typedecls
  (htypes,_,_) <- shallowTypeFromTable
  (hdefs,_) <- shallowDefinitions defs'
  return ( HM shmn (ModuleInfo []) $ lefts hdefs
         , HM ssmn (ModuleInfo []) $ rights htdecls ++ [htypes] ++ rights hdefs
         )

shallow :: Bool -> String -> Stage -> [Definition TypedExpr VarName] -> String -> (Doc, Doc)
shallow recoverTuples hs stg defs log =
  let (shal,shrd) = fst $ evalRWS (runSG (shallowFile hs stg defs))
                                         (SGTables (st defs) (stsyn defs) [] recoverTuples)
                                         (StateGen 0 M.empty)
      header = (PP.text ("{-\n" ++ log ++ "\n-}\n") PP.$+$)
   in (header $ ppr shal, header $ ppr shrd)


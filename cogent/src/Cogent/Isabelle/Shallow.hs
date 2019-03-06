--
-- Copyright 2017, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--


{-
 - Shallow.hs: shallow Isabelle embedding, SCorres proof and shallow-tuples proof.
 -}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Cogent.Isabelle.Shallow
--   ( shallow
--   , shallowConsts
--   , shallowTuplesProof
--   , MapTypeName
--   )
  where

import Cogent.Common.Syntax as CS
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Core as CC
import Cogent.Desugar as D (freshVarPrefix)
import Cogent.Isabelle.ShallowTable (TypeStr(..), st, getStrlType, toTypeStr)
import Cogent.Normal as N (freshVarPrefix)
import Cogent.Util (Stage(..), Warning)
import Data.Nat (Nat(Zero,Suc))
import Data.Vec as Vec

import Isabelle.ExprTH
import Isabelle.InnerAST as I
import Isabelle.OuterAST as O

import Control.Applicative
import Control.Arrow ((***))
import Control.Monad.RWS hiding (Product, Sum, mapM)
import Control.Monad.State
import Control.Monad.Writer (Writer, runWriter)
import Data.Char (ord, chr, intToDigit, isDigit)
import Data.Either (lefts, rights)
import Data.Function (on)
import Data.List (isPrefixOf, stripPrefix, partition, sortBy, minimumBy, groupBy, unzip5, intercalate)
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Numeric
import Prelude as P
import System.FilePath ((</>))
import Text.PrettyPrint.ANSI.Leijen (Doc, pretty, string)
import qualified Text.PrettyPrint.ANSI.Leijen as L ((<$$>))
import Lens.Micro
import Lens.Micro.TH
import Lens.Micro.Mtl
import Debug.Trace

isaReservedNames = ["o", "value", "from"]

type MapTypeName = M.Map TypeStr TypeName

data SGTables = SGTables { typeStrs      :: [TypeStr]
                         , typeNameMap   :: MapTypeName
                         , typeVars      :: [String]     -- ^ @Cogent var &#x21A6; Isabelle var@
                         , recoverTuples :: Bool         -- ^ not a table, but convenient to be included here
                         }

type MapConcTypeSyn = M.Map String TypeName

data StateGen = StateGen {
    _varNameGen   :: Int,            -- ^ counter for fresh variables
    _concTypeSyns :: MapConcTypeSyn  -- ^ @type structure hash &#x21A6; Cogent type synonym name@
}

makeLenses ''StateGen

newtype SG a = SG { runSG :: RWS SGTables [Warning] StateGen a }
               deriving (Functor, Applicative, Monad,
                         MonadReader SGTables,
                         MonadWriter [Warning],
                         MonadState  StateGen)

shallowTVar :: Int -> String
shallowTVar v = [chr $ ord 'a' + fromIntegral v]

shallowTypeWithName :: CC.Type t -> SG I.Type
shallowTypeWithName t = shallowType =<< findShortType t

shallowRecTupleType :: [(FieldName, (CC.Type t, Bool))] -> SG I.Type
shallowRecTupleType fs = shallowTupleType <$> mapM shallowType (map (fst . snd) fs)

shallowType :: CC.Type t -> SG I.Type
shallowType (TVar v) = I.TyVar <$> ((!!) <$> asks typeVars <*> pure (finInt v))
shallowType (TVarBang v) = shallowType (TVar v)
shallowType (TCon tn ts _) = I.TyDatatype tn <$> mapM shallowType ts
shallowType (TFun t1 t2) = I.TyArrow <$> shallowType t1 <*> shallowType t2
shallowType (TPrim pt) = pure $ shallowPrimType pt
shallowType (TString) = pure $ I.AntiType "string"
shallowType (TSum alts) = shallowTypeWithName (TSum alts)
shallowType (TProduct t1 t2) = I.TyTuple <$> shallowType t1 <*> shallowType t2
shallowType (TRecord fs s) = do
  tuples <- asks recoverTuples
  if tuples && isRecTuple (map fst fs) then
    shallowRecTupleType fs
  else
    shallowTypeWithName (TRecord fs s)
shallowType (TUnit) = return $ I.AntiType "unit"

shallowPrimType :: PrimInt -> I.Type
shallowPrimType U8  = I.TyDatatype "word" [I.AntiType "8"]
shallowPrimType U16 = I.TyDatatype "word" [I.AntiType "16"]
shallowPrimType U32 = I.TyDatatype "word" [I.AntiType "32"]
shallowPrimType U64 = I.TyDatatype "word" [I.AntiType "64"]
shallowPrimType Boolean = I.TyPrim I.BoolT

-- The `(foo)` syntax makes an infix operator prefix after Isabelle2018. There
-- is a special case on `(*)`, which doesn't work because comments start with
-- `(*`, which is why it's non-trivial to abstract making prefix ops here.
shallowPrimOp :: Op -> [Term] -> Term
shallowPrimOp CS.Plus   es = mkApp (mkId "(+)") es
shallowPrimOp CS.Minus  es = mkApp (mkId "(-)") es
shallowPrimOp CS.Times  es = mkApp (mkId "( * )") es
shallowPrimOp CS.Divide es = mkApp (mkId "checked_div") es
shallowPrimOp CS.Mod    es = mkApp (mkId "checked_mod") es
shallowPrimOp CS.Not    es = mkApp (mkId "HOL.Not") es
shallowPrimOp CS.And    es = TermBinOp Conj (es!!0) (es!!1)
shallowPrimOp CS.Or     es = TermBinOp Disj (es!!0) (es!!1)
shallowPrimOp CS.Gt     es = mkApp (mkId "(>)") es
shallowPrimOp CS.Lt     es = mkApp (mkId "(<)") es
shallowPrimOp CS.Le     es = mkApp (mkId "(<=)") es
shallowPrimOp CS.Ge     es = mkApp (mkId "(>=)") es
shallowPrimOp CS.Eq     es = mkApp (mkId "(=)") es
shallowPrimOp CS.NEq    es = mkApp (mkId "(~=)") es
shallowPrimOp CS.BitAnd es = mkApp (mkId "(AND)") es
shallowPrimOp CS.BitOr  es = mkApp (mkId "(OR)") es
shallowPrimOp CS.BitXor es = mkApp (mkId "(XOR)") es
shallowPrimOp CS.LShift [e1,e2] = mkApp (mkId "checked_shift") [mkId "shiftl", e1, e2]
shallowPrimOp CS.RShift [e1,e2] = mkApp (mkId "checked_shift") [mkId "shiftr", e1, e2]
shallowPrimOp CS.LShift _ = __impossible "shallowPrimOp"
shallowPrimOp CS.RShift _ = __impossible "shallowPrimOp"
shallowPrimOp CS.Complement [e] = mkApp (mkId "NOT") [e]
shallowPrimOp CS.Complement _ = __impossible "shallowPrimOp"

-- | Strip names and format them for Isabelle
snm :: String -> String
snm nm = case nm `elem` isaReservedNames of
  True -> nm ++ I.subSym ++ "r"
  _ -> case stripPrefix D.freshVarPrefix nm of
    Just nb -> "ds" ++ subSymStr nb
    Nothing -> case stripPrefix N.freshVarPrefix nm of
      Just nb -> "an" ++ subSymStr nb
      -- Add debug note
      Nothing -> case "_" `isPrefixOf` nm of
        True  -> dropWhile (== '_') nm ++ I.subSym ++ "d"
        False -> nm

list2 a b = [a,b]

shallowILit :: Integer -> PrimInt -> Term
shallowILit n Boolean = if n > 0 then mkTru else mkFls
shallowILit n v = TermWithType (mkId $ show n) (shallowPrimType v)

findType :: CC.Type t -> SG (CC.Type t)
findType t = getStrlType <$> asks typeNameMap <*> asks typeStrs <*> pure t

-- | Reverse engineer the type synonym of a algebraic data type
findShortType :: CC.Type t -> SG (CC.Type t)
findShortType t = do
  map <- use concTypeSyns
  case M.lookup (hashType t) map of
   Nothing -> findType t
   Just tn -> pure $ TCon tn [] (__impossible "findShortType")

findTypeSyn :: CC.Type t -> SG String
findTypeSyn t = findType t >>= \(TCon nm _ _) -> pure nm

shallowExpr :: TypedExpr t v VarName -> SG Term
shallowExpr (TE _ (Variable (_,v))) = pure $ mkId (snm v)
shallowExpr (TE _ (Fun fn ts _)) = pure $ mkId $ snm $ coreFunNameToIsabelleName fn  -- only prints the fun name
shallowExpr (TE _ (Op opr es)) = shallowPrimOp <$> pure opr <*> (mapM shallowExpr es)
shallowExpr (TE _ (App f arg)) = mkApp <$> shallowExpr f <*> (mapM shallowExpr [arg])
shallowExpr (TE t (Con cn e _))  = do
  tn <- findTypeSyn t
  econ <- mkApp <$> pure (mkStr [tn,".",cn]) <*> (mapM shallowExpr [e])
  TermWithType econ <$> shallowType t
shallowExpr (TE _ (Unit)) = pure $ mkId "()"
shallowExpr (TE _ (ILit n pt)) = pure $ shallowILit n pt
shallowExpr (TE _ (SLit s)) = pure $ mkString s
shallowExpr (TE _ (Let nm e1 e2)) = shallowLet nm e1 e2
shallowExpr (TE _ (LetBang vs nm e1 e2)) = shallowLet nm e1 e2
shallowExpr (TE _ (Tuple e1 e2)) = mkApp <$> (pure $ mkId "Pair") <*> (mapM shallowExpr [e1, e2])
shallowExpr (TE t (Struct fs)) = shallowMaker t fs
shallowExpr (TE _ (If c th el)) = mkApp <$> (pure $ mkId "HOL.If") <*> mapM shallowExpr [c, th, el]
shallowExpr (TE t (Case e tag (_,n1,e1) (_,n2,e2))) = do
  e' <- shallowExpr e
  let te@(TSum alts) = exprType e
  tn  <- findTypeSyn te
  te' <- shallowType te
  e1' <- mkLambdaE [snm n1] e1
  e2' <- mkLambdaE [snm n2] e2
  vn <- varNameGen <<%= (+1)
  vn2 <- varNameGen <<%= (+1)
  let vgn = "v" ++ (subSymStr $ "G" ++ show vn)
      vgn2 = "v" ++ (subSymStr $ "G" ++ show vn2)  -- This is the continuation @e2@
      es = flip map alts $ \(tag',(t',b')) ->
             if | tag == tag' -> e1'
                | b' -> mkId "undefined"
                | otherwise -> 
                    let cons = mkApp (mkStr [tn,".",tag']) [mkId vgn]
                        typedCons = TermWithType cons te'
                     in mkLambda [vgn] $ mkApp (mkId vgn2) [typedCons]
      rcase = mkApp (mkStr ["case_",tn]) $ es ++ [e']
  pure $ mkL vgn2 e2' rcase
-- \ ^^^ NOTE: We can't use the @case _ of@ syntax as our @case@s are binary (and nested).
-- It seems that Isabelle spends exponential time on processing the @case _ of@ syntax depending
-- on the level of nestings. / zilinc
shallowExpr (TE t (Esac e)) = do
  tn <- findTypeSyn $ exprType e
  e' <- shallowExpr e
  let TSum alts = exprType e
      es = flip map alts $ \(tag',(t',b')) -> 
             if | b' -> mkId "undefined"
                | otherwise -> mkId "Fun.id"
  pure $ mkApp (mkStr ["case_",tn]) $ es ++ [e'] 
shallowExpr (TE _ (Split (n1,n2) e1 e2)) = mkApp <$> mkLambdaE [mkPrettyPair n1 n2] e2 <*> mapM shallowExpr [e1]
shallowExpr (TE _ (Member rec fld)) = shallowExpr rec >>= \e -> shallowGetter rec fld e
shallowExpr (TE _ (Take (n1,n2) rec fld e)) = do
  erec <- shallowExpr rec
  efield <- mkId <$> getRecordFieldName (exprType rec) fld
  let take = mkApp (mkId $ "take" ++ subSymStr "cogent") [erec, efield]
      pp = mkPrettyPair n1 n2
  mkLet pp take <$> shallowExpr e
shallowExpr (TE _ (Put rec fld e)) = shallowSetter rec fld e
shallowExpr (TE _ (Promote ty e)) = shallowExpr e
shallowExpr (TE _ (Cast    (TPrim pt) (TE _ (ILit n _)))) = pure $ shallowILit n pt
shallowExpr (TE _ (Cast    (TPrim pt) e)) =
  TermWithType <$> (mkApp (mkId "ucast") <$> ((:[]) <$> shallowExpr e)) <*> pure (shallowPrimType pt)

-- | @'mkL' nm t1 t2@: 
--
--   It generates term @(&#x03bb; nm. t2) t1@
mkL :: VarName -> Term -> Term -> Term
mkL nm t1 t2 = mkApp (mkLambda [snm nm] t2) [t1]

mkLetds :: VarName -> Term -> Term -> Term
mkLetds nm t1 t2 = mkApp (mkId $ "Let" ++ subSymStr "ds") [t1, mkLambda [snm nm] t2]

mkLet :: VarName -> Term -> Term -> Term
mkLet nm t1 t2 =
 if D.freshVarPrefix `isPrefixOf` nm then
    --mkApp (mkLambda [snm nm] t2) [t1]
    mkLetds nm t1 t2
 else
    mkApp (mkId "HOL.Let") [t1, mkLambda [snm nm] t2]

shallowLet :: VarName -> TypedExpr t v VarName -> TypedExpr t ('Suc v) VarName -> SG Term
shallowLet nm e1 e2 = mkLet nm <$> shallowExpr e1 <*> shallowExpr e2

mkStr :: [String] -> Term
mkStr = mkId . concat

mkPrettyPair :: VarName -> VarName -> String
mkPrettyPair n1 n2 = "(" ++ snm n1 ++ "," ++ snm n2 ++ ")"

mkLambdaE :: [VarName] -> TypedExpr t v VarName -> SG Term
mkLambdaE vs e = mkLambda vs <$> shallowExpr e

-- | Reverse engineer whether a record type was a tuple by looking at the field names.
--   This is __hacky__.
isRecTuple :: [FieldName] -> Bool
isRecTuple fs =
  P.length fs > 1 &&
  filter (\xs -> xs!!0 == 'p' && let ys = drop 1 xs in filter isDigit ys == ys) fs == fs

shallowMaker :: CC.Type t -> [(FieldName, TypedExpr t v VarName)] -> SG Term
shallowMaker t fs = do
  tn <- findTypeSyn t
  let fnms = map fst fs
  tuples <- asks recoverTuples
  if tuples && isRecTuple fnms
  then mkTuple <$> mapM (shallowExpr . snd) fs
  else mkApp <$> pure (mkStr [tn ++ ".", "make"]) <*> (mapM (shallowExpr . snd) fs)

shallowSetter :: TypedExpr t v VarName -> Int -> TypedExpr t v VarName -> SG Term
shallowSetter rec idx e = do
  tn <- getRecordFieldName (exprType rec) idx
  let setter = tn ++ "_update"
  mkApp (mkId setter) <$> (list2 <$> mkLambdaE ["_"] e <*> shallowExpr rec)

shallowGetter :: TypedExpr t v VarName -> Int -> Term -> SG Term
shallowGetter rec idx rect = mkApp <$> (mkId <$> getRecordFieldName (exprType rec) idx) <*> pure [rect]

getRecordFieldName :: CC.Type t -> Int -> SG String
getRecordFieldName t@(TRecord fs _) ind = do
  tn <- findTypeSyn t
  let fnms = map fst fs
  tuples <- asks recoverTuples
  let prefix = if tuples && isRecTuple fnms then recTupleName fnms ++ "_" else tn ++ "."
  pure $ prefix ++ (map fst fs !! ind) ++ subSymStr "f"
getRecordFieldName _ _ = __impossible "getRecordFieldName"

typarUpd typar v = v {typeVars = typar}

-- Clear out all taken annotations and mark all sigil as Writable.
sanitizeType :: CC.Type t -> CC.Type t
sanitizeType (TSum ts) = TSum (map (\(tn,(t,b)) -> (tn,(sanitizeType t,b))) ts)
sanitizeType (TRecord ts s) = TRecord (map (\(tn, (t,_)) -> (tn, (sanitizeType t, False))) ts) s
sanitizeType (TCon tn ts s) = TCon tn (map sanitizeType ts) s
sanitizeType (TFun ti to) = TFun (sanitizeType ti) (sanitizeType to)
sanitizeType (TProduct t t') = TProduct (sanitizeType t) (sanitizeType t')
sanitizeType t = t

-- | Produce a hash for a record or variant type. Only the structure of the type matters;
--   taken entries or sigils do not.
hashType :: CC.Type t -> String
hashType (TSum ts)      = show (sanitizeType $ TSum ts)
hashType (TRecord ts s) = show (sanitizeType $ TRecord ts s)
hashType _              = error "hashType: should only pass Variant and Record types"

-- | A subscript @T@ will be added when generating type synonyms. 
--   Also adds an entry to the type synonyms table if it's not parameterised so that
--   a shorter (and hence more readable) name can be retrieved when a type is used.
shallowTypeDefSaveSyn:: TypeName -> [TyVarName] -> CC.Type t -> SG [TheoryDecl I.Type I.Term]
shallowTypeDefSaveSyn tn ps r = do
  st <- shallowType r
  let syname = tn ++ subSymStr "T"
      hash = hashType r
  -- FIXME: We might want to support type parameters but I can't be bothered.
  when (null ps) (concTypeSyns %= M.insert hash syname)
  pure [TypeSynonym (TypeSyn syname st ps)]

-- | Generates @type_synonym@ definitions for types.
shallowTypeDef :: TypeName -> [TyVarName] -> CC.Type t -> SG [TheoryDecl I.Type I.Term]
shallowTypeDef tn ps (TPrim p)      = pure [TypeSynonym (TypeSyn tn (shallowPrimType p) ps)]
shallowTypeDef tn ps (TRecord fs s) = shallowTypeDefSaveSyn tn ps (TRecord fs s)
shallowTypeDef tn ps (TSum ts)      = shallowTypeDefSaveSyn tn ps (TSum ts)
shallowTypeDef tn ps t = do
  st <- shallowType t
  pure [TypeSynonym (TypeSyn tn st ps)]

typeNameFromIdx :: Int -> String
typeNameFromIdx idx = 'T':show idx

simpLemma :: String -> String -> TheoryDecl I.Type I.Term
simpLemma nm tag =
  let simp = Attribute "simp" []
      valRelN = "valRel_" ++ nm
      thmN = valRelN ++ "_" ++ tag
      tytag = I.AntiTerm (nm ++ "." ++ tag)
      tagName = I.ConstTerm $ I.StringLiteral tag
      prop = [[isaTerm| valRel \<xi> ($tytag x) (VSum $tagName x') = valRel \<xi> x x'|]]
      methods = [Method "simp" ["add:", valRelN]]
   in LemmaDecl $ Lemma False (Just (TheoremDecl (Just thmN) [simp])) prop (Proof methods ProofDone)

mkPrettyTuple :: [VarName] -> String
mkPrettyTuple vn = "(" ++ intercalate "," vn ++ ")"

recTupleAccessors :: [FieldName] -> FieldName -> [(TheoryDecl I.Type I.Term, Name)]
recTupleAccessors fs fn =
  let dfnm = concat [recTupleName fs, "_", fn, subSymStr "f"]
      lhs = mkId dfnm
      rhs = mkLambda [mkPrettyTuple fs] (mkId fn)
      term = [isaTerm| $lhs \<equiv> $rhs |]
      getter = Definition (Def (Just (Sig dfnm Nothing)) term)
      f = "f" ++ subSymStr "fun"
      udfnm = dfnm ++ "_update"
      lhs2 = mkId udfnm
      tupelms = map (\nm -> if nm == fn then mkApp (mkId f) [mkId nm] else mkId fn) fs
      rhs2 = mkLambda [mkPrettyTuple fs, f] (mkTuple tupelms)
      term2 = [isaTerm| $lhs2 \<equiv> $rhs2 |]
      setter = Definition (Def (Just (Sig udfnm Nothing)) term2)
  in [(getter, dfnm ++ "_def"), (setter, udfnm ++ "_def")]

recTuplePrefix :: String
recTuplePrefix = "P"

recTupleName :: [FieldName] -> String
recTupleName fs = recTuplePrefix ++ (show $ P.length fs)

recTupleDecls :: [FieldName] -> [(TheoryDecl I.Type I.Term, Name)]
recTupleDecls fs = concatMap (recTupleAccessors fs) fs

shallowTupleType :: [I.Type] -> I.Type
shallowTupleType [] = error "Record should have at least 2 fields"  -- FIXME: does this error msg make sense? / zilinc
shallowTupleType [x] = x
shallowTupleType (x:xs) = I.TyTuple x (shallowTupleType xs)

fieldConjValRel :: [(I.Term, I.Term)] -> I.Term
fieldConjValRel [] = error "Can't have empty record"
fieldConjValRel [(var,fld)] = [isaTerm| valRel \<xi> ($fld x) $var |]
fieldConjValRel ((var,fld):r) = let rest = fieldConjValRel r in [isaTerm| valRel \<xi> ($fld x) $var \<and> $rest |]

data DeclT = RecordT | VariantT

shallowTT :: (Int, TypeStr)
          -> SG ( [TheoryDecl I.Type I.Term]
                , [(DeclT,TheoryDecl I.Type I.Term)]
                , [TheoryDecl I.Type I.Term]
                , [Name]
                , MapTypeName
                )
shallowTT (tidx, t) = do
  tnmap <- asks typeNameMap
  let mbsyn = M.lookup t tnmap
      nm = fromMaybe (typeNameFromIdx tidx) mbsyn
      newmap = M.insert t nm tnmap
  case t of
    RecordStr fs -> do
      tuples <- asks recoverTuples
      let tvars = map shallowTVar [0..P.length fs - 1]
          comb = P.zip tvars fs
          fields = map (\(tvar,fn) -> O.RecField (fn ++ subSymStr "f") $ I.TyVar tvar) comb
          evarNames = map ("f_" ++) fs
          tyNames = map ("t_" ++) fs
          (ity, (recdecls, defnames), prefix) = if tuples && isRecTuple fs
            then ( shallowTupleType (map I.TyVar tvars)
                 , ([], map snd (recTupleDecls fs)) --  P.unzip
                 , recTupleName fs ++ "_")
            else ( I.TyDatatype nm $ map I.TyVar tyNames
                 , ([O.RecordDecl (Record nm fields tvars)], [])
                 , nm ++ ".")
          evarIsaList = I.mkList $ map I.mkId evarNames
          conjs = fieldConjValRel (P.zip (map I.mkId evarNames) (map (I.mkId . (prefix ++) . (++ subSymStr "f")) fs))
          valRelBody = I.QuantifiedTerm Exists (map I.Id evarNames) [isaTerm| v = VRecord $evarIsaList \<and> $conjs |]
          valRelSpecName = "valRel_" ++ nm
          valRelDef = OverloadedDef
                        (Def (Just (Sig valRelSpecName Nothing)) [isaTerm| $(mkId valRelSpecName) \<xi> (x :: $ity) v \<equiv> $valRelBody |])
                        (Sig "valRel" Nothing)
          valRel = if tuples && isRecTuple fs then [] else [(RecordT, valRelDef)]
      return (recdecls, valRel, [], defnames, newmap)
    VariantStr fs ->
      let tvars = map shallowTVar [0..P.length fs - 1]
          comb = P.zip tvars fs
          cons = map (\(tvar,fn) -> O.DTCons fn $ [I.TyVar tvar]) comb
          ity = I.TyDatatype nm $ map I.TyVar tvars
          caseExpr = mkId $ "case_" ++ nm
          valRelBody' [] = [isaTerm| $caseExpr |]
          valRelBody' (x:xs) = let tagName = I.ConstTerm $ I.StringLiteral x
                                in I.TermApp (valRelBody' xs) [isaTerm|(\<lambda>x. \<exists>x'. v' = VSum $tagName x' \<and> valRel \<xi> x x') |]
          valRelBody = I.TermApp (valRelBody' $ reverse fs) [isaTerm| v |]
          valRelSpecName = "valRel_" ++ nm
          valRelDef = OverloadedDef
                        (Def (Just (Sig valRelSpecName Nothing)) [isaTerm| $(mkId valRelSpecName) \<xi> (v :: $ity) v' \<equiv> $valRelBody |])
                        (Sig "valRel" Nothing)
          simpLemmas = map (simpLemma nm) fs
      in pure $ ([O.DataTypeDecl (Datatype nm cons tvars)], [(VariantT, valRelDef)], simpLemmas, [], newmap)

-- | If several types share the same structure, we only keep the shortest synonym for it.
filterDuplicates :: [(TypeStr,TypeName)] -> [(TypeStr,TypeName)]
filterDuplicates xs =
  let sorted = sortBy (compare `on` fst) xs
      grouped = groupBy ((==) `on` fst) sorted
      grpdsrtd = map (sortBy (compare `on` snd)) grouped
  in map (minimumBy (compare `on` (P.length . snd))) grpdsrtd

stsyn :: [Definition TypedExpr VarName] -> MapTypeName
stsyn decls = M.fromList . filterDuplicates . concat $ P.map synAllTypeStr decls

synAllTypeStr :: Definition TypedExpr VarName -> [(TypeStr, TypeName)]
synAllTypeStr (TypeDef tn _ (Just (TRecord fs _))) = [(RecordStr $ P.map fst fs, tn)]
synAllTypeStr (TypeDef tn _ (Just (TSum alts))) = [(VariantStr $ P.map fst alts, tn)]
synAllTypeStr _ = []

shallowTypeFromTable :: SG ([TheoryDecl I.Type I.Term], [TheoryDecl I.Type I.Term], MapTypeName)
shallowTypeFromTable = do
  table <- asks typeStrs
  let itable = P.zip [0..] table
  (decls1,decls2,lemmas,defnames,maps) <- unzip5 <$> mapM shallowTT itable
  pure ( concat decls1
       , map snd (concat decls2) ++ concat lemmas ++
         lemmaBuckets (concat decls2) ++ defNameBucket (concat defnames)
       , M.unions maps )
  where
    defNameBucket [] = []
    defNameBucket ns@(_:_) = [O.LemmasDecl (O.Lemmas (O.TheoremDecl (Just "tuple_defs") [Attribute "simp" []]) $ map thmDecl ns)]
    thmDecl n = O.TheoremDecl (Just n) []

lemmaBuckets :: [(DeclT, TheoryDecl I.Type I.Term)] -> [TheoryDecl I.Type I.Term]
lemmaBuckets is =
  let (recs,variants) = P.unzip $ map lemmaBucket' is
   in lemmas "valRel_records" (concat recs) ++ lemmas "valRel_variants" (concat variants)
  where lemmaBucket' ((RecordT, O.OverloadedDef d s))
           | Just (Sig n _) <- defSig d
           , n' <- drop (P.length "valRel_") n
           = ([ O.TheoremDecl (Just n) [], O.TheoremDecl (Just ( n' ++ ".defs")) []], [])
        lemmaBucket' ((VariantT, O.OverloadedDef d s))
           | Just (Sig n _) <- defSig d
           = ([], [ O.TheoremDecl (Just n) [] ])
        lemmaBucket' _ = ([],[])

        lemmas nm [] = []
        lemmas nm thms@(_:_) = [O.LemmasDecl (O.Lemmas (O.TheoremDecl (Just nm) []) $ thms)]


mlFragment theoryNm stg = unlines
  [ "local_setup {*"
  , "gen_scorres_lemmas \"" ++ theoryNm ++ __cogent_suffix_of_shallow_shared ++ "\" " ++
              "\"" ++ theoryNm ++ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage stg ++ "\" " ++
              "\"" ++ theoryNm ++ __cogent_suffix_of_deep    ++ __cogent_suffix_of_stage stg ++ "\" Cogent_abstract_functions Cogent_functions"
  , "*}"
  ]


-- join the strings (type, tag or field names) in a way that is unlikely to clash with other names
mangleNames :: [String] -> String
mangleNames = intercalate "__"

defineLemmaBucket :: String -> [String] -> [TheoryDecl I.Type I.Term]
defineLemmaBucket _ [] = []
defineLemmaBucket name lems =
  [ O.LemmasDecl (O.Lemmas (O.TheoremDecl (Just name) []) $ map (\l -> O.TheoremDecl (Just l) []) lems) ]

{-
 - Generate rules for Case, Esac, Con, and Promote (for the TSum case).
 -}
data SCorresCaseData = SCCD { bigType :: String
                            , typeStr :: [String]
                            , smallType :: String
                            , tag :: String
                            }
                     | SCED { tag :: String
                            , bigType :: String
                            }
                     | SCCN { tag :: String
                            , bigType :: String }
                     | SCPromote { bigType   :: String
                                 , smallType :: String
                                 , typeStr   :: [String]
                                 }
                     deriving (Show, Eq, Ord)

scorresCaseExpr :: MapTypeName -> TypedExpr t v VarName -> S.Set SCorresCaseData
scorresCaseExpr m = CC.foldEPre unwrap scorresCaseExpr'
  where
    scorresCaseExpr' (TE t e@(Case (TE bt _) tag (_,_,e1) (_,_,e2)))
      | (tstr@(VariantStr vs):_) <- toTypeStr bt
      , Just bt' <- M.lookup tstr m
      , Just st' <- M.lookup (VariantStr (filter (/= tag) vs)) m
      = S.singleton $ SCCD bt' vs st' tag
    scorresCaseExpr' (TE t e@(Esac (TE bt@(TSum [(tag,_)]) _)))
      | (tstr@(VariantStr [v]):_) <- toTypeStr bt
      , Just bt' <- M.lookup tstr m
      = S.singleton $ SCED v bt'
    scorresCaseExpr' (TE bt@TSum{} e@(Promote _ (TE st e')))
      | (btstr@(VariantStr _):_)  <- toTypeStr bt
      , (ststr@(VariantStr vs):_) <- toTypeStr st
      , Just bt' <- M.lookup btstr m
      , Just st' <- M.lookup ststr m
      = S.singleton $ SCPromote bt' st' vs
    scorresCaseExpr' (TE bt e'@(Con tag e _))
      | (tstr@(VariantStr vs):_) <- toTypeStr bt
      , Just bt' <- M.lookup tstr m
      = S.singleton $ SCCN tag bt'
    scorresCaseExpr' (TE t e) = S.empty
    unwrap (TE t e) = e

data CaseLemmaBuckets = CaseLemmaBuckets [String] [String] [String] [String]

#if __GLASGOW_HASKELL__ < 803
instance Monoid CaseLemmaBuckets where
  mempty = CaseLemmaBuckets [] [] [] []
  mappend (CaseLemmaBuckets as bs cs ds) (CaseLemmaBuckets as' bs' cs' ds') =
    CaseLemmaBuckets (as ++ as') (bs ++ bs') (cs ++ cs') (ds ++ ds')
#else
instance Semigroup CaseLemmaBuckets where
  CaseLemmaBuckets as bs cs ds <> CaseLemmaBuckets as' bs' cs' ds' =
    CaseLemmaBuckets (as ++ as') (bs ++ bs') (cs ++ cs') (ds ++ ds')
instance Monoid CaseLemmaBuckets where
  mempty = CaseLemmaBuckets [] [] [] []
#endif

caseLemmaBuckets :: CaseLemmaBuckets -> [TheoryDecl I.Type I.Term]
caseLemmaBuckets (CaseLemmaBuckets cases esacs cons promotes) =
  concat $ P.zipWith defineLemmaBucket
    ["scorres_cases", "scorres_esacs", "scorres_cons", "scorres_promotes" ]
    [cases, esacs, cons, promotes]

toCaseLemma :: SCorresCaseData -> Writer CaseLemmaBuckets (TheoryDecl I.Type I.Term)
toCaseLemma (SCCD {..}) = let
    thmName = "scorres_case_" ++ mangleNames [bigType, tag]
    propStr = "scorres x x' \\<gamma> \\<xi> \\<Longrightarrow> \n"++
              "(\\<And>v v'. valRel \\<xi> v v' \\<Longrightarrow> "++
                "scorres (match (shallow_tac__var v)) match' (v'#\\<gamma>) \\<xi>) \\<Longrightarrow> \n"++
              "(\\<And>v v'. valRel \\<xi> v v' \\<Longrightarrow> "++
                "scorres (rest (shallow_tac__var v)) rest' (v'#\\<gamma>) \\<xi>) \\<Longrightarrow> \n"++
              "scorres (case_" ++ bigType ++ " " ++ unwords (map shallowCase typeStr) ++
                " x) (Case x' " ++ tagString ++ " match' rest') \\<gamma> \\<xi>"
    shallowCase tag' | tag == tag' = "match"
                     | otherwise   = "(\\<lambda>x. rest (" ++ smallType ++ "." ++ tag' ++ " x))"
    tagString = show $ pretty $ mkString tag
    methods = [ Method "clarsimp" ["simp:", "scorres_def", "shallow_tac__var_def", "valRel_" ++ bigType]
              , Method "erule" ["v_sem_caseE"] ] ++
              (concat $ replicate 2 $
                 [ foldr1 (MethodCompound MethodSeq)
                     [Method "erule" ["allE"], Method "erule" ["impE"], Method "assumption" []]
                 , Method "cases" ["x"] ] ++
                 replicate (P.length typeStr)
                   (Method "force" ["simp:", "valRel_" ++ smallType]))
  in do tell (CaseLemmaBuckets [thmName] [] [] [])
        return $ O.LemmaDecl (O.Lemma False (Just (TheoremDecl (Just thmName) [])) [mkId propStr] $ Proof methods ProofDone)
toCaseLemma (SCED {..}) = let
  thmName = "scorres_esac_" ++ bigType
  propStr = "scorres x x' \\<gamma> \\<xi> \\<Longrightarrow> "++
            "scorres (case_" ++ bigType ++ " Fun.id x) (Esac x') \\<gamma> \\<xi>"
  methods = [ Method "cases" ["x"],
              Method "fastforce" ["simp: scorres_def valRel_" ++ bigType ++ " elim!: v_sem_esacE"] ]
 in do tell (CaseLemmaBuckets [] [thmName] [] [])
       return $ O.LemmaDecl (O.Lemma False (Just (TheoremDecl (Just thmName) [])) [mkId propStr] $ Proof methods ProofDone)
toCaseLemma (SCCN {..}) = let
  thmName = "scorres_con_" ++ mangleNames [bigType, tag]
  btTag = mkId $ bigType ++ "." ++ tag
  tagString = mkString tag
  thmProp = [isaTerm| scorres x x' \<gamma> \<xi> |]
      `imp` [isaTerm| scorres ($btTag x) (Con ts $tagString x') \<gamma> \<xi> |]
  methods = [Method "erule" ["scorres_con"], Method "simp" []]
 in do tell (CaseLemmaBuckets [] [] [thmName] [])
       return $ O.LemmaDecl (O.Lemma False (Just (TheoremDecl (Just thmName) [])) [thmProp] $ Proof methods ProofDone)
toCaseLemma (SCPromote {..}) = let
  thmName = "scorres_promote_" ++ mangleNames [smallType, bigType]
  propStr = "scorres x x' \\<gamma> \\<xi> \\<Longrightarrow> " ++
            "scorres (case_" ++ smallType ++ " " ++
              unwords (map ((bigType ++ ".") ++) typeStr) ++ " x) " ++
            "(Promote ts x') \\<gamma> \\<xi>"
  methods = [Method "fastforce" ["simp:", "scorres_def", "valRel_" ++ bigType, "valRel_" ++ smallType,
                                 "split:", smallType ++ ".splits", "elim!:", "v_sem_elims"]]
  in do tell (CaseLemmaBuckets [] [] [] [thmName])
        return $ O.LemmaDecl (O.Lemma False (Just (TheoremDecl (Just thmName) [])) [mkId propStr] $ Proof methods ProofDone)

scorresCaseDef :: MapTypeName -> Definition TypedExpr VarName -> S.Set SCorresCaseData
scorresCaseDef m (FunDef _ fn ps ti to e) = scorresCaseExpr m e
scorresCaseDef m (_) = S.empty


{-
 - Generate rules for Struct, and shallow_tac_rec_field (which is then used to obtain Take, Put and Member rules).
 -}

-- simply generate rules for all types and fields; we expect the program to use most of them
scorresStructLemma :: TypeName -> [FieldName] -> (String, TheoryDecl I.Type I.Term)
scorresStructLemma name fields = let
  thmName = "scorres_struct_" ++ name
  varNames prefix = [ prefix ++ "_" ++ field | field <- fields ]
  assums = [ "scorres " ++ x ++ " " ++ y ++ " \\<gamma> \\<xi>"
           | (x, y) <- P.zip (varNames "s") (varNames "d") ]
  concl = "scorres (" ++ name ++ ".make " ++ unwords (varNames "s") ++ ") " ++
          "(Struct ts [" ++ intercalate ", " (varNames "d") ++ "]) \\<gamma> \\<xi>"
  prop = intercalate " \\<Longrightarrow>\n" (assums ++ [concl])
  method = Method "clarsimp" ["simp:", "scorres_def", "valRel_" ++ name, name ++ ".defs",
                              "elim!:", "v_sem_elims"]
  in (thmName, O.LemmaDecl (O.Lemma False (Just (TheoremDecl (Just thmName) [])) [mkId prop] $ Proof [method] ProofDone))

scorresStructFieldLemma :: TypeName -> [FieldName] -> FieldIndex -> (String, TheoryDecl I.Type I.Term)
scorresStructFieldLemma name fields n = let
  field = fields !! n
  thmName = "shallow_tac_rec_field_" ++ mangleNames [name, field]
  polyRecType = "(" ++ intercalate ", " [ "'t_" ++ fld | fld <- fields] ++ ") " ++ name
  prop = "shallow_tac_rec_field \\<xi> " ++
         "(" ++ name ++ "." ++ field ++ subSymStr "f" ++ " :: " ++ polyRecType ++ " \\<Rightarrow> 't_" ++ field ++ ") " ++
         name ++ "." ++ field ++ subSymStr "f" ++ "_update " ++ show n
  method = Method "fastforce" ["intro!:", "shallow_tac_rec_fieldI", "simp:", "valRel_" ++ name]
  in (thmName, O.LemmaDecl (O.Lemma False (Just (TheoremDecl (Just thmName) [])) [mkId prop] $ Proof [method] ProofDone))

scorresStructLemmas, scorresFieldLemmas :: [TypeStr] -> MapTypeName -> [TheoryDecl I.Type I.Term]
scorresStructLemmas types tmap =
  let (structLemmaNames, structLemmas) = P.unzip $
        [ scorresStructLemma name fields
        | rec@(RecordStr fields) <- types,
          name <- maybeToList $ M.lookup rec tmap ]
  in structLemmas ++
     defineLemmaBucket "scorres_structs" structLemmaNames

scorresFieldLemmas types tmap =
  let (fieldLemmaNames, fieldLemmas) = P.unzip $
        [ scorresStructFieldLemma name fields field
        | rec@(RecordStr fields) <- types,
          name <- maybeToList $ M.lookup rec tmap,
          field <- [0 .. P.length fields - 1] ]
  in fieldLemmas ++
     defineLemmaBucket "scorres_rec_fields" fieldLemmaNames



-- Left is concrete funs, Right is shared
shallowDefinition :: Definition TypedExpr VarName -> SG ([Either (TheoryDecl I.Type I.Term) (TheoryDecl I.Type I.Term)], Maybe FunName)
shallowDefinition (FunDef _ fn ps ti to e) =
    local (typarUpd typar) $ do
    e' <- shallowExpr e
    types <- shallowType $ TFun ti to
    let term = [isaTerm| $fn' $arg0 \<equiv> $e' |]
    pure ([Left $ Definition (Def (Just (Sig (snm fn) (Just types))) term)], Just $ snm fn)
  where fn'   = mkId (snm fn)
        arg0  = mkId $ snm $ D.freshVarPrefix ++ "0"
        typar = map fst $ Vec.cvtToList ps
shallowDefinition (AbsDecl _ fn ps ti to) =
    local (typarUpd typar) $ do
      types <- shallowType $ TFun ti to
      pure ([Right $ ConstsDecl $ Consts (Sig (snm fn) (Just types))], Nothing)
  where typar = map fst $ Vec.cvtToList ps
shallowDefinition (TypeDef tn ps Nothing) =
    local (typarUpd typar) $ pure ([Right $ TypeDeclDecl $ TypeDecl tn typar], Nothing)
  where typar = Vec.cvtToList ps
shallowDefinition (TypeDef tn ps (Just t)) =
    local (typarUpd typar) $ (, Nothing) <$> (map Right <$> shallowTypeDef tn typar t)
  where typar = Vec.cvtToList ps

shallowDefinitions :: [Definition TypedExpr VarName] -> SG ([Either (TheoryDecl I.Type I.Term) (TheoryDecl I.Type I.Term)], [FunName])
shallowDefinitions = (((concat *** catMaybes) . P.unzip) <$>) . mapM ((varNameGen .= 0 >>) . shallowDefinition)

-- | Returns @(shallow, shallow_shared, scorres, type names)@
shallowFile :: String -> Stage -> [Definition TypedExpr VarName]
            -> SG (Theory I.Type I.Term, Theory I.Type I.Term, Theory I.Type I.Term, MapTypeName)
shallowFile thy stg defs = do
  t <- asks typeStrs
  tuples <- asks recoverTuples
  let (typedecls,defs') = partition isAbsTyp defs
  (isatdecls,_) <- shallowDefinitions typedecls  -- should all be Right
  (isatypes, valrels, fullTypeMap) <- shallowTypeFromTable
  (isadefs,fnames) <- shallowDefinitions defs'
  fullTypes <- asks typeStrs
  let structLemmas = scorresStructLemmas fullTypes fullTypeMap ++ scorresFieldLemmas fullTypes fullTypeMap
  let (sccds,buckets) = runWriter (mapM toCaseLemma $ S.toList $ S.unions $ map (scorresCaseDef fullTypeMap) defs')
      shthy = thy ++ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage stg ++ (if tuples then __cogent_suffix_of_recover_tuples else "")
      dpthy = thy ++ __cogent_suffix_of_deep    ++ __cogent_suffix_of_stage stg
      ssthy = thy ++ __cogent_suffix_of_shallow_shared ++ (if tuples then __cogent_suffix_of_recover_tuples else "")
      scthy = thy ++ __cogent_suffix_of_scorres ++ __cogent_suffix_of_stage stg
      shalImports = TheoryImports [ssthy]
      shrdImports = TheoryImports [ __cogent_root_dir </> "cogent/isa/Util"
                                  , __cogent_root_dir </> "cogent/isa/shallow/ShallowUtil" ]
      scorImports = TheoryImports [shthy, dpthy, __cogent_root_dir </> "cogent/isa/shallow/Shallow_Tac"]
      strippedTypeMap = M.filterWithKey (\ts _ -> ts `S.member` S.fromList fullTypes) fullTypeMap
  return $ ( Theory shthy shalImports $ lefts isadefs
           , Theory ssthy shrdImports $ rights isatdecls ++ isatypes ++ rights isadefs
           , Theory scthy scorImports $
               valrels ++
               [ContextDecl (Context "shallow" $
                               sccds ++
                               caseLemmaBuckets buckets ++
                               structLemmas ++
                               [TheoryString (mlFragment thy stg)])]
           , strippedTypeMap
           )

-- | Returns @(shallow, shallow_shared, scorres, type names)@
shallow :: Bool -> String -> Stage -> [Definition TypedExpr VarName] -> String -> (Doc, Doc, Doc, MapTypeName)
shallow recoverTuples thy stg defs log =
  let (shal,shrd,scor,typeMap) = fst $ evalRWS (runSG (shallowFile thy stg defs))
                                               (SGTables (st defs) (stsyn defs) [] recoverTuples)
                                               (StateGen 0 M.empty)
      header = (string ("(*\n" ++ log ++ "\n*)\n") L.<$$>)
  in (header $ pretty shal, header $ pretty shrd, header $ pretty scor, typeMap)

genConstDecl :: CC.CoreConst TypedExpr -> SG (TheoryDecl I.Type I.Term)
genConstDecl (vn, te@(TE ty expr)) = do
  e <- shallowExpr te
  t <- shallowType ty
  let nm = mkId (snm vn)
      term = [isaTerm| $nm \<equiv> $e |]
  pure $ Definition (Def (Just (Sig (snm vn) (Just t))) term)

shallowConsts :: Bool -> String -> Stage -> [CC.CoreConst TypedExpr] -> [Definition TypedExpr VarName] -> String -> Doc
shallowConsts recoverTuples thy stg consts defs log =
  header $ pretty (Theory (thy ++ __cogent_suffix_of_shallow_consts ++ __cogent_suffix_of_stage stg ++
                           (if recoverTuples then __cogent_suffix_of_recover_tuples else ""))
                   (TheoryImports [thy ++ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage stg ++
                                   (if recoverTuples then __cogent_suffix_of_recover_tuples else "")])
                   (genConstTheoryDecls consts defs))
 where genConstTheoryDecls cs defs = fst $ evalRWS (runSG $ shallowConsts cs)
                                     (SGTables (st defs) (stsyn defs) [] recoverTuples)
                                     (StateGen 0 M.empty)
       shallowConsts = mapM genConstDecl
       header = (string ("(*\n" ++ log ++ "\n*)\n") L.<$$>)



{-
  Generate ShallowTuples proof on desugared AST.

  The theory file creates two lemma buckets,
  one for the helper lemmas (ShallowTuplesRules_proofname) and
  one to store the refinement proofs (ShallowTuplesThms_proofname).

  Currently, no ML code is used; the proofs are written directly.
  FIXME: lemmas for abstract functions are currently sorried.
-}

shallowTuplesProof :: String -> String -> String -> String -> String ->
                      MapTypeName -> [Definition TypedExpr VarName] -> String -> Doc
shallowTuplesProof baseName sharedDefThy defThy tupSharedDefThy tupDefThy typeMap defs log =
  header $ pretty (Theory (mkProofName baseName $ Just __cogent_suffix_of_shallow_tuples_proof)
                   (TheoryImports [defThy, tupDefThy,
                                   __cogent_root_dir </> "cogent/isa/shallow/ShallowTuples"])
                   (theorySetup ++
                    dataRelations ++
                    proofs) :: Theory I.Type I.Term)
  where
    thyBase = mkProofName baseName Nothing
    ruleBucket = "ShallowTuplesRules_" ++ thyBase
    proofBucket = "ShallowTuplesThms_" ++ thyBase
    header = (string ("(*\n" ++ log ++ "\n*)\n") L.<$$>)

    -- Set up the lemma buckets.
    theorySetup =
      [ TheoryString $ setupBucket ruleBucket
      , TheoryString $ setupBucket proofBucket
      ]
    setupBucket name = unlines
      [ "ML {*"
      , "structure " ++ name ++ " ="
      , "  Named_Thms ("
      , "    val name = Binding.name \"" ++ name ++ "\""
      , "    val description = \"\""
      , "  )"
      , "*}"
      , "setup {* " ++ name ++ ".setup *}"
      ]

    {- Define shallow_tuples_rel instances and proof rules for all our types.
       We expect that typeMap contains all types, and that the tupled shallow embedding
       uses the same type names (except for tuples, which are omitted). -}
    -- FIXME: use less TheoryString?
    dataRelations = map makeRel $ M.toList typeMap
      where makeRel (RecordStr fields, typeName) =
              if isRecTuple fields
              {- record, tuple -}
              then let
                fullName = sharedDefThy ++ "." ++ typeName
                fullType = polyType fullName "x" (P.length fields)
                tupleFullType = intercalate " \\<times> " ["'xt" ++ show n | n <- [1 .. P.length fields]]
                relName = "shallow_tuples_rel_" ++ typeName
                fieldEquivs = mapInitLast (++ " \\<and>") (++ "\"") $
                              [ "shallow_tuples_rel (" ++ fullName ++ "." ++ isaRecField field ++ " x) " ++
                                "(P" ++ show (P.length fields) ++ "_" ++ isaRecField ("p" ++ show (f :: Int)) ++ " xt)"
                              | (f, field) <- P.zip [1..] fields ]

                constrAssms = mapInitLast (++ ";") id $
                              [ "shallow_tuples_rel x" ++ show f ++ " xt" ++ show f
                              | f <- [1 .. P.length fields] ]
                in TheoryString $ unlines $
                   -- definition
                   [ "overloading " ++ relName ++ " \\<equiv> shallow_tuples_rel begin"
                   , "  definition \"" ++ relName ++ " (x :: " ++ fullType ++ ") (xt :: " ++ tupleFullType ++ ") \\<equiv>"
                   ] ++
                   indent 4 fieldEquivs ++
                   [ "end" ] ++

                   -- constructor
                   [ "lemma " ++ mangleNames ["shallow_tuples_rule", typeName ++ "_make"] ++ " [" ++ ruleBucket ++ "]:"
                   , "  \"\\<lbrakk>"
                   ] ++
                   indent 5 constrAssms ++
                   [ "  \\<rbrakk> \\<Longrightarrow> shallow_tuples_rel " ++
                     "(" ++ fullName ++ ".make " ++ unwords ["x" ++ show f | f <- [1 .. P.length fields]] ++ ") " ++
                     "(" ++ intercalate ", " ["xt" ++ show f | f <- [1 .. P.length fields]] ++ ")\""
                   , "  by (simp add: shallow_tuples_rel_" ++ typeName ++ "_def " ++
                     fullName ++ ".defs Px_px)"
                   ] ++

                   -- fields
                   concat [
                     [ "lemma " ++ mangleNames ["shallow_tuples_rule", typeName, field] ++ " [" ++ ruleBucket ++ "]:"
                     , "  \"shallow_tuples_rel (x :: " ++ fullType ++ ") (xt :: " ++ tupleFullType ++ ") \\<Longrightarrow>"
                     , "   shallow_tuples_rel (" ++ fullName ++ "." ++ field ++ " x) " ++
                       "(P" ++ show (P.length fields) ++ "_" ++ isaRecField ("p" ++ show f) ++ " xt)\""
                     , "  by (simp add: shallow_tuples_rel_" ++ typeName ++ "_def)"
                     ] | (f, field) <- P.zip [(1::Int) ..] (map isaRecField fields)
                   ]

                   -- no field updates for tuples (as they are always unboxed, hence immutable)

              {- record, record -}
              else let
                fullName = sharedDefThy ++ "." ++ typeName
                fullType = polyType fullName "x" (P.length fields)
                tupleFullName = tupSharedDefThy ++ "." ++ typeName
                tupleFullType = polyType tupleFullName "xt" (P.length fields)
                relName = "shallow_tuples_rel_" ++ typeName
                fieldEquivs = mapInitLast (++ " \\<and>") (++ "\"") $
                              [ "shallow_tuples_rel (" ++ fullName ++ "." ++ isaRecField field ++ " x) " ++
                                "(" ++ tupleFullName ++ "." ++ isaRecField field ++ " xt)"
                              | field <- fields ]

                constrAssms = mapInitLast (++ ";") id $
                              [ "shallow_tuples_rel x" ++ show f ++ " xt" ++ show f
                              | f <- [1 .. P.length fields] ]
                in TheoryString $ unlines $
                   -- definition
                   [ "overloading " ++ relName ++ " \\<equiv> shallow_tuples_rel begin"
                   , "  definition \"" ++ relName ++ " (x :: " ++ fullType ++ ") (xt :: " ++ tupleFullType ++ ") \\<equiv>"
                   ] ++
                   indent 4 fieldEquivs ++
                   [ "end" ] ++

                   -- constructor
                   [ "lemma " ++ mangleNames ["shallow_tuples_rule_make", typeName] ++ " [" ++ ruleBucket ++ "]:"
                   , "  \"\\<lbrakk>"
                   ] ++
                   indent 5 constrAssms ++
                   [ "  \\<rbrakk> \\<Longrightarrow> shallow_tuples_rel " ++
                     "(" ++ fullName ++ ".make " ++ unwords ["x" ++ show f | f <- [1 .. P.length fields]] ++ ") " ++
                     "(" ++ tupleFullName ++ ".make " ++ unwords ["xt" ++ show f | f <- [1 .. P.length fields]] ++ ")\""
                   , "  by (simp add: shallow_tuples_rel_" ++ typeName ++ "_def " ++
                     fullName ++ ".defs " ++ tupleFullName ++ ".defs)"
                   ] ++

                   -- fields
                   concat [
                     [ "lemma " ++ mangleNames ["shallow_tuples_rule", typeName, field] ++ " [" ++ ruleBucket ++ "]:"
                     , "  \"shallow_tuples_rel (x :: " ++ fullType ++ ") (xt :: " ++ tupleFullType ++ ") \\<Longrightarrow>"
                     , "   shallow_tuples_rel (" ++ fullName ++ "." ++ field ++ " x) (" ++ tupleFullName ++ "." ++ field ++ " xt)\""
                     , "  by (simp add: shallow_tuples_rel_" ++ typeName ++ "_def)"
                     ] | field <- map isaRecField fields
                   ] ++

                   -- field updates
                   concat [
                     [ "lemma " ++ mangleNames ["shallow_tuples_rule", typeName, field, "update"] ++ " [" ++ ruleBucket ++ "]:"
                     , "  \"\\<lbrakk> shallow_tuples_rel (x :: " ++ fullType ++ ") (xt :: " ++ tupleFullType ++ ");"
                     , "     shallow_tuples_rel v vt"
                     , "   \\<rbrakk> \\<Longrightarrow>"
                     , "   shallow_tuples_rel (" ++ fullName ++ "." ++ field ++ "_update (\\<lambda>_. v) x) " ++
                       "(" ++ tupleFullName ++ "." ++ field ++ "_update (\\<lambda>_. vt) xt)\""
                     , "  by (simp add: shallow_tuples_rel_" ++ typeName ++ "_def)"
                     ] | field <- map isaRecField fields
                   ]

            {- variant -}
            makeRel (VariantStr tags, typeName) = let
              fullName = sharedDefThy ++ "." ++ typeName
              fullType = polyType fullName "x" (P.length tags)
              tupleFullName = tupSharedDefThy ++ "." ++ typeName
              tupleFullType = polyType tupleFullName "xt" (P.length tags)
              relName = "shallow_tuples_rel_" ++ typeName
              tagEquivs = mapInitLast (++ " \\<or>") (++ "\"") $
                          [ "(\\<exists>v vt. shallow_tuples_rel v vt \\<and> " ++
                            "x = " ++ fullName ++ "." ++ tag ++ " v \\<and> " ++
                            "xt = " ++ tupleFullName ++ "." ++ tag ++ " vt)"
                          | tag <- tags ]

              handlers baseVar = [baseVar ++ show n | n <- [1 .. P.length tags]]
              caseTerm = sharedDefThy ++ ".case_" ++ typeName
              tupleCaseTerm = tupSharedDefThy ++ ".case_" ++ typeName
              caseAssms = mapInitLast (++ ";") id $
                          [ "\\<And>v vt. shallow_tuples_rel v vt \\<Longrightarrow> " ++
                            "shallow_tuples_rel (" ++ f ++ " v) (" ++ ft ++ " vt)"
                          | (f, ft) <- P.zip (handlers "f") (handlers "ft") ]
              in TheoryString $ unlines $
                 -- definition
                 [ "overloading " ++ relName ++ " \\<equiv> shallow_tuples_rel begin"
                 , "  definition \"" ++ relName ++ " (x :: " ++ fullType ++ ") (xt :: " ++ tupleFullType ++ ") \\<equiv>"
                 ] ++
                 indent 4 tagEquivs ++
                 [ "end" ] ++

                 -- case
                 [ "lemma " ++ mangleNames ["shallow_tuples_rule_case", typeName] ++ " [" ++ ruleBucket ++ "]:"
                 , "  \"\\<lbrakk> shallow_tuples_rel x xt;"
                 ] ++
                 indent 5 caseAssms ++
                 [ "   \\<rbrakk> \\<Longrightarrow>"
                 , "   shallow_tuples_rel (" ++ unwords ([caseTerm] ++ handlers "f" ++ ["x"]) ++ ") " ++
                   "(" ++ unwords ([tupleCaseTerm] ++ handlers "ft" ++ ["xt"]) ++ ")\""
                 , "  by (fastforce simp: shallow_tuples_rel_" ++ typeName ++ "_def"
                 , "        split: " ++ fullName ++ ".splits " ++ tupleFullName ++ ".splits)"
                 ] ++

                 -- constructors
                 concat [
                   [ "lemma " ++ mangleNames ["shallow_tuples_rule", typeName, tag] ++ " [" ++ ruleBucket ++ "]:"
                   , "  \"shallow_tuples_rel x xt \\<Longrightarrow>"
                   , "   shallow_tuples_rel (" ++ fullName ++ "." ++ tag ++ " x) (" ++ tupleFullName ++ "." ++ tag ++ " xt)\""
                   , "  by (simp add: shallow_tuples_rel_" ++ typeName ++ "_def)"
                   ] | tag <- tags
                 ]

            isaRecField = (++ subSymStr "f") -- sync with getRecordFieldName

            polyType name baseVar numArgs =
              "(" ++ intercalate ", " ["'" ++ baseVar ++ show n | n <- [1 .. numArgs]] ++ ") " ++ name

    indent k = map (replicate k ' ' ++)

    proofs = concatMap makeProof defs
      where makeProof (FunDef _ funName _ _ _ _) = let
              fullName = defThy ++ "." ++ funName
              funDef = fullName ++ "_def"
              tupleFullName = tupDefThy ++ "." ++ funName
              tupleFunDef = tupleFullName ++ "_def"
              in return $ TheoryString $ unlines $
                 [ "lemma " ++ mangleNames ["shallow_tuples", funName] ++ " [" ++ proofBucket ++ "]:"
                 , "  \"shallow_tuples_rel " ++ fullName ++ " " ++ tupleFullName ++ "\""
                 , "  apply (rule shallow_tuples_rel_funI)"
                 , "  apply (unfold " ++ unwords [funDef, tupleFunDef, "id_def" {- in Esacs -}] ++ ")"
                   -- main iteration
                 , "  by (assumption |"
                 , "      rule shallow_tuples_basic_bucket " ++ ruleBucket
                 , "           " ++ proofBucket ++ " " ++ proofBucket ++ "[THEN shallow_tuples_rel_funD])+"
                 ]

            makeProof (AbsDecl _ funName _ _ _) = let
              fullName = sharedDefThy ++ "." ++ funName
              tupleFullName = tupSharedDefThy ++ "." ++ funName
              in return $ TheoryString $ unlines $
                 [ "lemma " ++ mangleNames ["shallow_tuples", funName] ++ " [" ++ proofBucket ++ "]:"
                 , "  \"shallow_tuples_rel " ++ fullName ++ " " ++ tupleFullName ++ "\""
                 , "  sorry"
                 ]

            makeProof _ = []

mapInitLast :: (a -> a) -> (a -> a) -> [a] -> [a]
mapInitLast init last [] = []
mapInitLast init last [x] = [last x]
mapInitLast init last (x:xs) = init x : mapInitLast init last xs

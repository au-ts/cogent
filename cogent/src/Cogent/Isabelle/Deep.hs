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

{-# OPTIONS_GHC -Wwarn #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Cogent.Isabelle.Deep where

import Cogent.Common.Syntax as CS
import Cogent.Common.Types
import Cogent.Dargent.Core (DataLayout)
import Cogent.Dargent.Surface (Endianness(..))
import Cogent.Dargent.Allocation (BitRange(..))
import Cogent.Compiler
import Cogent.Core as CC
import Cogent.Isabelle.IsabelleName
import Cogent.Isabelle.Shallow (snm)
import Cogent.Util (NameMod, Stage(..))
import Data.Fin (Fin, finInt)
import Data.Vec (cvtToList)
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import qualified Data.Vec as Vec
import Data.Nat as Nat
import Isabelle.ExprTH
import Isabelle.InnerAST as I
import Isabelle.OuterAST as O

import qualified Data.Map.Strict as Map
import Data.List (intercalate, sort)
#if __GLASGOW_HASKELL__ >= 709
import Prelude hiding ((<$>))
#endif
import System.FilePath ((</>))
import Text.PrettyPrint.ANSI.Leijen hiding ((</>))

-- import Debug.Trace

deepIndex :: Fin v -> Term
deepIndex = mkInt . fromIntegral . finInt

deepSigil :: Sigil (DataLayout BitRange) -> Term
deepSigil (Boxed True  l) = mkApp (mkId "Boxed") [(mkId "ReadOnly"), deepDataLayout l]
deepSigil (Boxed False l) = mkApp (mkId "Boxed") [(mkId "Writable"), deepDataLayout l]
deepSigil Unboxed         = mkId "Unboxed"

deepDataLayout :: DataLayout BitRange -> Term
deepDataLayout CLayout = mkId "None"
deepDataLayout (Layout l) = mkApp (mkId "Some") [deepDataLayout' l]

deepDataLayout' :: DataLayout' BitRange -> Term
deepDataLayout' UnitLayout = deepDLBitRange (BitRange 0 0) ME
deepDataLayout' (PrimLayout b e) = deepDLBitRange b e
deepDataLayout' (RecordLayout fs) = 
  mkApp (mkId "LayRecord") [
    mkList $
    map (\ (name, d) -> mkTuple [mkString name, deepDataLayout' d]) 
    $ Map.toList fs ]
deepDataLayout' (SumLayout tag alts) = 
  mkApp (mkId "LayVariant") [ deepBitRange tag ,
     mkList $ map (\ (name, (t, l)) -> 
            mkTuple [mkString name, mkInt1S0 t, deepDataLayout' l]
         ) $ Map.toList alts
     ] 
deepDataLayout' (VarLayout v offset) = mkApp (mkId "LayVar") [mkInt1S0 (toInteger (Nat.natToInt v)), mkInt offset]
#ifdef BUILTIN_ARRAYS
deepDataLayout' (ArrayLayout _) = mkId "undefined"
#endif

deepEndianness :: Endianness -> Term
deepEndianness ME = mkId "ME"
deepEndianness BE = mkId "BE"
deepEndianness LE = mkId "LE"

deepDLBitRange :: BitRange -> Endianness -> Term
deepDLBitRange b e = mkApp (mkId "LayBitRange")  [ deepBitRange b, deepEndianness e ]

deepBitRange :: BitRange -> Term
deepBitRange (BitRange size offset) = mkTuple [mkInt1S0 size, mkInt1S0 offset]

type TypeAbbrevs = (Map.Map Term Int, Int)

deepVariantState :: Bool -> Term
deepVariantState False = mkId "Unchecked"
deepVariantState True  = mkId "Checked"

deepRecordState :: Bool -> Term
deepRecordState False = mkId "Present"
deepRecordState True  = mkId "Taken"

deepTypeInner :: (Ord b, Pretty b) => NameMod -> TypeAbbrevs -> CC.Type t b -> Term
deepTypeInner mod ta (TVar v) = mkApp (mkId "TVar") [deepIndex v]
deepTypeInner mod ta (TVarBang v) = mkApp (mkId "TVarBang") [deepIndex v]
deepTypeInner mod ta (TCon tn ts s) = mkApp (mkId "TCon") [mkString tn, mkList (map (deepType mod ta) ts), deepSigil $ fmap (const CLayout) s]
deepTypeInner mod ta (TFun ti to) = mkApp (mkId "TFun") [deepType mod ta ti, deepType mod ta to]
deepTypeInner mod ta (TPrim pt)
  | UInt s <- pt, s `notElem` wordSizes = deepCustomUInt pt
  | otherwise = mkApp (mkId "TPrim") [deepPrimType pt]
deepTypeInner mod ta (TString) = mkApp (mkId "TPrim") [mkId "String"]
deepTypeInner mod ta (TSum alts)
  = mkApp (mkId "TSum")
          [mkList $ map (\(n,(t,b)) -> mkPair (mkString n) (mkPair (deepType mod ta t) (deepVariantState b))) $ sort alts]
deepTypeInner mod ta (TProduct t1 t2) = mkApp (mkId "TProduct") [deepType mod ta t1, deepType mod ta t2]
-- TODO: Do recursive types have a place in the deep embedding?
deepTypeInner mod ta (TRecord _ fs s) = mkApp (mkId "TRecord") [mkList $ map (\(fn,(t,b)) -> mkPair (mkString fn) (mkPair (deepType mod ta t) (deepRecordState b))) fs, deepSigil s]
deepTypeInner mod ta (TUnit) = mkId "TUnit"
deepTypeInner mod ta (TSyn n _ _ _) = mkId n -- FIXME: we should unfold the type synonym
deepTypeInner _ _ t = __impossible $ "deepTypeInner: " ++ show (pretty t) ++ " is not yet implemented"

mkAbbrevNm :: NameMod -> Int -> String
mkAbbrevNm mod n = mod $ "abbreviatedType" ++ show n

mkAbbrevId :: NameMod -> Int -> Term
mkAbbrevId = (mkId .) . mkAbbrevNm

deepType :: (Ord b, Pretty b) => NameMod -> TypeAbbrevs -> CC.Type t b -> Term
deepType mod ta t = case Map.lookup term (fst ta) of
    Just n -> mkAbbrevId mod n
    Nothing -> term
  where
    term = deepTypeInner mod ta t

deepPrimType :: PrimInt -> Term
deepPrimType (UInt 8 ) = mkApp (mkId "Num") [mkId "U8" ]
deepPrimType (UInt 16) = mkApp (mkId "Num") [mkId "U16"]
deepPrimType (UInt 32) = mkApp (mkId "Num") [mkId "U32"]
deepPrimType (UInt 64) = mkApp (mkId "Num") [mkId "U64"]
deepPrimType Boolean = mkId "Bool"
deepPrimType _ = __impossible "deepPrimType: other-sized UInt"

deepCustomUInt :: PrimInt -> Term
deepCustomUInt (UInt x) | x `notElem` wordSizes = mkApp (mkId "TCustomNum") [mkInt x]
                        | otherwise = __impossible "deepCustomUInt: word-sized PrimInt"

deepNumType :: PrimInt -> Term
deepNumType (UInt 8 ) = mkId "U8"
deepNumType (UInt 16) = mkId "U16"
deepNumType (UInt 32) = mkId "U32"
deepNumType (UInt 64) = mkId "U64"
deepNumType Boolean   = __impossible "deepNumType: Boolean"
deepNumType (UInt _ ) = __impossible "deepNumType: other-sized UInt"

deepILit :: Integer -> PrimInt -> Term
deepILit n (UInt 8 ) = mkApp (mkId "LU8" ) [mkInt n]
deepILit n (UInt 16) = mkApp (mkId "LU16") [mkInt n]
deepILit n (UInt 32) = mkApp (mkId "LU32") [mkInt n]
deepILit n (UInt 64) = mkApp (mkId "LU64") [mkInt n]
deepILit n Boolean = mkApp (mkId "LBool") [if n == 0 then mkFls else mkTru]
deepILit _ (UInt _) = __impossible "deepILit: other-sized UInt"


deepPrimOp :: Op -> PrimInt -> Term
deepPrimOp CS.Plus   t = mkApp (mkId "Plus")   [deepNumType t]
deepPrimOp CS.Minus  t = mkApp (mkId "Minus")  [deepNumType t]
deepPrimOp CS.Times  t = mkApp (mkId "Times")  [deepNumType t]
deepPrimOp CS.Divide t = mkApp (mkId "Divide") [deepNumType t]
deepPrimOp CS.Mod    t = mkApp (mkId "Mod")    [deepNumType t]
deepPrimOp CS.Not    t = mkId "Not"
deepPrimOp CS.And    t = mkId "Cogent.And"
deepPrimOp CS.Or     t = mkId "Cogent.Or"
deepPrimOp CS.Gt     t = mkApp (mkId "Gt")     [deepNumType t]
deepPrimOp CS.Lt     t = mkApp (mkId "Lt")     [deepNumType t]
deepPrimOp CS.Le     t = mkApp (mkId "Le")     [deepNumType t]
deepPrimOp CS.Ge     t = mkApp (mkId "Ge")     [deepNumType t]
deepPrimOp CS.Eq     t = mkApp (mkId "Eq")     [deepPrimType t]
deepPrimOp CS.NEq    t = mkApp (mkId "NEq")    [deepPrimType t]
deepPrimOp CS.BitAnd t = mkApp (mkId "BitAnd") [deepNumType t]
deepPrimOp CS.BitOr  t = mkApp (mkId "BitOr")  [deepNumType t]
deepPrimOp CS.BitXor t = mkApp (mkId "BitXor") [deepNumType t]
deepPrimOp CS.LShift t = mkApp (mkId "LShift") [deepNumType t]
deepPrimOp CS.RShift t = mkApp (mkId "RShift") [deepNumType t]
deepPrimOp CS.Complement t = mkApp (mkId "Complement") [deepNumType t]

deepExpr :: (Pretty a, Ord b, Pretty b) => NameMod -> TypeAbbrevs -> [Definition TypedExpr a b] -> TypedExpr t v a b -> Term
deepExpr mod ta defs (TE _ (Variable v)) = mkApp (mkId "Var") [deepIndex (fst v)]
deepExpr mod ta defs (TE _ (Fun fn ts ls _))  -- FIXME
  | concreteFun fn = mkApp (mkId "Fun")  [mkId (mod (unIsabelleName $ mkIsabelleName $ unCoreFunName fn)), mkList (map (deepType mod ta) ts), mkList (map deepDL ls)]
  | otherwise      = mkApp (mkId "AFun") [mkString (unIsabelleName $ mkIsabelleName $ unCoreFunName fn), mkList (map (deepType mod ta) ts), mkList (map deepDL ls)]
  where
    concreteFun :: CoreFunName -> Bool
    concreteFun f = any (\def -> isFuncId f def && case def of FunDef{} -> True; _ -> False) defs
    deepDL :: DataLayout BitRange -> Term
    deepDL CLayout = error "error - cannot deeply embed C layout application"
    deepDL (Layout l) = deepDataLayout' l
deepExpr mod ta defs (TE _ (Op opr es))
  = mkApp (mkId "Prim") [deepPrimOp opr (let TPrim pt = exprType $ head es in pt),
                         mkList (map (deepExpr mod ta defs) es)]
deepExpr mod ta defs (TE _ (App f arg))
  = mkApp (mkId "App") [deepExpr mod ta defs f, deepExpr mod ta defs arg]
deepExpr mod ta defs (TE (TSum alts) (Con cn e _))
  = mkApp (mkId "Con") [mkList t', mkString cn, deepExpr mod ta defs e]
  where t' = map (\(c,(t,b)) -> mkPair (mkString c) (mkPair (deepType mod ta t) (deepVariantState b))) alts
deepExpr _ _ _ (TE _ (Con _ _ _)) = __impossible "deepExpr: Con"
deepExpr mod ta defs (TE _ (Promote ty e))
  = mkApp (mkId "Promote") [deepType mod ta ty, deepExpr mod ta defs e]
  -- = deepExpr mod ta defs e
--   | TE (TPrim pt) _ <- e, TPrim pt' <- ty, pt /= Boolean
--   = mkApp (mkId "Cast") [deepNumType pt', deepExpr mod ta defs e]  -- primInt cast
--   | TE (TSum _) (Con cn v _) <- e, TSum as <- ty
--   = mkApp (mkId "Con") [mkList $ map (\(an,(at,_)) -> mkPair (mkString an) (deepType mod ta at)) as, mkString cn, deepExpr mod ta defs v]  -- inlined Con
--   | TSum as <- ty = mkApp (mkId "Promote") [mkList $ map (\(an,(at,_)) -> mkPair (mkString an) (deepType mod ta at)) as, deepExpr mod ta defs e]  -- FIMXE: cogent.1
--   | otherwise = __impossible "deepExpr"
deepExpr mod ta defs (TE _ (Struct fs))
  = mkApp (mkId "Struct") [mkList (map (deepType mod ta . exprType . snd) fs),
                           mkList (map (deepExpr mod ta defs . snd) fs)]
deepExpr mod ta defs (TE _ (Member e fld))
  = mkApp (mkId "Member") [deepExpr mod ta defs e, mkInt (fromIntegral fld)]
deepExpr mod ta defs (TE _ (Unit)) = mkId "Unit"
deepExpr mod ta defs (TE _ (ILit n pt))
  | UInt s <- pt, s `notElem` wordSizes = mkApp (mkId "CustomInt") [mkInt s, mkInt n]
  | otherwise = mkApp (mkId "Lit") [deepILit n pt]
deepExpr mod ta defs (TE _ (SLit s)) = __fixme $ mkApp (mkId "SLit") [mkString s]  -- FIXME: there's no @SLit@ in the Isabelle definition at the moment / zilinc
deepExpr mod ta defs (TE _ (Tuple e1 e2))
  = mkApp (mkId "Tuple") [deepExpr mod ta defs e1, deepExpr mod ta defs e2]
deepExpr mod ta defs (TE _ (Put rec fld e))
  = mkApp (mkId "Put") [deepExpr mod ta defs rec, mkInt (fromIntegral fld), deepExpr mod ta defs e]
deepExpr mod ta defs (TE _ (Let _ e1 e2))
  = mkApp (mkId "Let") [deepExpr mod ta defs e1, deepExpr mod ta defs e2]
deepExpr mod ta defs (TE _ (LetBang vs _ e1 e2))
  = let vs' = mkApp (mkId "set") [mkList $ map (deepIndex . fst) vs]
     in mkApp (mkId "LetBang") [vs', deepExpr mod ta defs e1, deepExpr mod ta defs e2]
deepExpr mod ta defs (TE _ (Case e tag (l1,_,e1) (l2,_,e2)))
  = mkApp (mkId "Case") [deepExpr mod ta defs e,
                         mkString tag,
                         deepExpr mod ta defs e1,
                         deepExpr mod ta defs e2]
deepExpr mod ta defs (TE _ (Esac e@(TE (TSum alts) _)))
  | tag <- fst (head (filter (not . snd . snd) alts))
  = mkApp (mkId "Esac") [deepExpr mod ta defs e, mkString tag]
deepExpr mod ta defs (TE _ (If c th el)) = mkApp (mkId "If") $ map (deepExpr mod ta defs) [c, th, el]
deepExpr mod ta defs (TE _ (Take _ rec fld e))
  = mkApp (mkId "Take") [deepExpr mod ta defs rec, mkInt (fromIntegral fld), deepExpr mod ta defs e]
deepExpr mod ta defs (TE _ (Split _ e1 e2))
  = mkApp (mkId "Split") [deepExpr mod ta defs e1, deepExpr mod ta defs e2]
deepExpr mod ta defs (TE _ (Cast t e))
  | TE (TPrim (UInt small)) _ <- e, TPrim pt' <- t
  = if small `elem` wordSizes
       then mkApp (mkId "Cast") [deepNumType pt', deepExpr mod ta defs e]
       else mkApp (mkId "CustomUCast") [deepNumType pt', deepExpr mod ta defs e]
deepExpr mod ta defs (TE _ (Truncate t e))
  | TE (TPrim (UInt big)) _ <- e, TPrim (UInt small) <- t
  = mkApp (mkId "CustomDCast") [mkInt small, deepExpr mod ta defs e]
deepExpr mod ta defs (TE _ e) = __todo $ "deepExpr: " ++ show (pretty e)

deepKind :: Kind -> Term
deepKind (K e s d) = mkSet [ mkId str | (sig, str) <- [(e, "E"), (s, "S"), (d, "D")], sig ]

deepConstraint :: (Ord b, Pretty b) => NameMod -> TypeAbbrevs -> (DataLayout' BitRange, CC.Type t b) -> Term
deepConstraint mod ta (d, t) = mkTuple [deepDataLayout' d, mkApp (mkId "type_lrepr") [ deepType mod ta t ]]

deepConstraints ::  (Ord b, Pretty b) => NameMod -> TypeAbbrevs -> [(DataLayout' BitRange, CC.Type t b)] -> Term
deepConstraints mod ta lts = mkSet $ map (deepConstraint mod ta) lts

deepPolyType :: (Ord b, Pretty b) => NameMod -> TypeAbbrevs -> FunctionType b -> Term
deepPolyType mod ta (FT ks nl lts ti to) = mkTuple [mkInt $ toInteger $ Nat.toInt nl,
                                                mkList $ map deepKind $ cvtToList ks,  -- FIXME
                                                deepConstraints mod ta lts,  
                                                deepType mod ta ti,
                                                deepType mod ta to]

imports :: TheoryImports
imports = TheoryImports $ ["Cogent.Cogent"]

deepDefinition :: (Pretty a, Ord b, Pretty b)
               => NameMod
               -> TypeAbbrevs
               -> [Definition TypedExpr a b]
               -> Map FunName (FunctionType b)
               -> Definition TypedExpr a b
               -> [TheoryDecl I.Type I.Term]
               -> [TheoryDecl I.Type I.Term]
deepDefinition mod ta defs fts (FunDef _ fn ks ts ti to e) decls =
  let ty = deepPolyType mod ta $
           -- is it a (possibly generated) monomorphised function?
           case (ks, ts) of
             (Vec.Nil, Vec.Nil) -> FT Vec.Nil SZero [] ti to
             _ ->
                 fromMaybe                
                   (error("Error - unable to retrieve the inferred constraints for isabelle function '" ++ fn ++ "'" ))              
                 $ Map.lookup fn fts 
      tn = case editIsabelleName (mkIsabelleName fn) (++ "_type")  of
            Just n  -> unIsabelleName n
            Nothing -> error ("Error - unable to generate name for isabelle function '" ++ fn ++ "'")
      tysig = [isaType| poly_type |]       
      tydecl = [isaDecl| definition $tn :: "$tysig" where "$(mkId tn) \<equiv> $ty" |]
      e' = deepExpr mod ta defs e
      fntysig = AntiType "string Cogent.expr"
      fn' = unIsabelleName (mkIsabelleName fn)
      decl = [isaDecl| definition $fn' :: "$fntysig" where "$(mkId fn') \<equiv> $e'" |]
     in tydecl:decl:decls
deepDefinition mod ta _ fts (AbsDecl _ fn ks ts ti to) decls =
    let ty = deepPolyType mod ta $
              -- is it a (possibly generated) monomorphised function?
             case (ks, ts) of
               (Vec.Nil, Vec.Nil) -> FT Vec.Nil SZero [] ti to
               _ ->
                   fromMaybe                
                     (error("Error - unable to retrieve the inferred constraints for isabelle function '" ++ fn ++ "'" ))              
                   $ Map.lookup fn fts 
        tn = case editIsabelleName (mkIsabelleName fn) (++ "_type") of 
            Just n  -> unIsabelleName n
            Nothing -> error ("Error - unable to generate name for isabelle function '" ++ fn ++ "'")
        tysig = [isaType| poly_type |]
        tydecl = [isaDecl| definition $tn :: "$tysig" where "$(mkId tn) \<equiv> $ty" |]
     in tydecl:decls
deepDefinition _ _ _ _ _ decls = decls

deepDefinitions :: (Pretty a, Ord b, Pretty b) => NameMod -> TypeAbbrevs -> [Definition TypedExpr a b] -> Map FunName (FunctionType b) -> [TheoryDecl I.Type I.Term]
deepDefinitions mod ta defs fts = foldr (deepDefinition mod ta defs fts) [] defs ++
                              [TheoryString $
                               "ML \\<open>\n" ++
                               "val Cogent_functions = [" ++ showStrings (map (unIsabelleName . mkIsabelleName) $ cogentFuns defs) ++ "]\n" ++
                               "val Cogent_abstract_functions = [" ++ showStrings (map mod $ absFuns defs) ++ "]\n" ++
                               "\\<close>"
                              ]
  where absFuns [] = []
        absFuns (AbsDecl _ fn _ _ _ _ : fns) = fn : absFuns fns
        absFuns (_ : fns) = absFuns fns
        cogentFuns [] = []
        cogentFuns (FunDef _ fn _ _ _ _ _ : fns) = fn : cogentFuns fns
        cogentFuns (_ : fns) = cogentFuns fns

        showStrings :: [String] -> String
        showStrings [] = ""
        showStrings [x] = "\"" ++ x ++ "\""
        showStrings (x:xs) = "\"" ++ x ++ "\", " ++ showStrings xs

scanAggregates :: CC.Type t b -> [CC.Type t b]
scanAggregates (TCon tn ts _) = concatMap scanAggregates ts
scanAggregates (TFun ti to) = scanAggregates ti ++ scanAggregates to
scanAggregates (TSum alts) = concatMap (scanAggregates . fst . snd) alts ++ [TSum alts]
scanAggregates (TProduct t1 t2) = scanAggregates t1 ++ scanAggregates t2
scanAggregates (TRecord rp fs s) = concatMap (scanAggregates . fst . snd) fs ++ [TRecord rp fs s]
scanAggregates _ = []

addTypeAbbrev :: (Ord b, Pretty b) => NameMod -> CC.Type t b -> TypeAbbrevs -> TypeAbbrevs
addTypeAbbrev mod t ta = case Map.lookup term (fst ta) of
    Just s -> ta
    Nothing -> (Map.insert term (snd ta) (fst ta), snd ta + 1)
  where
    term = deepTypeInner mod ta t

getDefTypeAbbrevs :: (Ord b) => NameMod -> Definition TypedExpr a b -> TypeAbbrevs -> TypeAbbrevs
getDefTypeAbbrevs mod (FunDef _ _ _ _ ti to e) ta = foldr (addTypeAbbrev mod) ta
    (scanAggregates ti ++ scanAggregates to)
getDefTypeAbbrevs _ _ ta = ta

getTypeAbbrevs :: (Ord b) => NameMod -> [Definition TypedExpr a b] -> TypeAbbrevs
getTypeAbbrevs mod defs = foldr (getDefTypeAbbrevs mod) (Map.empty, 1) defs

deepTypeAbbrev :: NameMod -> (Int, Term) -> TheoryDecl I.Type I.Term
deepTypeAbbrev mod (n, tm) = let
    nm = mkAbbrevNm mod n
    tysig = [isaType| Cogent.type |]
  in [isaDecl| definition $nm :: "$tysig" where "$(mkId nm) \<equiv> $tm" |]

typeAbbrevBucketName = "abbreviated_type_defs"

typeAbbrevDefsLemma :: NameMod -> TypeAbbrevs -> TheoryDecl I.Type I.Term
typeAbbrevDefsLemma mod ta = let
    defTD = \n -> O.TheoremDecl { thmName = Just n, thmAttributes = [] }
    nms = [ (mkAbbrevNm mod n) ++ "_def" | (_, n) <- Map.toList (fst ta)]
  in O.LemmasDecl (O.Lemmas { lemmasName = defTD typeAbbrevBucketName,
                              lemmasThms = map defTD (if null nms then ["TrueI"] else nms) })


deepTypeAbbrevs :: NameMod -> TypeAbbrevs -> [TheoryDecl I.Type I.Term]
deepTypeAbbrevs mod ta = map (deepTypeAbbrev mod) defs ++ [typeAbbrevDefsLemma mod ta]
  where
    defs = sort $ map (\(x, y) -> (y, x)) $ Map.toList (fst ta)

deepDefinitionsAbb :: (Pretty a, Ord b, Pretty b) => NameMod -> [Definition TypedExpr a b] -> Map FunName (FunctionType b) -> (TypeAbbrevs, [TheoryDecl I.Type I.Term])
deepDefinitionsAbb mod defs fts = (ta, deepTypeAbbrevs mod ta ++ deepDefinitions mod ta defs fts)
  where ta = getTypeAbbrevs mod defs

deepFile :: (Pretty a, Ord b, Pretty b) => NameMod -> String -> [Definition TypedExpr a b] -> Map FunName (FunctionType b) -> Theory I.Type I.Term
deepFile mod thy defs fts = Theory thy imports (snd (deepDefinitionsAbb mod defs fts))

deep :: (Pretty a, Ord b, Pretty b) => String -> Stage -> [Definition TypedExpr a b] -> Map FunName (FunctionType b) -> String -> Doc
deep thy stg defs fts log = string ("(*\n" ++ log ++ "\n*)\n") <$>
                        pretty (deepFile snm thy defs fts)

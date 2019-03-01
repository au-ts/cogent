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

{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS_GHC -Wwarn #-}

module Cogent.Isabelle.Deep where

import Cogent.Common.Syntax as CS
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Core as CC
import Cogent.Util (NameMod, Stage(..))
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Vec (cvtToList, Fin, finInt)
import Isabelle.ExprTH
import Isabelle.InnerAST as I
import Isabelle.OuterAST as O

#if __GLASGOW_HASKELL__ >= 709
import Prelude hiding ((<$>))
#endif
import System.FilePath ((</>))
import Text.PrettyPrint.ANSI.Leijen hiding ((</>))

-- import Debug.Trace

deepIndex :: Fin v -> Term
deepIndex = mkInt . fromIntegral . finInt

-- TODO these undefineds should be swapped out for representations of the layout, once we work out what the C refinement framework
-- is going to do with them ~ v.jackson / 2018-08-27
deepSigil :: Sigil s -> Term
deepSigil (Boxed True  _) = mkApp (mkId "Boxed") [(mkId "ReadOnly"), (mkId "undefined")]
deepSigil (Boxed False _) = mkApp (mkId "Boxed") [(mkId "Writable"), (mkId "undefined")]
deepSigil Unboxed         = mkId "Unboxed"

type TypeAbbrevs = (Map.Map Term Int, Int)

deepVariantState :: Bool -> Term
deepVariantState False = mkId "Unchecked"
deepVariantState True  = mkId "Checked"

deepRecordState :: Bool -> Term
deepRecordState False = mkId "Present"
deepRecordState True  = mkId "Taken"

deepTypeInner :: (?namemod :: NameMod) =>  TypeAbbrevs -> CC.Type t -> Term
deepTypeInner ta (TVar v) = mkApp (mkId "TVar") [deepIndex v]
deepTypeInner ta (TVarBang v) = mkApp (mkId "TVarBang") [deepIndex v]
deepTypeInner ta (TCon tn ts s) = mkApp (mkId "TCon") [mkString tn, mkList (map (deepType ta) ts), deepSigil s]
deepTypeInner ta (TFun ti to) = mkApp (mkId "TFun") [deepType ta ti, deepType ta to]
deepTypeInner ta (TPrim pt) = mkApp (mkId "TPrim") [deepPrimType pt]
deepTypeInner ta (TString) = mkApp (mkId "TPrim") [mkId "String"]
deepTypeInner ta (TSum alts)
  = mkApp (mkId "TSum")
          [mkList $ map (\(n,(t,b)) -> mkPair (mkString n) (mkPair (deepType ta t) (deepVariantState b))) $ sort alts]
deepTypeInner ta (TProduct t1 t2) = mkApp (mkId "TProduct") [deepType ta t1, deepType ta t2]
deepTypeInner ta (TRecord fs s) = mkApp (mkId "TRecord") [mkList $ map (\(fn,(t,b)) -> mkPair (mkString fn) (mkPair (deepType ta t) (deepRecordState b))) fs, deepSigil s]
deepTypeInner ta (TUnit) = mkId "TUnit"
deepTypeInner _ t = __impossible $ "deepTypeInner: " ++ show (pretty t) ++ " is not yet implemented"

mkAbbrevNm :: (?namemod :: NameMod) =>  Int -> String
mkAbbrevNm n = ?namemod $ "abbreviatedType" ++ show n

mkAbbrevId :: (?namemod :: NameMod) =>  Int -> Term
mkAbbrevId = mkId . mkAbbrevNm

deepType :: (?namemod :: NameMod) =>  TypeAbbrevs -> CC.Type t -> Term
deepType ta t = case Map.lookup term (fst ta) of
    Just n -> mkAbbrevId n
    Nothing -> term
  where
    term = deepTypeInner ta t

deepPrimType :: PrimInt -> Term
deepPrimType U8  = mkApp (mkId "Num") [mkId "U8" ]
deepPrimType U16 = mkApp (mkId "Num") [mkId "U16"]
deepPrimType U32 = mkApp (mkId "Num") [mkId "U32"]
deepPrimType U64 = mkApp (mkId "Num") [mkId "U64"]
deepPrimType Boolean = mkId "Bool"

deepNumType :: PrimInt -> Term
deepNumType U8  = mkId "U8"
deepNumType U16 = mkId "U16"
deepNumType U32 = mkId "U32"
deepNumType U64 = mkId "U64"
deepNumType Boolean = __impossible "deepNumType"

deepILit :: Integer -> PrimInt -> Term
deepILit n U8  = mkApp (mkId "LU8" ) [mkInt n]
deepILit n U16 = mkApp (mkId "LU16") [mkInt n]
deepILit n U32 = mkApp (mkId "LU32") [mkInt n]
deepILit n U64 = mkApp (mkId "LU64") [mkInt n]
deepILit n Boolean = mkApp (mkId "LBool") [if n == 0 then mkFls else mkTru]

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

deepExpr :: (Pretty a, (?namemod :: NameMod)) =>  TypeAbbrevs -> [Definition TypedExpr a] -> TypedExpr t v a -> Term
deepExpr ta defs (TE _ (Variable v)) = mkApp (mkId "Var") [deepIndex (fst v)]
deepExpr ta defs (TE _ (Fun fn ts _))
  | concreteFun fn = mkApp (mkId "Fun")  [mkId (?namemod fn), mkList (map (deepType ta) ts)]
  | otherwise      = mkApp (mkId "AFun") [mkString fn, mkList (map (deepType ta) ts)]
  where concreteFun f = any (\def -> isFuncId f def && case def of FunDef{} -> True; _ -> False) defs
deepExpr ta defs (TE _ (Op opr es))
  = mkApp (mkId "Prim") [deepPrimOp opr (let TPrim pt = exprType $ head es in pt),
                         mkList (map (deepExpr ta defs) es)]
deepExpr ta defs (TE _ (App f arg))
  = mkApp (mkId "App") [deepExpr ta defs f, deepExpr ta defs arg]
deepExpr ta defs (TE (TSum alts) (Con cn e _))
  = mkApp (mkId "Con") [mkList t', mkString cn, deepExpr ta defs e]
  where t' = map (\(c,(t,b)) -> mkPair (mkString c) (mkPair (deepType ta t) (deepVariantState b))) alts
deepExpr _ _ (TE _ (Con _ _ _)) = __impossible "deepExpr: Con"
deepExpr ta defs (TE _ (Promote ty e))
  = mkApp (mkId "Promote") [deepType ta ty, deepExpr ta defs e]
  -- = deepExpr mod ta defs e
--   | TE (TPrim pt) _ <- e, TPrim pt' <- ty, pt /= Boolean
--   = mkApp (mkId "Cast") [deepNumType pt', deepExpr mod ta defs e]  -- primInt cast
--   | TE (TSum _) (Con cn v _) <- e, TSum as <- ty
--   = mkApp (mkId "Con") [mkList $ map (\(an,(at,_)) -> mkPair (mkString an) (deepType mod ta at)) as, mkString cn, deepExpr mod ta defs v]  -- inlined Con
--   | TSum as <- ty = mkApp (mkId "Promote") [mkList $ map (\(an,(at,_)) -> mkPair (mkString an) (deepType mod ta at)) as, deepExpr mod ta defs e]  -- FIMXE: cogent.1
--   | otherwise = __impossible "deepExpr"
deepExpr ta defs (TE _ (Struct fs))
  = mkApp (mkId "Struct") [mkList (map (deepType ta . exprType . snd) fs),
                           mkList (map (deepExpr ta defs . snd) fs)]
deepExpr ta defs (TE _ (Member e fld))
  = mkApp (mkId "Member") [deepExpr ta defs e, mkInt (fromIntegral fld)]
deepExpr ta defs (TE _ (Unit)) = mkId "Unit"
deepExpr ta defs (TE _ (ILit n pt)) = mkApp (mkId "Lit") [deepILit n pt]
deepExpr ta defs (TE _ (SLit s)) = __fixme $ mkApp (mkId "SLit") [mkString s]  -- FIXME: there's no @SLit@ in the Isabelle definition at the moment / zilinc
deepExpr ta defs (TE _ (Tuple e1 e2))
  = mkApp (mkId "Tuple") [deepExpr ta defs e1, deepExpr ta defs e2]
deepExpr ta defs (TE _ (Put rec fld e))
  = mkApp (mkId "Put") [deepExpr ta defs rec, mkInt (fromIntegral fld), deepExpr ta defs e]
deepExpr ta defs (TE _ (Let _ e1 e2))
  = mkApp (mkId "Let") [deepExpr ta defs e1, deepExpr ta defs e2]
deepExpr ta defs (TE _ (LetBang vs _ e1 e2))
  = let vs' = mkApp (mkId "set") [mkList $ map (deepIndex . fst) vs]
     in mkApp (mkId "LetBang") [vs', deepExpr ta defs e1, deepExpr ta defs e2]
deepExpr ta defs (TE _ (Case e tag (l1,_,e1) (l2,_,e2)))
  = mkApp (mkId "Case") [deepExpr ta defs e,
                         mkString tag,
                         deepExpr ta defs e1,
                         deepExpr ta defs e2]
deepExpr ta defs (TE _ (Esac e)) = mkApp (mkId "Esac") [deepExpr ta defs e]
deepExpr ta defs (TE _ (If c th el)) = mkApp (mkId "If") $ map (deepExpr ta defs) [c, th, el]
deepExpr ta defs (TE _ (Take _ rec fld e))
  = mkApp (mkId "Take") [deepExpr ta defs rec, mkInt (fromIntegral fld), deepExpr ta defs e]
deepExpr ta defs (TE _ (Split _ e1 e2))
  = mkApp (mkId "Split") [deepExpr ta defs e1, deepExpr ta defs e2]
deepExpr ta defs (TE _ (Cast t e))
  | TE (TPrim pt) _ <- e, TPrim pt' <- t, pt /= Boolean
  = mkApp (mkId "Cast") [deepNumType pt', deepExpr ta defs e]
deepExpr ta defs (TE _ e) = __todo $ "deepExpr: " ++ show (pretty e)

deepKind :: Kind -> Term
deepKind (K e s d) = ListTerm "{" [ mkId str | (sig, str) <- [(e, "E"), (s, "S"), (d, "D")], sig ] "}"

deepPolyType :: (?namemod :: NameMod) =>  TypeAbbrevs -> FunctionType -> Term
deepPolyType ta (FT ks ti to) = mkPair (mkList $ map deepKind $ cvtToList ks)
                                           (mkPair (deepType ta ti) (deepType ta to))

imports :: TheoryImports
imports = TheoryImports $ [__cogent_root_dir </> "cogent/isa/Cogent"]

deepDefinition :: (?namemod :: NameMod) =>  TypeAbbrevs -> [Definition TypedExpr a] -> Definition TypedExpr a ->
                    [TheoryDecl I.Type I.Term] -> [TheoryDecl I.Type I.Term]
deepDefinition ta defs (FunDef _ fn ks ti to e) decls =
    let ty = deepPolyType ta $ FT (fmap snd ks) ti to
        tn = ?namemod fn ++ "_type"
        tysig = [isaType| Cogent.kind list \<times> Cogent.type \<times> Cogent.type |]
        tydecl = [isaDecl| definition $tn :: "$tysig" where "$(mkId tn) \<equiv> $ty" |]
        e' = deepExpr ta defs e
        fntysig = AntiType "string Cogent.expr"
        fn' = ?namemod fn
        decl = [isaDecl| definition $fn' :: "$fntysig" where "$(mkId fn') \<equiv> $e'" |]
     in tydecl:decl:decls
deepDefinition ta _ (AbsDecl _ fn ks ti to) decls =
    let ty = deepPolyType ta $ FT (fmap snd ks) ti to
        tn = ?namemod fn ++ "_type"
        tysig = [isaType| Cogent.kind list \<times> Cogent.type \<times> Cogent.type |]
        tydecl = [isaDecl| definition $tn :: "$tysig" where "$(mkId tn) \<equiv> $ty" |]
     in tydecl:decls
deepDefinition _ _ _ decls = decls

deepDefinitions :: (?namemod :: NameMod) =>  TypeAbbrevs -> [Definition TypedExpr a] -> [TheoryDecl I.Type I.Term]
deepDefinitions ta defs = foldr (deepDefinition ta defs) [] defs ++
                              [TheoryString $
                               "ML {*\n" ++
                               "val Cogent_functions = " ++ show (cogentFuns defs) ++ "\n" ++
                               "val Cogent_abstract_functions = " ++ show (absFuns defs) ++ "\n" ++
                               "*}"
                              ]
  where absFuns [] = []
        absFuns (AbsDecl _ fn _ _ _ : fns) = fn : absFuns fns
        absFuns (_ : fns) = absFuns fns
        cogentFuns [] = []
        cogentFuns (FunDef _ fn _ _ _ _ : fns) = fn : cogentFuns fns
        cogentFuns (_ : fns) = cogentFuns fns

scanAggregates :: CC.Type t -> [CC.Type t]
scanAggregates (TCon tn ts _) = concatMap scanAggregates ts
scanAggregates (TFun ti to) = scanAggregates ti ++ scanAggregates to
scanAggregates (TSum alts) = concatMap (scanAggregates . fst . snd) alts ++ [TSum alts]
scanAggregates (TProduct t1 t2) = scanAggregates t1 ++ scanAggregates t2
scanAggregates (TRecord fs s) = concatMap (scanAggregates . fst . snd) fs ++ [TRecord fs s]
scanAggregates _ = []

addTypeAbbrev :: (?namemod :: NameMod) =>  CC.Type t -> TypeAbbrevs -> TypeAbbrevs
addTypeAbbrev t ta = case Map.lookup term (fst ta) of
    Just s -> ta
    Nothing -> (Map.insert term (snd ta) (fst ta), snd ta + 1)
  where
    term = deepTypeInner ta t

getDefTypeAbbrevs :: (?namemod :: NameMod) =>  Definition TypedExpr a -> TypeAbbrevs -> TypeAbbrevs
getDefTypeAbbrevs (FunDef _ _ _ ti to e) ta = foldr addTypeAbbrev ta
    (scanAggregates ti ++ scanAggregates to)
getDefTypeAbbrevs _ ta = ta

getTypeAbbrevs :: (?namemod :: NameMod) => [Definition TypedExpr a] -> TypeAbbrevs
getTypeAbbrevs defs = foldr getDefTypeAbbrevs (Map.empty, 1) defs

deepTypeAbbrev :: (?namemod :: NameMod) =>  (Int, Term) -> TheoryDecl I.Type I.Term
deepTypeAbbrev (n, tm) = let
    nm = mkAbbrevNm n
    tysig = [isaType| Cogent.type |]
  in [isaDecl| definition $nm :: "$tysig" where "$(mkId nm) \<equiv> $tm" |]

typeAbbrevBucketName = "abbreviated_type_defs"

typeAbbrevDefsLemma :: (?namemod :: NameMod) =>  TypeAbbrevs -> TheoryDecl I.Type I.Term
typeAbbrevDefsLemma ta = let
    defTD = \n -> O.TheoremDecl { thmName = Just n, thmAttributes = [] }
    nms = [mkAbbrevNm n ++ "_def" | (_, n) <- Map.toList (fst ta)]
  in O.LemmasDecl (O.Lemmas { lemmasName = defTD typeAbbrevBucketName,
                              lemmasThms = map defTD (if null nms then ["TrueI"] else nms) })

deepTypeAbbrevs :: (?namemod :: NameMod) =>  TypeAbbrevs -> [TheoryDecl I.Type I.Term]
deepTypeAbbrevs ta = map deepTypeAbbrev defs ++ [typeAbbrevDefsLemma ta]
  where
    defs = sort $ map (\(x, y) -> (y, x)) $ Map.toList (fst ta)

deepDefinitionsAbb :: (?namemod :: NameMod) =>  [Definition TypedExpr a] -> (TypeAbbrevs, [TheoryDecl I.Type I.Term])
deepDefinitionsAbb defs = (ta, deepTypeAbbrevs ta ++ deepDefinitions ta defs)
  where ta = getTypeAbbrevs defs

deepFile :: (?namemod :: NameMod) =>  String -> [Definition TypedExpr a] -> Theory I.Type I.Term
deepFile thy defs = Theory thy imports (snd (deepDefinitionsAbb defs))

deep :: String -> Stage -> [Definition TypedExpr a] -> String -> Doc
deep thy stg defs log = string ("(*\n" ++ log ++ "\n*)\n") <$>
                        let ?namemod = id in pretty (deepFile thy defs)


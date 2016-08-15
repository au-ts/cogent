--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS_GHC -Wwarn #-}

module Cogent.Deep where

import Cogent.Common.Syntax as CS
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Core as CC
import Cogent.Util (NameMod, Stage(..))
import Cogent.Vec (cvtToList, Fin, finInt)
import Data.List (sort)
import qualified Data.Map.Strict as Map
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

deepSigil :: Sigil -> Term
deepSigil ReadOnly = mkId "ReadOnly"
deepSigil Writable = mkId "Writable"
deepSigil Unboxed  = mkId "Unboxed"

type TypeAbbrevs = (Map.Map Term Int, Int)

deepTypeInner :: NameMod -> TypeAbbrevs -> CC.Type t -> Term
deepTypeInner mod ta (TVar v) = mkApp (mkId "TVar") [deepIndex v]
deepTypeInner mod ta (TVarBang v) = mkApp (mkId "TVarBang") [deepIndex v]
deepTypeInner mod ta (TCon tn ts s) = mkApp (mkId "TCon") [mkString tn, mkList (map (deepType mod ta) ts), deepSigil s]
deepTypeInner mod ta (TFun ti to) = mkApp (mkId "TFun") [deepType mod ta ti, deepType mod ta to]
deepTypeInner mod ta (TPrim pt) = mkApp (mkId "TPrim") [deepPrimType pt]
deepTypeInner mod ta (TString) = mkApp (mkId "TPrim") [mkId "String"]
deepTypeInner mod ta (TSum alts) = mkApp (mkId "TSum") [mkList $ map (\(n,(t,_)) -> mkPair (mkString n) (deepType mod ta t)) $ sort alts]  -- FIXME: cogent.1
deepTypeInner mod ta (TProduct t1 t2) = mkApp (mkId "TProduct") [deepType mod ta t1, deepType mod ta t2]
deepTypeInner mod ta (TRecord fs s) = mkApp (mkId "TRecord") [mkList $ map (\(fn,(t,b)) -> mkPair (deepType mod ta t) (mkBool b)) fs, deepSigil s]
deepTypeInner mod ta (TUnit) = mkId "TUnit"

mkAbbrevNm :: NameMod -> Int -> String
mkAbbrevNm mod n = mod $ "abbreviatedType" ++ show n

mkAbbrevId :: NameMod -> Int -> Term
mkAbbrevId = (mkId .) . mkAbbrevNm

deepType :: NameMod -> TypeAbbrevs -> CC.Type t -> Term
deepType mod ta t = case Map.lookup term (fst ta) of
    Just n -> mkAbbrevId mod n
    Nothing -> term
  where
    term = deepTypeInner mod ta t

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

deepExpr :: NameMod -> TypeAbbrevs -> [Definition TypedExpr a] -> TypedExpr t v a -> Term
deepExpr mod ta defs (TE _ (Variable v)) = mkApp (mkId "Var") [deepIndex (fst v)]
deepExpr mod ta defs (TE _ (Fun fn ts _))
  | concreteFun fn = mkApp (mkId "Fun") [mkId (mod fn), mkList (map (deepType mod ta) ts)]
  | otherwise = mkApp (mkId "AFun") [mkString fn, mkList (map (deepType mod ta) ts)]
  where concreteFun f = any (\def -> isFuncId f def && case def of FunDef{} -> True; _ -> False) defs
deepExpr mod ta defs (TE _ (Op opr es)) = mkApp (mkId "Prim") [deepPrimOp opr (let TPrim pt = exprType $ head es in pt),
                                                               mkList (map (deepExpr mod ta defs) es)]
deepExpr mod ta defs (TE _ (App f arg)) = mkApp (mkId "App") [deepExpr mod ta defs f, deepExpr mod ta defs arg]
deepExpr mod ta defs (TE (TSum alts) (Con cn e)) = mkApp (mkId "Con") [mkList t', mkString cn, deepExpr mod ta defs e]
  where t' = map (\(c,(ty,_)) -> mkPair (mkString c) (deepType mod ta ty)) alts  -- FIXME: cogent.1
deepExpr _ _ _ (TE _ (Con _ _)) = __impossible "deepExpr"
deepExpr mod ta defs (TE _ (Promote ty e))
  | TE (TPrim pt) _ <- e, TPrim pt' <- ty, pt /= Boolean = mkApp (mkId "Cast") [deepNumType pt', deepExpr mod ta defs e]  -- primInt cast
  | TE (TSum _) (Con cn v) <- e, TSum as <- ty =
      mkApp (mkId "Con") [mkList $ map (\(an,(at,_)) -> mkPair (mkString an) (deepType mod ta at)) as, mkString cn, deepExpr mod ta defs v]  -- inlined Con  -- FIXME: cogent.1
  | TSum as <- ty = mkApp (mkId "Promote") [mkList $ map (\(an,(at,_)) -> mkPair (mkString an) (deepType mod ta at)) as, deepExpr mod ta defs e]  -- FIMXE: cogent.1
  | otherwise = __impossible "deepExpr"
deepExpr mod ta defs (TE _ (Struct fs)) = mkApp (mkId "Struct") [mkList (map (deepType mod ta . exprType . snd) fs), mkList (map (deepExpr mod ta defs . snd) fs)]
deepExpr mod ta defs (TE _ (Member e fld)) = mkApp (mkId "Member") [deepExpr mod ta defs e, mkInt (fromIntegral fld)]
deepExpr mod ta defs (TE _ (Unit)) = mkId "Unit"
deepExpr mod ta defs (TE _ (ILit n pt)) = mkApp (mkId "Lit") [deepILit n pt]
deepExpr mod ta defs (TE _ (SLit s)) = __todo "deepExpr: SLit"
deepExpr mod ta defs (TE _ (Tuple e1 e2)) = mkApp (mkId "Tuple") [deepExpr mod ta defs e1, deepExpr mod ta defs e2]
deepExpr mod ta defs (TE _ (Put rec fld e)) = mkApp (mkId "Put") [deepExpr mod ta defs rec, mkInt (fromIntegral fld), deepExpr mod ta defs e]
deepExpr mod ta defs (TE _ (Let _ e1 e2)) = mkApp (mkId "Let") [deepExpr mod ta defs e1, deepExpr mod ta defs e2]
deepExpr mod ta defs (TE _ (LetBang vs _ e1 e2)) = let vs' = mkApp (mkId "set") [mkList $ map (deepIndex . fst) vs]
                                               in mkApp (mkId "LetBang") [vs', deepExpr mod ta defs e1, deepExpr mod ta defs e2]
deepExpr mod ta defs (TE _ (Case e tag (l1,_,e1) (l2,_,e2))) = mkApp (mkId "Case") [deepExpr mod ta defs e, mkString tag, deepExpr mod ta defs e1, deepExpr mod ta defs e2]
deepExpr mod ta defs (TE _ (Esac e)) = mkApp (mkId "Esac") [deepExpr mod ta defs e]
deepExpr mod ta defs (TE _ (If c th el)) = mkApp (mkId "If") $ map (deepExpr mod ta defs) [c, th, el]
deepExpr mod ta defs (TE _ (Take _ rec fld e)) = mkApp (mkId "Take") [deepExpr mod ta defs rec, mkInt (fromIntegral fld), deepExpr mod ta defs e]
deepExpr mod ta defs (TE _ (Split _ e1 e2)) = mkApp (mkId "Split") [deepExpr mod ta defs e1, deepExpr mod ta defs e2]

deepKind :: Kind -> Term
deepKind (K e s d) = ListTerm "{" [ mkId str | (sig, str) <- [(e, "E"), (s, "S"), (d, "D")], sig ] "}"

deepPolyType :: NameMod -> TypeAbbrevs -> FunctionType -> Term
deepPolyType mod ta (FT ks ti to) = mkPair (mkList $ map deepKind $ cvtToList ks) (mkPair (deepType mod ta ti) (deepType mod ta to))

imports :: TheoryImports
imports = TheoryImports $ [__cogent_root_dir </> "cogent/isa/Cogent"]

deepDefinition :: NameMod -> TypeAbbrevs -> [Definition TypedExpr a] -> Definition TypedExpr a ->
                    [TheoryDecl I.Type I.Term] -> [TheoryDecl I.Type I.Term]
deepDefinition mod ta defs (FunDef _ fn ks ti to e) decls =
    let ty = deepPolyType mod ta $ FT (fmap snd ks) ti to
        tn = mod fn ++ "_type"
        tysig = [isaType| Cogent.kind list \<times> Cogent.type \<times> Cogent.type |]
        tydecl = [isaDecl| definition $tn :: "$tysig" where "$(mkId tn) \<equiv> $ty" |]
        e' = deepExpr mod ta defs e
        fntysig = AntiType "string Cogent.expr"
        fn' = mod fn
        decl = [isaDecl| definition $fn' :: "$fntysig" where "$(mkId fn') \<equiv> $e'" |]
     in tydecl:decl:decls
deepDefinition mod ta _ (AbsDecl _ fn ks ti to) decls =
    let ty = deepPolyType mod ta $ FT (fmap snd ks) ti to
        tn = mod fn ++ "_type"
        tysig = [isaType| Cogent.kind list \<times> Cogent.type \<times> Cogent.type |]
        tydecl = [isaDecl| definition $tn :: "$tysig" where "$(mkId tn) \<equiv> $ty" |]
     in tydecl:decls
deepDefinition _ _ _ _ decls = decls

deepDefinitions :: NameMod -> TypeAbbrevs -> [Definition TypedExpr a] -> [TheoryDecl I.Type I.Term]
deepDefinitions mod ta defs = foldr (deepDefinition mod ta defs) [] defs ++
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
scanAggregates (TCon tn ts s) = concatMap scanAggregates ts
scanAggregates (TFun ti to) = scanAggregates ti ++ scanAggregates to
scanAggregates (TSum alts) = concatMap (scanAggregates . fst . snd) alts ++ [TSum alts]  -- FIXME: cogent.1
scanAggregates (TProduct t1 t2) = scanAggregates t1 ++ scanAggregates t2
scanAggregates (TRecord fs s) = concatMap (scanAggregates . fst . snd) fs ++ [TRecord fs s]
scanAggregates _ = []

addTypeAbbrev :: NameMod -> CC.Type t -> TypeAbbrevs -> TypeAbbrevs
addTypeAbbrev mod t ta = case Map.lookup term (fst ta) of
    Just s -> ta
    Nothing -> (Map.insert term (snd ta) (fst ta), snd ta + 1)
  where
    term = deepTypeInner mod ta t

getDefTypeAbbrevs :: NameMod -> Definition TypedExpr a -> TypeAbbrevs -> TypeAbbrevs
getDefTypeAbbrevs mod (FunDef _ _ _ ti to e) ta = foldr (addTypeAbbrev mod) ta
    (scanAggregates ti ++ scanAggregates to)
getDefTypeAbbrevs _ _ ta = ta

getTypeAbbrevs :: NameMod -> [Definition TypedExpr a] -> TypeAbbrevs
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
    nms = [mkAbbrevNm mod n ++ "_def" | (_, n) <- Map.toList (fst ta)]
  in O.LemmasDecl (O.Lemmas { lemmasName = defTD typeAbbrevBucketName,
                              lemmasThms = map defTD (if null nms then ["TrueI"] else nms) })

deepTypeAbbrevs :: NameMod -> TypeAbbrevs -> [TheoryDecl I.Type I.Term]
deepTypeAbbrevs mod ta = map (deepTypeAbbrev mod) defs ++ [typeAbbrevDefsLemma mod ta]
  where
    defs = sort $ map (\(x, y) -> (y, x)) $ Map.toList (fst ta)

deepDefinitionsAbb :: NameMod -> [Definition TypedExpr a] -> (TypeAbbrevs, [TheoryDecl I.Type I.Term])
deepDefinitionsAbb mod defs = (ta, deepTypeAbbrevs mod ta ++ deepDefinitions mod ta defs)
  where ta = getTypeAbbrevs mod defs

deepFile :: NameMod -> String -> [Definition TypedExpr a] -> Theory I.Type I.Term
deepFile mod thy defs = Theory thy imports (snd (deepDefinitionsAbb mod defs))

deep :: String -> Stage -> [Definition TypedExpr a] -> String -> Doc
deep thy stg defs log = string ("(*\n" ++ log ++ "\n*)\n") <$>
                        pretty (deepFile id thy defs)


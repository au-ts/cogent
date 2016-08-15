--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE MultiWayIf #-}

module Cogent.NormalProof (normalProof) where

import Cogent.Common.Syntax
import Cogent.Compiler
import Cogent.Core
import Cogent.Util
import Cogent.Shallow (MapTypeName)
import Cogent.ShallowTable (TypeStr (..))

import Isabelle.InnerAST as I
import Isabelle.OuterAST as O

import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import System.FilePath ((</>))
import Text.PrettyPrint.ANSI.Leijen as L (Doc, pretty, string, (<$>))

normalProof :: String -> MapTypeName -> [Definition TypedExpr VarName] -> String -> Doc
normalProof thy typeMap defs log =
  let sdthy = thy ++ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage STGDesugar
      snthy = thy ++ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage STGNormal
      header = (L.string ("(*\n" ++ log ++ "\n*)\n") L.<$>)
      theory = O.Theory { thyName = thy ++ __cogent_suffix_of_normal_proof
                        , thyImports = imports thy
                        , thyBody = genDesugarNormalProof sdthy snthy typeMap defs
                        } :: O.Theory I.Type I.Term
   in header $ L.pretty theory

imports :: String -> TheoryImports
imports thy =
  TheoryImports $ [ __cogent_root_dir </> "cogent/isa/shallow/Shallow_Normalisation_Tac"
                  , thy ++ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage STGDesugar
                  , thy ++ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage STGNormal
                  ]



{-
 - Rules needed for the normalisation proof.
 - The proof procedure can deal with most Shallow constructs generically,
 - but case splits and promotions use a different case construct for each
 - variant type, so we need to generate rules for each type.
 -}



{- Promotions for variant literals ("Promote ... (Con ...)") get special-cased in Shallow.
 - They are inlined for the desugared embedding but not the normalised one
 - (because the normalisation removes the inner Con).
 - So, these rules provide the inlining for normalised code also. -}

-- S.Set (srcType, destType, tagName)
getInlinedShallowPromotes :: MapTypeName -> TypedExpr t v n -> S.Set (String, String, String)
getInlinedShallowPromotes typeMap e =
  let get' (TE (TSum ts) (Promote _ (TE (TSum ts0) _))) =
        let tname = typeMap M.! VariantStr (map fst ts)
            tname0 = typeMap M.! VariantStr (map fst ts0)
        in case ts0 of -- only need promote rule from singleton variants
          [(tag, _)] -> S.singleton (tname0, tname, tag)
          _ -> S.empty
      get' _ = S.empty
      unwrap (TE _ e) = e
  in foldEPre unwrap get' e

promoteRules :: [(String, String, String)] -> Maybe (String, O.TheoryDecl I.Type I.Term)
promoteRules promotes = let
  thmName = "shallow_anormal_promotes"
  prop (srcType, destType, tagName) = let
    -- "(case A a of A x => B x) == B a"
    srcCon = srcType ++ "." ++ tagName
    destCon = destType ++ "." ++ tagName
    in "(case " ++ srcCon ++ " a of " ++
       srcCon ++ " x \\<Rightarrow> " ++ destCon ++ " x) \\<equiv> " ++
       destCon ++ " a"
  props = map (mkId . prop) promotes
  method = Method "simp_all" []
  in if null promotes then Nothing else
       Just (thmName, O.LemmaDecl (O.Lemma False (Just (O.TheoremDecl (Just thmName) [])) props $ Proof [method] ProofDone))


{- Rules for CPS-transforming Case expressions that are used as arguments or functions
 - (in the Isabelle/HOL sense, not Core.Fun).
 - The $ operator is used by the proof procedure to enforce first-order matching. -}

-- S.Set (typeName, tagCount)
getShallowCases :: MapTypeName -> TypedExpr t v n -> S.Set (String, Int)
getShallowCases typeMap e =
  let get' (TE _ (Case (TE (TSum tags) _) _ _ _)) =
        let tname = typeMap M.! VariantStr (map fst tags)
        in S.singleton (tname, length tags)
      get' _ = S.empty
      unwrap (TE _ e) = e
  in foldEPre unwrap get' e

anormalCaseRules :: [(String, Int)] -> Maybe (String, O.TheoryDecl I.Type I.Term)
anormalCaseRules variants = let
  thmName = "shallow_anormal_case_distribs"

  -- the following comments show the idealised rules,
  -- before $ operators are inserted.

  {- "forall x y f1 f2... .
        (case x of A1 v => f1 v | A2 v => f2 v | ...) y
         == (case x of A1 v => f1 v y | A2 v => f2 v y | ...)" -}
  funProp (typeName, tagCount) = let
    vars = map (\n -> 'f' : show n) [1..tagCount]
    in "\\<And>x y " ++ intercalate " " vars ++ ". " ++
       apply (["case_" ++ typeName] ++ vars ++ ["x", "y"]) ++ " \\<equiv> " ++
       apply (["case_" ++ typeName] ++
              ["(\\<lambda>v. " ++ f ++ " v $ y)" | f <- vars] ++ ["x"])

  {- "forall x g f1 f2... .
        g (case x of A1 v => f1 v | A2 v => f2 v | ...)
         == (case x of A1 v => g (f1 v) | A2 v => g (f2 v) | ...)" -}
  argProp (typeName, tagCount) = let
    vars = map (\n -> 'f' : show n) [1..tagCount]
    in "\\<And>x g " ++ intercalate " " vars ++ ". " ++
       "g $ " ++ apply (["case_" ++ typeName] ++ vars ++ ["x"]) ++ " \\<equiv> " ++
       apply (["case_" ++ typeName] ++
              ["(\\<lambda>v. g $ " ++ f ++ " v)" | f <- vars] ++ ["x"])

  -- intercalate with ($); we need to add parens because it's infixr
  apply = foldl1 (\f x -> "(" ++ f ++ " $ " ++ x ++ ")")

  props = concatMap (\v -> [mkId (funProp v), mkId (argProp v)]) variants
  splitRules = [typeName ++ ".splits" | (typeName, _) <- variants]
  method = Method "auto" $ ["intro!:", "eq_reflection", "split:"] ++ splitRules
  in if null variants then Nothing else
       Just (thmName, O.LemmaDecl (O.Lemma False (Just (O.TheoremDecl (Just thmName) [])) props $ Proof [method] ProofDone))


genDesugarNormalProof :: String -> String -> MapTypeName -> [Definition TypedExpr VarName] -> [O.TheoryDecl I.Type I.Term]
genDesugarNormalProof sdthy snthy typeMap defs =
  let getPromotes (FunDef _ _ _ _ _ e) = getInlinedShallowPromotes typeMap e
      getPromotes _ = S.empty
      getCases (FunDef _ _ _ _ _ e) = getShallowCases typeMap e
      getCases _ = S.empty

      promotes = S.unions $ map getPromotes defs
      cases = S.unions $ map getCases defs
      (promoteThms, promoteProofs) = case promoteRules $ S.toList promotes of
        Just (thmName, proof) -> ("@{thms " ++ thmName ++ "}", [proof])
        _ -> ("[]", [])
      (caseThms, caseProofs) = case anormalCaseRules $ S.toList cases of
        Just (thmName, proof) -> ("@{thms " ++ thmName ++ "}", [proof])
        _ -> ("[]", [])

      (fns, _) = foldr (\f (fs,as) -> if | isConFun f -> (getDefinitionId f:fs, as)
                                         | isAbsFun f -> (fs, getDefinitionId f:as)
                                         | otherwise  -> (fs, as)) ([],[]) defs
  in promoteProofs ++
     caseProofs ++
     [ O.TheoryString $ unlines
       [ "ML {*"
       , "val Cogent_functions = " ++ show fns
       , "*}"
       , ""
       , "ML {*"
       , "val normalisation_thms = normalisation_tac_all @{context} \"" ++
            sdthy ++ "\" \"" ++ snthy ++ "\" " ++ promoteThms ++ " " ++ caseThms ++ " Cogent_functions"
       , "*}"
       ]
     ]

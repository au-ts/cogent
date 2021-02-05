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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

module Cogent.Isabelle.TypeProofs2
  (deepTypeProofNew)
where

import Cogent.Common.Syntax
import Cogent.Common.Types (Kind)
import Cogent.Compiler
import Cogent.Core
import Cogent.Inference
import Cogent.Isabelle.Deep
import Cogent.Isabelle.IsabelleName
import Cogent.Isabelle.ProofGen
import Cogent.Util (NameMod)
import Data.Fin
import Data.LeafTree
import Data.List (intercalate)
import Data.Vec hiding (splitAt, length, zipWith, zip, unzip, head)
import qualified Data.Vec as V


import Isabelle.ExprTH
import qualified Isabelle.InnerAST as I
import Isabelle.InnerAST hiding (Type, Term)
import Isabelle.OuterAST

import Prelude hiding ((<$>))

import Text.PrettyPrint.ANSI.Leijen hiding ((</>))

-- import Data.Char
-- import Data.Foldable
-- import Data.List
-- import qualified Data.Map as M
import Data.Maybe (mapMaybe)
-- import Data.Ord (comparing)
-- import Numeric
-- import System.FilePath ((</>))
-- import Text.Printf
-- import Text.Show
-- import Lens.Micro ((^.))
-- import Lens.Micro.Mtl (use)

deepTypeProofNew :: (Pretty a) => NameMod -> Bool -> Bool -> String -> [Definition TypedExpr a VarName] -> String -> Doc
deepTypeProofNew mod withDecls withBodies thy decls log =
  let header = (string ("(*\n" ++ log ++ "\n*)\n") <$>)
      ta = getTypeAbbrevs mod decls
      imports = TheoryImports ["Cogent.TypeInfer"]
      theoryBody = deepTypeAbbrevs mod ta
                   ++ concatMap (generateFunctionDefinitionDefn mod ta decls) decls
                   ++ mapMaybe generateTypingLemmaDefn decls
  in header . pretty $ Theory thy imports theoryBody

generateFunctionDefinitionDefn ::
  (Ord vn, Pretty vn) =>
  NameMod ->
  TypeAbbrevs ->
  [Definition TypedExpr a vn] ->
  Definition TypedExpr a vn ->
  [TheoryDecl I.Type I.Term]
generateFunctionDefinitionDefn mod ta defs (FunDef _ fn ks ts ti to e) =
  let ty = deepPolyType mod ta $ FT (fmap snd ks) (fmap snd ts) ti to
      tn = case editIsabelleName (mkIsabelleName fn) (++ "_type")  of
            Just n  -> unIsabelleName n
            Nothing -> error ("Error - unable to generate name for isabelle function '" ++ fn ++ "'")
      tysig = [isaType| Cogent.kind list \<times> Cogent.type \<times> Cogent.type |]
      tydecl = [isaDecl| definition $tn :: "$tysig" where "$(mkId tn) \<equiv> $ty" |]
      e' = deepExpr mod ta defs e
      fntysig = AntiType "string Cogent.expr"
      fn' = unIsabelleName (mkIsabelleName fn)
      decl = [isaDecl| definition $fn' :: "$fntysig" where "$(mkId fn') \<equiv> $e'" |]
   in [tydecl, decl]
generateFunctionDefinitionDefn mod ta defs (AbsDecl _ fn ks ts ti to) =
  let ty = deepPolyType mod ta $ FT (fmap snd ks) (fmap snd ts) ti to
      tn = case editIsabelleName (mkIsabelleName fn) (++ "_type") of 
          Just n  -> unIsabelleName n
          Nothing -> error ("Error - unable to generate name for isabelle function '" ++ fn ++ "'")
      tysig = [isaType| Cogent.kind list \<times> Cogent.type \<times> Cogent.type |]
      tydecl = [isaDecl| definition $tn :: "$tysig" where "$(mkId tn) \<equiv> $ty" |]
   in [tydecl]
generateFunctionDefinitionDefn _ _ _ _ = []

generateFunctionDefinition ::
  String
    -> Vec t (TyVarName, Kind)
    -> Type t VarName
    -> Type t VarName
    -> TypedExpr t n a VarName
    -> TheoryDecl I.Type I.Term
generateFunctionDefinition fn k ti to e = undefined


generateTypingLemmaDefn :: Definition TypedExpr a VarName -> Maybe (TheoryDecl I.Type I.Term)
generateTypingLemmaDefn (FunDef _ fn k _ ti to e) = Just $ generateTypingLemma [] fn
generateTypingLemmaDefn _ = Nothing

generateTypingLemma :: [String] -> String -> TheoryDecl I.Type I.Term
generateTypingLemma prevfns fn =
  let safeFn = unIsabelleName $ mkIsabelleName fn
   in LemmaDecl $
        Lemma { lemmaSchematic = True
              , lemmaThmDecl = Just $
                  TheoremDecl
                    { thmName = Just (safeFn ++ "_typecorrect")
                    , thmAttributes = []
                    }
              , lemmaProps =
                [ mkApp (mkId "tyinf_check")
                  [ mkId $ "\\<Xi>"                                             -- external function environment
                  , mkApp (mkId "prod.fst") [mkId $ safeFn ++ "_type"]          -- kind environment
                  , mkList [mkApp (mkId "prod.fst") [mkApp (mkId "prod.snd") [mkId (safeFn ++ "_type")]]] -- typing environemnt
                  , mkId "?C"                                                   -- schematic 'count' context
                  , mkId safeFn                                                 -- function expression
                  , mkApp (mkId "prod.snd") [mkApp (mkId "prod.snd") [mkId (safeFn ++ "_type")]] -- type
                  ]
                ]
              , lemmaProof =
                  Proof
                    [ Method "unfold" [safeFn ++"_def", safeFn ++ "_type_def"]
                    , Method "tactic" ["\\<open>typinfer_tac @{context} @{thms "++(intercalate " " prevfns)++"}\\<close>"]
                    ]
                    ProofDone
              }
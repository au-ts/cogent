--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wwarn #-}

module Cogent.Isabelle.MonoProof where

import Cogent.Common.Syntax
import Cogent.Compiler
import Cogent.Core as CC
import Cogent.Isabelle.Deep hiding (imports)
import Cogent.Dargent.Allocation ( BitRange )
import Cogent.Mono
import Cogent.Util
import Data.Nat (Nat(Zero, Suc))
import Data.Vec
import Cogent.Isabelle.IsabelleName
import Isabelle.ExprTH
import Isabelle.InnerAST as I
import Isabelle.OuterAST as O hiding (Instance)

import Control.Arrow (second)
import Data.Map hiding (map, null)
import System.FilePath ((</>))
import Text.PrettyPrint.ANSI.Leijen as L (Doc, Pretty, pretty, string, (<$>))


monoProof :: (Ord b, Pretty b) => String -> FunMono b -> String -> Doc
monoProof source funMono log =
  let header = (L.string ("(*\n" ++ log ++ "\n*)\n") L.<$>)
      thy = mkProofName source (Just __cogent_suffix_of_mono_proof)
      imports = TheoryImports
                  [ "Cogent.Mono_Tac"
                    -- type_proof must be imported before deep_normal
                  , mkProofName source (Just __cogent_suffix_of_type_proof)
                  , mkProofName source (Just $ __cogent_suffix_of_deep ++ __cogent_suffix_of_stage STGNormal)
                  ]
      body = [ rename funMono, monoRename, monoExprThms source ]
   in header $ L.pretty $ O.Theory thy imports body

monoRename :: TheoryDecl I.Type I.Term
monoRename = TheoryString $ unlines
  [ "local_setup \\<open>"
  , "gen_mono_rename Cogent_functions @{thm rename__assocs_def} \"rename\""
  , "\\<close>"
  ]

monoExprThms :: String -> TheoryDecl I.Type I.Term
monoExprThms src = ContextDecl $ Context "monomorph_sem" $ ctxBody
  where ctxBody = [TheoryString $ unlines
                     [ "ML \\<open>"
                     , "local"
                     , "  (* Get mono-to-poly mapping from the assoc-list for @{term rename} *)"
                     , "  val rename_inverse ="
                     , "    Thm.prop_of @{thm rename__assocs_def}"
                     , "    |> Logic.dest_equals |> snd"
                     , "    |> HOLogic.dest_list"
                     , "    |> map (HOLogic.dest_prod #> apfst HOLogic.dest_prod)"
                     , "    |> map (fn ((poly_f, typs), mono_f) => (HOLogic.dest_string mono_f, (HOLogic.dest_string poly_f, typs)))"
                     , "    |> Symtab.make"
                     , "  val poly_thy = \"" ++ mkProofName src (Just $ __cogent_suffix_of_deep ++ __cogent_suffix_of_stage STGNormal) ++ "\""
                     , "  val mono_thy = \"" ++ mkProofName src (Just __cogent_suffix_of_type_proof) ++ "\""
                     , "  val abbrev_defs = maps (fn thy => Proof_Context.get_thms @{context} (thy ^ \".abbreviated_type_defs\"))"
                     , "                      [poly_thy, mono_thy]"
                     , "  val rename_simps = Proof_Context.get_thms @{context} \"rename_simps\""
                     , "                     handle ERROR _ => []"
                     , "in"
                     , "val monoexpr_thms ="
                     , "  fold (fn f => fn callees =>"
                     , "          gen_monoexpr_thm poly_thy mono_thy @{term rename} rename_inverse callees f"
                     , "                           (abbrev_defs @ rename_simps) @{context}"
                     , "          :: callees)"
                     , "       (* NB: here \"Cogent_functions\" must refer to the list of *monomorphic* Cogent functions."
                     , "        *     Obtain it by importing the TypeProof theory before the Deep_Normal theory."
                     , "        * FIXME: we should assign the poly and mono function lists to distinct names. *)"
                     , "       Cogent_functions []"
                     , "  |> (fn thms => Symtab.make (Cogent_functions ~~ rev thms))"
                     , "end"
                     , "\\<close>"
                     ]]

{-
 - Define a HOL association-list. It will be processed into a function using AssocLookup.thy.
 - (Yes, this is actually much more efficient than writing a function definition. Don't ask.)
 -}
rename :: (Ord b, Pretty b) => FunMono b -> TheoryDecl I.Type I.Term
rename funMono = [isaDecl| definition $alist_name :: "$sig" where "$(mkId alist_name) \<equiv> $def" |]
  where
    alist_name = __fixme "rename__assocs" -- should be parameter
    sig = [isaType| ((string \<times> Cogent.type list  \<times> Cogent.ptr_layout list) \<times> string) list |]
    def = mkList $ map (\(f, inst, instdl, f') -> mkPair (mkTuple [f, inst, instdl]) f') monoTable

    monoTable :: [(Term, Term, Term, Term)]
    monoTable = concatMap mkInst . map (second toList) . toList $ funMono

    subscript fn num =  fn ++ "_" ++ show num

    mkInst :: (Ord b, Pretty b) => (FunName, [(Instance b, Int)]) -> [(Term, Term, Term, Term)]
    mkInst (fn,insts) = let safeName = unIsabelleName $ mkIsabelleName fn
      in  if null insts
            then [([isaTerm| $(mkString safeName) |], [isaTerm| Nil |], [isaTerm| Nil |], [isaTerm| $(mkString safeName) |])]
            else __fixme $ map (\((tys,dls),num) -> ([isaTerm| $(mkString safeName) |], mkTyList tys, mkDlList dls, [isaTerm| $(mkString (subscript safeName num)) |])) insts  -- FIXME: currently second part of instance (data layouts) is ignored

    mkTyList :: (Ord b, Pretty b) => [CC.Type 'Zero b] -> Term
    mkTyList = I.mkList . map (deepType id (empty, 0))

    mkDlList :: [CC.DataLayout BitRange] -> Term
    mkDlList = I.mkList . map deepDataLayout
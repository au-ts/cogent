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

module Cogent.MonoProof where

import Cogent.Common.Syntax
import Cogent.Compiler
import Cogent.Core as CC
import Cogent.Deep hiding (imports)
import Cogent.Mono
import Cogent.Util
import Cogent.Vec
import Isabelle.ExprTH
import Isabelle.InnerAST as I
import Isabelle.OuterAST as O hiding (Instance)

import Control.Arrow (second)
import Data.Map hiding (map, null)
import System.FilePath ((</>))
import Text.PrettyPrint.ANSI.Leijen as L (Doc, pretty, string, (<$>))


monoProof :: String -> FunMono -> String -> Doc
monoProof source funMono log =
  let header = (L.string ("(*\n" ++ log ++ "\n*)\n") L.<$>)
      thy = mkProofName source (Just __cogent_suffix_of_mono_proof)
      imports = TheoryImports
                  [ __cogent_root_dir </> "cogent/isa/Mono_Tac"
                    -- type_proof must be imported before deep_normal
                  , mkProofName source (Just __cogent_suffix_of_type_proof)
                  , mkProofName source (Just $ __cogent_suffix_of_deep ++ __cogent_suffix_of_stage STGNormal)
                  ]
      body = [ rename funMono, monoRename, monoExprThms source ]
   in header $ L.pretty $ O.Theory thy imports body

monoRename :: TheoryDecl I.Type I.Term
monoRename = TheoryString $ unlines
  [ "local_setup {*"
  , "gen_mono_rename Cogent_functions @{thm rename__assocs_def} \"rename\""
  , "*}"
  ]

monoExprThms :: String -> TheoryDecl I.Type I.Term
monoExprThms src = ContextDecl $ Context "value_sem" $ ctxBody
  where ctxBody = [TheoryString $ unlines
                     [ "ML {*"
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
                     , "*}"
                     ]]

{-
 - Define a HOL association-list. It will be processed into a function using AssocLookup.thy.
 - (Yes, this is actually much more efficient than writing a function definition. Don't ask.)
 -}
rename :: FunMono -> TheoryDecl I.Type I.Term
rename funMono = [isaDecl| definition $alist_name :: "$sig" where "$(mkId alist_name) \<equiv> $def" |]
  where
    alist_name = __fixme "rename__assocs" -- should be parameter
    sig = [isaType| ((string \<times> Cogent.type list) \<times> string) list |]
    def = mkList $ map (\(f, inst, f') -> mkPair (mkPair f inst) f') monoTable

    monoTable :: [(Term, Term, Term)]
    monoTable = concatMap mkInst . map (second toList) . toList $ funMono

    mkInst :: (FunName, [(Instance, Int)]) -> [(Term, Term, Term)]
    mkInst (fn,insts) = if null insts
                          then [([isaTerm| $(mkString fn) |], [isaTerm| Nil |], [isaTerm| $(mkString fn) |])]
                          else map (\(tys,num) -> ([isaTerm| $(mkString fn) |], mkTyList tys, [isaTerm| $(mkString $ fn ++ "_" ++ show num) |])) insts

    mkTyList :: [CC.Type 'Zero] -> Term
    mkTyList = I.mkList . map (deepType id (empty, 0))

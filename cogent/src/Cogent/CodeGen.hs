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
{-# LANGUAGE PackageImports #-}

module Cogent.CodeGen where

import Cogent.C.Compile (compile, GenState, TableCTypes)
import Cogent.C.Render  (render)
import Cogent.C.Syntax
import Cogent.Common.Syntax
import Cogent.Core (Definition, Type, TypedExpr)
import Cogent.Haskell.HscGen (hscModule)
import Cogent.Haskell.HscSyntax (HscModule)
import Cogent.Mono (Instance)
import Cogent.Vec

import Data.Map as M
import Data.Set as S
import qualified "language-c-quote" Language.C as C (Definition)

cgen :: FilePath
     -> FilePath
     -> [Definition TypedExpr VarName]
     -> [(Type 'Zero, String)]
     -> M.Map FunName (M.Map Instance Int)
     -> String
     -> ([C.Definition], [C.Definition], [(TypeName, S.Set [CId])], [TableCTypes], HscModule, GenState)
cgen hName proofName defs ctygen insts log = 
  let (enums,tydefns,fndecls,disps,tydefs,fndefns,absts,corres,st) = compile defs ctygen insts
      (h,c) = render hName (enums++tydefns++fndecls++disps++tydefs) fndefns log
      hsc = hscModule proofName hName tydefns enums
   in (h,c,absts,corres,hsc,st)



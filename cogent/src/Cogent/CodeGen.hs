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

import Cogent.C.Compile (compile, ffiFuncs, GenState, TableCTypes)
import Cogent.C.Render  (render)
import Cogent.C.Syntax
import Cogent.Common.Syntax
import Cogent.Compiler
import Cogent.Core (Definition, Type, TypedExpr)
import Cogent.Haskell.FFIGen (ffiHs)
import Cogent.Haskell.HscGen (ffiHsc)
import Cogent.Mono (Instance)
import Data.Nat (Nat(Zero,Suc))
import Data.Vec

import Control.Lens ((^.))
import Data.Map as M
import Data.Set as S
import qualified "language-c-quote" Language.C as C (Definition)
-- import System.FilePath ((-<.>))
import Text.PrettyPrint as PP (Doc)
import Text.PrettyPrint.ANSI.Leijen as Leijen

cgen :: FilePath
     -> FilePath
     -> FilePath
     -> [Definition TypedExpr VarName]
     -> [(Type 'Zero, String)]
     -> M.Map FunName (M.Map Instance Int)
     -> String
     -> ([C.Definition], [C.Definition], [(TypeName, S.Set [CId])], [TableCTypes], Leijen.Doc, PP.Doc, GenState)
cgen hName hscName hsName defs ctygen insts log =
  let (enums,tydefns,fndecls,disps,tydefs,fndefns,absts,corres,st) = compile defs ctygen insts
      (h,c) = render hName (enums++tydefns++fndecls++disps++tydefs) fndefns log
      hsc = ffiHsc hscName hName tydefns enums log
      hs  = ffiHs  (st^.ffiFuncs) hsName hscName fndecls log
   in (h,c,absts,corres,hsc,hs,st)



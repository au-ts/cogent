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

module Cogent.CodeGen where

import Cogent.C.Compile (compile, TableCTypes)
import Cogent.C.GenState (ffiFuncs, GenState)
import Cogent.C.Render  (render)
import Cogent.C.Syntax
import Cogent.Common.Syntax
import Cogent.Compiler
import Cogent.Core (Definition, Type, TypedExpr)
#ifdef WITH_HASKELL
import Cogent.Haskell.FFIGen (ffiHs)
import Cogent.Haskell.HscGen (ffiHsc)
#endif
import Cogent.Mono (Instance)
import Data.Nat (Nat(Zero,Suc))
import Data.Vec

import Lens.Micro ((^.))
import Data.Map as M
import Data.Set as S
import qualified Language.C as C (Definition)
import Text.PrettyPrint.ANSI.Leijen as Leijen

cgen :: FilePath
     -> [FilePath]
     -> FilePath
     -> FilePath
     -> [Definition TypedExpr VarName]
     -> [(Type 'Zero, String)]
     -> String
     -> ([C.Definition], [C.Definition], [(TypeName, S.Set [CId])], [TableCTypes], Leijen.Doc, String, GenState)
cgen hName cNames hscName hsName defs ctygen log =
  let (enums,tydefns,fndecls,disps,tysyms,fndefns,absts,corres,fclsts,st) = compile defs ctygen
      (h,c) = render hName (enums++tydefns++fndecls++disps++tysyms) fndefns log
#ifdef WITH_HASKELL
      hsc = ffiHsc hscName cNames tydefns enums absts fclsts log
      hs  = ffiHs (st^.ffiFuncs) hsName hscName fndecls log
#else
      hsc = mempty
      hs = mempty
#endif
   in (h,c,absts,corres,hsc,hs,st)



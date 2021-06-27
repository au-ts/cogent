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

module Cogent.C (
  -- * Re-export everything in Cogent.C.*
    module Cogent.C.Expr
  , module Cogent.C.Monad
  , module Cogent.C.Render
  , module Cogent.C.Syntax
  , module Cogent.C.Type
  , cgen
  ) where

import Cogent.C.Expr
import Cogent.C.Monad
import Cogent.C.Render
import Cogent.C.Syntax
import Cogent.C.Type
import Cogent.Common.Syntax
import Cogent.Compiler
import Cogent.Core (Definition, Pragma_, Type, TypedExpr)
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
     -> [Definition PosTypedExpr VarName VarName]
     -> Maybe GenState
     -> [(Type 'Zero VarName, String)]
     -> [Pragma_ VarName]
     -> String
     -> ([C.Definition], [C.Definition], [(TypeName, S.Set [CId])], [TableCTypes], [NewTableCTypes], Leijen.Doc, String, GenState)
cgen hName cNames hscName hsName defs mcache ctygen pragmas log =
  let (enums,tydefns,fndecls,disps,tysyms,fndefns,absts,corres,corres',fclsts,st) = compile defs mcache ctygen pragmas
      (h,c) = render hName (enums++tydefns++fndecls++disps++tysyms) fndefns log
#ifdef WITH_HASKELL
      hsc = ffiHsc hscName cNames tydefns enums absts fclsts log
      hs  = ffiHs (st^.ffiFuncs) hsName hscName fndecls log
#else
      hsc = mempty
      hs = mempty
#endif
   in (h,c,absts,corres,corres',hsc,hs,st)



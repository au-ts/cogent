--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

module Cogent.TypeCheck where

import COGENT.TypeCheck.Generator
import COGENT.TypeCheck.Base

-- tc :: [(SourcePos, TopLevel LocType VarName LocExpr)]
--    -> ((Either (TypeError, [ErrorContext]) [TopLevel RawType TypedName TypedExpr], WarningErrorLog), TCState)
-- tc defs = undefined

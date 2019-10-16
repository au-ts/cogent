-- |
-- Module      : Minigent.TC.Assign
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- A module for solver assignments to unification variables.
--
-- May be imported unqualified.
module Minigent.TC.Assign
  ( Assign (..) 
  , substAssign 
  ) where 

import Minigent.Syntax
import Minigent.Syntax.Utils
import qualified Minigent.Syntax.Utils.Rewrite as Rewrite

-- | An assignment to a unification variable.
data Assign = TyAssign VarName Type
            | RowAssign VarName Row
            | SigilAssign VarName Sigil
            | RecParAssign VarName RecPar

-- | Apply an assignment to a unification variable to a type.
substAssign :: Assign -> Rewrite.Rewrite Type
substAssign (TyAssign v t) = substUV (v, t)
substAssign (RowAssign v t) = substRowV (v, t)
substAssign (SigilAssign v t) = substSigilV (v, t)
substAssign (RecParAssign v1 v2) = substRecPar (v1, v2)


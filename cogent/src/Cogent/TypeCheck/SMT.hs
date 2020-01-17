
--
-- Copyright 2019, Data61
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

module Cogent.TypeCheck.SMT where

import Cogent.TypeCheck.Base
import Cogent.Surface as S

import Language.SMTLib2 as SMT


sexprToSmt :: (Backend b) => TCSExpr -> SMT b (SMT.Expr b BoolType)
sexprToSmt (SU t x) = undefined  -- declareVarNamed bool ('?':show x)
sexprToSmt (SE t e) = undefined  -- exprToSmt t e
  -- where
  --   exprToSmt :: (Backend b) => S.Expr RawType RawPatn RawIrrefPatn SExpr -> SMT b (SMT.Expr b t)
  --   exprToSmt (PrimOp op es)
  --     | op `elem` ["not"], [e] <- es = undefined
  --     | op `elem` ["&&", "||", "<", "<=", ">", ">="] = undefined


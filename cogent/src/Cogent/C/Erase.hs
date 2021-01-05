--
-- Copyright 2021, Data61
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
{-# LANGUAGE UnicodeSyntax #-}

module Cogent.C.Erase (erase) where

import Cogent.Common.Syntax
import Cogent.Core
-- import Data.Nat

import Data.Generics.Schemes (everywhere)

-- ======================================================================
-- Erases refinement types from the program, and prepares for C code gen.
-- ======================================================================

erase ∷ [Definition TypedExpr VarName b] → [Definition TypedExpr VarName b]
erase ds = fmap erase1 ds

erase1 ∷ Definition TypedExpr VarName b → Definition TypedExpr VarName b
erase1 (FunDef attr fn γ δ τi τo e) = FunDef attr fn γ δ (eraseT τi) (eraseT τo) (eraseE e)
erase1 (AbsDecl attr fn γ δ τi τo) = AbsDecl attr fn γ δ (eraseT τi) (eraseT τo)
erase1 (TypeDef tn ps mτ) = TypeDef tn ps (fmap eraseT mτ)

-- FIXME: Currently doesn't assume so. / zilinc
-- XXX | ASSUME the input type is normalised (i.e. refinement at the outermost level)
eraseT ∷ Type t b → Type t b
eraseT (TRefine t _) = t
eraseT (TFun t1 t2) = TFun (eraseT t1) (eraseT t2)
eraseT t = fmapT eraseT t

eraseE ∷ TypedExpr t v VarName b → TypedExpr t v VarName b
eraseE (TE t e) = TE (eraseT t) (fmapE eraseE $ fmapTypeE eraseT e)

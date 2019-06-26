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

{-# LANGUAGE DeriveDataTypeable #-}

module Cogent.Dargent.Surface where

import Cogent.Common.Syntax (FieldName, TagName, RepName, Size)
import Cogent.Compiler (__fixme)

import Data.Data
import Text.Parsec.Pos (SourcePos)

-- | For gradual transition to eliminate Rep from the language.
type DataLayoutSize = RepSize
type DataLayoutDecl = RepDecl
type DataLayoutExpr = RepExpr

-- | TODO: Rename to DataLayoutSize
data RepSize 
  = Bytes Size
  | Bits  Size
  | Add   RepSize RepSize
  -- Future options, sizeof, offsetof, "after"
  deriving (Show, Data, Eq, Ord)

-- | TODO: Rename to DataLayoutDecl
data RepDecl
  = RepDecl SourcePos RepName RepExpr
  deriving (Show, Data, Eq, Ord)

-- | TODO: Rename to DataLayoutExpr
data RepExpr
  = Prim    RepSize
  | Record  [(FieldName, SourcePos, RepExpr)] 
  | Variant RepExpr [(TagName, SourcePos, Size, RepExpr)]
  | Offset  RepExpr RepSize
  | RepRef  RepName
  deriving (Show, Data, Eq, Ord)

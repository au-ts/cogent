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

module Cogent.Dargent.Surface
  ( module Cogent.Dargent.Surface
  , module Cogent.Dargent.Common
  )
where

import Cogent.Common.Syntax (FieldName, TagName, RepName, Size)
import Cogent.Compiler (__fixme)
import Cogent.Dargent.Common

import Data.Data
import Text.Parsec.Pos (SourcePos)

data DataLayoutSize 
  = Bytes Size
  | Bits  Size
  | Add   DataLayoutSize DataLayoutSize
  -- Future options, sizeof, offsetof, "after"
  deriving (Show, Data, Eq, Ord)

data DataLayoutDecl
  = DataLayoutDecl SourcePos RepName DataLayoutExpr
  deriving (Show, Data, Eq, Ord)

data DataLayoutExpr
  = Prim    DataLayoutSize
  | Record  [(FieldName, SourcePos, DataLayoutExpr)]
  | Variant DataLayoutExpr [(TagName, SourcePos, Size, DataLayoutExpr)]
  | Offset  DataLayoutExpr DataLayoutSize
  | RepRef  RepName
  deriving (Show, Data, Eq, Ord)

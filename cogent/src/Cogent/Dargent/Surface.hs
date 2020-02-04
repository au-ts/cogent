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
{-# LANGUAGE PatternSynonyms #-}

module Cogent.Dargent.Surface
  ( module Cogent.Dargent.Surface
  , TCDataLayout ( TLPrim, TLRecord, TLVariant, TLOffset, TLRepRef, TLPtr, TLVar
#ifdef BUILTIN_ARRAYS
                 , TLArray)
#else
                 )
#endif
  , DataLayoutExpr ( DLPrim, DLRecord, DLVariant, DLOffset, DLRepRef, DLPtr, DLVar
#ifdef BUILTIN_ARRAYS
                   , DLArray)
#else
                   )
#endif
  )
where

import Cogent.Common.Syntax (FieldName, TagName, RepName, Size, DLVarName)
import Cogent.Compiler (__fixme)

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

-- 'holes' are where subexpressions define the shape of the layout.
-- This is to allow us, in future, to use () to defer to the contained layouts
--  / v.jackson ~ 2019.08.23
data DataLayoutExpr' e
  = Prim    DataLayoutSize
  | Record  [(FieldName, SourcePos, e)]
  | Variant (DataLayoutExpr' e) [(TagName, SourcePos, Size, e)]
#ifdef BUILTIN_ARRAYS
  | Array   e SourcePos
#endif
  | Offset  (DataLayoutExpr' e) DataLayoutSize
  | RepRef  RepName
  | LVar    DLVarName
  | Ptr
  deriving (Show, Data, Eq, Ord)

-- We use 'tying the knot' here so we can make single level layouts later
newtype DataLayoutExpr = DL { unDataLayoutExpr :: DataLayoutExpr' DataLayoutExpr }
  deriving (Show, Data, Eq, Ord)

data TCDataLayout = TL { unTCDataLayout :: DataLayoutExpr' TCDataLayout }
                  | TLU Int
                  deriving (Show, Data, Eq, Ord)

pattern DLPrim s       = DL (Prim s)
pattern DLRecord ps    = DL (Record ps)
pattern DLVariant t ps = DL (Variant t ps)
#ifdef BUILTIN_ARRAYS
pattern DLArray e s    = DL (Array e s)
#endif
pattern DLOffset e s   = DL (Offset e s)
pattern DLRepRef n     = DL (RepRef n)
pattern DLVar n        = DL (LVar n)
pattern DLPtr          = DL Ptr

pattern TLPrim s       = TL (Prim s)
pattern TLRecord ps    = TL (Record ps)
pattern TLVariant t ps = TL (Variant t ps)
#ifdef BUILTIN_ARRAYS
pattern TLArray e s    = TL (Array e s)
#endif
pattern TLOffset e s   = TL (Offset e s)
pattern TLRepRef n     = TL (RepRef n)
pattern TLVar n        = TL (LVar n)
pattern TLPtr          = TL Ptr

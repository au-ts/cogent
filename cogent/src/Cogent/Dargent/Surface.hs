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
{-# LANGUAGE DeriveGeneric #-}

module Cogent.Dargent.Surface
  ( module Cogent.Dargent.Surface
  , DataLayoutExpr ( DLPrim, DLRecord, DLVariant, DLOffset, DLAfter, DLEndian, DLRepRef, DLPtr, DLVar
#ifdef BUILTIN_ARRAYS
                   , DLArray)
#else
                   )
#endif
  )
where

import Cogent.Common.Syntax (FieldName, TagName, RepName, Size, DLVarName)
import Cogent.Compiler (__fixme, __todo, __impossible)
import Cogent.Dargent.Util

import Data.Data
import Data.Binary
import GHC.Generics (Generic)
import Text.Parsec.Pos (SourcePos)

-- Little endian, Big endian or 'Machine' endian
data Endianness = LE | BE | ME
  deriving (Show, Data, Eq, Ord, Generic)

instance Binary Endianness

data DataLayoutSize
  = Bytes Size
  | Bits  Size
  | Add   DataLayoutSize DataLayoutSize
  -- Future options, sizeof, offsetof, "after"
  deriving (Show, Data)

instance Eq DataLayoutSize where
  (==) n m = evalSize n == evalSize m

instance Ord DataLayoutSize where
  (<=) n m = evalSize n <= evalSize m

evalSize :: DataLayoutSize -> Size
evalSize (Bytes b) = b * 8
evalSize (Bits b)  = b
evalSize (Add a b) = evalSize a + evalSize b

data DataLayoutDecl
  = DataLayoutDecl SourcePos RepName [DLVarName] DataLayoutExpr
  deriving (Show, Data, Eq, Ord)

-- 'holes' are where subexpressions define the shape of the layout.
-- This is to allow us, in future, to use () to defer to the contained layouts
--  / v.jackson ~ 2019.08.23
data DataLayoutExpr' e
  = Prim    DataLayoutSize
  | Record  [(FieldName, SourcePos, e)]
  | Variant e [(TagName, SourcePos, Integer, e)]
#ifdef BUILTIN_ARRAYS
  | Array   e Int SourcePos  -- for now use int for length
#endif
  | Offset  e DataLayoutSize
  | Endian  e Endianness
  | RepRef  RepName [e]
  | After   e FieldName  -- only valid inside a record layout
  | LVar    DLVarName
  | Ptr
  deriving (Show, Data, Eq, Ord)

-- We use 'tying the knot' here so we can make single level layouts later
newtype DataLayoutExpr = DL { unDataLayoutExpr :: DataLayoutExpr' DataLayoutExpr }
  deriving (Show, Data, Eq, Ord)

pattern DLPrim s       = DL (Prim s)
pattern DLRecord ps    = DL (Record ps)
pattern DLVariant t ps = DL (Variant t ps)
#ifdef BUILTIN_ARRAYS
pattern DLArray e l s  = DL (Array e l s)
#endif
pattern DLOffset e s   = DL (Offset e s)
pattern DLEndian e n   = DL (Endian e n)
pattern DLRepRef n s   = DL (RepRef n s)
pattern DLAfter e f    = DL (After e f)
pattern DLVar n        = DL (LVar n)
pattern DLPtr          = DL Ptr


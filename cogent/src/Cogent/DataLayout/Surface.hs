module Cogent.DataLayout.Surface where
import Cogent.Common.Syntax (FieldName, TagName, RepName, Size)
import Text.Parsec.Pos (SourcePos)
import Cogent.Compiler (__fixme)

{- SURFACE DATALAYOUT TYPES -}

-- For gradual transition to eliminate Rep from the language.
type DataLayoutSize = RepSize
type DataLayoutDecl = RepDecl
type DataLayoutExpr = RepExpr

-- Rename to DataLayoutSize
data RepSize 
  = Bytes Size
  | Bits  Size
  | Add   RepSize RepSize
  -- Future options, sizeof, offsetof, "after"
  deriving (Show, Eq, Ord)

-- Rename to DataLayoutDecl
data RepDecl
  = RepDecl SourcePos RepName RepExpr
  deriving (Show, Eq, Ord)

-- Rename to DataLayoutExpr
data RepExpr
  = Prim    RepSize
  | Record  [(FieldName, SourcePos, RepExpr)] 
  | Variant RepExpr [(TagName, SourcePos, Size, RepExpr)]
  | Offset  RepExpr RepSize
  | RepRef  RepName
  deriving (Show, Eq, Ord)
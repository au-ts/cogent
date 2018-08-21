module Cogent.DataLayout.Surface where
import Cogent.Common.Syntax (FieldName, TagName, RepName)
import Cogent.DataLayout.Syntax (SourcePos)

{- SURFACE DATALAYOUT TYPES -}

-- Rename to DataLayoutSize
data RepSize 
  = Bytes Integer
  | Bits  Integer
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
  | Variant RepExpr [(TagName, SourcePos, Integer, RepExpr)]
  | Offset  RepExpr RepSize
  | RepRef  RepName
  deriving (Show, Eq, Ord)
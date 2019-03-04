module Cogent.Dargent.Surface where
import Cogent.Common.Syntax (FieldName, TagName, RepName, Size)
import Text.Parsec.Pos (SourcePos)
import Cogent.Compiler (__fixme)

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
  deriving (Show, Eq, Ord)

-- | TODO: Rename to DataLayoutDecl
data RepDecl
  = RepDecl SourcePos RepName RepExpr
  deriving (Show, Eq, Ord)

-- | TODO: Rename to DataLayoutExpr
data RepExpr
  = Prim    RepSize
  | Record  [(FieldName, SourcePos, RepExpr)] 
  | Variant RepExpr [(TagName, SourcePos, Size, RepExpr)]
  | Offset  RepExpr RepSize
  | RepRef  RepName
  deriving (Show, Eq, Ord)

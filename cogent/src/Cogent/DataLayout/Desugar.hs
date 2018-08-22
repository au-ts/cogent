module Cogent.DataLayout.Desugar where
import Data.Map (Map)

import Cogent.Compiler (__fixme)
import Cogent.Common.Syntax (RepName)
import Cogent.DataLayout.Surface (RepExpr)
import Cogent.DataLayout.Core


type DataLayoutName = RepName -- TODO: eliminate RepName
type DataLayoutExpr = RepExpr


type DataLayoutDefs = Map DataLayoutName (DataLayout BitRange) 

-- TODO: Split dataLayoutSurfaceToCore in Cogent.DataLayout.Typecheck
-- into a type checking function and this desugar function!

desugarDataLayout :: DataLayoutDefs -> DataLayoutExpr -> DataLayout BitRange
desugarDataLayout _ _ = __fixme $ UnitLayout


module Cogent.DataLayout.Desugar where
import Data.Map (Map)

import Cogent.Compiler 				(__fixme, __impossible)
import Cogent.Common.Syntax 		(DataLayoutName)
import Cogent.Common.Types 			(Sigil(Unboxed, Boxed))
import Cogent.DataLayout.Surface 	(DataLayoutExpr)
import Cogent.DataLayout.Core

-- TODO: Split dataLayoutSurfaceToCore in Cogent.DataLayout.Typecheck
-- into a type checking function and this desugar function!

desugarDataLayout :: DataLayoutExpr -> DataLayout BitRange
desugarDataLayout _ = __fixme $ UnitLayout


-- Type checking, and the post type checking normalisation (Cogent.TypeCheck.Post)
-- guarantees that Boxed types have an associated layout
desugarSigil :: Sigil (Maybe DataLayoutExpr) -> Sigil (DataLayout BitRange)
desugarSigil Unboxed              = Unboxed
desugarSigil (Boxed ro (Just l))  = Boxed ro (desugarDataLayout l)
desugarSigil (Boxed ro Nothing)   = __impossible $ "desugarSigil (Nothing is not in WHNF)"
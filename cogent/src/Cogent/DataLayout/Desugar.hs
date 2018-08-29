module Cogent.DataLayout.Desugar where
import Data.Map (Map)
import Data.Map as M

import Cogent.Compiler            ( __fixme
                                  , __impossible
                                  )
import Cogent.Common.Syntax       ( DataLayoutName
                                  , Size
                                  )
import Cogent.Common.Types        ( Sigil(Unboxed, Boxed))
import Cogent.DataLayout.Surface  ( DataLayoutExpr
                                  , DataLayoutSize
                                  , RepSize(Bytes, Bits, Add)
                                  , RepExpr(RepRef, Prim, Offset, Record, Variant)
                                  )
import Cogent.DataLayout.Core

-- TODO: Split dataLayoutSurfaceToCore in Cogent.DataLayout.Typecheck
-- into a type checking function and this desugar function!
desugarSize :: DataLayoutSize -> Size
desugarSize (Bytes b) = b * 8
desugarSize (Bits b)  = b
desugarSize (Add a b) = desugarSize a + desugarSize b

desugarDataLayout :: DataLayoutExpr -> DataLayout BitRange
desugarDataLayout (RepRef _) = __impossible "desugarDataLayout (Called after normalisation)"
desugarDataLayout (Prim size)
  | bitSize <- desugarSize size
  , bitSize > 0
    = PrimLayout (BitRange bitSize 0)
  | otherwise = UnitLayout

desugarDataLayout (Offset dataLayoutExpr offsetSize) =
  offset (desugarSize offsetSize) (desugarDataLayout dataLayoutExpr)

desugarDataLayout (Record fields) =
  RecordLayout $ M.fromList fields'
  where fields' = fmap (\(fname, pos, layout) -> (fname, (desugarDataLayout layout, pos))) fields

desugarDataLayout (Variant tagExpr alts) =
  SumLayout tagBitRange $ M.fromList alts'
  where
    tagBitRange = case desugarDataLayout tagExpr of
      PrimLayout range -> range
      _                -> __impossible $ "desugarDataLayout (Called after typecheck, tag layouts known to be single range)"

    alts' = fmap (\(aname, pos, size, layout) -> (aname, (size, desugarDataLayout layout, pos))) alts


-- Type checking, and the post type checking normalisation (Cogent.TypeCheck.Post)
-- guarantees that Boxed types have an associated layout
desugarSigil :: Sigil (Maybe DataLayoutExpr) -> Sigil (DataLayout BitRange)
desugarSigil Unboxed              = Unboxed
desugarSigil (Boxed ro (Just l))  = Boxed ro (desugarDataLayout l)
desugarSigil (Boxed ro Nothing)   = __impossible $ "desugarSigil (Nothing is not in WHNF)"
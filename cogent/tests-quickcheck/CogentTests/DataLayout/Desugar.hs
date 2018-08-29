

prop_returnTrip = propReturnTrip 30
propReturnTrip :: Size -> RepName -> SourcePos -> Property
propReturnTrip size repName pos =
  forAll (genDataLayout size (InDecl repName pos)) $ \(layout, alloc) ->
  let
    repDecl = RepDecl pos repName (toRepExpr layout)
  in
    case dataLayoutSurfaceToCore M.empty repDecl of
      Left _                  -> False
      Right (layout', alloc') -> layout == layout' && (toSet alloc) == (toSet alloc')  
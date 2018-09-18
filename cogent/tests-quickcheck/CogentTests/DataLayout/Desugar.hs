{-# LANGUAGE TemplateHaskell #-}
module CogentTests.DataLayout.Desugar where

import Test.QuickCheck
import Test.QuickCheck.All
import CogentTests.DataLayout.Core
import CogentTests.DataLayout.TypeCheck (undesugarDataLayout)
import CogentTests.Core (genLayoutableType)
import Cogent.DataLayout.CoreTypeCheck (matchesDataLayout, checkDataLayout)
import Cogent.DataLayout.Desugar

prop_returnTrip :: Property
prop_returnTrip =
  forAll (genDataLayout size) $ \(layout, _) ->
    desugarDataLayout (undesugarDataLayout layout) == layout
  where size = 30

prop_constructDataLayoutMatchingLayout =
  forAll (sized genLayoutableType) $ \coreType ->
    matchesDataLayout coreType (constructDataLayout coreType)

prop_constructDataLayoutProducesValidLayout = 
  forAll (sized genLayoutableType) $ \coreType ->
    checkDataLayout (constructDataLayout coreType)


return []
testAll = $quickCheckAll
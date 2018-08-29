{-# LANGUAGE TemplateHaskell #-}
module CogentTests.DataLayout.Desugar where

import Test.QuickCheck
import Test.QuickCheck.All
import CogentTests.DataLayout.Core
import CogentTests.DataLayout.TypeCheck (undesugarDataLayout)
import Cogent.DataLayout.Desugar


prop_returnTrip :: Property
prop_returnTrip =
  forAll (genDataLayout size) $ \(layout, _) ->
    desugarDataLayout (undesugarDataLayout layout) == layout
  where size = 30

return []
testAll = $quickCheckAll
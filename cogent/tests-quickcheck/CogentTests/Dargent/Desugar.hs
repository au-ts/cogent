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

{-# LANGUAGE TemplateHaskell #-}
module CogentTests.Dargent.Desugar where

import Test.QuickCheck
import Test.QuickCheck.All
import CogentTests.Dargent.Core
import CogentTests.Dargent.TypeCheck (undesugarDataLayout)
import CogentTests.Core (genLayoutableType)
import Cogent.Dargent.Core
import Cogent.Dargent.CoreTypeCheck (matchesDataLayout, checkDataLayout)
import Cogent.Dargent.Desugar

prop_returnTrip :: Property
prop_returnTrip =
  forAll (genDataLayout size) $ \(Layout layout, _) ->  -- FIXME: CLayout / zilinc
    desugarDataLayout (undesugarDataLayout layout) == Layout layout
  where size = 30

prop_constructDataLayoutMatchingLayout =
  forAll (sized genLayoutableType) $ \coreType ->
    matchesDataLayout coreType (constructDataLayout coreType)

prop_constructDataLayoutProducesValidLayout =
  forAll (sized genLayoutableType) $ \coreType ->
    checkDataLayout (constructDataLayout coreType)

return []
testAll = $quickCheckAll

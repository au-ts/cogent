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
import CogentTests.Dargent.TypeCheck (sugarDataLayout)
import CogentTests.Core (genLayoutableType)
import Cogent.Dargent.Core
import Cogent.Dargent.TypeCheck
import Cogent.Desugar
import Cogent.Util

import Control.Monad.RWS.Strict
import qualified Data.Map as M
import Data.Vec

prop_returnTrip :: Property
prop_returnTrip =
  forAll (genDataLayout size) $ \(Layout layout, _) ->  -- FIXME: CLayout / zilinc
    fst (flip3 evalRWS state reader (runDS $ desugarLayout (sugarDataLayout layout))) == Layout layout
  where size = 30
        reader = (M.empty, M.empty, [])
        state = DsState Nil Nil Nil 0 0 []

return []
testAll = $quickCheckAll

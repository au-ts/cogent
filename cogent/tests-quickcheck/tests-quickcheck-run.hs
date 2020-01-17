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

module Main where

import Test.QuickCheck
import Control.Monad
import System.Exit
import CogentTests.Dargent.TypeCheck
import CogentTests.Dargent.Core
import CogentTests.Dargent.Desugar
import CogentTests.Dargent.CodeGen

main = do
  -- compileSanityCheck  -- it just prints the C code for manual inspection
  isSuccess <- and <$> sequenceA
      [ CogentTests.Dargent.TypeCheck.testAll
      , CogentTests.Dargent.Core.testAll
      , CogentTests.Dargent.Desugar.testAll
      ]
  if isSuccess
    then exitSuccess
    else exitFailure

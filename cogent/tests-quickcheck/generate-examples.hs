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

-- import System.Directory
import Prelude

import System.Directory (createDirectoryIfMissing)
import Test.QuickCheck
import Control.Monad
import System.Exit
import CogentTests.Dargent.Core
import Cogent.Dargent.Allocation
import CogentTests.Dargent.TypeWithLayout (genTestLayoutProg)
import Cogent.Surface (RawType( RT ), Type(TRecord))
import Data.List (intercalate)

import Text.PrettyPrint.ANSI.Leijen (Pretty, pretty)
import Cogent.PrettyPrint


{-
This creates a directory dargent-verifs in the tests directory
with a bunch of examples of record types with custom layouts.
A configuration file .yaml is also generated, creating a test
named 'pass-dargent-verifs' and testing the CorresProof phase
for these examples.
-}
main = do
  _ <- createDirectoryIfMissing False dir
  exs <- sample' (genTestLayoutProg size)
  let filenames = map (\ n -> "ex" ++ show n ++ ".cogent") [1..(length exs)]
  _ <- writeFile (dir ++ "/config.yaml") 
    ("- test_name: pass-dargent-verifs\n  files:" ++
    intercalate "" (map (\ s -> "\n    - " ++ s) filenames)
    ++ "\n  expected_result: pass\n  phase: 'corres_proof'")
  _ <- sequence $ zipWith (\ prog filename -> writeFile (dir ++ "/" ++ filename) (show prog)) exs filenames
  return ()
  where
    size = 300
    dir =  "tests/tests/dargent-verifs"

{-# LANGUAGE TemplateHaskell #-}
module Main where
import Test.QuickCheck
import Control.Monad
import System.Exit
import CogentTests.DataLayout.TypeCheck
import CogentTests.DataLayout.Core
import Cogent.DataLayout.Core
import Cogent.DataLayout.Desugar
import Cogent.DataLayout.TypeCheck

main = do
  isSuccess <- foldr <$> pure (&&) <*> pure True <*> sequenceA
      [ CogentTests.DataLayout.TypeCheck.testAll
      , CogentTests.DataLayout.Core.testAll
      ]
  if isSuccess
    then exitSuccess
    else exitFailure
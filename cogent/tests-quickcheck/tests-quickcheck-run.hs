{-# LANGUAGE TemplateHaskell #-}
module Main where
import Test.QuickCheck
import Control.Monad
import System.Exit
import CogentTests.DataLayout.TypeCheck
import CogentTests.DataLayout.Core

main = do
  isSuccess <- foldr <$> pure (&&) <*> pure True <*> sequenceA
      [ CogentTests.DataLayout.TypeCheck.testAll
      , CogentTests.DataLayout.Core.testAll
      ]
  if isSuccess
    then exitSuccess
    else exitFailure

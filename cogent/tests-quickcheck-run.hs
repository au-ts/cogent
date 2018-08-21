{-# LANGUAGE TemplateHaskell #-}
module Main where
import Test.QuickCheck
import CogentTests.DataLayout.TypeCheck
import CogentTests.DataLayout.Core

main = do
    CogentTests.DataLayout.TypeCheck.testAll
    CogentTests.DataLayout.Core.testAll
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
import qualified Syntax
import qualified Example
import System.Environment (getArgs)
import System.Exit (die)

main :: IO ()
main = do
  args <- getArgs
  case args of
    "pretty-printer":[] ->
      Syntax.test 10
    "example":fp:[] ->
      Example.example fp
    "update-expected":fp:[] ->
      Example.updateExpected fp
    _ -> die "Invalid test case to run."

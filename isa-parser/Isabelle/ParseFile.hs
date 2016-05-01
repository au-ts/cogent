--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

module Isabelle.Main
where

-- system imports
import System.Environment
import System.Exit
import Text.Printf
import Text.Parsec
import Text.Parsec.String
import Text.PrettyPrint.ANSI.Leijen

-- friends
import Isabelle.Parser

getFile :: IO (Maybe String)
getFile = do
  args <- getArgs
  return $ case args of 
             []     -> Nothing
             file:_ -> Just file

exitOnNothing :: String -> IO (Maybe a) -> IO a
exitOnNothing errorString io = do
  mb <- io
  case mb of
    Nothing -> putStrLn errorString >> exitWith (ExitFailure 1)
    Just x  -> return x
  

parseFile :: String -> IO ()
parseFile path = do
  eRes <- parseFromFile topLevelL path
  case eRes of
    Left err  -> printf "Error parsing %s\n%s\n" path (show err)
    Right res -> putDoc $ pretty res


main :: IO ()
main = do
  file <- exitOnNothing "You must provide a file name as first argument" getFile
  parseFile file

-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
module Example where
import System.Posix.Redirect
import System.FilePath
import System.Directory
import qualified Minigent.CLI as CLI
import qualified Data.ByteString.Char8 as B
import Control.Exception
import System.Console.ANSI
import Control.Monad.Except
import System.Exit
import Data.Char

trim, ltrim, rtrim :: B.ByteString -> B.ByteString
trim = ltrim . rtrim
ltrim s | Just (x, s') <- B.uncons s, isSpace x = ltrim s' 
        | otherwise = s
rtrim s | Just (s', x) <- B.unsnoc s, isSpace x = rtrim s' 
        | otherwise = s

updateExpected :: FilePath -> IO ()
updateExpected f = do
  phase <- loadConfig
  let compile = CLI.compiler phase [CLI.Dump phase CLI.Stdout CLI.PrettyPlain] [f </> "in.minigent"]
  (out', (err', _)) <- redirectStdout (redirectStderr (blockExceptions compile))
  let out = trim out'
      err = trim err'
  B.writeFile (f </> "expected.out") out
  B.writeFile (f </> "expected.err") err
  putStrLn $ "Writing files to " ++ f
  where

    loadConfig :: IO CLI.Phase
    loadConfig = do
      b <- doesFileExist (f </> "config")
      contents <- if b then readFile (f </> "config") else pure ""
      v <- runExceptT (CLI.parsePhase contents)
      pure $ case v of
        Left _ -> CLI.TC
        Right p -> p

    blockExceptions :: IO a -> IO (Either SomeException a)
    blockExceptions = try

example :: FilePath -> IO ()
example f = do
  phase <- loadConfig
  let compile = CLI.compiler phase [CLI.Dump phase CLI.Stdout CLI.PrettyPlain] [f </> "in.minigent"]
  (out', (err', _)) <- redirectStdout (redirectStderr (blockExceptions compile))
  let out = trim out'
      err = trim err'
  expectedErr <- trim <$> readIfExists (f </> "expected.err")
  expectedOut <- trim <$> readIfExists (f </> "expected.out")
  when (expectedErr /= err) $ do
    setSGR [SetColor Foreground Vivid Red]
    putStrLn ("Failed: " ++ f)
    putStrLn "Standard error output differed from expectations. The compiler produced:"
    setSGR [SetColor Foreground Vivid Cyan]
    B.putStrLn err
    setSGR [SetColor Foreground Vivid Red]
    putStrLn "But the test expects:"
    setSGR [SetColor Foreground Vivid Magenta]
    B.putStrLn expectedErr
    setSGR [Reset]
    exitFailure
  when (expectedOut /= out) $ do
    setSGR [SetColor Foreground Vivid Red]
    putStrLn ("Failed: " ++ f)
    putStrLn "Standard output differed from expectations. The compiler produced:"
    setSGR [SetColor Foreground Vivid Cyan]
    B.putStrLn out
    setSGR [SetColor Foreground Vivid Red]
    putStrLn "But the test expects:"
    setSGR [SetColor Foreground Vivid Magenta]
    B.putStrLn expectedOut
    setSGR [Reset]
    exitFailure
  setSGR [SetColor Foreground Vivid Green]
  putStrLn ("Passed: " ++ f)
  setSGR [Reset]
  return ()

  where

    loadConfig :: IO CLI.Phase
    loadConfig = do
      b <- doesFileExist (f </> "config")
      contents <- if b then readFile (f </> "config") else pure ""
      v <- runExceptT (CLI.parsePhase contents)
      pure $ case v of
        Left _ -> CLI.TC
        Right p -> p

    blockExceptions :: IO a -> IO (Either SomeException a)
    blockExceptions = try

    readIfExists :: FilePath -> IO B.ByteString
    readIfExists fp = do
      b <- doesFileExist fp
      if b then B.readFile fp else pure mempty

-- |
-- Module      : Minigent.CLI
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- The command line interface of the compiler.
--
{-# LANGUAGE FlexibleContexts #-}
module Minigent.CLI
    ( main
    , compiler
    , Phase (..)
    , Format (..)
    , Output (..)
    , Directive (..)
    -- * Internal
    , parsePhase
    ) where

import Minigent.Syntax
import Minigent.Syntax.Parser
import Minigent.Syntax.Lexer
import Minigent.Syntax.Utils
import Minigent.Syntax.PrettyPrint
import Minigent.Environment
import Minigent.Reorganiser
import Minigent.TC
import Minigent.Termination
import Minigent.CG
import Control.Monad
import Control.Applicative
import Control.Monad.Except
import Control.Monad.IO.Class
import System.Exit
import System.Environment
import System.IO
import System.FilePath
import System.Directory
import qualified Data.Map as M
import qualified Data.Text as T

import Text.Earley

import Data.Text.Prettyprint.Doc.Render.Terminal
import Data.Text.Prettyprint.Doc (unAnnotateS, unAnnotate, defaultLayoutOptions, layoutPretty, vcat, (<+>), pretty)


-- | The phases of the compiler, ordered in the order listed.
data Phase = Lex | Parse | Reorg | TC | Term | CG deriving (Ord, Enum, Eq)

-- | The way a dump should be formatted when printed.
data Format = PrettyColour -- ^ Print with a pretty printer and ANSI colours if printing to stdout
            | PrettyPlain  -- ^ Print with a pretty printer and no colours
            | Raw          -- ^ Print the raw abstract syntax tree (with 'Show')
  deriving (Eq)

-- | Where a dump should be output
data Output = File FilePath | Stdout
  deriving (Eq)

-- | The various command line arguments of the compiler.
data Directive
  = Dump Phase Output Format
  | NoColour
  deriving (Eq)


singleToken :: MonadError String m => (String -> m a) -> [String] -> m ([String],a)
singleToken parse [] = throwError "argument expected"
singleToken parse (x:xs) = do
  p <- parse x
  pure (xs, p)

parseFormat :: MonadError String m => String -> m Format
parseFormat "pretty"       = pure PrettyColour
parseFormat "pretty-plain" = pure PrettyPlain
parseFormat "raw"          = pure Raw
parseFormat _              = throwError "invalid output format"

-- | Exposed only for tests.
parsePhase :: MonadError String m => String -> m Phase
parsePhase "lexer" = pure Lex
parsePhase "parse" = pure Parse
parsePhase "reorg" = pure Reorg
parsePhase "tc"    = pure TC
parsePhase "cg"    = pure CG
parsePhase _       = throwError "invalid phase"

parseExtantFilePath :: (MonadError String m, MonadIO m) => String -> m FilePath
parseExtantFilePath s = do
  b <- liftIO $ doesFileExist s
  if b then pure s else throwError ("file does not exist: " ++ s)

parseOutputFilePath :: (MonadError String m, MonadIO m) => String -> m FilePath
parseOutputFilePath s = do
  b <- liftIO $ doesDirectoryExist (takeDirectory s)
  if b then pure s else throwError ("directory does not exist: " ++ takeDirectory s)


parseDirectives :: (Alternative m, MonadError String m, MonadIO m) => [String] -> m ([Directive], [FilePath])
parseDirectives [] = return ([],[])
parseDirectives ("--dump-stdout":rest) = do
  (rest', phase) <- singleToken parsePhase rest
  (rest'', format) <- singleToken parseFormat rest' <|> pure (rest', PrettyColour)
  (dirs, files) <- parseDirectives rest''
  pure (Dump phase Stdout format: dirs, files)
parseDirectives ("--no-colour":rest) = do
  (dirs, files) <- parseDirectives rest
  pure (NoColour:dirs, files)
parseDirectives ("--dump":rest) = do
  (rest', phase) <- singleToken parsePhase rest
  (rest'', format) <- singleToken parseFormat rest' <|> pure (rest', PrettyPlain)
  (rest''',outfile) <- singleToken parseOutputFilePath rest''
  (dirs, files) <- parseDirectives rest'''
  pure (Dump phase (File outfile) format: dirs, files)

parseDirectives (f:rest) = do
  (dirs, files) <- parseDirectives rest
  pure (dirs, f:files)


parseArgs :: [String] -> IO (Either String (Phase, [Directive], [FilePath]))
parseArgs [] = pure (Left "No argument given")
parseArgs (x:xs) = runExceptT $ do
  phase <- parsePhase x
  (dirs, files) <- parseDirectives xs
  return (phase, dirs, files)


printHelp :: IO ()
printHelp = putStrLn $ unlines
  [ "usage: minigent PHASE [DIRECTIVES ..] [FILE ..]"
  , ""
  , " Compiles up to a given phase, carrying out any relevant directives for each file."
  , ""
  , "  PHASE - one of: lexer, parse, reorg, tc, cg. "
  , ""
  , "  DIRECTIVES - one of: "
  , "    --dump PHASE [FORMAT] FILE     (writes the output of the given phase to the given file)"
  , "    --dump-stdout PHASE [FORMAT]   (writes the output of the given phase to stdout)"
  , ""
  , "    FORMAT - one of: pretty, pretty-plain, raw"
  , "             If not provided, --dump will use pretty-plain and --dump-stdout will use pretty"
  ]


-- | Main function.
main :: IO ()
main = do
  args <- getArgs
  if args == ["--help"]
    then printHelp
    else do
      args' <- parseArgs args
      case args' of
        Left err -> die ("minigent: " ++ err)
        Right (phase, dirs, files) -> do
          compiler phase dirs files


lexerPhase :: String -> IO [Token]
lexerPhase input =
  let toks = lexer input
   in case filter isUnknown toks of
       [] -> pure toks
       (Unknown c : _) -> do
         die ("Lexer error. Unrecognized character '" ++ c :"'")
  where
    isUnknown (Unknown _) = True
    isUnknown _           = False

parserPhase :: [Token] -> IO [RawTopLevel]
parserPhase input =
  let (rs, rp) = fullParses (parser toplevels) input
  in case rs of
    []    -> die ("Parsing failed.\n" ++ show rp )
    (x:_) -> pure x

reorgPhase :: [RawTopLevel] -> IO GlobalEnvironments
reorgPhase x =
  let (envs, errs) = reorg x
  in case errs of
       []   -> pure envs
       errs -> do
         die ("Reorg failed.\n" ++ unlines errs ++ "\n\n")

tcPhase :: Bool -> GlobalEnvironments -> IO GlobalEnvironments
tcPhase colour envs
  = let rs = withUnifVars (tc envs (M.toList (defns envs)))
     in GlobalEnvs <$> (M.fromList . concat <$> mapM go rs)
                   <*> pure (types envs)
  where
    handleColour = if not colour then unAnnotate else id
    go (Left (f, cs)) = do
      hPutStrLn stderr ("Typecheck failed in function " ++ f)
      hPutDoc stderr (handleColour (vcat (map ((pretty " • " <+>) . prettyConstraint) cs)))
      hPutStrLn stderr ""
      pure []
    go (Right b) = pure [b]

terminationPhase :: GlobalEnvironments -> IO ()
terminationPhase envs
  = case termCheck envs of
      [] -> return ()
      xs -> -- Error
        mapM_ (hPutStrLn stderr) xs


cgPhase :: GlobalEnvironments -> IO String
cgPhase gs = pure (cg gs)

lexerDump :: [Token] -> Directive -> IO ()
lexerDump toks (Dump Lex out fmt) =
    write out (format fmt toks)
  where
    write (File f) = writeFile f
    write (Stdout) = putStrLn

    format Raw = show
    format _   = unlines . map show
lexerDump _ _ = return ()

parserDump :: [RawTopLevel] -> Directive -> IO ()
parserDump tops (Dump Parse out fmt) =
    write out (format fmt tops)
  where
    write (File f) = writeFile f
    write (Stdout) = putStrLn

    format Raw          = show
    format PrettyColour = T.unpack
                        . renderStrict
                        . layoutPretty defaultLayoutOptions
                        . vcat
                        . map prettyToplevel
    format PrettyPlain  = T.unpack
                        . renderStrict
                        . unAnnotateS
                        . layoutPretty defaultLayoutOptions
                        . vcat
                        . map prettyToplevel
parserDump _ _ = return ()

reorgDump :: GlobalEnvironments -> Directive -> IO ()
reorgDump tops (Dump Reorg out fmt) =
    write out (format fmt tops)
  where
    write (File f) = writeFile f
    write (Stdout) = putStrLn

    format Raw          = show
    format PrettyColour = T.unpack
                        . renderStrict
                        . layoutPretty defaultLayoutOptions
                        . prettyGlobalEnvs
    format PrettyPlain  = T.unpack
                        . renderStrict
                        . unAnnotateS
                        . layoutPretty defaultLayoutOptions
                        . prettyGlobalEnvs
reorgDump _ _ = return ()

tcDump :: GlobalEnvironments -> Directive -> IO ()
tcDump tops (Dump TC out fmt) =
    write out (format fmt tops)
  where
    write (File f) = writeFile f
    write (Stdout) = putStrLn

    format Raw          = show
    format PrettyColour = T.unpack
                        . renderStrict
                        . layoutPretty defaultLayoutOptions
                        . prettyGlobalEnvs
    format PrettyPlain  = T.unpack
                        . renderStrict
                        . unAnnotateS
                        . layoutPretty defaultLayoutOptions
                        . prettyGlobalEnvs
tcDump _ _ = return ()

cgDump :: String -> Directive -> IO ()
cgDump s (Dump CG out fmt) = write out s
  where
    write (File f) = writeFile f
    write (Stdout) = putStrLn
cgDump _ _ = mempty


-- | Compile the given files up to the given phase, dumping
--   output according to the given directives.
compiler :: Phase -> [Directive] -> [FilePath] -> IO ()
compiler phase dirs [] = die "no input files given"
compiler phase dirs files = do
    input <- unlines <$> mapM readFile files
    upTo Lex
    toks <- lexerPhase input
    mapM_ (lexerDump toks) dirs
    upTo Parse
    ast <- parserPhase toks
    mapM_ (parserDump ast) dirs
    upTo Reorg
    envs <- reorgPhase ast
    mapM_ (reorgDump envs) dirs
    upTo TC
    binds <- tcPhase (NoColour `notElem` dirs) envs
    mapM_ (tcDump binds) dirs
    upTo Term
    _ <- terminationPhase envs
    upTo CG
    barf <- cgPhase binds
    mapM_ (cgDump barf) dirs
  where
    upTo p = unless (p <= phase) exitSuccess

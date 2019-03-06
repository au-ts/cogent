--
-- Copyright 2017, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--


{-# LANGUAGE LambdaCase, RecordWildCards, TupleSections #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

module Cogent.Preprocess where

import Cogent.Compiler
import Cogent.Common.Syntax hiding (Prefix)

import Control.Arrow ((+++))
import Control.Monad.IO.Class
import Data.Char
import Language.Preprocessor.Cpphs hiding (pragma)
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Language
import Text.Parsec.Pos
import Text.Parsec.Prim
import qualified Text.Parsec.Token as T

-- import Debug.Trace

language :: LanguageDef st
language = haskellStyle { T.commentStart = ""
                        , T.commentEnd   = ""
                        , T.reservedOpNames = ["{-#", "#-}"]
                        }

data LocPragma = LP { locOfLP    :: SourcePos
                    , pragmaOfLP :: Pragma
                    } deriving (Eq, Show)

T.TokenParser {..} = T.makeTokenParser language

genericName :: Parsec String u String
genericName = try (do (x:xs) <- identifier
                      (if isLower x || (x == '_' && not (null xs)) then return else unexpected) $ x:xs)

variableName :: Parsec String u VarName
variableName = genericName

functionName :: Parsec String u FunName
functionName = genericName

pragma :: Parsec String u [LocPragma]  -- We don't allow nested comments for pragmas
pragma = (try (reservedOp "{-#") >> inPragmaSingle)
         <|> (lexeme anyChar >> return [])

inPragmaSingle :: Parsec String u [LocPragma]
inPragmaSingle = do
  l <- getPosition
  p <- identifier -- pragma name
  fs <- sepBy1 functionName comma
  reservedOp "#-}"
  mkPragmas p l fs
  <?> "end of pragma"

mkPragmas :: String -> SourcePos -> [FunName] -> Parsec String u [LocPragma]
mkPragmas p l fs = let p' = map toLower p
                    in case p' of
                         "inline"  -> return $ map (LP l . InlinePragma ) fs
                         "cinline" -> return $ map (LP l . CInlinePragma) fs
                         "fnmacro" -> return $ if __cogent_ffncall_as_macro then map (LP l . FnMacroPragma) fs else []
                         _ -> unexpected ("unrecognised pragma " ++ p) -- LP l (UnrecPragma p) : []

program :: Parsec String u [LocPragma]
program | __cogent_fpragmas = do whiteSpace
                                 ps <- many pragma
                                 eof
                                 return $ concat ps
        | otherwise = return []

preprocess :: FilePath -> IO (Either String (String, [LocPragma]))
preprocess filename = do
  input <- readFile filename
  opts <- return $ if not (null __cogent_cogent_pp_args)
                     then parseOptions __cogent_cogent_pp_args
                     else Right myCpphsOptions
  case opts of
    Left err -> return $ Left $ "Invalid arguments to Cogent preprocessor (cpphs --help): " ++ err
    Right opts' -> do
      input' <- liftIO $ runCpphs opts' filename input
      -- (s1,tab) <- runCpphsReturningSymTab opts' filename input
      -- putStrLn "-----------------------------"
      -- putStrLn $ show tab
      -- putStrLn "-----------------------------"
      return . (show +++ (input',)) $ parse program filename input'
  where 
    myCpphsOptions = defaultCpphsOptions {boolopts = myBoolOptions}
    myBoolOptions = defaultBoolOptions {macros = True, locations = False}

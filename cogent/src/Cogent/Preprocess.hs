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
import Cogent.Surface (LocPragma (..))

import Control.Arrow ((+++))
import Control.Monad.IO.Class
import Data.Char
import Data.Maybe (catMaybes)
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

T.TokenParser {..} = T.makeTokenParser language

pragma :: Parsec String u (Maybe LocPragma)  -- We don't allow nested comments for pragmas
pragma = (try (reservedOp "{-#") >> (Just <$> inPragmaSingle))
         <|> (lexeme anyChar >> return Nothing)

inPragmaSingle :: Parsec String u LocPragma
inPragmaSingle = do
  l <- getPosition
  p <- identifier -- pragma name
  rest <- manyTill anyChar (try (reservedOp "#-}"))
  return $ LP l $ UnrecPragma p rest
  <?> "end of pragma"

program :: Parsec String u [LocPragma]
program | __cogent_fpragmas = do whiteSpace
                                 ps <- many pragma
                                 eof
                                 return $ catMaybes ps
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
    myBoolOptions = defaultBoolOptions {macros = True}

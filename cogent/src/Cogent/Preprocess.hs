--
-- Copyright 2016, NICTA
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

import Data.Char
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Language
import Text.Parsec.Pos
import Text.Parsec.Prim
import Text.Parsec.String (parseFromFile)
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

variableName = try (do (x:xs) <- identifier
                       (if isLower x || (x == '_' && not (null xs)) then return else unexpected) $ x:xs)

pragma :: Parsec String u [LocPragma]  -- We don't allow nested comments for pragmas
pragma = (try (reservedOp "{-#") >> inPragmaSingle)
         <|> (lexeme anyChar >> return [])

inPragmaSingle :: Parsec String u [LocPragma]
inPragmaSingle = do
  l <- getPosition
  p <- identifier -- pragma name
  fs <- sepBy1 variableName comma
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

preprocess :: FilePath -> IO (Either String [LocPragma])
preprocess filename = parseFromFile program filename >>= \case
                        Left err -> return $ Left $ show err
                        Right ps -> return $ Right ps


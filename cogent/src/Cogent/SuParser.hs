--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Cogent.SuParser where

import Cogent.Common.Syntax

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative hiding (many, (<|>), optional)
#endif
import Lens.Micro ((<&>))
import Control.Monad
import Data.Maybe
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Language
import Text.Parsec.Pos
import Text.Parsec.Prim as P
import qualified Text.Parsec.Token as T
import Prelude hiding (Bounded)

-- import Debug.Trace

language :: LanguageDef st
language = emptyDef { T.identLetter     = alphaNum <|> char '_'
                    , T.reservedNames   = ["static", "dynamic", "bounded"]
                    , T.reservedOpNames = [":"]
                    }

T.TokenParser {..} = T.makeTokenParser language

data Qualifier = Static | Dynamic Bounded deriving (Eq, Show)
type Bounded = Bool

data StackUsage = StackUsage OptFunName SourcePos Int Qualifier deriving (Eq, Show)
data OptFunName = OptFunName FunName [String] deriving (Eq, Show)

funcName = OptFunName <$> identifier <*> option [] (char '.' >>  (identifier <|> (show <$> natural)) `sepBy1` (char '.'))

fileName = manyTill anyChar (reservedOp ":")

oneFunc = do file <- fileName
             -- reservedOp ":"
             line <- natural
             reservedOp ":"
             col  <- natural
             reservedOp ":"
             func <- funcName
             size <- natural
             qual <-  (reserved "static" *> pure Static)
                  <|> (reserved "dynatic" *> (Dynamic <$> (optionMaybe (reserved "bounded") <&> isJust)))
             return $ StackUsage func (newPos file (fromIntegral line) (fromIntegral col)) (fromIntegral size) qual

-- oneFile = whiteSpace *> (many oneFunc) <* eof

parse sufile = readFile sufile >>=
               return . zip [1 :: Int ..] . lines >>=
               return . mapM (\(l,s) -> P.parse (getPosition >>= return . flip setSourceLine l >>= setPosition >> oneFunc) sufile s) >>= \case
                 Left  err -> return $ Left $ show err
                 Right sus -> return $ Right sus

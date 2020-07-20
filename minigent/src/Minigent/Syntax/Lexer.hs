-- |
-- Module      : Minigent.Syntax.Lexer
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- Contains the lexer for the concrete syntax of Minigent.
--
-- It expects to be imported qualified, as the keyword tokens clash with expression constructors.

module Minigent.Syntax.Lexer
  ( Token (..)
  , Bracket (..)
  , Keyword (..)
  , lexer
  ) where

import Minigent.Syntax (Op (..))
import Minigent.Syntax.Utils
import Data.Char
import Data.List (span)

data Bracket = Paren | Brace | Square
     deriving (Show, Eq)


data Keyword = Case | Of | If | Then | Else | Take | Put | Let | In | End | Rec | NoTermCheck
     deriving (Show, Eq)

data Token
  = LowerIdent String -- ^ @[a-z][a-zA-Z0-9]*@
  | UpperIdent String -- ^ @[A-Z][a-zA-Z0-9]*@
  | Numeric Integer   -- ^ @[0-9]+@
  | Open Bracket      -- ^ @( or [ or {@
  | Close Bracket     -- ^ @) or ] or }@
  | Keyword Keyword
  | Operator Op
  | Bang              -- ^ @!@
  | Colon             -- ^ @:@
  | Comma             -- ^ @,@
  | Bar               -- ^ @|@
  | Arrow             -- ^ @->@
  | Hash              -- ^ @#@
  | Equals            -- ^ @=@
  | Dot               -- ^ @.@
  | Semi              -- ^ @;@
  | Unknown Char -- ^ For errors
  deriving (Show, Eq)




toToken "case" = Keyword Case
toToken "of"   = Keyword Of
toToken "if"   = Keyword If
toToken "then" = Keyword Then
toToken "end"  = Keyword End
toToken "else" = Keyword Else
toToken "take" = Keyword Take 
toToken "put"  = Keyword Put 
toToken "let"  = Keyword Let
toToken "in"   = Keyword In 
toToken "rec"   = Keyword Rec
toToken "NoTermCheck" = Keyword NoTermCheck
toToken (x:xs) | isLower x = LowerIdent (x:xs)
               | otherwise = UpperIdent (x:xs)  

-- | An error in the lexer will produce 'Unknown' tokens.
lexer :: String -> [Token]
lexer [] = []
lexer (x:xs) | isSpace x = lexer xs
lexer (x:xs) | isLetter x = let
     (word, rest) = span isAlphaNum (x:xs)
  in toToken word : lexer rest
lexer (x:xs) | isDigit x = let
     (number, rest) = span isDigit (x:xs)
  in Numeric (read number) : lexer rest
lexer (x:y:xs) | Just o <- lookup [x,y] operators
               = Operator o : lexer xs
lexer ('-':'>':xs) = Arrow : lexer xs
lexer (x:xs) | Just o <- lookup [x] operators
             = Operator o : lexer xs
lexer ('(':xs) = Open Paren : lexer xs
lexer (')':xs) = Close Paren : lexer xs
lexer ('[':xs) = Open Square : lexer xs
lexer (']':xs) = Close Square : lexer xs
lexer ('{':xs) = Open Brace : lexer xs
lexer ('}':xs) = Close Brace : lexer xs
lexer ('=':xs) = Equals : lexer xs
lexer ('!':xs) = Bang : lexer xs
lexer (';':xs) = Semi : lexer xs
lexer (':':xs) = Colon : lexer xs
lexer ('.':xs) = Dot   : lexer xs
lexer ('#':xs) = Hash : lexer xs
lexer (',':xs) = Comma : lexer xs
lexer ('|':xs) = Bar : lexer xs
lexer (c:xs)   = Unknown c : lexer xs

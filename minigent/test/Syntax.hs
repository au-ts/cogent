-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Syntax where
import Test.SmallCheck.Series
import Test.SmallCheck.Drivers
import Test.SmallCheck

import Minigent.Syntax
import Minigent.Syntax.Parser
import Minigent.Syntax.Utils
import qualified Minigent.Syntax.Lexer as L
import qualified Minigent.Syntax.PrettyPrint as P
import System.Exit (die)
import Text.Earley.Generator
import Text.Earley
import Control.Monad.Trans.Maybe
import Control.Monad.Trans(lift)
import Control.Applicative
data ArbitrarySyntaxTree = SyntaxTree RawTopLevel [L.Token] deriving Show

instance Monad m => Serial m ArbitrarySyntaxTree where
  series = generate (\n -> map (uncurry SyntaxTree) (upTo n gen))
    where gen = generator toplevel testTokens

testTokens :: [L.Token]
testTokens = map L.LowerIdent [ "a" ]
          ++ map L.UpperIdent [ "A" ]
          ++ map L.Numeric    [ 1 ]
          ++ map L.Open       [ L.Brace, L.Paren, L.Square ]
          ++ map L.Close      [ L.Brace, L.Paren, L.Square ]
          ++ map L.Keyword    [ L.Let, L.In, L.End, L.Case, L.Of, L.If, L.Then, L.Else, L.Take, L.Put ]
          ++ map L.Operator   (map snd operators)
          ++ [L.Bang, L.Colon, L.Comma, L.Bar, L.Arrow, L.Hash, L.Equals, L.Dot, L.Semi ]

parserUnambiguous
  (SyntaxTree tops toks) =
    length (fst (fullParses (parser toplevel) toks)) == 1

parserPrettyPrintRoundTrip
  (SyntaxTree tops toks) =
    tops `elem` (fst (fullParses (parser toplevel) (L.lexer (P.testPrettyToplevel tops))))

test depth = do
  m <- runMaybeT cases
  case m of
    Just failure -> die (ppFailure failure)
    Nothing -> return ()
  where
    cases =
          do lift $ putStrLn "Checking that the parser is unambiguous..."
             MaybeT $ smallCheckM depth parserUnambiguous
      <|> do lift $ putStrLn "Checking that parse . prettyprint = id..."
             MaybeT $ smallCheckM depth parserPrettyPrintRoundTrip

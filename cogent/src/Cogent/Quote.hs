--
-- Copyright 2019, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

module Cogent.Quote where

import Cogent.Parser (toplevel', S(..))
import Cogent.Surface ()

import Data.Data
import Language.Haskell.TH.Quote (QuasiQuoter(..))
import Language.Haskell.TH.Syntax (Q(..), Exp, liftData)
import Text.Parsec (runParser)

cogent :: QuasiQuoter
cogent = QuasiQuoter { quoteExp  = parseCogentTl 
                     , quotePat  = error "quotePat undefined"
                     , quoteType = error "quoteType undefined"
                     , quoteDec  = error "quoteDec undefined"
                     }

parseCogentTl :: String -> Q Exp
parseCogentTl s = case runParser toplevel' (ParserState False) "" s of
                    Left  e -> error $ "Parsing failed with errors: " ++ show e
                    Right (_,_,x) -> liftData x

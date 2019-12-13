--
-- Copyright 2019, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

module Cogent.Isabelle.IsabelleName where

{-
 - IsabelleName.hs: generate names for an Isabelle embedding that are valid and don't clash with reserved words
 -}

import Isabelle.Parser (reservedWords)
import Isabelle.InnerAST as I
import Cogent.Desugar as D (freshVarPrefix)
import Cogent.Normal as N (freshVarPrefix)

import Data.List (stripPrefix, isPrefixOf, isSuffixOf)
import Data.Char (isDigit)

import Cogent.Compiler (__fixme)


newtype IsabelleName = IsabelleName { unIsabelleName :: String }
  deriving (Eq, Show, Ord)

{-
 - We change the name of the embedding as follows so:
 - 1) We don't use a reserved word for a function name (e.g. 'function' or 'open')
 - 2) We don't generate invalid names (like _free, free_, 1free, etc.)
 - 3) We don't take a name in the Isabelle standard proof library (e.g. 'map')
-}
safeName :: IsabelleName -> IsabelleName
safeName (IsabelleName nm) = IsabelleName $
  case isReserved nm of
    True -> __fixme nm -- "Error: function name `" ++ nm ++ "' is a reserved isabelle name" 
    -- Add debug note
    False -> case "_" `isPrefixOf` nm of
      True  ->  __fixme nm  -- "Error: function name `" ++ nm ++ "' cannot start with underscores"
      False -> case "_" `isSuffixOf` nm of
        True  -> __fixme nm -- "Error: function name `" ++ nm ++ "' cannot end with underscores"
        False -> nm

isReserved :: String -> Bool
isReserved n = n `elem` reservedWords

isInvalid :: String -> Bool
isInvalid n =
  isDigit (head n) || "_" `isPrefixOf` n || "_" `isSuffixOf` n

badName :: String -> Bool
badName s = isReserved s || isInvalid s

{- 
 - Generates a name that can be used in the isabelle embedding.
 - If the name is invalid, it is mapped to a valid name.
 - This name is suitable both for Isabelle ML and Isabelle (i.e. ascii only)
 -}
mkIsabelleName :: String -> IsabelleName
mkIsabelleName = safeName . IsabelleName

editIsabelleName :: IsabelleName -> (String -> String) -> Maybe IsabelleName
editIsabelleName (IsabelleName n) f  = 
  if badName n then
    Nothing
  else 
    Just $ IsabelleName (f n)

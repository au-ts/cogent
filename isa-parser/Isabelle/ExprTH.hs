--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

module Isabelle.ExprTH where

import Data.Generics.Aliases
import Data.Data 
import qualified Language.Haskell.ParseExp as M (parseExp)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import qualified Text.Parsec.Prim as P
import qualified Text.Parsec.Char as P

import Isabelle.InnerAST
import Isabelle.OuterAST
import Isabelle.Parser

-- import Debug.Trace

isaTheory :: QuasiQuoter
isaTheory = qq topLevelL

isaDecl :: QuasiQuoter
isaDecl = qq theoryDeclL

isaTerm :: QuasiQuoter
isaTerm = qq termL

isaType :: QuasiQuoter
isaType = qq typeL
        
isaMethods :: QuasiQuoter
isaMethods = qq (P.many methodL)

qq :: (Data x) => (ParserM x) -> QuasiQuoter
qq prs = QuasiQuoter { quoteExp  = parseExp prs
                     , quotePat  = parsePat prs
                     , quoteType = error "quoteType undefined"
                     , quoteDec  = error "quoteDec undefined" }

parse :: Monad m => (ParserM x) -> String -> m x
parse prs s = do
  let res = P.runP (P.many (P.space) >> prs) () "<isabelle>" s
  case res of
    Left err -> fail $ show err
    Right e  -> return e

parseExp :: (Data x) => (ParserM x) -> String -> TH.ExpQ
parseExp prs s = parse prs s >>= dataToExpQ (const Nothing `extQ` typeAntiE `extQ` termAntiE `extQ` nameAntiE)

termAntiE :: Term -> Maybe (TH.Q TH.Exp)
termAntiE (AntiTerm x) = case M.parseExp x of Right e -> return $ return e; Left s -> Nothing
termAntiE _ = Nothing 
typeAntiE :: Type -> Maybe (TH.Q TH.Exp)
typeAntiE (AntiType x) = case M.parseExp x of Right e -> return $ return e; Left s -> Nothing
typeAntiE _ = Nothing 
nameAntiE :: String -> Maybe (TH.Q TH.Exp)
nameAntiE ('$':xs) = Just $ TH.varE (TH.mkName xs)
nameAntiE _ = Nothing  

parsePat :: (Data x) => (ParserM x) -> String -> TH.PatQ
parsePat prs s = parse prs s >>= dataToPatQ (const Nothing `extQ` typeAntiP `extQ` termAntiP `extQ` nameAntiP)
termAntiP :: Term -> Maybe (TH.Q TH.Pat)
termAntiP (AntiTerm x) = Just $ TH.varP  (TH.mkName x)
termAntiP _ = Nothing 
typeAntiP :: Type -> Maybe (TH.Q TH.Pat )
typeAntiP (AntiType x) = Just $ TH.varP  (TH.mkName x)
typeAntiP _ = Nothing 
nameAntiP :: String -> Maybe (TH.Q TH.Pat)
nameAntiP ('$':xs) = Just $ TH.varP (TH.mkName xs)
nameAntiP _ = Nothing  

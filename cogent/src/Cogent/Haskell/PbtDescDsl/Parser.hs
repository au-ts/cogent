{-# LANGUAGE MultiWayIf #-}

module Cogent.Haskell.PbtDescDsl.Parser (parsePbtDescFile) where

import Cogent.Haskell.PbtDescDsl.Types
import Cogent.Compiler (__cogent_pbt_info, __impossible)
import qualified Language.Haskell.Exts.Syntax as HSS (Exp(..), Type(..))
import qualified Language.Haskell.Exts.Parser as HSP (parseType, parseExp, fromParseResult)
import qualified Language.Haskell.Names.SyntaxUtils as HSN (dropAnn)
import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Indent
import Text.Show.Pretty
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class
import Control.Applicative hiding ((<|>), optional, many)
import Data.List (find, isInfixOf)
import Data.List.Extra (trim)
import Data.Maybe
import Debug.Trace

-- Parser type
type Parser a = Parsec String () a

-- Top level parser functions (for parsing PBT description file, aka: __cogent_pbt_info)
-- -----------------------------------------
parsePbtDescFile :: FilePath -> ExceptT String IO [PbtDescStmt]
parsePbtDescFile f = pPbtFile pStmts f

readPbtFile = liftA lines . readFile

pPbtFile :: Parser a -> FilePath -> ExceptT String IO a
pPbtFile p f = do
    pbtFileLs <- case __cogent_pbt_info of 
                   Just f -> lift $ readPbtFile f
                   Nothing -> undefined
    case (Text.Parsec.parse p "" (unlines pbtFileLs)) of 
        Right pbtF -> return pbtF
        Left err -> throwE $ "Error: Failed to parse PBT Info file: " ++ show err

-- PBT DSL statement
-- -----------------------------------------
pStmts :: Parser [PbtDescStmt]
pStmts = (pspaces pStmt) `manyTill` eof

pStmt :: Parser PbtDescStmt
pStmt = do
    fname <- pspaces $ pbetweenQuotes pstrId
    decls <- pspaces $ pbetweenCurlys pDecls
    return $ PbtDescStmt fname decls

-- PBT DSL declarations
-- -----------------------------------------
pDecls :: Parser [PbtDescDecl]
pDecls = pDecl `manyTillLookAhead` rcurly

pDecl :: Parser PbtDescDecl
pDecl = do
    k <- pstrId <* (lookAhead lcurly)
    exprs <- pspaces $ pbetweenCurlys pExprs
    return $ PbtDescDecl (toPbtTyp k) exprs

-- PBT DSL expressions
-- -----------------------------------------
pExprs :: Parser [PbtDescExpr]
pExprs = pExpr `sepEndBy` (pspaces semi)

pExpr :: Parser PbtDescExpr 
pExpr = do
    lhs <- pstrId
    op <- lookAhead $ try tyOp <|> mapOp <|> rcurly
    let v = find (\x -> isInfixOf x lhs) keyvars
    e <- case v of
        Just x -> if | op == ':' -> pTypExpr x
                     | op == '=' -> pMapExpr x
                     | otherwise -> pJustExpr x
        Nothing -> pJustExpr lhs
    return $ e

pTypExpr lhs = do
    e <- tyOp *> pstrId 
    return $ PbtDescExpr (Just (toPbtTyp' lhs)) (HSS.QuasiQuote () (lhs) (e))

pMapExpr lhs = do
    e <- mapOp *> pstrId
    return $ PbtDescExpr (Just (toPbtTyp' lhs)) (HSS.QuasiQuote () (lhs) (e))

pJustExpr lhs = return $ PbtDescExpr Nothing (HSS.QuasiQuote () "x" lhs)

-- Helpers
-- -----------------------------------------
toPbtTyp "absf" = Absf
toPbtTyp "rrel" = Rrel
toPbtTyp "welf" = Welf
toPbtTyp "pure" = Pure
toPbtTyp "nond" = Nond
toPbtTyp s = toPbtTyp . trim $ s

toPbtTyp' "ic" = Ic
toPbtTyp' "ia" = Ia
toPbtTyp' "oc" = Oc
toPbtTyp' "oa" = Oa
toPbtTyp' s = toPbtTyp' . trim $ s

parseHsTyp :: String -> HSS.Type ()
parseHsTyp = HSN.dropAnn . HSP.fromParseResult . HSP.parseType

parseHsExp :: String -> HSS.Exp ()
parseHsExp = HSN.dropAnn . HSP.fromParseResult . HSP.parseExp

keyvars = ["ic", "ia", "oc", "oa"]

stopChars = ['\"', '\r', '\n', ':', '{', '}', ';']

pstrId :: Parser String 
pstrId = pspaces $ many1 $ noneOf $ stopChars

pspaces :: Parser a -> Parser a
pspaces a = spaces *> a <* spaces

pbetweenCurlys :: Parser a -> Parser a
pbetweenCurlys a = between lcurly rcurly a

pbetweenQuotes :: Parser a -> Parser a
pbetweenQuotes a = between (char '"') (char '"') a

lcurly = char '{'
rcurly = char '}'

colon = char ':'
equ = char '='
semi = char ';'

tyOp = colon >> colon
mapOp = colon >> equ

manyTillLookAhead p1 p2 = p1 `manyTill` (lookAhead $ try p2)

-- Debugging/Testing
-- -----------------------------------------
println a = traceShowM a

seeNext :: Int -> Parser ()
seeNext n = do
  s <- getParserState
  let out = take n (stateInput s)
  println out

testPBTParse' :: IO ()
testPBTParse' = pPrint $ Text.Parsec.parse pStmt "" exampleFile'

exampleFile' :: String
exampleFile' = unlines $
        [ "\"averageBag\" {                 \r"
        , "    pure { True }                \r"
        , "    nond { False }               \r"
        , "    absf {                       \r"
        , "         ic :: R4 Word32 Word32;  \r"
        , "         ia :: (Int, Int);        \r"
        , "         ia := ic;               \r"
        , "    }                            \r"
        , "    rrel {                       \r"
        , "         oc :: V0 () Word32;      \r"
        , "         oa :: Maybe Int;         \r"
        , "         oa := oc;               \r"
        , "    }                            \r"
        , "}                                \r"
        ]

{-# LANGUAGE MultiWayIf #-}

module Cogent.Haskell.ParseDSL (
    parsePbtDescFile,
    parseFile, 
    testPBTParse
) where

import Cogent.Haskell.GenDSL
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

-- Top level parser functions (for parsing PBT description file, aka: __cogent_pbt_info)
-- -----------------------------------------
parsePbtDescFile :: FilePath -> ExceptT String IO [PbtDescStmt]
parsePbtDescFile f = pPbtFile pStmts f

readPbtFile = liftA lines . readFile

pPbtFile :: Parser a -> FilePath -> ExceptT String IO a
pPbtFile p f = do
    pbtFileLs <- case __cogent_pbt_info of 
                   Just f -> lift $ getPBTFile f
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



















-- DSL Format Rules:
-- ------------------------------
-- fname must start function info, enclosed by quotes
-- fname is followed by keywords, until eof or another fname
-- keywords must have (:) on RHS, values is the following string until the eol

-- Indent Parser Type
-- ------------------------------
type IParser a = IndentParser String () a

type Parser a = Parsec String () a

keywords :: [String]
keywords = ["pure", "nond", "absf", "rrel", "welf"]
            ++ 
           ["IC", "IA", "OC", "OA"]

ignores :: [Char]
ignores = ['\"', '\r', '\n', ':', '{', '}', ';']

-- PBT Info Parser helpers
-- ------------------------------

strCmt :: IParser String 
strCmt = string "--" *> anyChar `manyTill` (many1 endOfLine)

int :: (Integral a, Read a) => IParser a
int = read <$> many1 digit 

strComma :: IParser String
strComma = lexeme $ many1 (noneOf (ignores++[',']))

parseList :: IParser [String]
parseList = (strComma `sepBy1` (char ',')) <* spaces <* char (';')
            <?> "Trying to parse list"
-- TODO: ^^ handle parantheses

--eol :: IParser String
--eol = many1 endOfLine

parseLn :: IParser (String, [String])
parseLn = do
    k <- spaces *> strKW
    v <- parseList <* spaces -- <|> many strCmt -- <* spaces
    return (k,v)

parseTyps :: IParser [(String, HSS.Type ())]
parseTyps = (pt `sepBy1` (char ',')) <* spaces <* char ';' <* spaces
     <?> "trying to parse multiple types"

pt :: IParser (String, HSS.Type ())
pt = do
    k <- spaces *> strKW
    v <- spaces *> strVT <* spaces 
    let v' = HSN.dropAnn $ HSP.fromParseResult $ HSP.parseType v
    return (k,v')
    <?> "trying to parse single types"

--strToTyp :: IParser String -> IParser (Type ())
--strToTyp p = undefined

strKW :: IParser String 
strKW = strV <* char ':'

strV :: IParser String 
strV = many1 (noneOf (ignores++[',']))
     <?> "trying to parse string value"

strVT :: IParser String 
strVT = many1 (noneOf (ignores))
     <?> "trying to parse string type value"

boolV :: IParser Bool 
boolV = read <$> strV

-- PBT Info Sub-component Parsing
-- ------------------------------
strFN :: IParser String 
strFN = between (char '"') (char '"') strV -- <* spaces
--char '"' *> strV <* char '"' <* spaces

parseFunExpr :: IParser (String, FunDefs)
parseFunExpr = do
    (k, v) <- spaces *> parseLn <* spaces
    t <- between (char '{') (char '}') (spaces *> parseTyps <* spaces)
    if | k == "absf" -> return $ ("AB", FunAbsF (k,v) t)
       | k == "rrel" -> return $ ("RR", FunRRel (k,v) t)
       | otherwise -> return $ ("RR", FunRRel (k,v) t)
        
parseExprL :: IParser [(String, FunDefs)]
parseExprL = do 
    ip <- strKW *> boolV <* spaces <* char (',') <* spaces
    nd <- strKW *> boolV <* spaces <* char (',') <* spaces
    rest <- ((spaces *> parseFunExpr <* spaces) `sepBy1` (char ',')) <* spaces <* char (';') <* spaces
    return $ [("FI", FunInfo ip nd)] ++ rest

{-
strFInfo :: IParser FunInfo 
strFInfo = do 
    ip <- strKW *> boolV <* spaces 
    nd <- strKW *> boolV <* spaces
    return $ FunInfo ip nd

strAbsF :: IParser FunAbsF
strAbsF = withBlock FunAbsF parseLn parseTyps
 
strRRel :: IParser FunRRel
strRRel = withBlock FunRRel parseLn parseTyps

strWelF :: IParser FunWelF
strWelF = withBlock FunWelF parseLn parseLn
-}

-- Parser for removing whitespace 
-- -----------------------------------------
lexeme :: IParser a -> IParser a 
lexeme p = wspace *> p <* wspace

wspace :: IParser String 
wspace = many $ char ' '







-- Top level parser
-- -----------------------------------------
pbtinfo :: IParser PBTInfo
pbtinfo = do
    fn <- lexeme strFN
    exprL <- between (char '{') (char '}') (spaces *> parseExprL <* spaces) -- <* spaces 
    --fi <- lexeme strFInfo
    --ab <- lexeme strAbsF
    --rr <- lexeme strRRel
    -- wf <- lexeme strWelF
    return $ PBTInfo fn (fromJust $ lookup "FI" exprL) (fromJust $ lookup "AB" exprL) (fromJust $ lookup "RR" exprL) --fi ab rr -- wf

-- Functions for interfacing with the parser
-- -----------------------------------------
pbtinfos :: IParser [PBTInfo]
pbtinfos = (spaces *> pbtinfo <* spaces) `manyTill` eof

parseFile :: FilePath -> ExceptT String IO [PBTInfo]
parseFile f = parsePBTFile pbtinfos f

parsePBTFile :: IParser a -> FilePath -> ExceptT String IO a
parsePBTFile p f = do
    pbtFLines <- case __cogent_pbt_info of 
                      Nothing -> undefined
                      Just f -> lift $ getPBTFile f
    case (iParse p "" (unlines pbtFLines)) of 
        Left err -> throwE $ "Error: Failed to parse PBT Info file: " ++ show err
        Right pbtF -> return pbtF

iParse :: IParser a -> SourceName -> String -> Either ParseError a
iParse aParser source_name input = runIndentParser aParser () source_name input

getPBTFile :: FilePath -> IO [String]
getPBTFile = liftA lines . readFile

-- Testing 
-- -------
testPBTParse :: IO ()
testPBTParse = pPrint $ iParse pbtinfos "" exampleFile

         
exampleFile :: String
exampleFile = unlines $
        [ "\"averageBag\" {\r"
        , "    pure: True , \r"
        , "    nond: False ,\r"
        , "    absf: direct, eq ; \r"
        , "        { IC: R4 Word32 Word32 \r"
        , "        , IA: (Int, Int) ; } , \r"
        , "    rrel: direct, eq; \r"
        , "        { OC: V0 () Word32 \r"
        , "        , OA: Maybe Int ; } ;\r"
        , "}\r"
        ]

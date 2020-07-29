-- PBT Parse file containing info used in PBT 
-- ------------------------------

module Cogent.Haskell.ParseDSL (parseFile, testPBTParse) where

import Cogent.Haskell.GenDSL
import Cogent.Compiler (__cogent_pbt_info)
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class
import Control.Applicative hiding ((<|>), optional, many)
import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Indent
import Text.Show.Pretty
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts (Type)
import Language.Haskell.Exts.SrcLoc
import Language.Haskell.Names.SyntaxUtils (dropAnn)


-- DSL Format Rules:
-- ------------------------------
-- fname must start function info, enclosed by quotes
-- fname is followed by keywords, until eof or another fname
-- keywords must have (:) on RHS, values is the following string until the eol

-- Indent Parser Type
-- ------------------------------
type IParser a = IndentParser String () a

keywords :: [String]
keywords = ["pure", "nond", "absf", "rrel", "welf"]
            ++ 
           ["IC", "IA", "OC", "OA"]

ignores :: [Char]
ignores = ['\"', '\r', '\n', ':']

-- PBT Info Parser helpers
-- ------------------------------

strCmt :: IParser String 
strCmt = string "--" *> anyChar `manyTill` (many1 endOfLine)

int :: (Integral a, Read a) => IParser a
int = read <$> many1 digit 

strComma :: IParser String
strComma = lexeme $ many1 (noneOf (ignores++[',']))

parseList :: IParser [String]
parseList = strComma `sepBy1` (char ',')
            <?> "Trying to parse list"
-- TODO: ^^ handle parantheses

--eol :: IParser String
--eol = many1 endOfLine

parseLn :: IParser (String, [String])
parseLn = do
    k <- strKW
    v <- parseList <* spaces -- <|> many strCmt -- <* spaces
    return (k,v)

parseTyps :: IParser (String, Type ())
parseTyps = do
    k <- strKW
    v <- lexeme $ strV <* spaces 
    let v' = dropAnn $ fromParseResult $ parseType v
    return (k,v')

--strToTyp :: IParser String -> IParser (Type ())
--strToTyp p = undefined

strKW :: IParser String 
strKW = strV <* char ':'

strV :: IParser String 
strV = many1 (noneOf ignores)

boolV :: IParser Bool 
boolV = read <$> strV

-- PBT Info Sub-component Parsing
-- ------------------------------
strFN :: IParser String 
strFN = between (char '"') (char '"') strV <* spaces
--char '"' *> strV <* char '"' <* spaces

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
    fi <- lexeme strFInfo
    ab <- lexeme strAbsF
    rr <- lexeme strRRel
    wf <- lexeme strWelF
    return $ PBTInfo fn fi ab rr wf

-- Functions for interfacing with the parser
-- -----------------------------------------
pbtinfos :: IParser [PBTInfo]
pbtinfos = pbtinfo `manyTill` eof

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
        [ "\"addToBag\"\r"
        , "    pure: True \r"
        , "    nond: False \r"
        , "    absf: direct \r"
        , "        IC: (Word32, R4 Word32 Word32) \r"-- U32, Bag \r"
        , "        IA: (Int, (Int, Int)) \r"
        , "    rrel: direct, eq \r"
        , "        OC: R4 Word32 Word32 \r"
        , "        OA: (Int, Int) \r"
        , "    welf: sum = sum List, count = length List\r"
        , "        List: normal 10, pos Int\r"
        , "\"averageBag\"\r"
        , "    pure: True \r"
        , "    nond: False \r"
        , "    absf: direct \r"
        , "        IC: R4 Word32 Word32 \r"
        , "        IA: (Int, Int) \r"
        , "    rrel: direct, eq \r"
        , "        OC: V0 () Word32 \r"
        , "        OA: Either () Int \r"
        , "    welf: sum = sum List, count = length List\r"
        , "        List: normal 10, pos Int\r"
        ]

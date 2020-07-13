-- PBT
-- Parse file containing info used in PBT 

module Cogent.Haskell.ParseDSL where

import Cogent.Haskell.GenDSL
import Text.ParserCombinators.Parsec
import Control.Applicative hiding ((<|>), optional, many)

-- Rules:
-- fname must start function info
-- fname must only have (:) on RHS
-- fname is followed by keywords, until string with no (-) on LHS is found or end keyword is reached (or eof unsure yet)
-- keywords must have (-) on LHS and (:) on RHS

keywords :: [String]
keywords = ["IP", "ND", "IA", "OA", "AI", "RO"]

seperators :: [String]
seperators = [":", "-"]

ignores :: [Char]
ignores = ['\"', '\r', '\n', ':']

returns :: [Char]
returns = ['\r', '\n']

ender :: String
ender = "end"

(<||>) :: Parser a -> Parser a -> Parser a 
p <||> q = try p <|> q

-- returns int as string
int :: (Integral a, Read a) => Parser a
int = read <$> many1 digit 

-- extract function name
-- defined as a string with (:) on its RHS
stringFName :: Parser String 
stringFName = char '"' *> strVal <* char '"' 

stringFInfo :: Parser FunInfo 
stringFInfo = do 
    ip <- strKeyW *> strVal
    nd <- strKeyW *> strVal
    return $ FunInfo (read ip) (read nd)

stringFTys :: Parser FunTypes
stringFTys = do 
    ia <- strKeyW *> strVal
    oa <- strKeyW *> strVal
    return $ FunTypes ia oa
    
stringFRels :: Parser FunRels
stringFRels = do 
    ia <- strKeyW *> strVal
    oa <- strKeyW *> strVal
    return $ FunRels ia oa

strVal :: Parser String 
strVal = many (noneOf ignores)

-- extract function keyword, defined as a string with (:) on its RHS and (-) on its LHS
strKeyW :: Parser String 
strKeyW = strVal <* char ':'

-- applies parser (oneOf " ") zero or more times, returning the list
wspace :: Parser String 
wspace = many $ oneOf " "

-- removes whitespaces from both sides (based of given Parser)
lexeme :: Parser a -> Parser a 
lexeme p = wspace *> p <* wspace

pbtinfo :: Parser PBTInfo
pbtinfo = do
    fn <- lexeme stringFName
    lexeme (many (oneOf returns))
    fi <- lexeme stringFInfo
    ft <- lexeme stringFTys
    fr <- lexeme stringFRels
    return $ PBTInfo fn fi ft fr

testParse :: IO ()
testParse = do
    print $ parse pbtinfo "" exampleFile

exampleFile :: String
exampleFile = unlines [
              "\"addToBag\"                             \r",
              "     IP: True                            \r",
              "     ND: False                           \r",
              "     IA: (Int, Int)                      \r",
              "     OA: (Int, Int)                      \r",
              "     AI: R4 Word32 Word32 -> (Int, Int)  \r",
              "     RO: ==                              \r" ,
              "end\r" 
              ]


{-
Ref:

-- Parse the anti-quoted C source code to produce a sequence of C definitions.

parseFile :: [Extensions] -> [String] -> FilePath -> ExceptT String IO [CS.Definition]
parseFile exts deftypnames filename = do
#if MIN_VERSION_language_c_quote(0,11,1)
  let start = Just $ startPos filename
#else
  let start = startPos filename
#endif
  s <- lift $ B.readFile filename
  typnames <- case __cogent_ext_types of Nothing -> lift (return deftypnames); Just f -> lift $ getTypnames f
  case CP.evalP (__fixme CP.parseUnit) (CP.emptyPState exts typnames s start) of -- FIXME: check for other antiquotes
    Left err -> throwE $ "Error: Failed to parse C: " ++ show err
    Right ds -> return ds
-}

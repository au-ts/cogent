-- PBT
-- Parse file containing info used in PBT 

module Cogent.Haskell.ParseDSL where

import Cogent.Haskell.GenDSL
import Cogent.Compiler (__cogent_pbt_info)
import Control.Applicative hiding ((<|>), optional, many)
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class
import qualified Data.ByteString.Char8 as B
import Text.ParserCombinators.Parsec
import Text.Parsec.Char
import Text.Show.Pretty


-- Rules:
-- fname must start function info, enclosed by quotes
-- fname is followed by keywords, until eof or another fname
-- keywords must have (:) on RHS, values is the following string until the eol

keywords :: [String]
keywords = ["IP", "ND", "IA", "OA", "AI", "RO"]

ignores :: [Char]
ignores = ['\"', '\r', '\n', ':']

(<||>) :: Parser a -> Parser a -> Parser a 
p <||> q = try p <|> q

-- returns int as string
int :: (Integral a, Read a) => Parser a
int = read <$> many1 digit 

-- extract function name
-- defined as a string with (:) on its RHS
stringFName :: Parser String 
stringFName = char '"' *> strVal <* char '"' <* wspace <* eol

stringFInfo :: Parser FunInfo 
stringFInfo = do 
    ip <- strKeyW *> strVal <* eol
    nd <- strKeyW *> strVal <* eol
    return $ FunInfo (read ip) (read nd)

stringFTys :: Parser FunTypes
stringFTys = do 
    ia <- strKeyW *> strVal <* eol
    oa <- strKeyW *> strVal <* eol
    return $ FunTypes ia oa
    
stringFRels :: Parser FunRels
stringFRels = do 
    ia <- strKeyW *> strVal <* eol 
    oa <- strKeyW *> strVal <* eol
    return $ FunRels ia oa

eol :: Parser String
eol = choice [ string "\n\r", string "\r\n"
             , string "\n", string "\r"] 

strVal :: Parser String 
strVal = many (noneOf ignores)

-- extract function keyword, defined as a string with (:) on its RHS and (-) on its LHS
strKeyW :: Parser String 
strKeyW = strVal <* char ':'

-- applies parser (oneOf " ") zero or more times, returning the list
wspace :: Parser String 
wspace = many $ char ' '

-- removes whitespaces from both sides (based of given Parser)
lexeme :: Parser a -> Parser a 
lexeme p = wspace *> p <* wspace

pbtinfo :: Parser PBTInfo
pbtinfo = do
    fn <- lexeme stringFName
    fi <- lexeme stringFInfo
    ft <- lexeme stringFTys
    fr <- lexeme stringFRels
    return $ PBTInfo fn fi ft fr

pbtinfos :: Parser [PBTInfo]
pbtinfos = pbtinfo `manyTill` eof

testPBTParse :: IO ()
testPBTParse = pPrint $ parse pbtinfos "" exampleFile

--parseFile :: FilePath -> ExceptT String IO Parser [PBTInfo]
--parseFile f = parsePBTFile pbtinfos f

-- Parse the PBT DSL info file to produce a sequence of PBTInfo definitions.
parsePBTFile :: Parser a -> FilePath -> ExceptT String IO a
parsePBTFile p f = do
    pbtFLines <- case __cogent_pbt_info of 
                      Nothing -> undefined
                      Just f -> lift $ getPBTFile f
    case (parse p "" (unlines pbtFLines)) of 
        Left err -> throwE $ "Error: Failed to parse PBT Info file: " ++ show err
        Right pbtF -> return pbtF

getPBTFile :: FilePath -> IO [String]
getPBTFile = liftA lines . readFile



exampleFile :: String
exampleFile = unlines [
              "\"addToBag\"                             \r",
              "     IP: True                            \r",
              "     ND: False                           \r",
              "     IA: (Int, Int)                      \r",
              "     OA: (Int, Int)                      \r",
              "     AI: R4 Word32 Word32 -> (Int, Int)  \r",
              "     RO: ==                              \r",
              "\"averageBag\"                           \r",
              "     IP: True                            \r",
              "     ND: False                           \r",
              "     IA: (Int, Int)                      \r",
              "     OA: Int                             \r",
              "     AI: R4 Word32 Word32 -> (Int, Int)  \r",
              "     RO: ==                              \r" 
              ]
-- REF:
-- Parse the anti-quoted C source code to produce a sequence of C definitions.
{-
parseFile :: FilePath -> ExceptT String IO [CS.Definition]
parseFile filename = do
  let start = startPos filename
  s <- lift $ B.readFile filename
  typnames <- case __cogent_ext_types of 
            Nothing -> lift (return deftypnames); 
            Just f -> lift $ getTypnames f
  case CP.evalP (__fixme CP.parseUnit) (CP.emptyPState exts typnames s start) of -- FIXME: check for other antiquotes
    Left err -> throwE $ "Error: Failed to parse C: " ++ show err
    Right ds -> return ds



glue :: [FilePath] -> ExceptT String IO [(FilePath, [CS.Definition])]
glue s typnames mode filenames = liftA (M.toList . M.fromListWith (flip (++)) . concat) .
  forM filenames $ \filename -> do
    ds <- parseFile defaultExts typnames filename

-}

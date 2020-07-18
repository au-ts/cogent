-- PBT
-- Parse file containing info used in PBT 

module Cogent.Haskell.ParseDSL (parseFile, testPBTParse) where

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
keywords = ["pure", "nond", "absf", "rrel", "welf"]
            ++ 
           ["IC", "IA", "OC", "OA"]

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
stringFName = char '"' *> strVal <* char '"' 
                <* ((wspace <* many1 eol) <||> many1 eol)

stringFInfo :: Parser FunInfo 
stringFInfo = do 
    ip <- strKeyW *> strVal <* eol
    nd <- strKeyW *> strVal <* eol
    return $ FunInfo (read ip) (read nd)

stringAbsF :: Parser FunAbsF
stringAbsF = do 
    ab <- strKeyW *> strVal <* eol
    ic <- strKeyW *> strVal <* eol
    ia <- strKeyW *> strVal <* eol
    return $ FunAbsF ab ic ia
    
stringRRel :: Parser FunRRel
stringRRel = do 
    rr <- strKeyW *> strVal <* eol 
    oc <- strKeyW *> strVal <* eol 
    oa <- strKeyW *> strVal <* eol
    return $ FunRRel rr oc oa

stringWelF :: Parser FunWelF
stringWelF = do 
    wf <- strKeyW *> strVal <* eol 
    ts <- strKeyW *> strVal <* eol 
    return $ FunWelF wf [ts]

eol :: Parser Char
eol = endOfLine
-- choice [newline, crlf] 
        -- [ string "\n\r", string "\r\n"
--      <?> "end of line"

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
    ab <- lexeme stringAbsF
    rr <- lexeme stringRRel
    wf <- lexeme stringWelF
    return $ PBTInfo fn fi ab rr wf

pbtinfos :: Parser [PBTInfo]
pbtinfos = pbtinfo `manyTill` eof

parseFile :: FilePath -> ExceptT String IO [PBTInfo]
parseFile f = parsePBTFile pbtinfos f

getPBTFile :: FilePath -> IO [String]
getPBTFile = liftA lines . readFile

-- Parse the PBT DSL info file to produce a sequence of PBTInfo definitions.
parsePBTFile :: Parser a -> FilePath -> ExceptT String IO a
parsePBTFile p f = do
    pbtFLines <- case __cogent_pbt_info of 
                      Nothing -> undefined
                      Just f -> lift $ getPBTFile f
    case (parse p "" (unlines pbtFLines)) of 
        Left err -> throwE $ "Error: Failed to parse PBT Info file: " ++ show err
        Right pbtF -> return pbtF

testPBTParse :: IO ()
testPBTParse = pPrint $ parse pbtinfos "" exampleFile

exampleFile :: String
exampleFile = unlines $
        [ "\"addToBag\"     \r"
        , "    pure: True\r"
        , "    nond: False\r"
        , "    absf: direct\r"
        , "        IC: U32, Bag \r"
        , "        IA: Int, (Int, Int) \r"
        , "    rrel: direct (==)\r"
        , "        OC: Bag\r"
        , "        OA: Tuple \r"
        , "    welf: sum = sum List, count = length List\r"
        , "        List: normal at 10, arbitrary Pos Int\r"
        , "\"averageBag\"\r"
        , "    pure: True\r"
        , "    nond: False\r"
        , "    absf: direct\r"
        , "        IC: Bag\r"
        , "        IA: Tuple\r"
        , "    rrel: direct (==)\r"
        , "        OC: EmptyBag | Success U32\r"
        , "        OA: Either \r"
        , "    welf: sum = sum List, count = length List\r"
        , "        List: normal at 10, arbitrary Pos Int\r"
        ]
{-
= unlines [
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
              -}

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

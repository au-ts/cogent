{-# LANGUAGE MultiWayIf #-}

module Cogent.Haskell.PBT.DSL.Parser (parsePbtDescFile) where

import Cogent.Haskell.PBT.DSL.Types
import Cogent.Compiler (__cogent_pbt_info, __impossible)
import qualified Language.Haskell.Exts.Syntax as HSS (Exp(..), Type(..))
import qualified Language.Haskell.Exts.Parser as HSP (parseTypeWithComments, fromParseResult, ParseMode(..), parseExpWithComments)
import qualified Language.Haskell.Exts.Extension as HSE (Language(..), knownExtensions)
import qualified Language.Haskell.Exts.Fixity as HSF (infixl_, preludeFixities, baseFixities)
import qualified Language.Haskell.Names.SyntaxUtils as HSN (dropAnn)
import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Indent
import Text.Show.Pretty
import Control.Monad.Trans.Except
import Control.Monad (guard)
import Control.Monad.Trans.Class
import Control.Applicative hiding ((<|>), optional, many)
import Data.List (find, isInfixOf)
import Data.List.Extra (trim)
import Data.Maybe
import Data.Functor
import Debug.Trace

-- Parser type
type Parser a = Parsec String () a

-- Top level parser functions (for parsing PBT description file, aka: __cogent_pbt_info)
-- -----------------------------------------
parsePbtDescFile :: FilePath -> ExceptT String IO [PbtDescStmt]
parsePbtDescFile f = pPbtFile pStmts f

readPbtFile = fmap lines . readFile

pPbtFile :: Parser a -> FilePath -> ExceptT String IO a
pPbtFile p f = do
    pbtFileLs <- case __cogent_pbt_info of
                   Just f -> lift $ readPbtFile f
                   Nothing -> undefined
    case Text.Parsec.parse p "" (unlines pbtFileLs) of
        Right pbtF -> return pbtF
        Left err -> throwE $ "Error: Failed to parse PBT Info file: " ++ show err

-- PBT DSL statement
-- -----------------------------------------
pStmts :: Parser [PbtDescStmt]
pStmts = pspaces pStmt `manyTill` eof

pStmt :: Parser PbtDescStmt
pStmt = do
    fname <- pspaces $ pbetweenQuotes pstrId
    -- TODO: lookAhead for checking for args 
    decls <- pspaces $ pbetweenCurlys pDecls
    return $ PbtDescStmt fname decls

-- PBT DSL declarations
-- -----------------------------------------
pDecls :: Parser [PbtDescDecl]
pDecls = pDecl `manyTillLookAhead` rcurly

pDecl :: Parser PbtDescDecl
pDecl = do
    k <- pstrId <* lookAhead lcurly
    exprs <- pspaces $ pbetweenCurlys (pExprs (toPbtTyp k))
    return $ PbtDescDecl (toPbtTyp k) exprs

-- PBT DSL expressions
-- -----------------------------------------
pExprs :: PbtKeyword -> Parser [PbtDescExpr]
pExprs b = (pExpr b) `sepEndBy` pspaces semi

pExpr :: PbtKeyword -> Parser PbtDescExpr
pExpr block = do
    -- TODO: check for comment here 
    lhs <- try (pspaces predOp) <|> pstrId
    if (lhs == predStr) then pExpr' else pExpr'' lhs block

pExpr'' lhs block = do
    op <- lookAhead $     try mapOp 
                      <|> try predOp
                      <|> try typOp 
                      <|> endOp -- check for end of exp, i.e. no RHS
    let (ident, v) = if trim lhs `elem` keyidents
                        then ( trim lhs
                             , find (`isInfixOf` lhs) keyidents )
                        else ( case find (`isInfixOf` lhs) keyidents of
                                 Just x -> x
                                 Nothing -> __impossible $ "LHS must contain a key identifier: one of " ++ show keyidents
                             , Just lhs )
    case v of
       Just x -> if | op == typStr -> pTypExpr x
                    | op == mapStr -> pMapExpr x block
                    | op == predStr -> pPredExpr x
                    | otherwise -> pJustExpr x
       Nothing ->  pJustExpr lhs


pExpr' :: Parser PbtDescExpr
pExpr' = do
    e <- pHsExp
    let ident = case find (`isInfixOf` e) keyidents of
                  Just x -> x
                  Nothing -> __impossible $ "Predicate must contain a key identifier: one of " ++ show keyidents
    return $ PbtDescExpr (Just (toPbtTyp' "pred")) Nothing $ Just $ Right (parseHsExp e)

pTypExpr lhs = do
    e <- typOp *> pHsExp
    let t = toPbtTyp' lhs
    return $ PbtDescExpr (Just t) Nothing $
        -- prevent cogent syntax from being parsed as HS syntax
        if t == Ic || t == Oc then Nothing else Just $ Left (parseHsTyp e)

pMapExpr lhs block = do
    e <- mapOp *> pHsExp
    let (lhsId, lhsExp) = if (any (==trim lhs) keyidents) then (trim lhs, Nothing)
                          else ( fromMaybe (
                                    if | block == Welf -> "ic"
                                       | block == Rrel -> "pred"
                                       | block == Absf -> "ia"
                                       | otherwise -> "pred"
                                 ) $ find (`isInfixOf` lhs) keyidents
                               , Just (parseHsExp lhs))
    let x = PbtDescExpr (Just (toPbtTyp' lhsId)) lhsExp $ Just $ Right (parseHsExp e)
    return $ x

pPredExpr lhs = do
    e <- predOp *> pHsExp
    let (lhsId, lhsExp) = if (any (==trim lhs) keyidents) then (trim lhs, Nothing)
                          else ( fromMaybe (__impossible $ "RHS transform must contain a key identifier: one of " ++ show keyidents
                                 ) $ find (`isInfixOf` lhs) keyidents
                               , Just (parseHsExp lhs))
    let x = PbtDescExpr (Just (toPbtTyp' "pred")) lhsExp $ Just $ Right (parseHsExp e)
    return $ x

pJustExpr lhs = return $ PbtDescExpr Nothing Nothing $ Just $ Left (parseHsTyp lhs)

-- Parsing Identifiers/Hs Exps transforming identifiers
-- ----------------------------------------------------
pHsExp :: Parser String
pHsExp = pspaces $ many1 $ noneOf $ hsExpStopChars

pstrId :: Parser String
pstrId = pspaces $ many1 $ noneOf $ stopChars

-- Combinators for parsing structure
-- -----------------------------------------
pspaces :: Parser a -> Parser a
pspaces a = spaces *> a <* spaces

pbetweenCurlys :: Parser a -> Parser a
pbetweenCurlys a = between lcurly rcurly a

pbetweenQuotes :: Parser a -> Parser a
pbetweenQuotes a = between backtic backtic a

manyTillLookAhead p1 p2 = p1 `manyTill` (lookAhead $ try p2)

-- Operators / Strings / Chars / Key-Identifiers
-- -----------------------------------------
-- key identifiers
keyidents = ["ia","oa","ic","oc"]

-- chars for when parsing of Hs syntax will stop
-- important these don't overlap with HS syntax
hsExpStopChars = [semiCh]

-- chars for when parsing of PBT DSL syntax will stop
stopChars = [ backticCh     -- func name
            , colCh         -- operator
            , semiCh        -- end exp
            -- , eqlCh         
            , lcurlyCh , rcurlyCh , '\r' , '\n' ]

-- important (for structure) chars
lcurly = char lcurlyCh
rcurly = char rcurlyCh
backtic = char backticCh
semi = char semiCh

-- important operators
typOp = string typStr
mapOp = string mapStr
-- eqlOp = string eqlStr
predOp = string predStr
endOp = try (string semiStr) <|> string rcurlyStr

-- Operator strings
typStr = ":"
mapStr = ":="
-- eqlStr = "=="
predStr = ":|"  -- :| <hs-exp> ;
semiStr = ";"
rcurlyStr = "}"

-- Operator chars
semiCh = ';'
colCh = ':'
backticCh = '`'
lcurlyCh = '{'
rcurlyCh = '}'
-- eqlCh = '='
-- predCh = '|'

-- Converting to Strings to Types
-- -----------------------------------------
toPbtTyp "absf" = Absf
toPbtTyp "rrel" = Rrel
toPbtTyp "welf" = Welf
toPbtTyp "pure" = Pure
toPbtTyp "nond" = Nond
toPbtTyp "spec" = Spec
toPbtTyp s = toPbtTyp . trim $ s

toPbtTyp' "ic" = Ic
toPbtTyp' "ia" = Ia
toPbtTyp' "oc" = Oc
toPbtTyp' "oa" = Oa
toPbtTyp' "pred" = Pred
toPbtTyp' s = toPbtTyp' . trim $ s

parseHsTyp :: String -> HSS.Type ()
parseHsTyp = HSN.dropAnn . HSP.fromParseResult . (\x -> fst <$> HSP.parseTypeWithComments parseMode x)

parseHsExp :: String -> HSS.Exp ()
parseHsExp = HSN.dropAnn . HSP.fromParseResult . (\x -> fst <$> HSP.parseExpWithComments parseMode x)

parseMode = HSP.ParseMode "unknown" HSE.Haskell2010 HSE.knownExtensions True True (Just $ fixes) True
    -- note: have to give lens/prism operators their correct fixity to successfully parse
    where fixes = HSF.infixl_ 8 ["^.", "^?"] ++ HSF.preludeFixities ++ HSF.baseFixities

-- Debugging/Testing
-- -----------------------------------------
println a = traceShowM a

seeNext :: Int -> Parser ()
seeNext n = do
  s <- getParserState
  let out = take n (stateInput s)
  println out

testPBTParse :: IO ()
testPBTParse = pPrint $ Text.Parsec.parse pStmts "" exampleFile

exampleFile :: String
exampleFile = unlines $
        [ "`averageBag` {                 \r"
        , "    pure { True }                \r"
        , "    nond { False }               \r"
        , "    spec {                       \r"
        , "         ia : (Int, Int);        \r"
        , "         oa : R4 Word32 Word32;  \r"
        , "         oa := ia ^. _1 `div` ia ^. _2;               \r"
        , "    }                            \r"
        , "    absf {                       \r"
        --, "         ic : R4 Word32 Word32;  \r"
        , "         ia : (Int, Int);        \r"
        , "         ia := ic ;               \r"
        , "    }                            \r"
        , "    rrel {                       \r"
        -- , "       oc : < Failure | Success U32 > ;      \r"
        , "       oa : Maybe Int;         \r"
        , "       :| (oa ^? _Just) == (oc ^? _V0_Success <&> fromIntegral) ;              \r"
        , "    }                            \r"
        , "    welf {                       \r"
        , "       (ic ^. sum) :| (ic ^. sum) > (ic ^. count) ; \r"
        , "    }                            \r"
        , "}                                \r"
        , "`addToBag` {                 \r"
        , "    pure { True }                \r"
        , "    nond { False }               \r"
        , "    absf {                       \r"
        , "         ic : (Word32, R4 Word32 Word32);  \r"
        , "         ia : Int;        \r"
        , "         ia := ic ^. _2 . sum ;                    \r"
        -- , "               ic ^. count;               \r"
        , "    }                            \r"
        , "    rrel {                       \r"
        , "         oc : V0 () Word32;      \r"
        , "         oa : Maybe Int;         \r"
        -- , "         oa := oc ;               \r"
        , "    }                            \r"
        , "    welf {                       \r"
        , "        ic ^. _1 := choose(0, 1000) ;                       \r"
        , "        ic ^. _2 . sum :| ic ^. _2 . sum >= ic ^. _2 . count; \r"
        , "    }                            \r"
        , "}                                \r"
        ]

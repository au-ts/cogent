module Cogent.PrettifyLexer where
-- currently not in lexer:
--  :<
--  the < == thing


-- changes:
-- doc, // and /// instead of @ and @@
-- type app, @ instead of []
-- composition, |> and <| instead of "o"

-- TODO:
-- indexing, []
-- 
-- let success error branch
-- Quantifier
-- something with error handling (replacing the original |>)
-- indentation
-- ignore indentation when \ followed by \n

import Data.Char(isSpace, isAlpha, isDigit, isUpper, isAlphaNum)
import qualified Data.Map as M

data SourcePos
    = Pos { col :: Int
          , line :: Int
          , file :: FilePath
          }
        deriving (Show)

data Token
    = Kwd Keyword
    | Plus | Minus | Times | Divide | Modulo
    | LAnd | LOr
    | GEq | LEq | Gt | Lt | Eq | NEq
    | BAnd | BOr | BXor | LShift | RShift
    | Col | Define | Bar | Bang
    | Dot | DDot | Underscore | Hash | Comma
    | Unbox | TypeApp
    | LAngle | RAngle | LParen | RParen | LBracket | RBracket | LBrace | RBrace
    | TildeArrow | Arrow | ThickArrow
    | Number Int
    | UpperIdent String
    | LowerIdent String
    | StringLit String
    | Comment String
    | Doc String
    | Indent Int | Dedent | Shimdent
    | Unknown Char
    deriving(Show)

data Keyword 
    = Let | In | Except | Type | Include | All | Take | Put
    | Inline | Upcast | Repr | Variant | Record | At
    | If | Then | Else | Not | Complement | And | Fn
    | Drop | Share | Escape
    deriving(Show)

symTokens :: M.Map String Token
symTokens = M.fromList 
            [ (".&.", BAnd)
            , (".|.", BOr)
            , (".^.", BXor)
            , ("&&", LAnd)
            , ("||", LOr)
            , (">=", GEq)
            , ("<=", LEq)
            , ("==", Eq)
            , ("/=", NEq)
            , ("<<", LShift)
            , (">>", RShift)
            , ("..", DDot)
            , ("->", Arrow)
            , ("=>", ThickArrow)
            , ("~>", TildeArrow)
            , ("+", Plus)
            , ("-", Minus)
            , ("*", Times)
            , ("/", Divide)
            , ("%", Modulo)
            , (":", Col)
            , ("=", Define)
            , ("!", Bang)
            , ("|", Bar)
            , (".", Dot)
            , ("_", Underscore)
            , ("#", Hash)
            , ("@", TypeApp)
            , ("<", LAngle)
            , (">", RAngle)
            , ("(", LParen)
            , (")", RParen)
            , ("[", LBracket)
            , ("]", RBracket)
            , ("{", LBrace)
            , ("}", RBrace)
            , (",", Comma)
            ]

preprocess :: SourcePos -> String -> [(Char, SourcePos)]
preprocess p [] = [('\0',p)]
preprocess p ('\n':cs) = ('\n',p):preprocess (p {col = 0, line = line p + 1}) cs
preprocess p (c:cs) = (c,p):preprocess (p {col = col p + 1}) cs
    
lexer :: [(Char, SourcePos)] -> [Int] -> [(Token, SourcePos)]
lexer [('\0',p)] stack = map (const (Dedent, p)) stack

lexer cs stack      | take 2 (map fst cs) == "--"
                   = let (comment, rest) = span ((/= '\n') . fst) cs
                     in (Comment (map fst comment), snd (head comment)): lexer rest stack
lexer cs stack       | take 2 (map fst cs) == "//"
                   = let (docStr, rest) = span ((/= '\n') . fst) cs
                     in (Doc (map fst docStr), snd (head docStr)): lexer rest stack
lexer (c:cs) stack   | fst c == '"'
                   = let (string, rest) = span ((/= '"') . fst) cs
                     in (StringLit (map fst string), snd c): lexer (drop 1 rest) stack
                   
lexer cs stack      | Just t <- M.lookup (take 3 (map fst cs)) symTokens 
                   = (t, snd(head cs)):lexer (drop 3 cs) stack
lexer cs stack       | Just t <- M.lookup (take 2 (map fst cs)) symTokens 
                   = (t, snd(head cs)):lexer (drop 2 cs) stack
lexer cs stack       | take 2 (map fst cs) == "\\\n"
                   = let cs' = dropWhile (isSpace . fst) (drop 1 cs)
                     in lexer cs' stack
lexer (c:cs) stack | fst c == '\n'
                = let (indentation, rest) = span ((== ' ') . fst) cs
                      indent = length indentation
                      (as, bs) = span (> indent) stack 
                      top = case bs of
                            [] -> 0
                            (x:_) -> x
                      stack' = if indent > top then (indent:bs) else bs
                      (pipe, rest') = case rest of
                              (('|', p):rest') -> ([(Bar, p)], rest')
                              _                -> ([], rest)
                  in map (const (Dedent, snd c)) as 
                  ++ (if indent > top then [(Indent indent, snd c)] else []) 
                  ++ lexer rest' stack'
lexer (c:cs) stack | fst c == '|'
                   = let stack' = (col (snd c)):stack
                     in [(Shimdent, snd c), (Bar, snd c)]++lexer cs stack'

lexer cs stack       | Just t <- M.lookup (take 1 (map fst cs)) symTokens 
                   = (t, snd(head cs)):lexer (drop 1 cs) stack
lexer (c:cs) stack   | isSpace (fst c) = lexer cs stack

lexer (c:cs) stack | isAlpha (fst c) = let
    (word, rest) = span (\(x,_) -> isAlphaNum x || x `elem` "_'") (c:cs)
    in (toToken (map fst word), snd c) : lexer rest stack
    where
        toToken :: String -> Token
        toToken "let" = Kwd Let
        toToken "in" = Kwd In
        toToken "type" = Kwd Type
        toToken "include" = Kwd Include
        toToken "all" = Kwd All
        toToken "take" = Kwd Take
        toToken "put" = Kwd Put
        toToken "inline" = Kwd Inline
        toToken "upcast" = Kwd Upcast
        toToken "repr" = Kwd Repr
        toToken "variant" = Kwd Variant
        toToken "record" = Kwd Record
        toToken "at" = Kwd At
        toToken "if" = Kwd If
        toToken "then" = Kwd Then
        toToken "else" = Kwd Else
        toToken "not" = Kwd Not
        toToken "complement" = Kwd Complement
        toToken "and" = Kwd And
        toToken str@(x:xs) = 
            if isUpper x then UpperIdent str else LowerIdent str


lexer (c:cs) stack | isDigit (fst c) = let
    (numStr, rest) = span (isDigit . fst) (c:cs)
    in (Number (read (map fst numStr)), snd c): lexer rest stack

lexer (c:cs) stack = (Unknown (fst c), snd c) : lexer cs stack
lexer _ stack = []

lexFile :: FilePath -> IO [(Token, SourcePos)]
lexFile fp = do 
    contents <- readFile fp
    pure (lexer (preprocess initialSourcePos contents) [])
  where
    initialSourcePos = Pos 0 0 fp
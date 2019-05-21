-- currently not in lexer:
--  :<
--  the < == thing


-- changes:
-- doc, // and /// instead of @ and @@
-- type app, @ instead of []
-- got rid of $

-- TODO:
-- indexing, []
-- add composition, |> and <|
-- new syntax for lambda
-- let success error branch
-- Quantifier

import Data.Char(isSpace, isAlpha)

data Token
    = Kwd Keyword
    | Plus | Times | Divide | Modulo
    | Land | Lor
    | Geq | Leq | Gt | Lt | Eq | Neq
    | Band | Bor | Bxor | Lshift | Rshift
    | Col | Assgn | Bar | Bang
    | Dot | Ddot | Underscore | 
    | Unbox | Typeapp | 
    | Llikely | Likely | MLikely
    deriving(Show)

data Keyword 
    = Let | In | Type | Include | All | Take | Put
    | Inline | Upcast | Repr | Variant | Record | At
    | If | Then | Else | Not | Complement | And | True | False | O  -- what is "o"?

lexer :: String -> [Token]
lexer [] = []
lexer (' ':cs) = lexer cs
lexer ('\n':cs) = lexer cs
lexer (c:cs) | isSpace c = lexer cs
lexer ('+':cs) = Plus : lexer cs
lexer ('*':cs) = Times : lexer cs
lexer ('/':cs) = Divide : lexer cs
lexer ('%':cs) = Modulo : lexer cs
lexer ('&':'&':cs) = Land : lexer cs
lexer ('|':'|':cs) = Lor : lexer cs
lexer ('>':'=':cs) = Gt : lexer cs
lexer ('<':'=':cs) = Lt : lexer cs
lexer ('=':'=':cs) = Eq : lexer cs
lexer ('/':'=':cs) = Neq : lexer cs
lexer ('.':'&':'.':cs) = Band : lexer cs
lexer ('.':'|':'.':cs) = Bor : lexer cs
lexer ('.':'^':'.':cs) = Bxor : lexer cs
lexer ('<':'<':cs) = Lshift : lexer cs
lexer ('>':'>':cs) = Rshift : lexer cs
lexer (':':cs) = Col : lexer cs
lexer ('=':cs) = Assgn : lexer cs
lexer ('!':cs) = Bang : lexer cs
lexer ('|':cs) = Bar : lexer cs
lexer ('.':cs) = Dot : lexer cs
lexer ('.':'.':cs) = Ddot : lexer cs
lexer ('_':cs) = Underscore : lexer cs
lexer ('#':cs) = Unbox : lexer cs
lexer ('@':cs) = Typeapp : lexer cs
lexer ('-':'>':cs) = Likely : lexer cs
lexer ('=':'>':cs) = MLikely : lexer cs
lexer ('~':'>':cs) = LLikely : lexer cs
lexer (c:cs) | isAlpha c = let
    (word, rest) = span isAlpha (c:cs)
    in checkKeyword word : lexer rest
    where
      -- check keyword stuff

lexer _ = []

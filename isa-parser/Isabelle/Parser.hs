--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE FlexibleContexts, GADTs, LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

module Isabelle.Parser where
--
-- System imports
--
import Control.Applicative hiding (many)
import Control.Monad.Identity 
import Data.Char (isSpace)
import Data.List
import Data.Monoid
import qualified Text.Parsec as P
import Text.Parsec hiding ((<|>))
import Text.Parsec.Expr
-- import Debug.Trace

-- friends
import Isabelle.InnerAST
import Isabelle.OuterAST
import Isabelle.PrettyHelper

type OperatorM a = Operator String () Identity a

--------------------------------------------------------------------------------
-- Introduction
--------------------------------------------------------------------------------

--
-- The parser is also a scanner/lexer (i.e. the tokens are just characters). Each parser is a
-- "lexeme parser" which means it parses what it expects and any trailing white space.
-- 
--

type ParserM a = Parsec String () a

--
-- Important: Do not nest uses of the @many@ combinator. Why? The |many| combinator cannot be
-- applied to parsers which accept the empty string. It will cause a run-time error if it is applied
-- to an empty string. However, @many p@ where @p@ is a parser will accept the empty string. Thus,
-- something like @many (many p)@ will not work.
--

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

--
-- |reservedWords| is a collection of names that cannot be identifiers
-- (i.e. be parsed by |nameL|)
--
-- FIXME: This is just for the "theory" language. Need to think about
-- what comes between "begin" and "end"
-- FIXME: Model as a data structure and then feed this data structure into @reserved@ combinator.
--
-- FIXME: I'm concerned that there is no notion of globally reserved words. Some words are (perhaps)
-- reserved only at certain levels within the parse e.g. top-level parser vs. theory parser
-- vs. definition parser
--
-- FIXME: Don't duplicate the names here and elsewhere. Define as one constant in one place.
--

reservedWords :: [String]
reservedWords = [
  "abbreviation", "and", "apply", "apply_end", "assumes", "begin", "by", "chapter", "class", "consts",
  "datatype", "definition", "defs", "domintros", "done", "end", "fixes", "for", "fun",
  "function", "imports", "instance", "instantiation", "is", "keywords", "lemma", "lemmas",
  "no_translations", "open", "overloaded", "primrec", "record ", "section", "sequential", "sorry",
  "subsection", "subsubsection", "termination", "text", "theorems", "theory", "translations",
  "type_synonym", "typedecl", "unchecked", "uses", "where", "declare"]

reservedWordsInner = ["case", "of", "if", "then", "else", "do", "od", "let", "in", "o"]

---------------------------------------------------------------
-- Utility functions and combinators
-------------------------------------------------------------

lift :: Monad m => (a -> b) -> m a -> m b
lift f m = m >>= return . f

concatP :: Monoid m => ParserM [m] -> ParserM m
concatP m = m >>= return . foldl mappend mempty

manyP :: Monoid m => ParserM m -> ParserM m
manyP = concatP . many

manyP1 :: Monoid m => ParserM m -> ParserM m
manyP1 = concatP . many1

mb :: ParserM a -> ParserM (Maybe a)
mb p = option Nothing (Just <$> p)

--
-- For the sake of correctness I've decided to throw the notion of efficiency out the window and
-- define my own "alternative" combinator that applies "try" to the first argument. With this
-- combinator, the problem where the first parser @p@ fails, but consumes some input in the process
-- causing parser @q@ not to succeed does not occurr.
--
infixr 1 <||>
p <||> q = try $ (try p P.<|> q)

--
-- FIXME: Note the use of "try". May remove later to improve performance
--
infixr 5 <++>
(<++>) :: Monoid m => ParserM m -> ParserM m -> ParserM m
p <++> q = try $ do { x <- p; y <- q; return (x `mappend` y)  }

oneStringOf :: [String] -> ParserM String
oneStringOf [] = error "Must be applied to at least one parser"
oneStringOf ss = foldl1 (<||>) (map string ss)

parensL :: ParserM a -> ParserM a
parensL p = do { stringL "("; r <- p; stringL ")"; return r }

quotedL :: ParserM a -> ParserM a
quotedL p = do { stringL "\""; r <- p; stringL "\""; return r }

bracketL :: ParserM a -> ParserM a 
bracketL p = do { stringL "["; r <- p; stringL "]"; return r }

bracesL :: ParserM a -> ParserM a 
bracesL p = do { stringL "{"; r <- p; stringL "}"; return r }

--------------------------------------------------------------------------------
-- Primitive parsers
--------------------------------------------------------------------------------

--
-- NOTE: The perils of lexeme parsers
--
-- Most of the time Parsec is used as a "scanner-less" parser library.  This means that there is no
-- separate lexical analysis phase. i.e. the input is not tokenized.
--
-- The common solution is to define everything as a lexeme parser, a parser that accepts a token
-- /and/ its trailing white space (/zero/ or more characters of it)
--
-- However, you don't want this behaviour for identifiers or reserved words. It's common that a
-- name/identifier could have a reserved word as its prefex. e.g. "and" is a reserved word by "andy"
-- isn't.
--

--
-- In this file we have the convention that parsers ending in a 'L' are "lexeme parsers". They
-- consume trailing whitespace.
-- See |lexeme|
--
-- Parsers ending in an 'S' are parsers that are NOT lexeme parsers.
--

--
-- @lexeme@ takes a parser @p@ and turns it into a parser that parses what @p@ does plus any
-- trailing white space (/zero/ or more characters)
--
lexeme :: ParserM a -> ParserM a
lexeme p = do { s <- p; many (satisfy isSpace); return s }

importsL :: ParserM TheoryImports
importsL = do
  reserved "imports"
  ns <- many1 nameL
  return (TheoryImports ns)
  
--
-- |reserved' s| expects the reserved word |s| and nothing else.
--
-- FIXME: Need to check that string is actually a reserved word and not a word that is longer than
-- it e.g. "androgenous" has prefix "and".
--
reserved :: String -> ParserM ()
reserved = lexeme . reservedS
  where
    reservedS :: String -> ParserM ()
    reservedS s = do { try (sequence (map char s))
                     ; notFollowedBy quasiletterS
                     ; return () } <?> ("reserved word '" ++ s ++ "'")

identS :: ParserM String
identS = letterS <++> manyP quasiletterS

identSL :: ParserM String
identSL = letterS <++> manyP quasiletterSL

identL :: ParserM String
identL = lexeme . try $
  do { s <- identS 
     ; if s `elem` reservedWordsInner
       then unexpected ("'" ++ s ++ "' is a reserved word")
       else return s }

identLL :: ParserM String
identLL = lexeme . try $
  do { s <- identSL 
     ; if s `elem` reservedWordsInner
       then unexpected ("'" ++ s ++ "' is a reserved word")
       else return s }

antiquoteS :: ParserM String 
antiquoteS = char '$' >> lookAhead anyChar >>= \case
               '(' -> char '(' >> hsExprL 0 ""
               _   -> identS 

hsExprL :: Int -> String -> ParserM String
hsExprL = (lexeme .) . hsExprS

hsExprS :: Int -> String -> ParserM String
hsExprS depth s = anyChar >>= \case
            '(' -> hsExprL (depth+1) ('(':s)
            ')' | depth == 0 -> return $ reverse s
                | otherwise  -> hsExprL (depth-1) (')':s)
            c -> hsExprL depth (c:s)

antiquoteL :: ParserM String 
antiquoteL = lexeme antiquoteS 

antiquoteNameS :: ParserM String 
antiquoteNameS = ('$':) <$> antiquoteS

letterS :: ParserM String
letterS = latinS <||> greekS

latinS :: ParserM String
latinS = s $ oneOf "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
  where s = lift (:[])

greekS :: ParserM String
greekS = oneStringOf ["\\<alpha>",  "\\<beta>", "\\<gamma>", "\\<delta>",
                           "\\epsilon>", "\\<zeta>", "\\<eta>",   "\\<theta>",
                           "\\<iota>", "\\<kappa>", "\\<mu>", "\\<nu>",
                           "\\<xi>", "\\<pi>", "\\<rho>", "\\<sigma>", "\\<tau>",
                           "\\<upsilon>", "\\<phi>", "\\<chi>", "\\<psi>",
                           "\\<omega>", "\\<Gamma>", "\\<Delta>", "\\<Theta>",
                           "\\<Lambda>", "\\<Xi>", "\\<Pi>", "\\<Sigma>",
                           "\\<Upsilon>", "\\<Phi>", "\\<Psi>", "\\<Omega>" ]

symbolS :: ParserM String 
symbolS = oneStringOf ["\\<^sub>"]

quasiletterS :: ParserM String
quasiletterS = ((letterS <||> digitS <||> charString '_' <||> symbolS) <||> charString '\'') <?> "quasi-letter"

quasiletterSL :: ParserM String
quasiletterSL = ((letterS <||> digitS <||> charString '_' <||> symbolS) <||> charString '\'' <||> charString '.') <?> "quasi-letterL"

digitS :: ParserM String
digitS =  s $ oneOf "0123456789"
  where s = lift (:[])

natS :: ParserM String
natS = manyP1 digitS

natL :: ParserM String
natL = lexeme natS

--
-- Parses an Isabelle name
--
nameS :: ParserM String
nameS = (antiquoteNameS <||> identS <||> symidentS <||> natS <||> isabelleStringS) <?> "an Isabelle name"
  where

isabelleStringS = charString '"' <++> many1 (satisfy (\c -> c /= '"')) <++> charString '"'

symS :: ParserM Char
symS   = oneOf $ "!#$%&*+-/<=>?@^_|~"
    
symidentS :: ParserM String
symidentS = manySyms <||> (string "\\<" <++> identS <++> string ">")
  where manySyms = many1 symS


namerefS :: ParserM String
namerefS = longIdentS <||> nameS 

namerefL :: ParserM String
namerefL = notReservedLexeme namerefS

charString :: Char -> ParserM String
charString = lift (:[]) . char 

longIdentS :: ParserM String
longIdentS = identS <++> manyP1 (charString '.' <++> identS)

--
-- Like @lexeme@ but also checks that the thing parsed is not a reserved word.
--
notReservedLexeme :: ParserM String -> ParserM String
notReservedLexeme p = lexeme . try $
  do { s <- p
     ; if s `elem` reservedWords
              then unexpected ("'" ++ s ++ "' is a reserved word")
              else return s }


nameL :: ParserM String
nameL = notReservedLexeme nameS



--------------------------------------------------------------------------------
-- Theory language parser
--------------------------------------------------------------------------------

--
-- The parser presented in this section is for Isabelle's theory language.
-- Within the 'begin' and 'end' is Isabelle's SOMETHING language.
--

type L d = d Type Term

--
-- Parser for top-level
--
topLevelL :: ParserM (L Theory)
topLevelL = do
  many (satisfy isSpace)
  reserved "theory"
  n <- nameL
  imports <- importsL
  reserved "begin"
  theoryDecls <- many theoryDeclL
  reserved "end"
  return $ Theory n imports theoryDecls
  

theoryDeclL :: ParserM (TheoryDecl Type Term)
theoryDeclL = (Definition <$> definitionL) <||>
              (Abbreviation <$> abbreviationL) <||>
              (LemmaDecl <$> lemmaL) <||> 
              (LemmasDecl <$> lemmasL) <||> 
              (TypeSynonym <$> typeSynL) <||>
              (TypeDeclDecl <$> typeDeclL) <||>
              (ConstsDecl <$> constsL) <||>
              (RecordDecl <$> recordL) <||>
              (DataTypeDecl <$> datatypeL) <||>
              (PrimRec <$> primRecL) <||>
              (Declare <$> declareL)

declareL :: ParserM (L Dcl)
declareL = do 
  reserved "declare"
  name <- nameL 
  rules <- bracketL $ sepBy1 nameL (stringL ",")
  return $ Dcl name rules 

primRecL :: ParserM (L Prc)
primRecL = do 
  reserved "primrec"
  res <- alt1 <||> alt2
  return res

  where
    alt1 = do
      t <- sepBy1 (try $ quotedL eqTermL) (stringL "|")
      return (Prc Nothing t)
    alt2 = do
      sig <- sigL
      reserved "where"
      alts <- sepBy1 (try $ quotedL eqTermL) (stringL "|")
      return $ Prc (Just sig) alts

eqTermL :: ParserM (Term, Term)
eqTermL = do
  TermBinOp Eq term1 term2 <- termL
  return (term1, term2)

definitionL :: ParserM (L Def)
definitionL = do
  reserved "definition"
  res <- alt1 <||> alt2
  return res

  where
    alt1 = do
      t <- quotedTermL
      return (Def Nothing t)
    alt2 = do
      sig <- sigL
      reserved "where"
      t     <- quotedTermL
      return $ Def (Just sig) t

sigL :: ParserM (Sig Type)
sigL = do
  name  <- nameL
  stringL "::"
  mbTyp <- mb (quotedL typeL)
  return (Sig name mbTyp)

abbreviationL :: ParserM (L Abbrev)
abbreviationL = do
  reserved "abbreviation"
  res <- alt1 <||> alt2
  return res

  where
    alt1 = do
      t <- quotedTermL
      return (Abbrev Nothing t) 
    alt2 = do
      sig <- sigL
      reserved "where"
      t     <- quotedTermL
      return $ Abbrev (Just sig) t

lemmaL :: ParserM (L Lemma)
lemmaL = do 
   reserved "lemma"
   l <- justPropsL <||> withTheoremDeclL -- order is important here
   return l
  where
    justPropsL = do
      ts <- many1 quotedTermL
      pf <- proofL
      return $ Lemma False Nothing ts pf
    withTheoremDeclL = do
      d  <- thmDeclL
      ts <- many1 quotedTermL
      pf <- proofL
      return $ Lemma False (Just d) ts pf

lemmasL :: ParserM (L Lemmas)
lemmasL = do 
   reserved "lemmas"
   name <- thmDeclL
   stringL "="
   lems <- many1 thmDeclL
   return $ Lemmas name lems

typeSynL :: ParserM (L TypeSyn)
typeSynL = do
  reserved "type_synonym"
  tyvars <- tyParamsL
  name  <- nameL
  stringL "="
  mbTyp <- quotedL typeL
  return $ TypeSyn name mbTyp tyvars

typeDeclL :: ParserM (L TypeDecl)
typeDeclL = do
  reserved "typedecl"
  tyvars <- tyParamsL
  name  <- nameL
  return $ TypeDecl name tyvars

constsL :: ParserM (L Consts)
constsL = do
  reserved "consts"
  sig <- sigL -- FIXME sigL has a maybe types, consts must have types
  return $ Consts sig

recFieldL :: ParserM (L RecField)
recFieldL = do
  name  <- nameL
  stringL "::"
  typ <- alt1 <||> alt2 
  return $ RecField name typ
    where 
      alt1 = do 
        res <- quotedL typeL
        return res 
      alt2 = do 
        res <- (TyDatatype <$> identL <*> pure [])
        return res

recordL :: ParserM (L Record)
recordL = do
  reserved "record"
  tyvars <- tyParamsL
  name  <- nameL
  stringL "="
  fields <- many1 recFieldL
  return $ Record name fields tyvars

dtConsL :: ParserM (L DTCons)
dtConsL = do
  conName <- nameL
  conTypes <- many1 (quotedL typeL)
  return $ DTCons conName conTypes

datatypeL :: ParserM (L Datatype)
datatypeL = do
  reserved "datatype"
  tyvars <- tyParamsL
  name  <- nameL
  stringL "="
  cons <- sepBy1 dtConsL (stringL "|")   
  return $ Datatype name cons tyvars

thmDeclL :: ParserM TheoremDecl
thmDeclL = do { d <- nameAndAttrsL <||> justNameL <||> justAttrsL; stringL ":"; return d }
           -- order is important. @justNameL@ has to come after @nameAndAttrsL@
  where
    justNameL = try $ do
      nm <- namerefL
      return $ TheoremDecl (Just nm) []
    nameAndAttrsL = try $ do
      nm <- namerefL
      attrs <- attributesL
      return $ TheoremDecl (Just nm) attrs
    justAttrsL = try $ do
      attrs <- attributesL
      return $ TheoremDecl Nothing attrs

attributesL :: ParserM [Attribute]
attributesL = do
  stringL "["
  as <- sepBy1 attributeL (stringL ",")
  stringL "]"
  return as

attributeL :: ParserM Attribute
attributeL = do
  nm   <- namerefL
  args <- option [] $ many1 nameL
  return $ Attribute nm args
  
proofL :: ParserM Proof
proofL = Proof <$> many1 applyMethodL <*> proofEndL

proofEndL :: ParserM ProofEnd
proofEndL = proofDoneL <||> proofSorryL
  where
    proofDoneL  = reserved "done" >> return ProofDone
    proofSorryL = reserved "sorry" >> return ProofSorry

applyMethodL :: ParserM Method
applyMethodL = do
  reserved "apply"
  methodTopLevelL

--
-- For simplicity's sake we only allow method modifiers +,?, and [n] at the top-level of an "apply".
-- That is, there are no nested occurrences. 
--
methodTopLevelL = noArgsMethodL <||> bracketedMethodL 
  where
    noArgsMethodL = do
      nm <- namerefL
      return $ Method nm []
    bracketedMethodL = do
      stringL "("
      m <- methodL
      stringL ")"
      mbMM <- mb methodModifierL
      return $ case mbMM of 
        Just mm -> MethodModified m mm
        Nothing -> m 



methodL = buildExpressionParser table restL
  where
    table = sortExprParserTable . mkBinOpTable methodBinOpRec MethodCompound $ [ MethodSeq, MethodOr ]
    restL = parensL methodL <||> methodWithArgsL



methodWithArgsL = do
      nm   <- namerefL
      args <- many argL
      return $ Method nm args
      where
        argS = do
          n <- identS -- FIXME: What about: thm[THEN something]
          mbColon <- option "" (string ":")
          return $ n ++ mbColon
        argL = lexeme argS


quotedTermL :: ParserM Term
quotedTermL = quotedL termL

methodModifierL :: ParserM MethodModifier
methodModifierL = 
  (stringL "?" >> return MMOptional) <||>
  (stringL "+" >> return MMOneOrMore) <||>
  goalRestrictionL
  where
    goalRestrictionL = do
      stringL "["
      i <- option Nothing (read <$> natL)
      stringL "]"
      return $ MMGoalRestriction i

-----------------------------------------------------------------------

stringL = lexeme . string

-- Precedence of type annotation operator "::"
-- (should less than application precedence)
typeAnnotationPrec = 90

sortExprParserTable :: [(Int, OperatorM t)] -> [[OperatorM t]]
sortExprParserTable = map (map snd) . descendingSortByPrec . groupByPrec 
  where
    infixr 5 <:$:>
    (<:$:>) :: (b -> b -> r) -> (a -> b) -> (a -> a -> r)
    f <:$:> g = \x y -> f (g x) (g y)
    -- the @flip@ makes it a descending sort.
    descendingSortByPrec = sortBy  (flip (compare <:$:> fst . head))
    groupByPrec          = groupBy ((==) <:$:> fst)

mkBinOpTable :: (b -> BinOpRec) -> (b -> t -> t -> t) -> [b] -> [(Int, OperatorM t)]
mkBinOpTable f con binOps = map binOpParser binOps
  where
    binOpParser b = (binOpRecPrec rec, Infix (do { try (stringL (binOpRecSym rec))
                                                 ; return (con b) }) (binOpRecAssoc rec))
      where
        rec = f b 


antiquoteTermL :: ParserM Term 
antiquoteTermL =  AntiTerm <$> antiquoteL


--
-- Term parser
--
--
-- We are using Parsec's @buildExpressionParser@ function to handle binary operators, unary operators
-- and, surprisingly, quantified terms.
--
-- The trick I have pulled with quantified terms is to treat them as
-- unary operators.  The quantifier plus the identifiers that follow
-- it are considered as a unary operator. (.e.g. "\<exists>x y z." is
-- considered to be a unary operator which is applied to a term.)
--
termL :: ParserM Term
termL = buildExpressionParser table restL
  where
    table =  sortExprParserTable $
               compParser      :
               appParser       :
               typedTermParser :
               (  mkBinOpTable termBinOpRec TermBinOp binOps
               ++ map quantifierParser quantifiers
               ++ map unOpParser termUnOps
                )

    -- Think of application as an infix operator which is the empty string!
    appParser  = (termAppPrec, Infix (do { return TermApp }) AssocLeft)
    typedTermParser = (typeAnnotationPrec, Postfix (try$ do { stringL "::"; ty <- typeL
                                                       ; return (\t -> TermWithType t ty) }))
    quantifierParser q = (quantifierPrec q, Prefix (do { try (stringL (quantifierSym q))
                                                       ; is <- many1 (try listTermL <||> (TermIdent <$> innerIdentL))
                                                       -- note that string "." must be followed by at least one space
                                                       ; string "." 
                                                       ; many1 (satisfy isSpace)
                                                       ; return (QuantifiedTerm q is) }))
    unOpParser u = (termUnOpPrec u, Prefix (do { try (stringL (termUnOpSym u))
                                           ; return (TermUnOp u) }))


    restL =  antiquoteTermL <||> parensTermL <||> constTermL <||> doBlockTermL <||> 
             caseOfTermL <||> recordUpdTermL <||> recordDclTermL <||> ifThenElseTermL <||> 
             listTermL <||> setTermL <||> (TermIdent <$> innerIdentLL) 
             <||> letInTermL
    parensTermL = parensL termL
    compParser :: (Precedence, OperatorM Term)
    compParser = ( termBinOpPrec Comp
                 , Infix ((try (char 'o' >>
                               notFollowedBy quasiletterS >>
                               many (satisfy isSpace))) >>
                          return (TermBinOp Comp))
                         (termBinOpAssoc Comp)
                 )

letInTermL :: ParserM Term 
letInTermL = do 
  reserved "let"
  eles <- sepBy1 letTermL (stringL ";")
  reserved "in"
  i <- termL
  return $ LetIn eles i 

letTermL :: ParserM (Term, Term) 
letTermL = do 
  term1 <- try listTermL <||> (TermIdent <$> innerIdentLL) 
  stringL "="
  term2 <- termL
  return (term1, term2) 

setTermL :: ParserM Term
setTermL = do 
  stringL "{"
  st <- (try st1) <||> (try st2) <||> (try st3) <||> (try st4) 
  return $ Set st

  where 
    st1 = do 
      stringL "}"
      return $ Listing []
    st2 = do 
      eles <- sepBy1 termL (stringL ",") 
      stringL "}"
      return $ Listing eles 
    st3 = do 
      term1 <- try termL 
      stringL ".."
      term2 <- termL
      stringL "}"
      return $ Range term1 term2
    st4 = do 
      q <- try termL  
      stringL "."
      c <- termL
      stringL "}" 
      return $ Quant q c 


-- FIXME: Does not check if return exists 
doBlockTermL :: ParserM Term 
doBlockTermL = do 
  reserved "do"
  dos <- sepBy1 (try dosTermL) (stringL ";") 
  reserved "od"
  return $ DoBlock dos

dosTermL :: ParserM Term
dosTermL = do 
  res <- (try do1) <||> do2 
  return res 
  
  where 
    do1 = do 
      term1 <- try termL
      stringL "\\<leftarrow>"
      term2 <- try termL
      return $ DoItem term1 term2
    do2 = do 
      term <- termL 
      return term

listTermL :: ParserM Term 
listTermL = do  
  lstt <- list <||> tuple <||> pair
  return lstt
  where 
    list = do 
      stringL "["
      res <- alt1 <||> alt2 
      return $ ListTerm "[" res "]"
      where 
        alt1 = do 
          eles <- sepBy1 termL (stringL ",")
          stringL "]"
          return eles
        alt2 = do 
          stringL "]"
          return []
    
    tuple = do 
      stringL "("
      res <- alt1 <||> alt2 
      return $ ListTerm "(" res ")"
      where 
        alt1 = do 
          eles <- sepBy1 termL (stringL ",")
          stringL ")"
          return eles
        alt2 = do 
          stringL ")"
          return []
    
    pair = do 
      stringL "("
      stringL "["
      e1 <- termL 
      stringL ","
      e2 <- termL 
      stringL "]"
      stringL ")"
      return $ ListTerm "(" [e1, e2] ")"


ifThenElseTermL :: ParserM Term
ifThenElseTermL = do
  reserved "if"
  cond <- termL 
  reserved "then"
  case1 <- termL
  reserved "else"
  case2 <- termL
  return $ IfThenElse cond case1 case2

recordDclTermL :: ParserM Term 
recordDclTermL = do  
  stringL "\\<lparr>"
  dcls <- sepBy1 (try dclTermL) (stringL ",")
  stringL "\\<rparr>"
  return $ RecordDcl dcls 

dclTermL :: ParserM (Term, Term)
dclTermL = do
  term1 <- fieldL
  stringL "="
  term2 <- termL
  return (TermIdent $ Id term1, term2) 

recordUpdTermL :: ParserM Term 
recordUpdTermL = do 
  stringL "\\<lparr>"
  upds <- sepBy1 (try updTermL) (stringL ",")
  stringL "\\<rparr>"
  return $ RecordUpd upds 

updTermL :: ParserM (Term, Term)
updTermL = do
  term1 <- fieldL
  stringL ":="
  term2 <- termL
  return (TermIdent $ Id term1, term2) 

fieldL :: ParserM String 
fieldL = notReservedLexeme fieldS 

fieldS :: ParserM String 
fieldS = letterS <++> manyP fieldLetters
    where 
      fieldLetters = ((letterS <||> digitS <||> charString '_') <||> charString '\'' <||> charString '.') <?> "quasi-letter"

caseOfTermL :: ParserM Term
caseOfTermL = do 
  reserved "case"
  term <- termL
  reserved "of"
  alts <- sepBy1 (try altTermL) (stringL "|") 
  return $ CaseOf term alts 

altTermL :: ParserM (Term, Term)
altTermL = do 
  term1 <- termL
  stringL "\\<Rightarrow>"
  term2 <- termL
  return (term1, term2) 

innerIdentL :: ParserM Ident
innerIdentL = (Id <$> identL) <||> wildcardL <||> parensL typedIdentL


innerIdentLL :: ParserM Ident
innerIdentLL = (Id <$> identLL) <||> wildcardL <||> parensL typedIdentL

wildcardL :: ParserM Ident
wildcardL = do { char '_'; return Wildcard }

typedIdentL :: ParserM Ident
typedIdentL = do 
  ident <- innerIdentL
  stringL "::"
  ty <- typeL
  return $ TypedIdent ident ty

typedTermL :: ParserM Term
typedTermL = do
  t  <- termL
  stringL "::"
  ty <- typeL 
  return (TermWithType t ty)
  
constTermL :: ParserM Term
constTermL = ConstTerm <$> (trueL <||> falseL <||> (IntLiteral <$> intL))  -- TODO: only support very limited forms of constants / zilinc
  where
    trueL  = stringL "True" >> return TrueC
    falseL = stringL "False" >> return FalseC
    intL = read <$> natL


antiquoteTypeL :: ParserM Type 
antiquoteTypeL = AntiType <$> antiquoteL

--
-- Type parser
--
typeL :: ParserM Type
typeL = buildExpressionParser table restL
  where
    table = [Postfix (do { s <- identL; return (\t -> TyDatatype s [t])})] : 
              (map (map toInfixR) [ [(tyTupleSym, TyTuple)], [(tyArrowSym, TyArrow)] ])
    toInfixR (s,c) = Infix (do { try (stringL s); return c }) AssocRight
    restL = antiquoteTypeL <||> parensL typeL <||> tyPrimL <||> tyVarL <||>
            multiParamDatatypeL <||> (TyDatatype <$> namerefL <*> pure [])

multiParamL :: ParserM a -> ParserM [a]
multiParamL pparser = do
  stringL "("
  t <- pparser
  stringL ","
  ts <- sepBy1 pparser (try (stringL ","))
  stringL ")"
  return (t:ts)

multiParamDatatypeL = do
  ts <- multiParamL typeL
  s <- identL
  return $ TyDatatype s ts

tyVarL :: ParserM Type
tyVarL = do
  char '\''
  v <- lexeme (letterS <++> manyP quasiletterS)
  return $ TyVar v

stripTyVar = map (\t -> let (TyVar v) = t in v)

tyParamsL :: ParserM [String]
tyParamsL = do 
  xs <- (do { s <- tyVarL ; return [s] }) <||> multiParamL tyVarL <||> return []
  return (stripTyVar xs)

tyPrimL = TyPrim <$> primTypeL


primTypeL :: ParserM PrimType
primTypeL = foldl1 (<||>) [p "int" IntT, p "bool" BoolT, p "nat" NatT]
  where
    p s c = stringL s >> return c

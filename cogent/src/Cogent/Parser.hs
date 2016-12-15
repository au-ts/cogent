--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE LambdaCase, RecordWildCards, TupleSections #-}

module Cogent.Parser where

import Cogent.Common.Syntax hiding (Prefix)
import Cogent.Common.Types
import Cogent.Compiler
import qualified Cogent.Preprocess as PP
import Cogent.Surface
import Cogent.Util (getStdIncFullPath)

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative hiding (many, (<|>), optional)
import Data.Monoid (mconcat)
#endif
import Control.Arrow (second)
import Control.Monad
import Control.Monad.Identity
import Data.Char
import Data.IORef
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Error
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.Pos
import Text.Parsec.Prim
-- import Text.Parsec.String (parseFromFile)
import qualified Text.Parsec.Token as T
import System.Directory
import System.FilePath


language :: LanguageDef st
language = haskellStyle
           { T.reservedOpNames = [":","=","+","*","/","%","!",":<",".","_","..","#", "@", "@@",
                                  "&&","||",">=","<=",">","<","==","/=",".&.",".|.",".^.",">>","<<"]
           , T.reservedNames   = ["let","in","type","include","all","take","put","inline",
                                  "if","then","else","not","complement","and","True","False"]
           , T.identStart = letter <|> char '_'
           }

T.TokenParser {..} = T.makeTokenParser language

sepByAligned1 p s c = (:) <$> p <*> many (getPosition >>= \o -> guard (sourceColumn o == c) >> s >> p)
manyAligned1 p = do whiteSpace; c <- sourceColumn <$> getPosition
                    (:) <$> p <*> many (whiteSpace >> getPosition >>= \o -> guard (sourceColumn o == c) >> p)

variableName = try (do (x:xs) <- identifier
                       (if isLower x || (x == '_' && not (null xs)) then return else unexpected) $ x:xs)

typeConName = try (do (x:xs) <- identifier
                      (if isUpper x then return else unexpected) $ x:xs)

avoidInitial = do whiteSpace; p <- sourceColumn <$> getPosition; guard (p > 1)


-- TODO: add support for patterns like `_ {f1, f2}', where the record name is anonymous / zilinc
irrefutablePattern :: Parser LocIrrefPatn t
irrefutablePattern = avoidInitial >> LocIrrefPatn <$> getPosition <*>
             (variableOrRecord <$> variableName <*> optionMaybe (braces recAssignsAndOrWildcard)
         <|> tuple <$> parens (commaSep irrefutablePattern)
         <|> PUnboxedRecord <$ reservedOp "#" <*> braces recAssignsAndOrWildcard
         <|> PUnderscore <$ reservedOp "_")
       <?> "irrefutable pattern"
  where tuple [] = PUnitel
        tuple [LocIrrefPatn _ p] = p
        tuple ps  = PTuple ps
        variableOrRecord v Nothing = PVar v
        variableOrRecord v (Just rs) = PTake v rs
        recordAssignment = (\p n m -> (n, fromMaybe (LocIrrefPatn p $ PVar n) m))
                        <$> getPosition <*> variableName <*> optionMaybe (reservedOp "=" *> irrefutablePattern)
                        <?> "record assignment pattern"
        wildcard = reservedOp ".." >> return Nothing
        recAssign = Just <$> recordAssignment
        recAssignsAndOrWildcard = ((:[]) <$> wildcard)
                              <|> ((:) <$> recAssign <*> ((++) <$> many (try (comma >> recAssign))
                                                               <*> (liftM maybeToList . optionMaybe) (comma >> wildcard)))

pattern = avoidInitial >> LocPatn <$> getPosition <*>
            (PBoolLit <$> boolean
         <|> PCon <$> typeConName <*> many irrefutablePattern
         <|> PIntLit <$> integer
         <|> PCharLit <$> charLiteral
         <|> try (patnOfLP <$> parens pattern)
         <|> PIrrefutable <$> irrefutablePattern)
       <?> "pattern"


boolean = True <$ reserved "True"
      <|> False <$ reserved "False"
      <?> "boolean literal"

-- A hack to handle boolean matching exhaustivity :)
matchExpr m =  flip fmap (matchExpr' m) (\case
  (LocExpr p (Match e bs [Alt (LocPatn p1 (PBoolLit True )) a e1, Alt (LocPatn p2 (PBoolLit False)) a' e2])) ->
   LocExpr p (Match e bs [Alt (LocPatn p1 (PBoolLit True )) a e1, Alt (LocPatn p2 (PIrrefutable (LocIrrefPatn p2 PUnderscore))) a' e2])
  (LocExpr p (Match e bs [Alt (LocPatn p1 (PBoolLit False)) a e1, Alt (LocPatn p2 (PBoolLit True )) a' e2])) ->
   LocExpr p (Match e bs [Alt (LocPatn p1 (PBoolLit False)) a e1, Alt (LocPatn p2 (PIrrefutable (LocIrrefPatn p2 PUnderscore))) a' e2])
  e -> e)

matchExpr' m = do
  e <- basicExpr m
  (try (do bangs <- many (reservedOp "!" >> variableName)
           c <- sourceColumn <$> getPosition
           guard (c > m)
           reservedOp "|"
           return (c,bangs))
         >>= (\(c,bangs) -> LocExpr (posOfE e) . Match e bangs <$> sepByAligned1 (alternative c) (reservedOp "|") c))
   <|> pure e
  <?> "basic expression or case distinction"

alternative m = (Alt <$> pattern <*> matchArrow <*> expr m) <?> "alternative"
  where matchArrow =  Likely   <$ reservedOp "=>"
                  <|> Unlikely <$ reservedOp "~>"
                  <|> Regular  <$ reservedOp "->"

postfix p = Postfix . chainl1 p $ return (flip (.))

basicExpr m = do e <- basicExpr'
                 LocExpr (posOfE e) . Seq e <$ semi <*> expr m
                  <|> pure e
basicExpr' = avoidInitial >> buildExpressionParser
            [ [postfix ((\f e -> LocExpr (posOfE e) (Member e f)) <$ reservedOp "." <*> variableName)]
            , [Prefix (getPosition >>= \p -> reserved "upcast"     *> pure (LocExpr p . Upcast))] 
--            , [Prefix (getPosition >>= \p -> reserved "widen"      *> pure (LocExpr p . Widen ))] 
            , [Prefix (getPosition >>= \p -> reserved "complement" *> pure (LocExpr p . PrimOp "complement" . (:[])))]
            , [Prefix (getPosition >>= \p -> reserved "not" *> pure (LocExpr p . PrimOp "not" . (:[])))]
            , [Infix (pure (\a b -> LocExpr (posOfE a) (App a b))) AssocLeft]
            , [Postfix ((\rs x -> LocExpr (posOfE x) (Put x rs)) <$> braces recAssignsAndOrWildcard)]
            , [binary "*" AssocLeft, binary "/" AssocLeft, binary "%" AssocLeft ]
            , [binary "+" AssocLeft, binary "-" AssocLeft ]
            , map (`binary` AssocNone) [">", "<", ">=", "<=", "==", "/="]
            , [binary ".&." AssocLeft]
            , [binary ".^." AssocLeft]
            , [binary ".|." AssocLeft]
            , [binary ">>" AssocLeft, binary "<<" AssocLeft]
            , [binary "&&" AssocRight]
            , [binary "||" AssocRight]
            ] term <?> "basic expression"
  where binary name = Infix (reservedOp name *> pure (\a b -> LocExpr (posOfE a) (PrimOp name [a,b])))

        term = avoidInitial >> (LocExpr <$> getPosition <*>
                  (var <$> optionMaybe (reserved "inline")
                       <*> variableName
                       <*> optionMaybe (brackets (commaSep1 ((char '_' >> return Nothing)
                                                         <|> (Just <$> monotype))))
               <|> BoolLit <$> boolean
               <|> Con <$> typeConName <*> many term
               <|> IntLit <$> natural
               <|> CharLit <$> charLiteral
               <|> StringLit <$> stringLiteral
               <|> tuple <$> parens (commaSep $ expr 1)
               <|> UnboxedRecord <$ reservedOp "#" <*> braces (commaSep1 recordAssignment)))
            <?> "term"
        var Nothing  v Nothing = Var v
        var (Just _) v Nothing = TypeApp v [] Inline
        var Nothing  v (Just ts) = TypeApp v ts NoInline
        var (Just _) v (Just ts) = TypeApp v ts Inline
        tuple [] = Unitel
        tuple [e] = exprOfLE e
        tuple es  = Tuple es
        recordAssignment = (\p n m -> (n, fromMaybe (LocExpr p (Var n)) m))
                        <$> getPosition <*> variableName <*> optionMaybe (reservedOp "=" *> expr 1)
                        <?> "record assignment"
        wildcard = reservedOp ".." >> return Nothing
        recAssign = Just <$> recordAssignment
        recAssignsAndOrWildcard = ((:[]) <$> wildcard)
                              <|> ((:) <$> recAssign <*> ((++) <$> many (try (comma >> recAssign)) <*> (liftM maybeToList . optionMaybe) (comma >> wildcard)))

expr m = do avoidInitial; LocExpr <$> getPosition <*>
                 (Let <$ reserved "let" <*> bindings <* reserved "in" <*> expr m
              <|> If  <$ reserved "if" <*> expr m <*> many (reservedOp "!" >> variableName)
                      <* reserved "then" <*> expr m <* reserved "else" <*> expr m)
    <|> matchExpr m
    <?> "expression"
  where binding = Binding <$> irrefutablePattern <*> optionMaybe (reservedOp ":" *> monotype)
                          <*  reservedOp "=" <*> expr 1 <*> many (reservedOp "!" >> variableName)
        bindings = binding `sepBy1` reserved "and"


-- monotype ::= typeA1 ("->" typeA1)?
-- typeA1   ::= Con typeA2*
--            | typeA2 (take fList | put fList)?
-- typeA2   ::= "#" atomtype
--            | atomtype "!"?
-- atomtype ::= "(" monotype "," ...")"
--            | "{" fieldname ":" monotype "," ... "}"
--            | "<" Con typeA2 "|" ... ">"
--            | var
--            | Con

docHunk = do whiteSpace; _ <- try (reservedOp "@"); x <- manyTill anyChar newline; whiteSpace; return x

monotype = do avoidInitial
              t1 <- typeA1
              t2 <- optionMaybe (reservedOp "->" >> typeA1)
              case t2 of Nothing -> return t1; Just t2' -> return $ LocType (posOfT t1) $ TFun t1 t2'
  where
    typeA1 = do
      x <- typeA1'
      t2 <- optionMaybe (avoidInitial >> docHunk)
      case t2 of Nothing -> return x; Just doc -> do
                    return (Documentation doc x)
    typeA2 = do
      x <- typeA2'
      t2 <- optionMaybe (avoidInitial >> docHunk)
      case t2 of Nothing -> return x; Just doc -> do
                    return (Documentation doc x)
    typeA1' = do avoidInitial
                 try paramtype
                 <|> (do t <- typeA2'
                         op <- optionMaybe takeput
                         case op of Nothing -> return t; Just f -> return (f t)
                     )
    typeA2' = avoidInitial >>
               ((unbox >>= \op -> atomtype >>= \at -> return (op at))
           <|>  (atomtype >>= \t -> optionMaybe bang >>= \op -> case op of Nothing -> return t; Just f -> return (f t)))
    paramtype = avoidInitial >> LocType <$> getPosition <*> (TCon <$> typeConName <*> many1 typeA2 <*> pure Writable)
    unbox = avoidInitial >> reservedOp "#" >> return (\x -> LocType (posOfT x) (TUnbox x))
    bang  = avoidInitial >> reservedOp "!" >> return (\x -> LocType (posOfT x) (TBang x))
    takeput = avoidInitial >>
             ((reservedOp "take" >> fList >>= \fs -> return (\x -> LocType (posOfT x) (TTake fs x)))
          <|> (reservedOp "put"  >> fList >>= \fs -> return (\x -> LocType (posOfT x) (TPut  fs x))))
    atomtype = avoidInitial >>
               LocType <$> getPosition <*>
                 (TVar <$> variableName <*> pure False
              <|> (do tn <- typeConName
                      let s = if tn `elem` primTypeCons  -- give correct sigil to primitive types
                                then Unboxed
                                else Writable
                      return $ TCon tn [] s
                  )
              -- <|> TCon <$> typeConName <*> pure [] <*> pure Writable
              <|> tuple <$> parens (commaSep monotype)
              <|> TRecord <$> braces (commaSep1 ((\a b c -> (a,(b,c))) <$> variableName <* reservedOp ":" <*> monotype <*> pure False)) <*> pure Writable
              <|> TVariant . M.fromList <$> angles (((,) <$> typeConName <*> fmap ((,False)) (many typeA2)) `sepBy` reservedOp "|"))
    tuple [] = TUnit
    tuple [e] = typeOfLT e
    tuple es  = TTuple es

    fList = (Just . (:[])) <$> identifier
        <|> parens ((reservedOp ".." >> return Nothing) <|> (commaSep identifier >>= return . Just))

polytype = PT <$ reserved "all" <*> (((:[]) <$> kindSignature) <|> parens (commaSep1 kindSignature)) <* reservedOp "." <*> monotype
       <|> PT [] <$> monotype

kindSignature = do n <- variableName
                   (n,) <$> (reservedOp ":<" *> (kind <?> "kind")
                          <|> pure (K False False False))
  where kind = do x <- identifier
                  determineKind x (K False False False)
        determineKind ('D':xs) k =  determineKind xs (k { canDiscard = True })
        determineKind ('S':xs) k =  determineKind xs (k { canShare = True })
        determineKind ('E':xs) k =  determineKind xs (k { canEscape = True })
        determineKind [] k = return k
        determineKind _ k = fail "Kinds are made of three letters: D, S, E"


docBlock = do whiteSpace; _ <- try (reservedOp "@@"); x <- manyTill anyChar (newline); whiteSpace; return x

toplevel = getPosition >>= \p ->
                 (p, "",) <$> DocBlock <$> unlines <$> many1 docBlock
             <|> toplevel'

toplevel' = do
  docs <- unlines . fromMaybe [] <$> optionMaybe (many1 docHunk)
  p <- getPosition
  when (sourceColumn p > 1) $ fail "toplevel entries should start at column 1"
  (p,docs,) <$> (try (Include <$ reserved "include" <*> stringLiteral)
        <|> IncludeStd <$ reserved "include" <*> angles (many (noneOf "\r\n>"))
        <|> typeDec <$ reserved "type" <*> typeConName <*> many (avoidInitial >> variableName) <*> optionMaybe (reservedOp "=" *> monotype)
        <|> do n <- variableName
               reservedOp ":"
               tau <- polytype
               do try (do n' <- variableName
                          when (n /= n') $ fail $ "The name in the type signature, `" ++ n
                                               ++ "` does not match the name in the equation, `" ++ n' ++ "`." )
                  let fundef = FunDef n tau <$> (functionAlts <|> (:[]) <$> functionSingle)
                  case tau of
                    PT [] t -> (ConstDef n t <$ reservedOp "=" <*> expr 1 <|> fundef)
                    _       -> fundef
                <|> pure (AbsDec n tau))
  where
    typeDec n vs Nothing = AbsTypeDec n vs
    typeDec n vs (Just t) = TypeDec n vs t
    functionAlts = do
      c <- sourceColumn <$> getPosition
      reservedOp "|"
      sepByAligned1 (alternative c) (reservedOp "|") c
    functionSingle = Alt <$> (LocPatn <$> getPosition <*> (PIrrefutable <$> irrefutablePattern))
                         <*> pure Regular <* reservedOp "=" <*> expr 1

type Parser a t = ParsecT String t Identity a

program :: Parser [(SourcePos, DocString, TopLevel LocType VarName LocExpr)] t
program = whiteSpace *> many1 toplevel <* eof

-- NOTE: It will search for the path provided in the files. If it cannot find anything, it will
--   check for directories given in the -I arguments, relative to the current working dir.
--   A path (B) in an include clauses is relative to the file (A) containing the include.
--   When searching with -I, it looks for B in A/I/B. If I is absolute, it ignores A.
-- Example:
--   current dir: C
--   file a in dir: A, relative to C
--   file b included in file a, in dir B, relative to A
--   -I argument: S
--   * It searches for file a in A, from C
--     case 1) a found. Then it searches for file b in A/B, from C
--       case 1-1) b found. DONE
--       case 1-2) b not found. It then attempts A/S/B, from C
--     case 2) a not found. It tries S/A, from C, and finds a. Next
--             it searches for file b in A/B, from C
--       case 2-1) b found. DONE
--       case 2-2) b not found. It attempts A/S/B from C
--   We can conclude that the search path for b is independent of where a was found

parseWithIncludes :: FilePath -> [FilePath]
                  -> IO (Either String ([(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)], [PP.LocPragma]))
parseWithIncludes f paths = do
  r <- newIORef S.empty
  loadTransitive' r f paths "."  -- relative to orig, we're in orig

-- r: IORef
-- fp: file path declared in the include clause, or the given path in command-line (only for the initial one)
-- paths: search paths, relative to origin
-- ro: the path of the current file, relative to original dir
loadTransitive' :: IORef (S.Set FilePath) -> FilePath -> [FilePath] -> FilePath
                -> IO (Either String ([(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)], [PP.LocPragma]))
loadTransitive' r fp paths ro = do
  let fps = map (flip combine fp) (ro:paths)  -- all file paths need to search
      fpdir = takeDirectory (combine ro fp)
  findPath fps >>= \case
    Nothing  -> return $ Left $ "File not found " ++ fp
    Just fp' -> canonicalizePath fp' >>= \fpc -> (S.member fpc <$> readIORef r) >>= \case
      True  -> return $ Right ([],[])
      False -> do modifyIORef r (S.insert fpc)
                  pragmas <- parseFromFile PP.program fp'
                  defs <- parseFromFile program fp'
                  return ((,) <$> defs <*> pragmas)
               >>= \case
                     Left err -> return $ Left $ show err
                     Right (defs,pragmas) -> do
                        defs' <- mapM (flip transitive fpdir) defs
                        return $ fmap (second (pragmas ++) . mconcat) . sequence $ defs'

  where
    transitive :: (SourcePos, DocString, TopLevel LocType LocPatn LocExpr)
               -> FilePath
               -> IO (Either String ([(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)], [PP.LocPragma]))
    transitive (p,d,Include x) curr = loadTransitive' r x (map (combine curr) paths) curr
    transitive (p,d,IncludeStd x) curr = do filepath <- (getStdIncFullPath x); loadTransitive' r filepath (map (combine curr) paths) curr
    transitive x _ = return (Right ([x],[]))

    findPath :: [FilePath] -> IO (Maybe FilePath)
    findPath [] = return Nothing
    findPath (p:paths) = doesFileExist p >>= \case
      False -> findPath paths
      True  -> return $ Just p

parseFromFile :: Parser a () -> FilePath -> IO (Either ParseError a)
parseFromFile p fname = do
  input <- readFile fname
  return $ runP p () (if __cogent_ffull_src_path then fname else takeFileName fname) input


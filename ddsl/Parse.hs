{-# LANGUAGE RecordWildCards #-}

module Parse (Parse.parse, ParseError) where

import Control.Applicative ((<$>), (<*>), pure)
import Control.Monad (when)
import Data.Char
import Data.IORef
import Data.List as L
import Text.Parsec
import Text.Parsec.Error
import Text.Parsec.Expr
import Text.Parsec.Language as PL
import Text.Parsec.Prim as PP
import qualified Text.Parsec.String as PS
import qualified Text.Parsec.Token as PT

import Syntax as DS
import Pretty
import Util

type Parser = PS.Parser

language ::  PL.LanguageDef t
language = haskellStyle 
             { PT.reservedOpNames = ["=", "{", "}", "::", "|", "->", ".", "`", 
                                     ",", "~", "!", "+", "-", "*", "/", "%", "&&", "||",
                                     "(", ")", ".&.", ".^.", ".|.", "==", "/=",
                                     "<", ">", ">=", "<=", "{-#", "#-}"]
             , PT.reservedNames   = ["import", "data", "bitfield", "type", "enum", "const",
                                     "of", "case", "where", "instance",
                                     "Array", "tag", "_", "Bool", "True", "False",
                                     "U8", "U16", "U32", "U64", 
                                     "Pu8", "Ple16", "Pbe16", 
                                     "Ple32", "Pbe32", "Ple64", "Pbe64"] ++ 
                                    if allow_u24_internal 
                                      then ["U24", "Ple24", "Pbe24"] else []
                                    
             } 

PT.TokenParser {..} = PT.makeTokenParser language

-------------------------------------------------------------------------------

identifier' :: Parser Ident
identifier' = do { id <- identifier
                 ; if genPrefix `isPrefixOf` id || genPREFIX `isPrefixOf` id
                     then unexpected ("identifier " ++ show id ++ " with reserved prefix")
                     else return id }

parseLowerId :: Parser Ident
parseLowerId = try (do { id <- identifier'
                       ; if (isLower . head) id then return id else unexpected ("identifier " ++ show id) }) 

parseUpperId :: Parser Ident
parseUpperId = try (do { id <- identifier'
                       ; if (isUpper . head) id then return id else unexpected ("identifier " ++ show id) })

parseAllUpperId :: Parser Ident
parseAllUpperId = try (do { id <- identifier 
                          ; if all (\id -> isUpper id || id `elem` "_'1234567890") id 
                              then return id else unexpected ("identifier " ++ show id) })

parseVar    = parseLowerId <?> "Variable"
parseFunc   = parseLowerId <?> "Function"
parseConst  = parseLowerId <?> "Constant"
parseType   = parseUpperId <?> "Type"

parseOpIdent :: Parser DS.OpIdent
parseOpIdent =   do { reserved "_"
                    ; return Nothing }
             <|> do { var <- parseVar
                    ; return (Just var)}
             <?> "Identifier or Wildcard"

-------------------------------------------------------------------------------

parseFile :: Parser Module
parseFile = do { name <- sourceName <$> getPosition
               ; imps <- many parseImport
               ; decls <- many parseDef
               ; return $ Module (ModName name) (ModHead imps) (concat decls) }

parseImport :: Parser ModName
parseImport = do { reserved "import"
                 ; ModName <$> stringLiteral
                 } <?> "Import files"

parseDef :: Parser [DataDesc]
parseDef =  do { d <-  parseTypeDef
                   <|> parseDataDef
                   <|> parseConstDef
               ; return [d] }
           <|> parseEnumDef

parseTypeDef :: Parser DataDesc
parseTypeDef = do { pos <- getPosition
                  ; reserved "type"
                  ; t <- parseType
                  ; ps <- parseParams
                  ; reservedOp "="
                  ; tu <- parseTypeUse
                  ; tc <- parseTypeCons
                  ; return (DTypeSyn t ps tu tc pos)
                  } <?> "Type definition"

parseDataDef :: Parser DataDesc
parseDataDef = do { pos <- getPosition
                  ; reserved "data"
                  ; t <- parseType
                  ; ps <- parseParams
                  ; parseSU (t, ps) pos <|> parseBT (t, ps) pos
                  } <?> "Data definition"

parseSU :: (Ident, [Param]) -> SourcePos -> Parser DataDesc
parseSU h pos = do { reservedOp "="
                   ; parseStruct h pos <|> parseTUnion h pos }

parseBT :: (Ident, [Param]) -> SourcePos -> Parser DataDesc
parseBT h pos = do { reservedOp "::"
                   ; t <- parseTypeUse
                   ; reservedOp "="
                   ; parseBitfield h t pos <|> parseBUnion h t pos }

parseStruct :: (Ident, [Param]) -> SourcePos -> Parser DataDesc
parseStruct (t, ps) pos = do { fs <- braces $ (if allow_empty_struct_internal 
                                                 then commaSep else commaSep1) parseField
                             ; tc <- parseTypeCons
                             ; return $ DStruct t ps fs tc pos } <?> "Struct"

parseTUnion :: (Ident, [Param]) -> SourcePos -> Parser DataDesc
parseTUnion (id, ps) pos = do { reserved "case"
                              ; reserved "tag"
                              ; reservedOp "::"
                              ; t <- parseTypeUse
                              ; reserved "of"
                              ; cs <- semiSep parseCase
                              ; return $ DTUnion id ps t cs pos
                              } <?> "TUnion"

parseBitfield :: (Ident, [Param]) -> Type -> SourcePos -> Parser DataDesc
parseBitfield (t, ps) t' pos = do { bfs <- braces $ commaSep parseBField
                                  ; tc <- parseTypeCons
                                  ; return $ DBitfield t ps t' bfs tc pos } <?> "Bitfield"

parseBUnion :: (Ident, [Param]) -> Type -> SourcePos -> Parser DataDesc 
parseBUnion (id, ps) t pos = do { reserved "case"
                                ; reserved "tag"
                                ; reserved "of"
                                ; cs <- semiSep parseCase
                                ; return $ DBUnion id ps t cs pos
                                } <?> "BUnion"

parseEnumDef :: Parser [DataDesc]
parseEnumDef = do { pos <- getPosition
                  ; reserved "enum"
                  ; ty <- parseConst
                  ; reservedOp "::"
                  ; tu <- parseTypeUse
                  ; reservedOp "="
                  ; do { es <- braces $ commaSep1 parseExpr
                       ; return [DEnum ty tu es pos]
                       } 
                <|> do { pos' <- getPosition 
                       ; (eit , e) <- parseEnumItem  tu (ILit 0 pos') 
                       ; pos'' <- getPosition
                       ; (eits, es) <- parseEnumItems tu (BinExpr AddOp e (ILit 1 pos'') pos'') 
                       ; return (eit:eits ++ [DEnum ty tu (e:es) pos])
                       }
                  } <?> "Enumeration definition"

parseConstDef :: Parser DataDesc
parseConstDef = do { pos <- getPosition
                   ; reserved "const"
                   ; c <- parseConst
                   ; reservedOp "::"
                   ; tu <- parseTypeUse
                   ; reservedOp "="
                   ; e <- parseExpr
                   ; return (DConst c tu e pos)
                   } <?> "Constant definition"

parseParams :: Parser [Param]
parseParams =   (braces $ commaSep parseParam)
            <|> (return [])
            <?> "Parameters"

parseParam :: Parser Param
parseParam = do { id <- parseOpIdent
                ; reservedOp "::"
                ; ty <- parseTypeUse
                ; return (id, ty)
                } <?> "Parameter"

parseArg :: Parser Arg
parseArg = parsePrimaryExpr <?> "Argument"

-------------------------------------------------------------------------------

parseField :: Parser Field
parseField = do { pos <- getPosition
                ; oi <- parseOpIdent
                ; reservedOp "::"
                ; tu <- parseTypeUse
                ; mc <- option Nothing $ do { c <- parseConstraints
                                            ; return (Just c) }
                ; return (Field oi tu mc pos)
                } <?> "Field"

parseBField :: Parser BField
parseBField = do { pos <- getPosition
                 ; tag <- option False $
                            do { reserved "tag"; return True }
                 ; oi <- parseOpIdent
                 ; reservedOp "::"
                 ; expr <- parseExpr
                 ; mc <- option Nothing $
                             do { c <- parseConstraints
                                ; return (Just c) }
                 ; return (BField (Tag tag) oi expr mc pos)
                 } <?> "B-field"

parseEnumItems :: DS.Type -> Expr -> Parser ([DataDesc], [Expr])
parseEnumItems t e =   do { reservedOp "|"
                          ; (eit, e) <- parseEnumItem t e
                          ; pos <- getPosition
                          ; (eits, es) <- parseEnumItems t (BinExpr AddOp e (ILit 1 pos) pos)
                          ; return (eit:eits, e:es) }
                   <|> return ([], [])
                   <?> "Enumeration items"

parseEnumItem :: DS.Type -> Expr -> Parser (DataDesc, Expr)
parseEnumItem t e = do { pos <- getPosition
                       ; c <- parseConst
                       ;   do { reservedOp "->"
                              ; e' <- parseExpr
                              ; return (DConst c t e' pos, Var c pos) }
                       <|> return (DConst c t e pos, Var c pos)
                       } <?> "Enumeration item"

parseCase :: Parser Case
parseCase = do { pos <- getPosition
               ; expr <- parseExpr
               ; reservedOp "->"
               ; f <- parseField
               ; return (Case expr f pos)
               } <?> "Case"

parseTypeCons :: Parser TyConstraint
parseTypeCons = (option Nothing $
                    do { ins <- option Nothing $ parseInstance
                       ; cons <- parseConstraints
                       ; return (Just (ins, cons)) })
              <?> "Constraints on type"

parseInstance :: Parser (Maybe Instance)
parseInstance = do { reserved "instance"
                   ; v <- parseVar
                   ; return (Just v) }
                   <?> "instance"

parseConstraints :: Parser Constraint
parseConstraints = do { reserved "where"
                      ; expr <- parseExpr
                      ; return expr
                      } <?> "Constraints"

-------------------------------------------------------------------------------


parseAtomType :: Parser DS.Type
parseAtomType =   (parens $ parseTypeUse)
              <|> parseBuiltInType
              <|> do { ty <- parseType
                     ; return (CompTy ty []) }
              <?> "Atomic type"

parseTypeUse :: Parser DS.Type
parseTypeUse =   do { reserved "Array"
                    ; ty <- parseAtomType
                    ; expr <- parsePrimaryExpr
                    ; return (Array ty expr) }
             <|> try parseParamedType
             <|> parseAtomType 
             <?> "Type"

parseParamedType :: Parser DS.Type
parseParamedType = do { ty <- parseType
                      ; as <- many1 parseArg
                      ; return (CompTy ty as) }
                   <?> "Parameterised type"

parseBuiltInType :: Parser DS.Type
parseBuiltInType =   do { reserved "Bool" ; return Bool  }
                 <|> do { reserved "U8"   ; return (UInt 8  View) }
                 <|> do { reserved "U16"  ; return (UInt 16 View) }
                 <|> do { reserved "U32"  ; return (UInt 32 View) }
                 <|> do { reserved "U64"  ; return (UInt 64 View) }
                 <|> do { reserved "Pu8"  ; return (UInt 8  (Phys LEn)) }
                 <|> do { reserved "Ple16"; return (UInt 16 (Phys LEn)) }
                 <|> do { reserved "Pbe16"; return (UInt 16 (Phys BEn)) }
                 <|> ( if allow_u24_internal 
                         then     do { reserved "U24"  ; return (UInt 24 View) }
                              <|> do { reserved "Ple24"; return (UInt 24 (Phys LEn)) }
                              <|> do { reserved "Pbe24"; return (UInt 24 (Phys BEn)) } 
                         else parserZero )
                 <|> do { reserved "Ple32"; return (UInt 32 (Phys LEn)) }
                 <|> do { reserved "Pbe32"; return (UInt 32 (Phys BEn)) }
                 <|> do { reserved "Ple64"; return (UInt 64 (Phys LEn)) }
                 <|> do { reserved "Pbe64"; return (UInt 64 (Phys BEn)) }
                 <?> "Base type"

-------------------------------------------------------------------------------

parseExpr :: Parser Expr
parseExpr = buildExpressionParser exprTable parseTerm
            <?> "Expression"

parseTerm :: Parser Expr
parseTerm = try parseFuncApp <|> parsePrimaryExpr

exprTable = [ [ infixFunc ]
            , [ prefix "+"   (\pos e     -> UnExpr  Plus    e     pos)
              , prefix "-"   (\pos e     -> UnExpr  Minus   e     pos)
              , prefix "~"   (\pos e     -> UnExpr  BitComp e     pos)
              , prefix "!"   (\pos e     -> UnExpr  Not     e     pos)   ]
            , [ binary "*"   (\pos e1 e2 -> BinExpr MulOp   e1 e2 pos) l
              , binary "/"   (\pos e1 e2 -> BinExpr DivOp   e1 e2 pos) l
              , binary "%"   (\pos e1 e2 -> BinExpr ModOp   e1 e2 pos) l ]
            , [ binary "+"   (\pos e1 e2 -> BinExpr AddOp   e1 e2 pos) l
              , binary "-"   (\pos e1 e2 -> BinExpr SubOp   e1 e2 pos) l ]
            , [ binary ".&." (\pos e1 e2 -> BinExpr BitAnd  e1 e2 pos) l ]
            , [ binary ".^." (\pos e1 e2 -> BinExpr BitXor  e1 e2 pos) l ]
            , [ binary ".|." (\pos e1 e2 -> BinExpr BitOr   e1 e2 pos) l ]
            , [ binary "<"   (\pos e1 e2 -> BinExpr Lt      e1 e2 pos) n
              , binary "<="  (\pos e1 e2 -> BinExpr Le      e1 e2 pos) n
              , binary ">"   (\pos e1 e2 -> BinExpr Gt      e1 e2 pos) n 
              , binary ">="  (\pos e1 e2 -> BinExpr Ge      e1 e2 pos) n ]
            , [ binary "=="  (\pos e1 e2 -> BinExpr Eq      e1 e2 pos) n 
              , binary "/="  (\pos e1 e2 -> BinExpr Ne      e1 e2 pos) n ]
            , [ binary "&&"  (\pos e1 e2 -> BinExpr And     e1 e2 pos) l ]
            , [ binary "||"  (\pos e1 e2 -> BinExpr Or      e1 e2 pos) l ]
            ]
  where
    infixFunc = Infix (do { pos <- getPosition
                          ; f <- between (reservedOp "`") (reservedOp "`") parseFunc
                          ; return (\e1 e2 -> App (Func f) [e1, e2] pos) }) l
    binary name fun assoc = Infix  (do { pos <- getPosition 
                                       ; reservedOp name
                                       ; return (fun pos) }) assoc
    prefix name fun       = Prefix (do { pos <- getPosition
                                       ; reservedOp name
                                       ; return (fun pos) })
    l = AssocLeft
    n = AssocNone
    r = AssocRight

parsePrimaryExpr :: Parser Expr
parsePrimaryExpr = getPosition >>= \pos ->
                     do { i <- natural     ; return (ILit i     pos) }
                 <|> do { reserved "True"  ; return (BLit True  pos) }
                 <|> do { reserved "False" ; return (BLit False pos) }
                 <|> try parseMember
                 -- <|> do { c <- parseConst  ; return (Const c    pos) }
                 <|> try parseFuncApp
                 <|> do { v <- parseVar    ; return (Var  v     pos) }
                 <|> (parens $ parseExpr)
                 <?> "Primary expression"

parseFuncApp :: Parser Expr
parseFuncApp = do { pos <- getPosition
                  ; func <- parseFunc
                  ; args <- many1 parseArg
                  ; return (App (Func func) args pos) }
               <?> "Function application"

parseMember :: Parser Expr
parseMember = do { pos <- getPosition
                 ; chainl1 (Var <$> parseVar <*> pure pos)
                           (reservedOp "." >> return (\e1 (Var v2 _) -> Member e1 v2 pos))
                 } <?> "Member projection"

parse :: SourceName -> String -> Either ParseError Module
parse filePath input = PP.parse p filePath input
  where p = do { whiteSpace
               ; x <- parseFile
               ; eof
               ; return x
               }



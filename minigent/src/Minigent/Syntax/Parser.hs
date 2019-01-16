-- |
-- Module      : Minigent.Syntax.Parser
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- This parser uses the @Earley@ library to make it based on a nice declarative grammar
-- specification without too much noise.
--
-- The algorithm is cubic in the worst case but linear normally. We test for and avoid ambiguity,
-- even though the Earley algorithm can handle ambiguous grammars, so that the parser can have
-- good errors and fast performance.
--
-- It can be imported unqualified or qualiifed, as there are very few exports.
{-# LANGUAGE RecursiveDo #-}
module Minigent.Syntax.Parser where

import Text.Earley
import Control.Applicative
import Data.Maybe (isJust)

import qualified Minigent.Syntax.Lexer as L

import Minigent.Syntax
import Minigent.Syntax.Utils
import qualified Minigent.Syntax.Utils.Row as Row

-- | The grammar for multiple top-level declarations.
toplevels :: Grammar r (Prod r String L.Token [RawTopLevel])
toplevels = mdo
    tl <- toplevel
    tls <- rule $ many tl
    return tls

-- | The grammar for a single top-level declarations.
toplevel :: Grammar r (Prod r String L.Token RawTopLevel)
toplevel = mdo

    let fromLowerIdent (L.LowerIdent n) = Just n
        fromLowerIdent _                = Nothing
        fromNumeric    (L.Numeric n)    = Just n
        fromNumeric    _                = Nothing

        reservedTypeNames = ["U8","U16","U32", "U64", "Bool","Unit"]

        reservedValueNames = ["Unit","True","False"]

        fromUpperType (L.UpperIdent n) | n `notElem` reservedTypeNames
                                       = Just n
        fromUpperType _                = Nothing
        fromUpperValue (L.UpperIdent n) | n `notElem` reservedValueNames
                                        = Just n 
        fromUpperValue _                = Nothing

    primTy <- rule $  U8   <$ token (L.UpperIdent "U8")
                  <|> U16  <$ token (L.UpperIdent "U16")   
                  <|> U32  <$ token (L.UpperIdent "U32")   
                  <|> U64  <$ token (L.UpperIdent "U64")   
                  <|> Bool <$ token (L.UpperIdent "Bool")   
                  <|> Unit <$ token (L.UpperIdent "Unit")   
                  <?> "primitive type"
                  

    typeVar      <- rule $ terminal fromLowerIdent <?> "type variable"
    var          <- rule $ terminal fromLowerIdent <?> "variable"
    fieldName    <- rule $ terminal fromLowerIdent <?> "field name"
    absTypeName  <- rule $ terminal fromUpperType  <?> "abstract type"
    conName      <- rule $ terminal fromUpperValue <?> "Constructor"

    takenTag     <- rule $  isJust <$> optional (token (L.Keyword L.Take)) 
                        <?> "optional taken tag"

    fieldEntry   <- rule $  Entry <$> fieldName <* token L.Colon <*> ty <*> takenTag  
                        <?> "field entry"

    fieldEntries <- rule $  (:)   <$> fieldEntry <* token L.Comma <*> fieldEntries
                        <|> (:[]) <$> fieldEntry
                        <?> "field entries"

    conEntry     <- rule $  Entry <$> conName <*> ty <*> takenTag
                        <?> "constructor entry"
    
    conEntries   <- rule $  (:)   <$> conEntry <* token L.Bar <*> conEntries
                        <|> (:[]) <$> conEntry
                        <?> "constructor entries"
  

    sigil <- rule $  Unboxed  <$ token L.Hash
                 <|> ReadOnly <$ token L.Bang
                 <|> pure Writable
                 <?> "sigil"


    atomicTy <- rule $  PrimType    <$> primTy
                    <|> TypeVar     <$> typeVar
                    <|> TypeVarBang <$> typeVar <* token (L.Bang)
                    <|> Record      <$  token (L.Open L.Brace)
                                    <*> (Row.fromList <$> fieldEntries)
                                    <*  token (L.Close L.Brace)
                                    <*> sigil 
                    <|> Variant     <$  token (L.Operator Less)
                                    <*> (Row.fromList <$> conEntries )
                                    <*  token (L.Operator Greater)
                    <|> AbsType     <$> absTypeName
                                    <*> sigil
                                    <*> pure []
                    <|> id          <$  token (L.Open L.Paren)
                                    <*> ty
                                    <*  token (L.Close L.Paren)

    ty' <- rule $ AbsType <$> absTypeName
                          <*> sigil
                          <*> some atomicTy
               <|> atomicTy

    ty <- rule $  Function <$> ty' <* token (L.Arrow) <*> ty
              <|> ty'

  
    bool <- rule $  True  <$ token (L.UpperIdent "True")
                <|> False <$ token (L.UpperIdent "False")
                <?> "boolean"

    number <- rule $ terminal fromNumeric <?> "number"
    literal <- rule $  BoolV <$> bool
                   <|> IntV  <$> number 
                   <|> UnitV <$ token (L.UpperIdent "Unit")
                   <?> "literal"

    types <- rule $  (:)   <$> ty <* token (L.Comma) <*> types
                 <|> (:[]) <$> ty
                 <|> pure []

    fieldInitialiser <- rule $  (,) <$> fieldName <* token (L.Equals) <*> exp
                            <?> "field initialiser" 

    fieldInitialisers <- rule $ (:) <$> fieldInitialiser <* token (L.Comma) <*> fieldInitialisers
                                    <|> (:[]) <$> fieldInitialiser

    atomExp <- rule $  Literal <$> literal  
                   <|> Var     <$> var 
                   <|> TypeApp <$> var 
                               <*  token (L.Open L.Square)
                               <*> types
                               <*  token (L.Close L.Square)
                   <|> If      <$  token (L.Keyword L.If)
                               <*> exp 
                               <*  token (L.Keyword L.Then)
                               <*> exp 
                               <*  token (L.Keyword L.Else)
                               <*> exp  
                               <*  token (L.Keyword L.End)
                   <|> Let     <$  token (L.Keyword L.Let)
                               <*> var
                               <*  token (L.Equals)
                               <*> exp 
                               <*  token (L.Keyword L.In)
                               <*> exp  
                               <*  token (L.Keyword L.End)
                   <|> LetBang <$  token (L.Keyword L.Let)
                               <*  token (L.Bang)
                               <*  token (L.Open L.Paren)
                               <*> many var
                               <*  token (L.Close L.Paren)
                               <*> var
                               <*  token (L.Equals)
                               <*> exp 
                               <*  token (L.Keyword L.In)
                               <*> exp  
                               <*  token (L.Keyword L.End)
                   <|> Struct  <$  token (L.Open L.Brace)
                               <*> fieldInitialisers
                               <*  token (L.Close L.Brace)
                   <|> Case    <$  token (L.Keyword L.Case)
                               <*> exp
                               <*  token (L.Keyword L.Of)
                               <*> conName 
                               <*> var
                               <*  token (L.Arrow)
                               <*> exp 
                               <*  token (L.Bar)
                               <*> var
                               <*  token (L.Arrow)
                               <*> exp
                               <*  token (L.Keyword L.End)
                   <|> Esac    <$  token (L.Keyword L.Case)
                               <*> exp
                               <*  token (L.Keyword L.Of)
                               <*> conName 
                               <*> var
                               <*  token (L.Arrow)
                               <*> exp 
                               <*  token (L.Keyword L.End)
                   <|> Take    <$  token (L.Keyword L.Take)
                               <*> var 
                               <*  token (L.Open L.Brace)
                               <*> fieldName 
                               <*  token (L.Equals) 
                               <*> var
                               <*  token (L.Close L.Brace)
                               <*  token (L.Equals)
                               <*> exp
                               <*  token (L.Keyword L.In)
                               <*> exp  
                               <*  token (L.Keyword L.End)
                   <|> Put     <$  token (L.Keyword L.Put)
                               <*> exp
                               <*  token (L.Dot)
                               <*> fieldName 
                               <*  token (L.Colon)
                               <*  token (L.Equals) 
                               <*> exp
                               <*  token (L.Keyword L.End)
                   <|> Member  <$> atomExp <* token (L.Dot) <*> fieldName
                   <|> id      <$  token (L.Open L.Paren)
                               <*> exp 
                               <*  token (L.Close L.Paren)
                   <?> "expression (atomic)"

    appExp <- rule $  Apply <$> appExp <*> atomExp
                  <|> Con   <$> conName <*> atomExp
                  <|> PrimOp Not . pure <$ token (L.Operator Not) <*> atomExp 
                  <|> atomExp
                  <?> "expression (appExp)"


    let binOp e1 o e2 = PrimOp o [e1, e2]
        fromOp set (L.Operator o) | o `elem` set = Just o
        fromOp _ _                               = Nothing 
              

    prodExp <- rule $ binOp <$> prodExp <*> terminal (fromOp prodOps) <*> appExp
                   <|> appExp
                   <?> "expression (prodExp)"
    sumExp <- rule $ binOp <$> sumExp <*> terminal (fromOp sumOps) <*> prodExp
                  <|> prodExp
                  <?> "expression (sumExp)"
    compExp <- rule $ binOp <$> sumExp <*> terminal (fromOp compOps) <*> sumExp
                   <|> sumExp
                   <?> "expression (compExp)"
    boolExp <- rule $ binOp <$> boolExp <*> terminal (fromOp boolOps) <*> compExp
                   <|> compExp
                   <?> "expression (boolExp)"
    exp <- rule $  Sig <$> exp <* token (L.Colon) <*> ty
               <|> boolExp <?> "expression"

    typeVars <- rule $  (:)   <$> typeVar <* token (L.Comma) <*> typeVars
                    <|> (:[]) <$> typeVar
                    <|> pure []

    constraint <- rule $  Share  . TypeVar <$ token (L.UpperIdent "Share")  <*> typeVar
                      <|> Drop   . TypeVar <$ token (L.UpperIdent "Drop")   <*> typeVar
                      <|> Escape . TypeVar <$ token (L.UpperIdent "Escape") <*> typeVar

    constraints <- rule $  (:)   <$> constraint <* token (L.Comma) <*> constraints
                       <|> (:[]) <$> constraint
                       <|> pure []

    polyType <- rule $  Forall <$  token (L.Open L.Square) 
                               <*> typeVars 
                               <*  token (L.Close L.Square)
                               <*> constraints
                               <*  token (L.Dot)
                               <*> ty
                    <|> Forall [] [] <$> ty
    topLevel <- rule $  TypeSig  <$> var
                                 <*  token (L.Colon) 
                                 <*> polyType 
                                 <*  token (L.Semi)
                    <|> Equation <$> var
                                 <*> var
                                 <*  token (L.Equals) 
                                 <*> exp 
                                 <*  token (L.Semi) 
    return topLevel

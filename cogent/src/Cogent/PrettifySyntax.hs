module Cogent.PrettifySyntax where

import Cogent.PrettifyLexer(Token, SourcePos)

data Type' =
    Abstract Name
    | PrimType PrimType
    | TypeVar Name
    | Bang Type
    | Unbox Type
    | TyApp Type Type
    | Fun Type Type
    | Tuple [Type]
    | Record [FieldDecl]
    | Variant [ConsDecl]
    | Take Type TakePut
    | Put Type TakePut
    | Parens Type
    deriving (Show)

data PrimType =
    U8 | U16 | U32 | U64 | Bool | Unit
    deriving (Show)

type Name = String

data FieldDecl = 
    Field Name Type [(Token, SourcePos)]
    deriving (Show)
    
data ConsDecl = 
    Cons Name Type [(Token, SourcePos)]
    deriving (Show)

data TakePut =
    TakePut [Name] [(Token, SourcePos)]
    | Everything SourcePos
    deriving (Show)

data Type =
    T Type' [(Token, SourcePos)]
    deriving (Show)
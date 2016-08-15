-- @LICENSE(NICTA_CORE)

{-# LANGUAGE CPP #-}

module Cogent.Common.Syntax where

import Cogent.Compiler

#if __GLASGOW_HASKELL__ < 709
import Data.Monoid
#endif
import Data.Group
import Text.PrettyPrint.ANSI.Leijen

type FieldName   = String
type TagName     = String
type FunName     = String
type VarName     = String
type TyVarName   = String
type TypeName    = String

type FieldIndex = Int

type OpName = String

data Op
  = Plus | Minus | Times | Divide | Mod
  | Not | And | Or
  | Gt | Lt | Le | Ge | Eq | NEq
  | BitAnd | BitOr | BitXor | LShift | RShift | Complement
  deriving (Eq, Show)

data Pragma = InlinePragma FunName
            | CInlinePragma FunName
            | FnMacroPragma FunName
            | UnrecPragma String
            deriving (Eq, Show)

data Associativity = LeftAssoc Int
                   | RightAssoc Int
                   | NoAssoc Int
                   | Prefix
                   deriving Eq

associativity :: Op -> Associativity
associativity x | x `elem` [Times, Divide, Mod] = LeftAssoc 3
                | x `elem` [Plus, Minus] = LeftAssoc 4
                | x `elem` [LShift, RShift] = LeftAssoc 5
                | x `elem` [Gt, Lt, Le, Ge, Eq, NEq] = NoAssoc 6
                | x `elem` [BitAnd] = LeftAssoc 8
                | x `elem` [BitXor] = LeftAssoc 9
                | x `elem` [BitOr]  = LeftAssoc 10
                | x `elem` [And] = RightAssoc 11
                | x `elem` [Or]  = RightAssoc 12
                | otherwise = Prefix

symbolOp :: OpName -> Op
symbolOp "+"   = Plus
symbolOp "-"   = Minus
symbolOp "*"   = Times
symbolOp "/"   = Divide
symbolOp "%"   = Mod
symbolOp "not" = Not
symbolOp "&&"  = And
symbolOp "||"  = Or
symbolOp ">="  = Ge
symbolOp "<="  = Le
symbolOp "<"   = Lt
symbolOp ">"   = Gt
symbolOp "=="  = Eq
symbolOp "/="  = NEq
symbolOp ".&." = BitAnd
symbolOp ".|." = BitOr
symbolOp ".^." = BitXor
symbolOp ">>"  = RShift
symbolOp "<<"  = LShift
symbolOp "complement" = Complement
symbolOp x     = __impossible "symbolOp"

opSymbol :: Op -> String
opSymbol Plus  = "+"
opSymbol Minus = "-"
opSymbol Times = "*"
opSymbol Divide = "/"
opSymbol Mod = "%"
opSymbol Not = "not"
opSymbol And = "&&"
opSymbol Or = "||"
opSymbol Gt = ">"
opSymbol Lt = "<"
opSymbol Le = "<="
opSymbol Ge = ">="
opSymbol Eq = "=="
opSymbol NEq = "/="
opSymbol BitAnd = ".&."
opSymbol BitOr = ".|."
opSymbol BitXor = ".^."
opSymbol LShift = "<<"
opSymbol RShift = ">>"
opSymbol Complement = "complement"

instance Pretty Op where
  pretty = string . opSymbol

data Likelihood = Unlikely | Regular | Likely deriving (Show, Eq, Ord)

instance Monoid Likelihood where
  mempty = Regular
  mappend Unlikely Likely   = Regular
  mappend Unlikely _        = Unlikely
  mappend Likely   Unlikely = Regular
  mappend Likely   _        = Likely
  mappend Regular  l        = l

instance Group Likelihood where
  invert Regular  = Regular
  invert Likely   = Unlikely
  invert Unlikely = Likely

instance Abelian Likelihood

tagSuccess = "Success" :: TagName
tagFail    = "Fail"    :: TagName


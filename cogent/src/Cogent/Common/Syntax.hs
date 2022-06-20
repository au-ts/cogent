-- @LICENSE(NICTA_CORE)

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Cogent.Common.Syntax where

import Cogent.Compiler

import Data.Binary (Binary)
import Data.Data hiding (Prefix)
#if __GLASGOW_HASKELL__ < 709
import Data.Monoid
#endif
import Data.Word
import GHC.Generics (Generic)
import Text.PrettyPrint.ANSI.Leijen

type RepName     = String
type DataLayoutName = RepName -- For gradual transition to eliminate Rep from the compiler
type FieldName   = String
type TagName     = String
type FunName     = String
type ConstName   = String
type VarName     = String
type TyVarName   = String
type RecParName  = String
type TypeName    = String
type DLVarName   = String

newtype CoreFunName = CoreFunName { unCoreFunName :: String }
  deriving (Eq, Show, Ord, Generic)

instance Binary CoreFunName

funNameToCoreFunName :: FunName -> CoreFunName
funNameToCoreFunName = CoreFunName

unsafeNameToCoreFunName :: String -> CoreFunName
unsafeNameToCoreFunName = CoreFunName

unsafeCoreFunName :: String -> CoreFunName
unsafeCoreFunName = CoreFunName

type FieldIndex = Int
type ArrayIndex = Word32  -- It actually can be large on 64-bit machines, but for now we just leave them Word32 for simplicity / zilinc
type ArraySize  = Word32

type Size = Integer  -- Not sure why quickcheck tests infinite loop if Size = Word32.

type OpName = String


data GetOrSet = Get | Set deriving (Data, Eq, Show)

data Pragma t = InlinePragma FunName
              | CInlinePragma FunName
              | FnMacroPragma FunName
              | GSetterPragma GetOrSet t FieldName FunName
              | UnrecPragma String String  -- pragma name, the rest
              deriving (Data, Eq, Show, Functor)

data Op
  = Plus | Minus | Times | Divide | Mod
  | Not | And | Or
  | Gt | Lt | Le | Ge | Eq | NEq
  | BitAnd | BitOr | BitXor | LShift | RShift | Complement
  deriving (Data, Eq, Ord, Show, Generic)

instance Binary Op

data Associativity = LeftAssoc Int
                   | RightAssoc Int
                   | NoAssoc Int
                   | Prefix
                   deriving Eq

associativity :: Op -> Associativity
associativity x | x `elem` [Times, Divide, Mod] = LeftAssoc 11
                | x `elem` [Plus, Minus] = LeftAssoc 12
                | x `elem` [Gt, Lt, Le, Ge, Eq, NEq] = NoAssoc 13
                | x `elem` [BitAnd] = LeftAssoc 14
                | x `elem` [BitXor] = LeftAssoc 15
                | x `elem` [BitOr]  = LeftAssoc 16
                | x `elem` [LShift, RShift] = LeftAssoc 17
                | x `elem` [And] = RightAssoc 18
                | x `elem` [Or]  = RightAssoc 19
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

data Likelihood = Unlikely | Regular | Likely deriving (Show, Data, Eq, Ord)

#if __GLASGOW_HASKELL__ < 803
instance Monoid Likelihood where
  mempty = Regular
  mappend Unlikely Likely   = Regular
  mappend Unlikely _        = Unlikely
  mappend Likely   Unlikely = Regular
  mappend Likely   _        = Likely
  mappend Regular  l        = l
#else
instance Semigroup Likelihood where
  (<>) Unlikely Likely   = Regular
  (<>) Unlikely _        = Unlikely
  (<>) Likely   Unlikely = Regular
  (<>) Likely   _        = Likely
  (<>) Regular  l        = l
instance Monoid Likelihood where
  mempty = Regular
#endif

tagSuccess = "Success" :: TagName
tagFail    = "Fail"    :: TagName


-- ----------------------------------------------------------------------------
-- custTyGen

data CustTyGenInfo = CTGI  deriving (Show, Generic) -- TODO: info like field mapping, etc.

instance Binary CustTyGenInfo

-- ex1 :: M.Map (Type 'Zero) (String, CustTypeGenInfo)
-- ex1 = M.singleton (TRecord [("f1", (TCon "A" [] Unboxed, False)),
--                             ("f2", (TCon "B" [] Unboxed, False)),
--                             ("f3", (TCon "C" [] Writable, False))] Writable) ("T_c_t", CTGI)



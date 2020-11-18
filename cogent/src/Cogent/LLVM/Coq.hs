{-# LANGUAGE DataKinds #-}

module Cogent.LLVM.Coq (toCoq) where

import Cogent.Common.Syntax (Op, VarName)
import qualified Cogent.Common.Syntax as S (Op (..))
import Cogent.Common.Types (PrimInt)
import qualified Cogent.Common.Types as T (PrimInt (..))
import Cogent.Core (Definition (FunDef), Type (..), TypedExpr (TE))
import qualified Cogent.Core as E (Expr (..))
import Control.Monad (void)
import Data.Fin (finInt)
import Data.List (intercalate)
import System.FilePath (replaceExtension)
import Text.Show.Pretty (ppShow)

newtype CoqList a = CoqList [a]
instance Show a => Show (CoqList a) where
    show (CoqList xs) = "[" ++ intercalate ";" (show <$> xs) ++ "]"

newtype CoqBool = CoqBool Bool
instance Show CoqBool where show (CoqBool b) = if b then "true" else "false"

type CoqNat = Int

type Index = CoqNat
type Field = CoqNat
type Name = String

data NumType = U8 | U16 | U32 | U64 deriving (Show)
data PrimType = Num NumType | Bool | String deriving (Show)

data PrimOp
    = Plus NumType
    | Minus NumType
    | Times NumType
    | Divide NumType
    | Mod NumType
    | Not
    | And
    | Or
    | Gt NumType
    | Lt NumType
    | Le NumType
    | Ge NumType
    | Eq PrimType
    | NEq PrimType
    | BitAnd NumType
    | BitOr NumType
    | BitXor NumType
    | LShift NumType
    | RShift NumType
    | Complement NumType
    deriving (Show)

data Lit
    = LBool CoqBool
    | LU8 Integer
    | LU16 Integer
    | LU32 Integer
    | LU64 Integer
    deriving (Show)

data Expr
    = Prim PrimOp (CoqList Expr)
    | App Expr Expr
    | Unit
    | Lit Lit
    | SLit String
    | Cast NumType Expr
    | Let Expr Expr
    | Var Index
    | Case Expr Name Expr Expr
    | Esac Expr Name
    | -- | Fun Expr (CoqList Type)
      -- | Con (CoqList (Name, Type, VariantState)) Name Expr
      -- | Struct (CoqList Type) (CoqList Expr)
      -- | Member Expr Field
      -- | Put Expr Field Expr
      -- | LetBang (Set Index) Expr Expr
      -- | Take Expr Field Expr
      -- | Promote Type Expr
      If Expr Expr Expr
    deriving (Show)

-- data Def = FunDef Name Type Type Expr
type Def = Expr

-- Take a list of Cogent definitions and output the resultant definition to a file
toCoq :: [Definition TypedExpr VarName VarName] -> FilePath -> IO ()
toCoq monoed source = void $ writeFile (replaceExtension source "v") $ genModule monoed

fileHeader :: String
fileHeader =
    unlines
        [ "From Coq Require Import List ZArith."
        , ""
        , "From Checker Require Import Cogent."
        , ""
        , "Import ListNotations."
        , ""
        , "Definition CogentInput :="
        ]

genModule :: [Definition TypedExpr VarName VarName] -> String
genModule defs = fileHeader ++ ppShow (genDefinition <$> defs) ++ "."

genDefinition :: Definition TypedExpr VarName VarName -> Def
genDefinition (FunDef _ name _ _ t rt body) = genExpr body -- TODO: generate function definition
genDefinition _ = error "not implemented"

genExpr :: (Show a, Show b) => TypedExpr t v a b -> Expr
genExpr (TE _ (E.ILit int p)) = Lit $ genLit int p
genExpr (TE _ (E.Op op os@((TE t' _) : _))) = Prim (genOp t' op) $ CoqList (genExpr <$> os)
genExpr (TE _ (E.Let _ val body)) = Let (genExpr val) (genExpr body)
genExpr (TE _ (E.Variable (idx, _))) = Var (finInt idx) -- TODO: generate variable
genExpr t = error $ show t

genLit :: Integer -> PrimInt -> Lit
genLit w T.U8 = LU8 w
genLit w T.U16 = LU16 w
genLit w T.U32 = LU32 w
genLit w T.U64 = LU64 w
genLit w T.Boolean = LBool (CoqBool (w /= 0))

genOp :: Type t b -> Op -> PrimOp
genOp t S.Plus = Plus $ genNumType t
genOp t S.Minus = Minus $ genNumType t
genOp t S.Times = Times $ genNumType t
genOp t S.Divide = Divide $ genNumType t
genOp t S.Mod = Mod $ genNumType t
genOp _ S.Not = Not
genOp _ S.And = And
genOp _ S.Or = Or
genOp t S.Gt = Gt $ genNumType t
genOp t S.Lt = Lt $ genNumType t
genOp t S.Le = Le $ genNumType t
genOp t S.Ge = Ge $ genNumType t
genOp t S.Eq = Eq $ genPrimType t
genOp t S.NEq = NEq $ genPrimType t
genOp t S.BitAnd = BitAnd $ genNumType t
genOp t S.BitOr = BitOr $ genNumType t
genOp t S.BitXor = BitXor $ genNumType t
genOp t S.LShift = LShift $ genNumType t
genOp t S.RShift = RShift $ genNumType t
genOp t S.Complement = Complement $ genNumType t

genPrimType :: Type t b -> PrimType
genPrimType (TPrim T.Boolean) = Bool
genPrimType t@(TPrim _) = Num $ genNumType t
genPrimType TString = String
genPrimType _ = error "not  a PrimType"

genNumType :: Type t b -> NumType
genNumType (TPrim T.U8) = U8
genNumType (TPrim T.U16) = U16
genNumType (TPrim T.U32) = U32
genNumType (TPrim T.U64) = U64
genNumType _ = error "not a NumType"

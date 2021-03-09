{-# LANGUAGE DataKinds #-}

module Cogent.LLVM.Coq (toCoq) where

import Cogent.Common.Syntax (Op, VarName)
import qualified Cogent.Common.Syntax as S (Op (..))
import Cogent.Common.Types (PrimInt)
import qualified Cogent.Common.Types as T (PrimInt (..), Sigil (..))
import Cogent.Core (Definition, TypedExpr (TE, exprType))
import qualified Cogent.Core as C (Definition (..), Expr (..), Type (..))
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

data Sigil = Boxed | Unboxed deriving (Show)
data VariantState = Checked | Unchecked deriving (Show)
data RecordState = Taken | Present deriving (Show)

data Type
    = TVar Index
    | TVarBang Index
    | TCon Name [Type] Sigil
    | TFun Type Type
    | TPrim PrimType
    | TSum [(Name, (Type, VariantState))]
    | TRecord (CoqList (Name, (Type, RecordState))) Sigil
    | TUnit
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
    | Struct (CoqList Type) (CoqList Expr)
    | Member Expr Field
    | Take Expr Field Expr
    | Put Expr Field Expr
    | -- | Fun Expr (CoqList Type)
      -- | Con (CoqList (Name, Type, VariantState)) Name Expr
      -- | LetBang (Set Index) Expr Expr
      -- | Promote Type Expr
      If Expr Expr Expr
    deriving (Show)

data Def = FunDef Name Type Type Expr deriving (Show)

-- Take a list of Cogent definitions and output the resultant definition to a file
toCoq :: [Definition TypedExpr VarName VarName] -> FilePath -> IO ()
toCoq monoed source = void $ writeFile (replaceExtension source "v") $ genModule monoed

fileHeader :: String
fileHeader =
    unlines
        [ "From Coq Require Import List String ZArith."
        , ""
        , "From Checker Require Import Cogent."
        , ""
        , "Import ListNotations."
        , "Local Open Scope string_scope."
        , ""
        , "Definition CogentInput :="
        ]

genModule :: [Definition TypedExpr VarName VarName] -> String
genModule defs = fileHeader ++ ppShow (genDefinition <$> defs) ++ "."

genDefinition :: Definition TypedExpr VarName VarName -> Def
genDefinition (C.FunDef _ name _ _ t rt body) = FunDef name (genType t) (genType rt) (genExpr body)
genDefinition _ = error "not implemented"

genType :: Show b => C.Type t b -> Type
genType C.TUnit = TUnit
-- genType (C.TFun t rt) = TFun (genType t) (genType rt)
genType t@(C.TPrim _) = TPrim (genPrimType t)
genType C.TString = TPrim String
genType (C.TRecord _ flds s) =
    let flds' = ([(f, (genType t, if b then Taken else Present)) | (f, (t, b)) <- flds])
     in TRecord (CoqList flds') (genSigil s)
genType t = error $ show t

genExpr :: (Show a, Show b) => TypedExpr t v a b -> Expr
genExpr (TE _ (C.ILit int p)) = Lit $ genLit int p
genExpr (TE _ (C.Op op os@((TE t' _) : _))) = Prim (genOp t' op) $ CoqList (genExpr <$> os)
genExpr (TE _ (C.Let _ val body)) = Let (genExpr val) (genExpr body)
genExpr (TE _ (C.Variable (idx, _))) = Var (finInt idx)
genExpr (TE _ C.Unit) = Unit
genExpr (TE _ (C.If c b1 b2)) = If (genExpr c) (genExpr b1) (genExpr b2)
genExpr (TE _ (C.Cast t e)) = Cast (genNumType t) (genExpr e)
genExpr (TE _ (C.Struct flds)) = Struct (CoqList (genType . exprType . snd <$> flds)) (CoqList (genExpr . snd <$> flds))
genExpr (TE _ (C.Member recd fld)) = Member (genExpr recd) fld
genExpr (TE _ (C.Take _ recd fld body)) = Take (genExpr recd) fld (genExpr body)
genExpr (TE _ (C.Put recd fld val)) = Put (genExpr recd) fld (genExpr val)
genExpr e = error $ show e

genLit :: Integer -> PrimInt -> Lit
genLit w T.U8 = LU8 w
genLit w T.U16 = LU16 w
genLit w T.U32 = LU32 w
genLit w T.U64 = LU64 w
genLit w T.Boolean = LBool (CoqBool (w /= 0))

genOp :: C.Type t b -> Op -> PrimOp
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

genPrimType :: C.Type t b -> PrimType
genPrimType (C.TPrim T.Boolean) = Bool
genPrimType t@(C.TPrim _) = Num $ genNumType t
genPrimType C.TString = String
genPrimType _ = error "not  a PrimType"

genNumType :: C.Type t b -> NumType
genNumType (C.TPrim T.U8) = U8
genNumType (C.TPrim T.U16) = U16
genNumType (C.TPrim T.U32) = U32
genNumType (C.TPrim T.U64) = U64
genNumType _ = error "not a NumType"

genSigil :: T.Sigil r -> Sigil
genSigil (T.Boxed _ _) = Boxed
genSigil T.Unboxed = Unboxed

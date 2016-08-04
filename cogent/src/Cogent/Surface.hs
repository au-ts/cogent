--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE DeriveFunctor, FlexibleInstances, TupleSections, DeriveFoldable, DeriveTraversable #-}

module Cogent.Surface where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Util

import qualified Data.Map as M
#if __GLASGOW_HASKELL__ < 709
import Data.Foldable hiding (elem)
import Data.Traversable
#endif
import Text.Parsec.Pos

type OpName = String

data IrrefutablePattern v = PVar v
                          | PTuple [IrrefutablePattern v]
                          | PUnboxedRecord [Maybe (FieldName, IrrefutablePattern v)]
                          | PUnderscore
                          | PUnitel
                          | PTake v [Maybe (FieldName, IrrefutablePattern v)]
                              -- Note: `Nothing' will be desugared to `Just' in TypeCheck / zilinc
                          deriving (Show, Functor, Foldable, Traversable, Eq)

data Pattern v = PCon TagName [IrrefutablePattern v]
               | PIntLit Integer
               | PBoolLit Bool
               | PCharLit Char
               | PIrrefutable (IrrefutablePattern v)
               deriving (Show, Functor, Foldable, Traversable, Eq)

data Alt pv e = Alt (Pattern pv) Likelihood e deriving (Show, Functor, Foldable,Traversable)

data Binding t pv e = Binding (IrrefutablePattern pv) (Maybe t) e [VarName]
                    deriving (Show, Functor, Foldable, Traversable)

data Inline = Inline
            | NoInline
            deriving (Eq, Show)

data Expr t pv e = PrimOp OpName [e]
                 | Var VarName
                 | Match e [VarName] [Alt pv e]
                 | TypeApp VarName [t] Inline
                 | Con TagName [e]
                 | Seq e e
                 | App e e
                 | If e [VarName] e e
                 | Member e FieldName
                 | Unitel
                 | IntLit Integer
                 | BoolLit Bool
                 | CharLit Char
                 | StringLit String
                 | Tuple [e]
                 | UnboxedRecord [(FieldName, e)]
                 | Let [Binding t pv e] e
                 | Upcast e
                 | Widen  e
                 | Put e [Maybe (FieldName, e)]  -- Note: `Nothing' will be desugared to `Just' in TypeCheck / zilinc
                 deriving (Show, Functor, Foldable, Traversable)

type Banged = Bool
type Taken  = Bool

data Type t =
            -- They are in WHNF
              TCon TypeName [t] Sigil
            | TVar VarName Banged
            | TFun t t
            | TRecord [(FieldName, (t, Taken))] Sigil
            | TVariant (M.Map TagName [t])
            | TTuple [t]
            | TUnit
            -- They will be elimiated at some point / zilinc
            | TUnbox   t
            | TBang    t
            | TTake (Maybe [FieldName]) t
            | TPut  (Maybe [FieldName]) t
            deriving (Show, Functor, Eq, Foldable, Traversable)

data Polytype t = PT [(TyVarName, Kind)] t deriving (Show, Functor, Foldable, Traversable)

data TopLevel t pv e = Include String
                     | IncludeStd String
                     | TypeDec TypeName [TyVarName] t
                     | AbsTypeDec TypeName [TyVarName]
                     | AbsDec VarName (Polytype t)
                     | FunDef VarName (Polytype t) [Alt pv e]
                     | ConstDef VarName t e
                     deriving (Show, Functor, Foldable, Traversable)

-- XXX | eqTopLevelId :: String -> TopLevel t pv e -> Bool
-- XXX | eqTopLevelId x (Include {}) = False
-- XXX | eqTopLevelId x (IncludeStd {}) = False
-- XXX | eqTopLevelId x (TypeDec tn _ _) = x == tn
-- XXX | eqTopLevelId x (AbsTypeDec tn _) = x == tn
-- XXX | eqTopLevelId x (AbsDec fn _) = x == fn
-- XXX | eqTopLevelId x (FunDef fn _ _) = x == fn
-- XXX | eqTopLevelId x (ConstDef vn _ _) = x == vn  -- should not matter

absFnDeclId :: String -> TopLevel t pv e -> Bool
absFnDeclId x (AbsDec fn _) = x == fn
absFnDeclId _ _ = False

absTyDeclId :: String -> TopLevel t pv e -> Bool
absTyDeclId x (AbsTypeDec tn _) = x == tn
absTyDeclId _ _ = False


data LocExpr = LocExpr { posOfE :: SourcePos, exprOfLE :: Expr LocType VarName LocExpr } deriving (Show)
data LocType = LocType { posOfT :: SourcePos, typeOfLT :: Type LocType } deriving (Show)

data RawType = RT { unRT :: Type RawType } deriving (Show, Eq)
data RawExpr = RE { unRE :: Expr RawType VarName RawExpr } deriving Show

instance Functor (Flip (Binding t) e) where
  fmap f (Flip (Binding p mt e vs)) = Flip (Binding (fmap f p) mt e vs)
instance Functor (Flip2 Binding p e) where
  fmap f (Flip2 (Binding p mt e vs)) = Flip2 (Binding p (fmap f mt) e vs)
instance Functor (Flip Alt e) where
  fmap f (Flip (Alt p b e)) = Flip (Alt (fmap f p) b e)
instance Functor (Flip (Expr t) e) where
  fmap f (Flip (Match e v alt))     = Flip (Match e v (map (ffmap f) alt))
  fmap f (Flip (Let bs e))          = Flip (Let (map (ffmap f) bs) e)
  fmap _ (Flip (Member e f))        = Flip (Member e f)
  fmap _ (Flip (PrimOp op e))       = Flip (PrimOp op e)
  fmap _ (Flip (Var v))             = Flip (Var v)
  fmap _ (Flip (TypeApp v ts nt))   = Flip (TypeApp v ts nt)
  fmap _ (Flip (Seq e e'))          = Flip (Seq e e')
  fmap _ (Flip (If c vs e e'))      = Flip (If c vs e e')
  fmap _ (Flip (App e e'))          = Flip (App e e')
  fmap _ (Flip (Con n e))           = Flip (Con n e)
  fmap _ (Flip Unitel)              = Flip Unitel
  fmap _ (Flip (IntLit l))          = Flip (IntLit l)
  fmap _ (Flip (BoolLit l))         = Flip (BoolLit l)
  fmap _ (Flip (CharLit l))         = Flip (CharLit l)
  fmap _ (Flip (StringLit l))       = Flip (StringLit l)
  fmap _ (Flip (Tuple es))          = Flip (Tuple es)
  fmap _ (Flip (UnboxedRecord es))  = Flip (UnboxedRecord es)
  fmap _ (Flip (Put e es))          = Flip (Put e es)
  fmap _ (Flip (Upcast e))          = Flip (Upcast e)
  fmap _ (Flip (Widen e))           = Flip (Widen e)
instance Functor (Flip2 Expr p e) where
  fmap f (Flip2 (Let bs e))         = Flip2 (Let (map (fffmap f) bs) e)
  fmap f (Flip2 (TypeApp v ts nt))  = Flip2 (TypeApp v (map f ts) nt)
  -- never been more tempted to use unsafeCoerce
  fmap _ (Flip2 (Match e v alt))    = Flip2 (Match e v alt)
  fmap _ (Flip2 (PrimOp op e))      = Flip2 (PrimOp op e)
  fmap _ (Flip2 (Var v))            = Flip2 (Var v)
  fmap _ (Flip2 (Seq e e'))         = Flip2 (Seq e e')
  fmap _ (Flip2 (If c vs e e'))     = Flip2 (If c vs e e')
  fmap _ (Flip2 (App e e'))         = Flip2 (App e e')
  fmap _ (Flip2 (Member e f))       = Flip2 (Member e f)
  fmap _ (Flip2 (Con n e))          = Flip2 (Con n e)
  fmap _ (Flip2 Unitel)             = Flip2 Unitel
  fmap _ (Flip2 (IntLit l))         = Flip2 (IntLit l)
  fmap _ (Flip2 (BoolLit l))        = Flip2 (BoolLit l)
  fmap _ (Flip2 (CharLit l))        = Flip2 (CharLit l)
  fmap _ (Flip2 (StringLit l))      = Flip2 (StringLit l)
  fmap _ (Flip2 (Tuple es))         = Flip2 (Tuple es)
  fmap _ (Flip2 (UnboxedRecord es)) = Flip2 (UnboxedRecord es)
  fmap _ (Flip2 (Put e es))         = Flip2 (Put e es)
  fmap _ (Flip2 (Widen e))          = Flip2 (Widen e)
  fmap _ (Flip2 (Upcast e))         = Flip2 (Upcast e)
instance Functor (Flip (TopLevel t) e) where
  fmap f (Flip (FunDef v pt alts))  = Flip (FunDef v pt (map (ffmap f) alts))
  fmap _ (Flip (Include s))         = Flip (Include s)
  fmap _ (Flip (IncludeStd s))      = Flip (IncludeStd s)
  fmap _ (Flip (TypeDec n vs t))    = Flip (TypeDec n vs t)
  fmap _ (Flip (AbsTypeDec n vs))   = Flip (AbsTypeDec n vs)
  fmap _ (Flip (AbsDec v pt))       = Flip (AbsDec v pt)
  fmap _ (Flip (ConstDef v t e))    = Flip (ConstDef v t e)
instance Functor (Flip2 TopLevel p e) where
  fmap f (Flip2 (FunDef v pt alts)) = Flip2 (FunDef v (fmap f pt) alts)
  fmap f (Flip2 (AbsDec v pt))      = Flip2 (AbsDec v (fmap f pt))
  fmap f (Flip2 (ConstDef v t e))   = Flip2 (ConstDef v (f t) e)
  fmap f (Flip2 (TypeDec n vs t))   = Flip2 (TypeDec n vs (f t))
  fmap _ (Flip2 (Include s))        = Flip2 (Include s)
  fmap _ (Flip2 (IncludeStd s))     = Flip2 (IncludeStd s)
  fmap _ (Flip2 (AbsTypeDec n vs))  = Flip2 (AbsTypeDec n vs)


stripLocT :: LocType -> RawType
stripLocT = RT . fmap stripLocT . typeOfLT

stripLocE :: LocExpr -> RawExpr
stripLocE = RE . fffmap stripLocT . fmap stripLocE . exprOfLE

noPos :: SourcePos
noPos = newPos "unknown" 0 0

dummyLocT :: RawType -> LocType
dummyLocT = LocType noPos . fmap dummyLocT . unRT

dummyLocE :: RawExpr -> LocExpr
dummyLocE = LocExpr noPos . fffmap dummyLocT . fmap dummyLocE . unRE

stripAllLoc :: TopLevel LocType VarName LocExpr -> TopLevel RawType VarName RawExpr
stripAllLoc = fffmap stripLocT . fmap stripLocE

isIntType :: RawType -> Bool
isIntType (RT (TCon cn ts s)) | cn `elem` words "U8 U16 U32 U64", null ts, s == Unboxed = True
isIntType _ = False

isVariantType :: RawType -> Bool
isVariantType (RT (TVariant _)) = True
isVariantType _ = False

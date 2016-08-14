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
import Data.Functor.Identity
import Control.Applicative
#if __GLASGOW_HASKELL__ < 709
import Data.Foldable hiding (elem)
import Data.Traversable
#endif
import Text.Parsec.Pos

type OpName = String

type DocString = String

data IrrefutablePattern pv = PVar pv
                           | PTuple [IrrefutablePattern pv]
                           | PUnboxedRecord [Maybe (FieldName, IrrefutablePattern pv)]
                           | PUnderscore
                           | PUnitel
                           | PTake pv [Maybe (FieldName, IrrefutablePattern pv)]
                               -- Note: `Nothing' will be desugared to `Just' in TypeCheck / zilinc
                           deriving (Show, Functor, Foldable, Traversable, Eq)

data Pattern pv = PCon TagName [IrrefutablePattern pv]
                | PIntLit Integer
                | PBoolLit Bool
                | PCharLit Char
                | PIrrefutable (IrrefutablePattern pv)
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

numOfArgs (PT x _) = length x

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
data LocType = LocType { posOfT :: SourcePos, typeOfLT' :: Type LocType }
             | Documentation String LocType deriving (Show)

typeOfLT (LocType _ t) = t
typeOfLT (Documentation s t) = typeOfLT t

data RawType = RT { unRT :: Type RawType } deriving (Show, Eq)
data RawExpr = RE { unRE :: Expr RawType VarName RawExpr } deriving Show
instance Foldable (Flip Alt e) where
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip (Expr t) e) where
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip (Binding t) e) where
  foldMap f a = getConst $ traverse (Const . f) a
instance Traversable (Flip Alt e) where
  traverse f (Flip (Alt p b e)) = Flip <$> (Alt <$> traverse f p <*> pure b <*> pure e)
instance Traversable (Flip (Binding t) e) where
  traverse f (Flip (Binding p mt e vs)) = Flip <$> (Binding <$> traverse f p <*> pure mt <*> pure e <*> pure vs)
instance Traversable (Flip (Expr t) e) where
  traverse f (Flip (Match e v alt))     = Flip <$> (Match e v <$> traverse (ttraverse f) alt)
  traverse f (Flip (Let bs e))          = Flip <$> (Let  <$> (traverse (ttraverse f) bs) <*> pure e)
  traverse _ (Flip (Member e f))        = pure $ Flip (Member e f)
  traverse _ (Flip (PrimOp op e))       = pure $ Flip (PrimOp op e)
  traverse _ (Flip (Var v))             = pure $ Flip (Var v)
  traverse _ (Flip (TypeApp v ts nt))   = pure $ Flip (TypeApp v ts nt)
  traverse _ (Flip (Seq e e'))          = pure $ Flip (Seq e e')
  traverse _ (Flip (If c vs e e'))      = pure $ Flip (If c vs e e')
  traverse _ (Flip (App e e'))          = pure $ Flip (App e e')
  traverse _ (Flip (Con n e))           = pure $ Flip (Con n e)
  traverse _ (Flip Unitel)              = pure $ Flip Unitel
  traverse _ (Flip (IntLit l))          = pure $ Flip (IntLit l)
  traverse _ (Flip (BoolLit l))         = pure $ Flip (BoolLit l)
  traverse _ (Flip (CharLit l))         = pure $ Flip (CharLit l)
  traverse _ (Flip (StringLit l))       = pure $ Flip (StringLit l)
  traverse _ (Flip (Tuple es))          = pure $ Flip (Tuple es)
  traverse _ (Flip (UnboxedRecord es))  = pure $ Flip (UnboxedRecord es)
  traverse _ (Flip (Put e es))          = pure $ Flip (Put e es)
  traverse _ (Flip (Upcast e))          = pure $ Flip (Upcast e)
  traverse _ (Flip (Widen e))           = pure $ Flip (Widen e)
instance Functor (Flip (Binding t) e) where
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip Alt e) where
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip (Expr t) e) where
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip2 Binding p e) where
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Foldable (Flip2 Binding p e) where
  foldMap f a = getConst $ traverse (Const . f) a
instance Traversable (Flip2 Binding p e) where
  traverse f (Flip2 (Binding p mt e vs)) = Flip2 <$> (Binding p <$> traverse f mt <*> pure e <*> pure vs)
instance Foldable (Flip2 Expr p e) where
  foldMap f a = getConst $ traverse (Const . f) a
instance Functor (Flip2 Expr p e) where
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Traversable (Flip2 Expr p e) where
  traverse f (Flip2 (Let bs e))         = Flip2 <$> (Let <$> traverse (tttraverse f) bs <*> pure e)
  traverse f (Flip2 (TypeApp v ts nt))  = Flip2 <$> (TypeApp v <$> traverse f ts <*> pure nt)
  traverse _ (Flip2 (Match e v alt))    = pure $ Flip2 (Match e v alt)
  traverse _ (Flip2 (PrimOp op e))      = pure $ Flip2 (PrimOp op e)
  traverse _ (Flip2 (Var v))            = pure $ Flip2 (Var v)
  traverse _ (Flip2 (Seq e e'))         = pure $ Flip2 (Seq e e')
  traverse _ (Flip2 (If c vs e e'))     = pure $ Flip2 (If c vs e e')
  traverse _ (Flip2 (App e e'))         = pure $ Flip2 (App e e')
  traverse _ (Flip2 (Member e f))       = pure $ Flip2 (Member e f)
  traverse _ (Flip2 (Con n e))          = pure $ Flip2 (Con n e)
  traverse _ (Flip2 Unitel)             = pure $ Flip2 Unitel
  traverse _ (Flip2 (IntLit l))         = pure $ Flip2 (IntLit l)
  traverse _ (Flip2 (BoolLit l))        = pure $ Flip2 (BoolLit l)
  traverse _ (Flip2 (CharLit l))        = pure $ Flip2 (CharLit l)
  traverse _ (Flip2 (StringLit l))      = pure $ Flip2 (StringLit l)
  traverse _ (Flip2 (Tuple es))         = pure $ Flip2 (Tuple es)
  traverse _ (Flip2 (UnboxedRecord es)) = pure $ Flip2 (UnboxedRecord es)
  traverse _ (Flip2 (Put e es))         = pure $ Flip2 (Put e es)
  traverse _ (Flip2 (Widen e))          = pure $ Flip2 (Widen e)
  traverse _ (Flip2 (Upcast e))         = pure $ Flip2 (Upcast e)
instance Functor (Flip (TopLevel t) e) where
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Foldable (Flip (TopLevel t) e) where
  foldMap f a = getConst $ traverse (Const . f) a
instance Traversable (Flip (TopLevel t) e) where
  traverse f (Flip (FunDef v pt alts))  = Flip <$> (FunDef v pt <$> traverse (ttraverse f) alts)
  traverse _ (Flip (Include s))         = pure $ Flip (Include s)
  traverse _ (Flip (TypeDec n vs t))    = pure $ Flip (TypeDec n vs t)
  traverse _ (Flip (AbsTypeDec n vs))   = pure $ Flip (AbsTypeDec n vs)
  traverse _ (Flip (AbsDec v pt))       = pure $ Flip (AbsDec v pt)
  traverse _ (Flip (ConstDef v t e))    = pure $ Flip (ConstDef v t e)
instance Functor (Flip2 TopLevel p e) where
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Foldable (Flip2 TopLevel p e) where
  foldMap f a = getConst $ traverse (Const . f) a
instance Traversable (Flip2 TopLevel p e) where
  traverse f (Flip2 (FunDef v pt alts)) = Flip2 <$> (FunDef   v <$> traverse f pt <*> pure alts)
  traverse f (Flip2 (AbsDec v pt))      = Flip2 <$> (AbsDec   v <$> traverse f pt)
  traverse f (Flip2 (ConstDef v t e))   = Flip2 <$> (ConstDef v <$> f t <*> pure e)
  traverse f (Flip2 (TypeDec n vs t))   = Flip2 <$> (TypeDec  n vs <$> f t)
  traverse _ (Flip2 (Include s))        = pure $ Flip2 (Include s)
  traverse _ (Flip2 (AbsTypeDec n vs))  = pure $ Flip2 (AbsTypeDec n vs)

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

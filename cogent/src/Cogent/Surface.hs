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

type DocString = String

data IrrefutablePattern pv ip = PVar pv
                              | PTuple [ip]
                              | PUnboxedRecord [Maybe (FieldName, ip)]
                              | PUnderscore
                              | PUnitel
                              | PTake pv [Maybe (FieldName, ip)]
                                  -- Note: `Nothing' will be desugared to `Just' in TypeCheck / zilinc
                              deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Pattern ip = PCon TagName [ip]
                | PIntLit Integer
                | PBoolLit Bool
                | PCharLit Char
                | PIrrefutable ip
                deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Alt p e = Alt p Likelihood e deriving (Eq, Ord, Show, Functor, Foldable,Traversable)

data Binding t ip e = Binding ip (Maybe t) e [VarName]
                    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Inline = Inline
            | NoInline
            deriving (Eq, Ord, Show)

data Expr t p ip e = PrimOp OpName [e]
                   | Var VarName
                   | Match e [VarName] [Alt p e]
                   | TypeApp FunName [Maybe t] Inline
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
                   | Let [Binding t ip e] e
                   | Upcast e
--                   | Widen  e
                   | Put e [Maybe (FieldName, e)]  -- Note: `Nothing' will be desugared to `Just' in TypeCheck / zilinc
                   deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type Banged = Bool
type Taken  = Bool

data Type t =
            -- They are in WHNF
              TCon TypeName [t] Sigil
            | TVar VarName Banged
            | TFun t t
            | TRecord [(FieldName, (t, Taken))] Sigil
            | TVariant (M.Map TagName ([t], Taken))
            | TTuple [t]
            | TUnit
            -- They will be eliminated at some point / zilinc
            | TUnbox   t
            | TBang    t
            -- Used for both field names in records and tag names in variants
            | TTake (Maybe [FieldName]) t
            | TPut  (Maybe [FieldName]) t
            deriving (Show, Functor, Eq, Foldable, Traversable, Ord)

data Polytype t = PT [(TyVarName, Kind)] t deriving (Eq, Show, Functor, Foldable, Traversable, Ord)

numOfArgs (PT x _) = length x

data TopLevel t p e = Include    String
                    | IncludeStd String
                    | DocBlock   String
                    | AbsTypeDec TypeName [TyVarName]
                    | TypeDec    TypeName [TyVarName] t
                    | AbsDec VarName (Polytype t)
                    | FunDef VarName (Polytype t) [Alt p e]
                    | ConstDef VarName t e
                    deriving (Eq, Show, Functor, Foldable, Traversable)

absFnDeclId :: String -> TopLevel t p e -> Bool
absFnDeclId x (AbsDec fn _) = x == fn
absFnDeclId _ _ = False

absTyDeclId :: String -> TopLevel t p e -> Bool
absTyDeclId x (AbsTypeDec tn _) = x == tn
absTyDeclId _ _ = False


data LocExpr = LocExpr { posOfE :: SourcePos, exprOfLE :: Expr LocType LocPatn LocIrrefPatn LocExpr } deriving (Eq, Show)
data LocPatn = LocPatn { posOfP :: SourcePos, patnOfLP :: Pattern LocIrrefPatn } deriving (Eq, Show)
data LocIrrefPatn = LocIrrefPatn { posOfIP :: SourcePos, irpatnOfLIP :: IrrefutablePattern VarName LocIrrefPatn } deriving (Eq, Show)
data LocType = LocType { posOfT :: SourcePos, typeOfLT' :: Type LocType }
             | Documentation String LocType deriving (Eq, Show)

typeOfLT (LocType _ t) = t
typeOfLT (Documentation s t) = typeOfLT t

data RawType = RT { unRT :: Type RawType } deriving (Eq, Ord, Show)
data RawExpr = RE { unRE :: Expr RawType RawPatn RawIrrefPatn RawExpr } deriving (Eq, Ord, Show)
data RawPatn = RP { unRP :: Pattern RawIrrefPatn } deriving (Eq, Ord, Show)
data RawIrrefPatn = RIP { unRIP :: IrrefutablePattern VarName RawIrrefPatn } deriving (Eq, Ord, Show)

instance Foldable (Flip Alt e) where
  foldMap f a = getConst $ traverse (Const . f) a

instance Foldable (Flip (Binding t) e) where  -- ip
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip2 Binding e ip) where  -- t
  foldMap f a = getConst $ traverse (Const . f) a

instance Foldable (Flip (Expr t p) e) where  -- ip
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip2 (Expr t) e ip) where  -- p
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip3 Expr e ip p) where  -- t
  foldMap f a = getConst $ traverse (Const . f) a

instance Foldable (Flip IrrefutablePattern pv) where  -- ip
  foldMap f a = getConst $ traverse (Const . f) a

instance Foldable (Flip (TopLevel t) e) where
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip2 TopLevel p e) where
  foldMap f a = getConst $ traverse (Const . f) a

instance Traversable (Flip Alt e) where  -- p
  traverse f (Flip (Alt p b e)) = Flip <$> (Alt <$> f p <*> pure b <*> pure e)

instance Traversable (Flip (Binding t) e) where  -- ip
  traverse f (Flip (Binding p mt e vs)) = Flip <$> (Binding <$> f p <*> pure mt <*> pure e <*> pure vs)
instance Traversable (Flip2 Binding e ip) where  -- t
  traverse f (Flip2 (Binding p mt e vs)) = Flip2 <$> (Binding p <$> traverse f mt <*> pure e <*> pure vs)

instance Traversable (Flip (Expr t p) e) where  -- ip
  traverse f (Flip (Let bs e))          = Flip <$> (Let <$> (traverse (ttraverse f) bs) <*> pure e)
  traverse _ (Flip (Member e f))        = pure $ Flip (Member e f)
  traverse _ (Flip (PrimOp op e))       = pure $ Flip (PrimOp op e)
  traverse _ (Flip (Var v))             = pure $ Flip (Var v)
  traverse _ (Flip (Match e v alt))     = pure $ Flip (Match e v alt)
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
  -- traverse _ (Flip (Widen e))           = pure $ Flip (Widen e)
instance Traversable (Flip2 (Expr t) e ip) where  -- p
  traverse f (Flip2 (Match e v alt))    = Flip2 <$> (Match e v <$> traverse (ttraverse f) alt)
  traverse _ (Flip2 (PrimOp op e))      = pure $ Flip2 (PrimOp op e)
  traverse _ (Flip2 (Var v))            = pure $ Flip2 (Var v)
  traverse _ (Flip2 (TypeApp v ts nt))  = pure $ Flip2 (TypeApp v ts nt)
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
  traverse _ (Flip2 (Let bs e))         = pure $ Flip2 (Let bs e)
  traverse _ (Flip2 (Upcast e))         = pure $ Flip2 (Upcast e)
  --traverse _ (Flip2 (Widen e))          = pure $ Flip2 (Widen e)
instance Traversable (Flip3 Expr e ip p) where  -- t
  traverse f (Flip3 (Let bs e))          = Flip3 <$> (Let <$> (traverse (tttraverse f) bs) <*> pure e)
  traverse f (Flip3 (TypeApp v ts nt))   = Flip3 <$> (TypeApp v <$> traverse (traverse f) ts <*> pure nt)
  traverse _ (Flip3 (Match e v alt))     = pure $ Flip3 (Match e v alt)
  traverse _ (Flip3 (Member e f))        = pure $ Flip3 (Member e f)
  traverse _ (Flip3 (PrimOp op e))       = pure $ Flip3 (PrimOp op e)
  traverse _ (Flip3 (Var v))             = pure $ Flip3 (Var v)
  traverse _ (Flip3 (Seq e e'))          = pure $ Flip3 (Seq e e')
  traverse _ (Flip3 (If c vs e e'))      = pure $ Flip3 (If c vs e e')
  traverse _ (Flip3 (App e e'))          = pure $ Flip3 (App e e')
  traverse _ (Flip3 (Con n e))           = pure $ Flip3 (Con n e)
  traverse _ (Flip3 Unitel)              = pure $ Flip3 Unitel
  traverse _ (Flip3 (IntLit l))          = pure $ Flip3 (IntLit l)
  traverse _ (Flip3 (BoolLit l))         = pure $ Flip3 (BoolLit l)
  traverse _ (Flip3 (CharLit l))         = pure $ Flip3 (CharLit l)
  traverse _ (Flip3 (StringLit l))       = pure $ Flip3 (StringLit l)
  traverse _ (Flip3 (Tuple es))          = pure $ Flip3 (Tuple es)
  traverse _ (Flip3 (UnboxedRecord es))  = pure $ Flip3 (UnboxedRecord es)
  traverse _ (Flip3 (Put e es))          = pure $ Flip3 (Put e es)
  traverse _ (Flip3 (Upcast e))          = pure $ Flip3 (Upcast e)
  -- traverse _ (Flip3 (Widen e))           = pure $ Flip3 (Widen e)

instance Traversable (Flip IrrefutablePattern pv) where  -- ip
  traverse f (Flip (PVar pv))            = Flip <$> (PVar <$> f pv)
  traverse _ (Flip (PTuple ips))         = pure $ Flip (PTuple ips)
  traverse _ (Flip (PUnboxedRecord mfs)) = pure $ Flip (PUnboxedRecord mfs)
  traverse _ (Flip PUnderscore)          = pure $ Flip PUnderscore
  traverse _ (Flip PUnitel)              = pure $ Flip PUnitel
  traverse f (Flip (PTake pv mfs))       = Flip <$> (PTake <$> f pv <*> pure mfs)

instance Traversable (Flip (TopLevel t) e) where  -- p
  traverse _ (Flip (Include s))         = pure $ Flip (Include s)
  traverse _ (Flip (IncludeStd s))      = pure $ Flip (IncludeStd s)
  traverse _ (Flip (DocBlock s))        = pure $ Flip (DocBlock s)
  traverse _ (Flip (AbsTypeDec n vs))   = pure $ Flip (AbsTypeDec n vs)
  traverse _ (Flip (TypeDec n vs t))    = pure $ Flip (TypeDec n vs t)
  traverse _ (Flip (AbsDec v pt))       = pure $ Flip (AbsDec v pt)
  traverse f (Flip (FunDef v pt alts))  = Flip <$> (FunDef v pt <$> traverse (ttraverse f) alts)
  traverse _ (Flip (ConstDef v t e))    = pure $ Flip (ConstDef v t e)
instance Traversable (Flip2 TopLevel e p) where  -- t
  traverse _ (Flip2 (Include s))        = pure $ Flip2 (Include s)
  traverse _ (Flip2 (IncludeStd s))     = pure $ Flip2 (IncludeStd s)
  traverse _ (Flip2 (DocBlock s))       = pure $ Flip2 (DocBlock s)
  traverse _ (Flip2 (AbsTypeDec n vs))  = pure $ Flip2 (AbsTypeDec n vs)
  traverse f (Flip2 (TypeDec n vs t))   = Flip2 <$> (TypeDec  n vs <$> f t)
  traverse f (Flip2 (AbsDec v pt))      = Flip2 <$> (AbsDec   v <$> traverse f pt)
  traverse f (Flip2 (FunDef v pt alts)) = Flip2 <$> (FunDef   v <$> traverse f pt <*> pure alts)
  traverse f (Flip2 (ConstDef v t e))   = Flip2 <$> (ConstDef v <$> f t <*> pure e)

instance Functor (Flip (Binding t) e) where  -- ip
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip2 Binding e ip) where  -- t
  fmap f x = runIdentity (traverse (Identity . f) x)

instance Functor (Flip Alt e) where  -- p
  fmap f x = runIdentity (traverse (Identity . f) x)

instance Functor (Flip (Expr t p) e) where
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip2 (Expr t) e ip) where
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip3 Expr e ip p) where
  fmap f x = runIdentity (traverse (Identity . f) x)

instance Functor (Flip IrrefutablePattern ip) where  -- pv
  fmap f x = runIdentity (traverse (Identity . f) x)

instance Functor (Flip (TopLevel t) e) where
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip2 TopLevel e p) where
  fmap f x = runIdentity (traverse (Identity . f) x)


stripLocT :: LocType -> RawType
stripLocT = RT . fmap stripLocT . typeOfLT

stripLocP :: LocPatn -> RawPatn
stripLocP = RP . fmap stripLocIP . patnOfLP

stripLocIP :: LocIrrefPatn -> RawIrrefPatn
stripLocIP = RIP . fmap stripLocIP . irpatnOfLIP

stripLocE :: LocExpr -> RawExpr
stripLocE = RE . ffffmap stripLocT . fffmap stripLocP . ffmap stripLocIP . fmap stripLocE . exprOfLE

noPos :: SourcePos
noPos = newPos "unknown" 0 0

dummyLocT :: RawType -> LocType
dummyLocT = LocType noPos . fmap dummyLocT . unRT

dummyLocP :: RawPatn -> LocPatn
dummyLocP = LocPatn noPos . fmap dummyLocIP . unRP

dummyLocIP :: RawIrrefPatn -> LocIrrefPatn
dummyLocIP = LocIrrefPatn noPos . fmap dummyLocIP . unRIP

dummyLocE :: RawExpr -> LocExpr
dummyLocE = LocExpr noPos . ffffmap dummyLocT . fffmap dummyLocP . ffmap dummyLocIP . fmap dummyLocE . unRE

stripAllLoc :: TopLevel LocType LocPatn LocExpr -> TopLevel RawType RawPatn RawExpr
stripAllLoc = fffmap stripLocT . ffmap stripLocP . fmap stripLocE

isIntType :: RawType -> Bool
isIntType (RT (TCon cn ts s)) | cn `elem` words "U8 U16 U32 U64", null ts, s == Unboxed = True
isIntType _ = False

isVariantType :: RawType -> Bool
isVariantType (RT (TVariant _)) = True
isVariantType _ = False

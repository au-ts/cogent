--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor, FlexibleInstances, TupleSections, DeriveFoldable, DeriveTraversable #-}

module Cogent.Surface
  ( module Cogent.Surface
  , module Cogent.Dargent.Surface
  ) where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Util

import Control.Applicative
import Control.Arrow (first)
import Data.Data
import Data.Functor.Compose
import Data.Functor.Identity
#if __GLASGOW_HASKELL__ < 709
import Data.Foldable hiding (elem)
import Data.Traversable
#endif
import Data.IntMap as IM (IntMap)
import qualified Data.Map as M
import Text.Parsec.Pos

import Cogent.Dargent.Surface

type DocString = String

type AExpr = RawExpr  -- the expression type for statically-known array indices

data IrrefutablePattern pv ip e = PVar pv
                                | PTuple [ip]
                                | PUnboxedRecord [Maybe (FieldName, ip)]
                                | PUnderscore
                                | PUnitel
                                | PTake pv [Maybe (FieldName, ip)]
                                    -- ^^^ Note: `Nothing' will be desugared to `Just' in TypeCheck / zilinc
#ifdef BUILTIN_ARRAYS
                                | PArray [ip]
                                | PArrayTake pv [(e, ip)]
#endif
                                deriving (Data, Eq, Ord, Show, Functor, Foldable, Traversable)

data Pattern ip = PCon TagName [ip]
                | PIntLit Integer
                | PBoolLit Bool
                | PCharLit Char
                | PIrrefutable ip
                deriving (Data, Eq, Ord, Show, Functor, Foldable, Traversable)

data Alt p e = Alt p Likelihood e deriving (Data, Eq, Ord, Show, Functor, Foldable,Traversable)

data Binding t p ip e = Binding ip (Maybe t) e [VarName]
                      | BindingAlts p (Maybe t) e [VarName] [Alt p e]
                      deriving (Data, Eq, Ord, Show, Functor, Foldable, Traversable)

data Inline = Inline
            | NoInline
            deriving (Data, Eq, Ord, Show)

data Expr t p ip e = PrimOp OpName [e]
                   | Var VarName
                   | Match e [VarName] [Alt p e]
                   | TypeApp FunName [Maybe t] Inline
                   | Con TagName [e]
                   | Seq e e
                   | Lam ip (Maybe t) e
                   | App e e Bool   -- True for infix App
                   | Comp e e
                   | LamC ip (Maybe t) e [VarName]  -- closure lambda
                   | AppC e e             -- closure application
                   | If e [VarName] e e
                   | MultiWayIf [(e, [VarName], Likelihood, e)] e
                     -- ^ (condition, !-ed vars, likelihood, body)
                   | Member e FieldName
                   | Unitel
                   | IntLit Integer
                   | BoolLit Bool
                   | CharLit Char
                   | StringLit String
#ifdef BUILTIN_ARRAYS
                   | ArrayLit [e]
                   | ArrayIndex e e
                   | ArrayMap2 ((ip, ip), e) (e, e)
                   | ArrayPut e [(e, e)]
#endif
                   | Tuple [e]  -- When desugared into tuples, it's right associative.
                   | UnboxedRecord [(FieldName, e)]
                   | Let [Binding t p ip e] e
                   | Put e [Maybe (FieldName, e)]  -- Note: `Nothing' will be desugared to `Just' in TypeCheck / zilinc
                   | Upcast e
                   | Annot e t
                   deriving (Data, Eq, Ord, Show, Functor, Foldable, Traversable)

type Banged = Bool
type Taken  = Bool

type Entry t = (FieldName, (t, Taken))

data Type e t =
              -- They are in WHNF
                TCon TypeName [t] (Sigil (Maybe DataLayoutExpr))  -- FIXME: can polymorphise the `Representation`
              | TVar VarName Banged
              | TFun t t
              | TRecord [(FieldName, (t, Taken))] (Sigil (Maybe DataLayoutExpr))
              | TVariant (M.Map TagName ([t], Taken))
              | TTuple [t]
              | TUnit
#ifdef BUILTIN_ARRAYS
              | TArray t e (Sigil (Maybe DataLayoutExpr)) [(e, Taken)]
                                                     -- \ ^^^ a list of taken/put indices
              -- The TATake and TAPut type-operators will be normalised away.
              | TATake [e] t
              | TAPut  [e] t
#endif
              -- In TypeCheck.Post, the TUnbox and TBang type-operators
              -- are normalised out of the syntax tree by altering the Sigil
              -- of the type they act on / zilinc, mdimeglio
              | TUnbox   t
              | TBang    t
              -- Used for both field names in records and tag names in variants
              | TTake (Maybe [FieldName]) t
              | TPut  (Maybe [FieldName]) t
              | TLayout DataLayoutExpr t
              deriving (Show, Functor, Data, Eq, Foldable, Traversable, Ord)

data Polytype t = PT [(TyVarName, Kind)] t deriving (Data, Eq, Show, Functor, Foldable, Traversable, Ord)

numOfArgs (PT x _) = length x

data TopLevel t p e = Include    String
                    | IncludeStd String
                    | DocBlock   String
                    | AbsTypeDec TypeName [TyVarName] [t]
                    | TypeDec    TypeName [TyVarName] t
                    | AbsDec     FunName (Polytype t)
                    | FunDef     FunName (Polytype t) [Alt p e]
                    | ConstDef   ConstName t e
                    | RepDef DataLayoutDecl
                    deriving (Data, Eq, Show, Functor, Foldable, Traversable)

absFnDeclId :: String -> TopLevel t p e -> Bool
absFnDeclId x (AbsDec fn _) = x == fn
absFnDeclId _ _ = False

absTyDeclId :: String -> TopLevel t p e -> Bool
absTyDeclId x (AbsTypeDec tn _ _) = x == tn
absTyDeclId _ _ = False


data LocExpr = LocExpr { posOfE :: SourcePos, exprOfLE :: Expr LocType LocPatn LocIrrefPatn LocExpr }
             deriving (Data, Eq, Show)
data LocPatn = LocPatn { posOfP :: SourcePos, patnOfLP :: Pattern LocIrrefPatn }
             deriving (Data, Eq, Show)
data LocIrrefPatn = LocIrrefPatn { posOfIP :: SourcePos, irpatnOfLIP :: IrrefutablePattern VarName LocIrrefPatn LocExpr }
                  deriving (Data, Eq, Show)
data LocType = LocType { posOfT :: SourcePos, typeOfLT' :: Type LocExpr LocType }
             | Documentation String LocType
             deriving (Data, Eq, Show)

typeOfLT (LocType _ t) = t
typeOfLT (Documentation s t) = typeOfLT t

posOfLT (LocType p _) = p
posOfLT (Documentation _ t) = posOfLT t

data RawType = RT { unRT :: Type RawExpr RawType } deriving (Data, Eq, Ord, Show)
data RawExpr = RE { unRE :: Expr RawType RawPatn RawIrrefPatn RawExpr } deriving (Data, Eq, Ord, Show)
data RawPatn = RP { unRP :: Pattern RawIrrefPatn } deriving (Data, Eq, Ord, Show)
data RawIrrefPatn = RIP { unRIP :: IrrefutablePattern VarName RawIrrefPatn RawExpr } deriving (Data, Eq, Ord, Show)

-- -----------------------------------------------------------------------------

instance Foldable (Flip Alt e) where
  foldMap f a = getConst $ traverse (Const . f) a

instance Foldable (Flip (Binding t p) e) where  -- ip
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip2 (Binding t) e ip) where  -- p
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip3 Binding e ip p) where  -- t
  foldMap f a = getConst $ traverse (Const . f) a

instance Foldable (Flip (Expr t p) e) where  -- ip
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip2 (Expr t) e ip) where  -- p
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip3 Expr e ip p) where  -- t
  foldMap f a = getConst $ traverse (Const . f) a

instance Foldable (Flip (IrrefutablePattern pv) e) where  -- ip
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip2 IrrefutablePattern e ip) where  -- pv
  foldMap f a = getConst $ traverse (Const . f) a


instance Foldable (Flip Type t) where  -- e
  foldMap f a = getConst $ traverse (Const . f) a

instance Foldable (Flip (TopLevel t) e) where
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip2 TopLevel p e) where
  foldMap f a = getConst $ traverse (Const . f) a

instance Traversable (Flip Alt e) where  -- p
  traverse f (Flip (Alt p b e)) = Flip <$> (Alt <$> f p <*> pure b <*> pure e)

instance Traversable (Flip (Binding t p) e) where  -- ip
  traverse f (Flip (Binding ip mt e vs)) = Flip <$> (Binding <$> f ip <*> pure mt <*> pure e <*> pure vs)
  traverse f (Flip (BindingAlts p mt e vs alts)) = pure $ Flip (BindingAlts p mt e vs alts)
instance Traversable (Flip2 (Binding t) e ip) where  -- p
  traverse f (Flip2 (Binding ip mt e vs)) = pure $ Flip2 (Binding ip mt e vs)
  traverse f (Flip2 (BindingAlts p mt e vs alts)) = Flip2 <$> (BindingAlts <$> f p <*> pure mt <*> pure e <*> pure vs <*> traverse (ttraverse f) alts)
instance Traversable (Flip3 Binding e ip p) where  -- t
  traverse f (Flip3 (Binding ip mt e vs)) = Flip3 <$> (Binding ip <$> traverse f mt <*> pure e <*> pure vs)
  traverse f (Flip3 (BindingAlts p mt e vs alts)) = Flip3 <$> (BindingAlts p <$> traverse f mt <*> pure e <*> pure vs <*> pure alts)

instance Traversable (Flip (Expr t p) e) where  -- ip
  traverse _ (Flip (PrimOp op e))       = pure $ Flip (PrimOp op e)
  traverse _ (Flip (Var v))             = pure $ Flip (Var v)
  traverse _ (Flip (Match e v alt))     = pure $ Flip (Match e v alt)
  traverse _ (Flip (TypeApp v ts nt))   = pure $ Flip (TypeApp v ts nt)
  traverse _ (Flip (Con n e))           = pure $ Flip (Con n e)
  traverse _ (Flip (Seq e e'))          = pure $ Flip (Seq e e')
  traverse f (Flip (Lam  ip mt e))      = Flip <$> (Lam  <$> f ip <*> pure mt <*> pure e)
  traverse f (Flip (LamC ip mt e vs))   = Flip <$> (LamC <$> f ip <*> pure mt <*> pure e <*> pure vs)
  traverse _ (Flip (App  e e' i))       = pure $ Flip (App  e e' i)
  traverse _ (Flip (Comp f g))          = pure $ Flip (Comp f g)
  traverse _ (Flip (AppC e e'))         = pure $ Flip (AppC e e')
  traverse _ (Flip (If c vs e e'))      = pure $ Flip (If c vs e e')
  traverse _ (Flip (MultiWayIf es el))  = pure $ Flip (MultiWayIf es el)
  traverse _ (Flip (Member e f))        = pure $ Flip (Member e f)
  traverse _ (Flip Unitel)              = pure $ Flip Unitel
  traverse _ (Flip (IntLit l))          = pure $ Flip (IntLit l)
  traverse _ (Flip (BoolLit l))         = pure $ Flip (BoolLit l)
  traverse _ (Flip (CharLit l))         = pure $ Flip (CharLit l)
  traverse _ (Flip (StringLit l))       = pure $ Flip (StringLit l)
#ifdef BUILTIN_ARRAYS
  traverse _ (Flip (ArrayLit es))       = pure $ Flip (ArrayLit es)
  traverse _ (Flip (ArrayIndex e i))    = pure $ Flip (ArrayIndex e i)
  traverse f (Flip (ArrayMap2 m es))    = Flip <$> (ArrayMap2 <$> firstM (bothM f) m <*> pure es)
  traverse _ (Flip (ArrayPut e es))     = pure $ Flip (ArrayPut e es)
#endif
  traverse _ (Flip (Tuple es))          = pure $ Flip (Tuple es)
  traverse _ (Flip (UnboxedRecord es))  = pure $ Flip (UnboxedRecord es)
  traverse f (Flip (Let bs e))          = Flip <$> (Let <$> (traverse (ttraverse f) bs) <*> pure e)
  traverse _ (Flip (Put e es))          = pure $ Flip (Put e es)
  traverse _ (Flip (Upcast e))          = pure $ Flip (Upcast e)
  traverse _ (Flip (Annot e t))         = pure $ Flip (Annot e t)
instance Traversable (Flip2 (Expr t) e ip) where  -- p
  traverse _ (Flip2 (PrimOp op e))      = pure $ Flip2 (PrimOp op e)
  traverse _ (Flip2 (Var v))            = pure $ Flip2 (Var v)
  traverse f (Flip2 (Match e v alt))    = Flip2 <$> (Match e v <$> traverse (ttraverse f) alt)
  traverse _ (Flip2 (TypeApp v ts nt))  = pure $ Flip2 (TypeApp v ts nt)
  traverse _ (Flip2 (Con n e))          = pure $ Flip2 (Con n e)
  traverse _ (Flip2 (Seq e e'))         = pure $ Flip2 (Seq e e')
  traverse _ (Flip2 (Lam  ip mt e))     = pure $ Flip2 (Lam  ip mt e)
  traverse _ (Flip2 (LamC ip mt e vs))  = pure $ Flip2 (LamC ip mt e vs)
  traverse _ (Flip2 (App  e e' i))      = pure $ Flip2 (App  e e' i)
  traverse _ (Flip2 (Comp f g))         = pure $ Flip2 (Comp f g)
  traverse _ (Flip2 (AppC e e'))        = pure $ Flip2 (AppC e e')
  traverse _ (Flip2 (If c vs e e'))     = pure $ Flip2 (If c vs e e')
  traverse _ (Flip2 (MultiWayIf es el)) = pure $ Flip2 (MultiWayIf es el)
  traverse _ (Flip2 (Member e f))       = pure $ Flip2 (Member e f)
  traverse _ (Flip2 Unitel)             = pure $ Flip2 Unitel
  traverse _ (Flip2 (IntLit l))         = pure $ Flip2 (IntLit l)
  traverse _ (Flip2 (BoolLit l))        = pure $ Flip2 (BoolLit l)
  traverse _ (Flip2 (CharLit l))        = pure $ Flip2 (CharLit l)
  traverse _ (Flip2 (StringLit l))      = pure $ Flip2 (StringLit l)
#ifdef BUILTIN_ARRAYS
  traverse _ (Flip2 (ArrayLit es))      = pure $ Flip2 (ArrayLit es)
  traverse _ (Flip2 (ArrayIndex e i))   = pure $ Flip2 (ArrayIndex e i)
  traverse _ (Flip2 (ArrayMap2 f es))   = pure $ Flip2 (ArrayMap2 f es)
  traverse _ (Flip2 (ArrayPut e es))    = pure $ Flip2 (ArrayPut e es)
#endif
  traverse _ (Flip2 (Tuple es))         = pure $ Flip2 (Tuple es)
  traverse _ (Flip2 (UnboxedRecord es)) = pure $ Flip2 (UnboxedRecord es)
  traverse f (Flip2 (Let bs e))         = Flip2 <$> (Let <$> traverse (tttraverse f) bs <*> pure e)
  traverse _ (Flip2 (Put e es))         = pure $ Flip2 (Put e es)
  traverse _ (Flip2 (Upcast e))         = pure $ Flip2 (Upcast e)
  traverse _ (Flip2 (Annot e t))        = pure $ Flip2 (Annot e t)
instance Traversable (Flip3 Expr e ip p) where  -- t
  traverse _ (Flip3 (PrimOp op e))       = pure $ Flip3 (PrimOp op e)
  traverse _ (Flip3 (Var v))             = pure $ Flip3 (Var v)
  traverse _ (Flip3 (Match e v alt))     = pure $ Flip3 (Match e v alt)
  traverse f (Flip3 (TypeApp v ts nt))   = Flip3 <$> (TypeApp v <$> traverse (traverse f) ts <*> pure nt)
  traverse _ (Flip3 (Con n e))           = pure $ Flip3 (Con n e)
  traverse _ (Flip3 (Seq e e'))          = pure $ Flip3 (Seq e e')
  traverse f (Flip3 (Lam  ip mt e))      = Flip3 <$> (Lam  ip <$> traverse f mt <*> pure e)
  traverse f (Flip3 (LamC ip mt e vs))   = Flip3 <$> (LamC ip <$> traverse f mt <*> pure e <*> pure vs)
  traverse _ (Flip3 (App  e e' i))       = pure $ Flip3 (App  e e' i)
  traverse _ (Flip3 (Comp f g))          = pure $ Flip3 (Comp f g)
  traverse _ (Flip3 (AppC e e'))         = pure $ Flip3 (AppC e e')
  traverse _ (Flip3 (If c vs e e'))      = pure $ Flip3 (If c vs e e')
  traverse _ (Flip3 (MultiWayIf es el))  = pure $ Flip3 (MultiWayIf es el)
  traverse _ (Flip3 (Member e f))        = pure $ Flip3 (Member e f)
  traverse _ (Flip3 Unitel)              = pure $ Flip3 Unitel
  traverse _ (Flip3 (IntLit l))          = pure $ Flip3 (IntLit l)
  traverse _ (Flip3 (BoolLit l))         = pure $ Flip3 (BoolLit l)
  traverse _ (Flip3 (CharLit l))         = pure $ Flip3 (CharLit l)
  traverse _ (Flip3 (StringLit l))       = pure $ Flip3 (StringLit l)
#ifdef BUILTIN_ARRAYS
  traverse _ (Flip3 (ArrayLit es))       = pure $ Flip3 (ArrayLit es)
  traverse _ (Flip3 (ArrayIndex e i))    = pure $ Flip3 (ArrayIndex e i)
  traverse _ (Flip3 (ArrayMap2 f es))    = pure $ Flip3 (ArrayMap2 f es) 
  traverse _ (Flip3 (ArrayPut e es))     = pure $ Flip3 (ArrayPut e es)
#endif
  traverse _ (Flip3 (Tuple es))          = pure $ Flip3 (Tuple es)
  traverse _ (Flip3 (UnboxedRecord es))  = pure $ Flip3 (UnboxedRecord es)
  traverse f (Flip3 (Let bs e))          = Flip3 <$> (Let <$> (traverse (ttttraverse f) bs) <*> pure e)
  traverse _ (Flip3 (Put e es))          = pure $ Flip3 (Put e es)
  traverse _ (Flip3 (Upcast e))          = pure $ Flip3 (Upcast e)
  traverse f (Flip3 (Annot e t))         = Flip3 <$> (Annot <$> pure e <*> f t)

instance Traversable (Flip (IrrefutablePattern pv) e) where  -- ip
  traverse f (Flip (PVar pv))             = pure $ Flip (PVar pv)
  traverse f (Flip (PTuple ips))          = Flip <$> (PTuple <$> traverse f ips)
  traverse f (Flip (PUnboxedRecord mfs))  = Flip <$> (PUnboxedRecord <$> traverse (traverse $ traverse f) mfs)
  traverse _ (Flip (PUnderscore))         = pure $ Flip PUnderscore
  traverse f (Flip (PUnitel))             = pure $ Flip (PUnitel)
  traverse f (Flip (PTake pv mfs))        = Flip <$> (PTake pv <$> traverse (traverse $ traverse f) mfs)
#ifdef BUILTIN_ARRAYS
  traverse f (Flip (PArray ips))          = Flip <$> (PArray <$> traverse f ips)
  traverse f (Flip (PArrayTake pv eps))   = Flip <$> (PArrayTake pv <$> traverse (traverse f) eps)
#endif

instance Traversable (Flip2 IrrefutablePattern e ip) where  -- pv
  traverse f (Flip2 (PVar pv))            = Flip2 <$> (PVar <$> f pv)
  traverse _ (Flip2 (PTuple ips))         = pure $ Flip2 (PTuple ips)
  traverse _ (Flip2 (PUnboxedRecord mfs)) = pure $ Flip2 (PUnboxedRecord mfs)
  traverse _ (Flip2 PUnderscore)          = pure $ Flip2 PUnderscore
  traverse _ (Flip2 PUnitel)              = pure $ Flip2 PUnitel
  traverse f (Flip2 (PTake pv mfs))       = Flip2 <$> (PTake <$> f pv <*> pure mfs)
#ifdef BUILTIN_ARRAYS
  traverse _ (Flip2 (PArray ips))         = pure $ Flip2 (PArray ips)
  traverse f (Flip2 (PArrayTake pv ivs))  = Flip2 <$> (PArrayTake <$> f pv <*> pure ivs)
#endif

instance Traversable (Flip Type t) where  -- e
  traverse _ (Flip (TCon n ts s))        = pure $ Flip (TCon n ts s)
  traverse _ (Flip (TVar v b))           = pure $ Flip (TVar v b)
  traverse _ (Flip (TFun t1 t2))         = pure $ Flip (TFun t1 t2)
  traverse _ (Flip (TRecord fs s))       = pure $ Flip (TRecord fs s)
  traverse _ (Flip (TVariant alts))      = pure $ Flip (TVariant alts)
  traverse _ (Flip (TTuple ts))          = pure $ Flip (TTuple ts)
  traverse _ (Flip (TUnit))              = pure $ Flip (TUnit)
#ifdef BUILTIN_ARRAYS
  traverse f (Flip (TArray t e s tkns))  = Flip <$> (TArray t <$> f e <*> pure s <*> traverse (firstM f) tkns)
  traverse f (Flip (TATake idxs t))      = Flip <$> (TATake <$> traverse f idxs <*> pure t)
  traverse f (Flip (TAPut  idxs t))      = Flip <$> (TAPut  <$> traverse f idxs <*> pure t)
#endif
  traverse _ (Flip (TUnbox t))           = pure $ Flip (TUnbox t)
  traverse _ (Flip (TBang t))            = pure $ Flip (TBang t)
  traverse _ (Flip (TTake fs t))         = pure $ Flip (TTake fs t)
  traverse _ (Flip (TPut  fs t))         = pure $ Flip (TPut  fs t)
  traverse _ (Flip (TLayout l t))        = pure $ Flip (TLayout l t)

instance Traversable (Flip (TopLevel t) e) where  -- p
  traverse _ (Flip (Include s))           = pure $ Flip (Include s)
  traverse _ (Flip (IncludeStd s))        = pure $ Flip (IncludeStd s)
  traverse _ (Flip (DocBlock s))          = pure $ Flip (DocBlock s)
  traverse _ (Flip (RepDef s))            = pure $ Flip (RepDef s)
  traverse _ (Flip (AbsTypeDec n vs ts))  = pure $ Flip (AbsTypeDec n vs ts)
  traverse _ (Flip (TypeDec n vs t))      = pure $ Flip (TypeDec n vs t)
  traverse _ (Flip (AbsDec v pt))         = pure $ Flip (AbsDec v pt)
  traverse f (Flip (FunDef v pt alts))    = Flip <$> (FunDef v pt <$> traverse (ttraverse f) alts)
  traverse _ (Flip (ConstDef v t e))      = pure $ Flip (ConstDef v t e)
instance Traversable (Flip2 TopLevel e p) where  -- t
  traverse _ (Flip2 (Include s))          = pure $ Flip2 (Include s)
  traverse _ (Flip2 (IncludeStd s))       = pure $ Flip2 (IncludeStd s)
  traverse _ (Flip2 (DocBlock s))         = pure $ Flip2 (DocBlock s)
  traverse _ (Flip2 (RepDef s))           = pure $ Flip2 (RepDef s)
  traverse f (Flip2 (AbsTypeDec n vs ts)) = Flip2 <$> (AbsTypeDec n vs <$> traverse f ts)
  traverse f (Flip2 (TypeDec n vs t))     = Flip2 <$> (TypeDec  n vs <$> f t)
  traverse f (Flip2 (AbsDec v pt))        = Flip2 <$> (AbsDec   v <$> traverse f pt)
  traverse f (Flip2 (FunDef v pt alts))   = Flip2 <$> (FunDef   v <$> traverse f pt <*> pure alts)
  traverse f (Flip2 (ConstDef v t e))     = Flip2 <$> (ConstDef v <$> f t <*> pure e)

instance Functor (Flip (Binding t p) e) where  -- ip
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip2 (Binding t) e ip) where  -- p
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip3 Binding e ip p) where  -- t
  fmap f x = runIdentity (traverse (Identity . f) x)

instance Functor (Flip Alt e) where  -- p
  fmap f x = runIdentity (traverse (Identity . f) x)

instance Functor (Flip (Expr t p) e) where
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip2 (Expr t) e ip) where
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip3 Expr e ip p) where
  fmap f x = runIdentity (traverse (Identity . f) x)

instance Functor (Flip (IrrefutablePattern pv) e) where  -- ip
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip2 IrrefutablePattern e ip) where  -- pv
  fmap f x = runIdentity (traverse (Identity . f) x)

instance Functor (Flip Type e) where  -- t
  fmap f x = runIdentity (traverse (Identity . f) x)

instance Functor (Flip (TopLevel t) e) where
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip2 TopLevel e p) where
  fmap f x = runIdentity (traverse (Identity . f) x)

-- -----------------------------------------------------------------------------

-- FIXME: Many of the following folder functions are not exhaustive, esp.
-- as we are adding more constructors to the AST. / zilinc

fvA :: Alt RawPatn RawExpr -> [VarName]
fvA (Alt p _ e) = let locals = fvP p
                   in filter (`notElem` locals) (fvE e)

fvB :: Binding RawType RawPatn RawIrrefPatn RawExpr -> ([VarName], [VarName])
fvB (Binding ip t e _) = (fvIP ip, foldMap fvT t ++ fvE e)
fvB (BindingAlts p t e _ alts) = (fvP p ++ foldMap fvA alts, foldMap fvT t ++ fvE e)

fvP :: RawPatn -> [VarName]
fvP (RP (PCon _ ips)) = foldMap fvIP ips
fvP (RP (PIrrefutable ip)) = fvIP ip
fvP _ = []

fvIP :: RawIrrefPatn -> [VarName]
fvIP (RIP (PVar pv)) = [pv]
fvIP (RIP (PTuple ips)) = foldMap fvIP ips
fvIP (RIP (PUnboxedRecord mfs)) = foldMap (fvIP . snd) $ Compose mfs
fvIP (RIP (PTake pv mfs)) = foldMap (fvIP . snd) $ Compose mfs
#ifdef BUILTIN_ARRAYS
fvIP (RIP (PArray ips)) = foldMap fvIP ips
#endif
fvIP _ = []

fvE :: RawExpr -> [VarName]
fvE (RE (Var v)) = [v]
fvE (RE (Match e _ alts)) = fvE e ++ foldMap fvA alts
fvE (RE (TypeApp v ts _)) = v : foldMap (foldMap fvT) ts
fvE (RE (Lam  p t e)) = filter (`notElem` fvIP p) (foldMap fvT t ++ fvE e)
fvE (RE (LamC _ _ _ vs)) = vs  -- FIXME
fvE (RE (Let (b:bs) e)) = let (locals, fvs) = fvB b
                              fvs' = filter (`notElem` locals) (fvE (RE (Let bs e)))
                           in fvs ++ fvs'
#ifdef BUILTIN_ARRAYS
fvE (RE (ArrayLit es)) = foldMap fvE es
fvE (RE (ArrayIndex e i)) = fvE e ++ fvE i
fvE (RE (ArrayMap2 ((p1,p2),f) (e1,e2))) = filter (`notElem` fvIP p1 ++ fvIP p2) $ fvE f ++ fvE e1 ++ fvE e2
#endif
fvE (RE (Annot e t)) = fvE e ++ fvT t
fvE (RE e) = foldMap fvE e

fvT :: RawType -> [VarName]
fvT (RT (TCon _ ts _)) = foldMap fvT ts
fvT (RT (TVar _ _)) = []
fvT (RT (TFun t1 t2)) = fvT t1 ++ fvT t2
fvT (RT (TRecord fs _)) = foldMap (fvT . fst . snd) fs
fvT (RT (TVariant alts)) = foldMap (foldMap fvT . fst) alts
fvT (RT (TTuple ts)) = foldMap fvT ts
fvT (RT (TUnit)) = []
#ifdef BUILTIN_ARRAYS
fvT (RT (TArray t e _ tkns)) = fvT t ++ fvE e ++ foldMap (fvE . fst) tkns
fvT (RT (TATake idxs t)) = fvT t ++ foldMap fvE idxs
fvT (RT (TAPut  idxs t)) = fvT t ++ foldMap fvE idxs
#endif
fvT (RT (TUnbox   t)) = fvT t
fvT (RT (TBang    t)) = fvT t
fvT (RT (TTake  _ t)) = fvT t
fvT (RT (TPut   _ t)) = fvT t
fvT (RT (TLayout _ t)) = fvT t

fcA :: Alt v RawExpr -> [TagName]
fcA (Alt _ _ e) = fcE e

fcB :: Binding RawType RawPatn RawIrrefPatn RawExpr -> [TagName]
fcB (Binding _ t e _) = foldMap fcT t ++ fcE e
fcB (BindingAlts _ t e _ alts) = foldMap fcT t ++ fcE e ++ foldMap fcA alts

fcE :: RawExpr -> [TagName]
fcE (RE (Let bs e)) = fcE e ++ foldMap fcB bs
fcE (RE (Match e _ as)) = fcE e ++ foldMap fcA as
fcE (RE (TypeApp _ ts _)) = foldMap fcT (Compose ts)
fcE (RE (Annot e t)) = fcE e ++ fcT t
fcE (RE e) = foldMap fcE e

fcT :: RawType -> [TagName]
fcT (RT (TCon n ts _)) = n : foldMap fcT ts
#ifdef BUILTIN_ARRAYS
fcT (RT (TArray t e _ tkns)) = fcT t ++ fcE e ++ foldMap (fcE . fst) tkns
fcT (RT (TATake idxs t)) = foldMap fcE idxs ++ fcT t
fcT (RT (TAPut  idxs t)) = foldMap fcE idxs ++ fcT t
#endif
fcT (RT t) = foldMap fcT t

tvT :: RawType -> [TyVarName]
tvT (RT (TCon _ ts _)) = foldMap tvT ts
tvT (RT (TVar v _)) = [v]
tvT (RT (TFun t1 t2)) = tvT t1 ++ tvT t2
tvT (RT (TRecord fs _)) = foldMap (tvT . fst . snd) fs
tvT (RT (TVariant alts)) = foldMap (foldMap tvT . fst) alts
tvT (RT (TTuple ts)) = foldMap tvT ts
tvT (RT (TUnit)) = []
#ifdef BUILTIN_ARRAYS
tvT (RT (TArray t e _ tkns)) = tvT t  -- TODO: tvE
tvT (RT (TATake idxs t)) = tvT t   -- TODO: tvE
tvT (RT (TAPut  idxs t)) = tvT t   -- TODO: tvE
#endif
tvT (RT (TUnbox   t)) = tvT t
tvT (RT (TBang    t)) = tvT t
tvT (RT (TTake  _ t)) = tvT t
tvT (RT (TPut   _ t)) = tvT t
tvT (RT (TLayout _ t)) = tvT t

-- Dargent variables

dvA :: Alt v RawExpr -> [RepName]
dvA (Alt _ _ e) = dvE e

dvB :: Binding RawType RawPatn RawIrrefPatn RawExpr -> [RepName]
dvB (Binding _ mt e _) = foldMap dvT mt ++ dvE e
dvB (BindingAlts _ mt e _ alts) = foldMap dvT mt ++ dvE e ++ foldMap dvA alts

dvT :: RawType -> [RepName]
dvT _ = []

dvE :: RawExpr -> [RepName]
dvE (RE (Let bs e)) = dvE e ++ foldMap dvB bs
dvE (RE (Match e _ as)) = dvE e ++ foldMap dvA as
dvE (RE (TypeApp _ ts _)) = foldMap dvT (Compose ts)
dvE (RE (Annot e t)) = dvE e ++ dvT t
dvE (RE e) = foldMap dvE e

allRepRefs :: DataLayoutExpr -> [RepName]
allRepRefs (DL d) = allRepRefs' d
  where
    allRepRefs' (Prim _) = []
    allRepRefs' (Record fs) = concatMap (allRepRefs . thd3) fs
    allRepRefs' (Variant tag cs) = allRepRefs' tag ++ concatMap (\(_,_,_,e) -> allRepRefs e) cs
#ifdef BUILTIN_ARRAYS
    allRepRefs' (Array e _) = allRepRefs e
#endif
    allRepRefs' (Offset e _) = allRepRefs' e
    allRepRefs' (RepRef n) = [n]
    allRepRefs' Ptr = []



-- -----------------------------------------------------------------------------

stripLocT :: LocType -> RawType
stripLocT = RT . fmap stripLocT . ffmap stripLocE . typeOfLT

stripLocP :: LocPatn -> RawPatn
stripLocP = RP . fmap stripLocIP . patnOfLP

stripLocIP :: LocIrrefPatn -> RawIrrefPatn
stripLocIP = RIP . ffmap stripLocIP . fmap stripLocE . irpatnOfLIP

stripLocE :: LocExpr -> RawExpr
stripLocE = RE . ffffmap stripLocT . fffmap stripLocP . ffmap stripLocIP . fmap stripLocE . exprOfLE

noPos :: SourcePos
noPos = newPos "unknown" 0 0

dummyLocT :: RawType -> LocType
dummyLocT = rawToLocT noPos

dummyLocP :: RawPatn -> LocPatn
dummyLocP = rawToLocP noPos

dummyLocIP :: RawIrrefPatn -> LocIrrefPatn
dummyLocIP = rawToLocIP noPos

dummyLocE :: RawExpr -> LocExpr
dummyLocE = rawToLocE noPos

stripAllLoc :: TopLevel LocType LocPatn LocExpr -> TopLevel RawType RawPatn RawExpr
stripAllLoc = fffmap stripLocT . ffmap stripLocP . fmap stripLocE

rawToLocT :: SourcePos -> RawType -> LocType
rawToLocT l (RT t) = LocType l (fmap (rawToLocT l) $ ffmap (rawToLocE l) t)

rawToLocP :: SourcePos -> RawPatn -> LocPatn
rawToLocP l (RP p) = LocPatn l (fmap (rawToLocIP l) p)

rawToLocIP :: SourcePos -> RawIrrefPatn -> LocIrrefPatn
rawToLocIP l (RIP ip) = LocIrrefPatn l (ffmap (rawToLocIP l) $ fmap (rawToLocE l) ip)

rawToLocE :: SourcePos -> RawExpr -> LocExpr
rawToLocE l (RE e) = LocExpr l ( ffffmap (rawToLocT  l)
                               $ fffmap  (rawToLocP  l)
                               $ ffmap   (rawToLocIP l)
                               $ fmap    (rawToLocE  l) e)

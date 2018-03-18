--
-- Copyright 2017, NICTA
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

import Control.Applicative
import Data.Functor.Compose
import Data.Functor.Identity
#if __GLASGOW_HASKELL__ < 709
import Data.Foldable hiding (elem)
import Data.Traversable
#endif
import qualified Data.Map as M
import Text.Parsec.Pos

type DocString = String

data IrrefutablePattern pv ip = PVar pv
                              | PIPVar pv  -- implicit binder
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

data Binding t p ip e = Binding ip (Maybe t) e [VarName]
                      | BindingAlts p (Maybe t) e [VarName] [Alt p e]
                      deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Inline = Inline
            | NoInline
            deriving (Eq, Ord, Show)

data Expr t p ip e = PrimOp OpName [e]
                   | Var VarName
                   | IPVar VarName
                   | Match e [VarName] [Alt p e]
                   | TypeApp FunName [Maybe t] Inline
                   | Con TagName [e]
                   | Seq e e
                   | Lam ip (Maybe t) e
                   | App e e
                   | LamC ip (Maybe t) e [VarName]  -- closure lambda
                   | AppC e e             -- closure application
                   | If e [VarName] e e
                   | Member e FieldName
                   | Unitel
                   | IntLit Integer
                   | BoolLit Bool
                   | CharLit Char
                   | StringLit String
                   | Tuple [e]
                   | UnboxedRecord [(FieldName, e)]
                   | Let [Binding t p ip e] e
                   | Put e [Maybe (FieldName, e)]  -- Note: `Nothing' will be desugared to `Just' in TypeCheck / zilinc
                   | Upcast e
                   | Annot e t
                   deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type Banged = Bool
type Taken  = Bool

type TIPConstraint t = (VarName, t)

data Type t =
            -- They are in WHNF
              TCon TypeName [t] Sigil
            | TVar VarName Banged
            | TFun [TIPConstraint t] t t
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
                    | AbsTypeDec TypeName [TyVarName] [t]
                    | TypeDec    TypeName [TyVarName] t
                    | AbsDec VarName (Polytype t)
                    | FunDef VarName (Polytype t) [Alt p e]
                    | ConstDef VarName t e
                    deriving (Eq, Show, Functor, Foldable, Traversable)

absFnDeclId :: String -> TopLevel t p e -> Bool
absFnDeclId x (AbsDec fn _) = x == fn
absFnDeclId _ _ = False

absTyDeclId :: String -> TopLevel t p e -> Bool
absTyDeclId x (AbsTypeDec tn _ _) = x == tn
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

instance Foldable (Flip IrrefutablePattern pv) where  -- ip
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
  traverse _ (Flip (IPVar v))           = pure $ Flip (IPVar v)
  traverse _ (Flip (Match e v alt))     = pure $ Flip (Match e v alt)
  traverse _ (Flip (TypeApp v ts nt))   = pure $ Flip (TypeApp v ts nt)
  traverse _ (Flip (Con n e))           = pure $ Flip (Con n e)
  traverse _ (Flip (Seq e e'))          = pure $ Flip (Seq e e')
  traverse f (Flip (Lam  ip mt e))      = Flip <$> (Lam  <$> f ip <*> pure mt <*> pure e)
  traverse f (Flip (LamC ip mt e vs))   = Flip <$> (LamC <$> f ip <*> pure mt <*> pure e <*> pure vs)
  traverse _ (Flip (App  e e'))         = pure $ Flip (App  e e')
  traverse _ (Flip (AppC e e'))         = pure $ Flip (AppC e e')
  traverse _ (Flip (If c vs e e'))      = pure $ Flip (If c vs e e')
  traverse _ (Flip (Member e f))        = pure $ Flip (Member e f)
  traverse _ (Flip Unitel)              = pure $ Flip Unitel
  traverse _ (Flip (IntLit l))          = pure $ Flip (IntLit l)
  traverse _ (Flip (BoolLit l))         = pure $ Flip (BoolLit l)
  traverse _ (Flip (CharLit l))         = pure $ Flip (CharLit l)
  traverse _ (Flip (StringLit l))       = pure $ Flip (StringLit l)
  traverse _ (Flip (Tuple es))          = pure $ Flip (Tuple es)
  traverse _ (Flip (UnboxedRecord es))  = pure $ Flip (UnboxedRecord es)
  traverse f (Flip (Let bs e))          = Flip <$> (Let <$> (traverse (ttraverse f) bs) <*> pure e)
  traverse _ (Flip (Put e es))          = pure $ Flip (Put e es)
  traverse _ (Flip (Upcast e))          = pure $ Flip (Upcast e)
  traverse _ (Flip (Annot e t))         = pure $ Flip (Annot e t)
instance Traversable (Flip2 (Expr t) e ip) where  -- p
  traverse _ (Flip2 (PrimOp op e))      = pure $ Flip2 (PrimOp op e)
  traverse _ (Flip2 (Var v))            = pure $ Flip2 (Var v)
  traverse _ (Flip2 (IPVar v))          = pure $ Flip2 (IPVar v)
  traverse f (Flip2 (Match e v alt))    = Flip2 <$> (Match e v <$> traverse (ttraverse f) alt)
  traverse _ (Flip2 (TypeApp v ts nt))  = pure $ Flip2 (TypeApp v ts nt)
  traverse _ (Flip2 (Con n e))          = pure $ Flip2 (Con n e)
  traverse _ (Flip2 (Seq e e'))         = pure $ Flip2 (Seq e e')
  traverse _ (Flip2 (Lam  ip mt e))     = pure $ Flip2 (Lam  ip mt e)
  traverse _ (Flip2 (LamC ip mt e vs))  = pure $ Flip2 (LamC ip mt e vs)
  traverse _ (Flip2 (App  e e'))        = pure $ Flip2 (App  e e')
  traverse _ (Flip2 (AppC e e'))        = pure $ Flip2 (AppC e e')
  traverse _ (Flip2 (If c vs e e'))     = pure $ Flip2 (If c vs e e')
  traverse _ (Flip2 (Member e f))       = pure $ Flip2 (Member e f)
  traverse _ (Flip2 Unitel)             = pure $ Flip2 Unitel
  traverse _ (Flip2 (IntLit l))         = pure $ Flip2 (IntLit l)
  traverse _ (Flip2 (BoolLit l))        = pure $ Flip2 (BoolLit l)
  traverse _ (Flip2 (CharLit l))        = pure $ Flip2 (CharLit l)
  traverse _ (Flip2 (StringLit l))      = pure $ Flip2 (StringLit l)
  traverse _ (Flip2 (Tuple es))         = pure $ Flip2 (Tuple es)
  traverse _ (Flip2 (UnboxedRecord es)) = pure $ Flip2 (UnboxedRecord es)
  traverse f (Flip2 (Let bs e))         = Flip2 <$> (Let <$> traverse (tttraverse f) bs <*> pure e)
  traverse _ (Flip2 (Put e es))         = pure $ Flip2 (Put e es)
  traverse _ (Flip2 (Upcast e))         = pure $ Flip2 (Upcast e)
  traverse _ (Flip2 (Annot e t))        = pure $ Flip2 (Annot e t)
instance Traversable (Flip3 Expr e ip p) where  -- t
  traverse _ (Flip3 (PrimOp op e))       = pure $ Flip3 (PrimOp op e)
  traverse _ (Flip3 (Var v))             = pure $ Flip3 (Var v)
  traverse _ (Flip3 (IPVar v))           = pure $ Flip3 (IPVar v)
  traverse _ (Flip3 (Match e v alt))     = pure $ Flip3 (Match e v alt)
  traverse f (Flip3 (TypeApp v ts nt))   = Flip3 <$> (TypeApp v <$> traverse (traverse f) ts <*> pure nt)
  traverse _ (Flip3 (Con n e))           = pure $ Flip3 (Con n e)
  traverse _ (Flip3 (Seq e e'))          = pure $ Flip3 (Seq e e')
  traverse f (Flip3 (Lam  ip mt e))      = Flip3 <$> (Lam  ip <$> traverse f mt <*> pure e)
  traverse f (Flip3 (LamC ip mt e vs))   = Flip3 <$> (LamC ip <$> traverse f mt <*> pure e <*> pure vs)
  traverse _ (Flip3 (App  e e'))         = pure $ Flip3 (App  e e')
  traverse _ (Flip3 (AppC e e'))         = pure $ Flip3 (AppC e e')
  traverse _ (Flip3 (If c vs e e'))      = pure $ Flip3 (If c vs e e')
  traverse _ (Flip3 (Member e f))        = pure $ Flip3 (Member e f)
  traverse _ (Flip3 Unitel)              = pure $ Flip3 Unitel
  traverse _ (Flip3 (IntLit l))          = pure $ Flip3 (IntLit l)
  traverse _ (Flip3 (BoolLit l))         = pure $ Flip3 (BoolLit l)
  traverse _ (Flip3 (CharLit l))         = pure $ Flip3 (CharLit l)
  traverse _ (Flip3 (StringLit l))       = pure $ Flip3 (StringLit l)
  traverse _ (Flip3 (Tuple es))          = pure $ Flip3 (Tuple es)
  traverse _ (Flip3 (UnboxedRecord es))  = pure $ Flip3 (UnboxedRecord es)
  traverse f (Flip3 (Let bs e))          = Flip3 <$> (Let <$> (traverse (ttttraverse f) bs) <*> pure e)
  traverse _ (Flip3 (Put e es))          = pure $ Flip3 (Put e es)
  traverse _ (Flip3 (Upcast e))          = pure $ Flip3 (Upcast e)
  traverse f (Flip3 (Annot e t))         = Flip3 <$> (Annot <$> pure e <*> f t)

instance Traversable (Flip IrrefutablePattern pv) where  -- ip
  traverse f (Flip (PVar pv))            = Flip <$> (PVar <$> f pv)
  traverse f (Flip (PIPVar pv))          = Flip <$> (PIPVar <$> f pv)
  traverse _ (Flip (PTuple ips))         = pure $ Flip (PTuple ips)
  traverse _ (Flip (PUnboxedRecord mfs)) = pure $ Flip (PUnboxedRecord mfs)
  traverse _ (Flip PUnderscore)          = pure $ Flip PUnderscore
  traverse _ (Flip PUnitel)              = pure $ Flip PUnitel
  traverse f (Flip (PTake pv mfs))       = Flip <$> (PTake <$> f pv <*> pure mfs)

instance Traversable (Flip (TopLevel t) e) where  -- p
  traverse _ (Flip (Include s))           = pure $ Flip (Include s)
  traverse _ (Flip (IncludeStd s))        = pure $ Flip (IncludeStd s)
  traverse _ (Flip (DocBlock s))          = pure $ Flip (DocBlock s)
  traverse _ (Flip (AbsTypeDec n vs ts))  = pure $ Flip (AbsTypeDec n vs ts)
  traverse _ (Flip (TypeDec n vs t))      = pure $ Flip (TypeDec n vs t)
  traverse _ (Flip (AbsDec v pt))         = pure $ Flip (AbsDec v pt)
  traverse f (Flip (FunDef v pt alts))    = Flip <$> (FunDef v pt <$> traverse (ttraverse f) alts)
  traverse _ (Flip (ConstDef v t e))      = pure $ Flip (ConstDef v t e)
instance Traversable (Flip2 TopLevel e p) where  -- t
  traverse _ (Flip2 (Include s))          = pure $ Flip2 (Include s)
  traverse _ (Flip2 (IncludeStd s))       = pure $ Flip2 (IncludeStd s)
  traverse _ (Flip2 (DocBlock s))         = pure $ Flip2 (DocBlock s)
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

instance Functor (Flip IrrefutablePattern ip) where  -- pv
  fmap f x = runIdentity (traverse (Identity . f) x)

instance Functor (Flip (TopLevel t) e) where
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip2 TopLevel e p) where
  fmap f x = runIdentity (traverse (Identity . f) x)

-- -----------------------------------------------------------------------------

fvA :: Alt RawPatn RawExpr -> [VarName]
fvA (Alt p _ e) = let locals = fvP p
                   in filter (`notElem` locals) (fvE e)

fvB :: Binding RawType RawPatn RawIrrefPatn RawExpr -> ([VarName], [VarName])
fvB (Binding ip _ e _) = (fvIP ip, fvE e)
fvB (BindingAlts p _ e _ alts) = (fvP p ++ foldMap fvA alts, fvE e)

fvP :: RawPatn -> [VarName]
fvP (RP (PCon _ ips)) = foldMap fvIP ips
fvP (RP (PIrrefutable ip)) = fvIP ip
fvP _ = []

fvIP :: RawIrrefPatn -> [VarName]
fvIP (RIP (PVar pv)) = [pv]
fvIP (RIP (PIPVar pv)) = [pv]
fvIP (RIP (PTuple ips)) = foldMap fvIP ips
fvIP (RIP (PUnboxedRecord mfs)) = foldMap (fvIP . snd) $ Compose mfs
fvIP (RIP (PTake pv mfs)) = foldMap (fvIP . snd) $ Compose mfs
fvIP _ = []

fvE :: RawExpr -> [VarName]
fvE (RE (TypeApp v _ _)) = [v]
fvE (RE (Var v)) = [v]
fvE (RE (IPVar v)) = [v]
fvE (RE (Match e _ alts)) = fvE e ++ foldMap fvA alts
fvE (RE (Lam  p _ e)) = filter (`notElem` fvIP p) (fvE e)
fvE (RE (LamC _ _ _ vs)) = vs
fvE (RE (Let (b:bs) e)) = let (locals, fvs) = fvB b
                              fvs' = filter (`notElem` locals) (fvE (RE (Let bs e)))
                           in fvs ++ fvs'
fvE (RE e) = foldMap fvE e

fcA :: Alt v RawExpr -> [TagName]
fcA (Alt _ _ e) = fcE e

fcB :: Binding RawType RawPatn RawIrrefPatn RawExpr -> [TagName]
fcB (Binding _ t e _) = foldMap fcT t ++ fcE e
fcB (BindingAlts _ t e _ alts) = foldMap fcT t ++ fcE e ++ foldMap fcA alts

fcE :: RawExpr -> [TagName]
fcE (RE (Let bs e)) = fcE e ++ foldMap fcB bs
fcE (RE (Match e _ as)) = fcE e ++ foldMap fcA as
fcE (RE (TypeApp _ ts _)) = foldMap fcT (Compose ts)
fcE (RE e) = foldMap fcE e

fcT :: RawType -> [TagName]
fcT (RT (TCon n ts _)) = n : foldMap fcT ts
fcT (RT t) = foldMap fcT t

-- -----------------------------------------------------------------------------

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


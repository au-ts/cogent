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
import Cogent.Dargent.Surface
import Cogent.Util

import Control.Applicative
import Control.Arrow (first)
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
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


type DocString = String

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

data Alt p e = Alt p Likelihood e deriving (Data, Eq, Ord, Show, Functor, Foldable, Traversable)

data Binding t p ip e = Binding ip (Maybe t) e [VarName]
                      | BindingAlts p (Maybe t) e [VarName] [Alt p e]
                      deriving (Data, Eq, Ord, Show, Functor, Foldable, Traversable)

data Inline = Inline
            | NoInline
            deriving (Data, Eq, Ord, Show)

data Expr t p ip l e = PrimOp OpName [e]
                     | Var VarName
                     | Match e [VarName] [Alt p e]
                     | TLApp FunName [Maybe t] [Maybe l] Inline
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
                     | Buffer Integer [(FieldName, e)]
                     deriving (Data, Eq, Ord, Show, Functor, Foldable, Traversable)

type Banged  = Bool
type Unboxed = Bool
type Taken   = Bool

data Type e l t =
                -- They are in WHNF
                  TCon TypeName [t] (Sigil (Maybe l))
                | TVar VarName Banged Unboxed
                | TFun t t
                | TRecord RecursiveParameter [(FieldName, (t, Taken))] (Sigil (Maybe l))
                | TVariant (M.Map TagName ([t], Taken))
                | TTuple [t]
                | TUnit
#ifdef BUILTIN_ARRAYS
                | TArray t e (Sigil (Maybe l)) [(e, Taken)]
                                                       -- \ ^^^ a list of taken/put indices
                -- The TATake and TAPut type-operators will be normalised away.
                | TATake [e] t
                | TAPut  [e] t
#endif
#ifdef REFINEMENT_TYPES
                | TRefine VarName t e
#endif
                -- In TypeCheck.Post, the TUnbox and TBang type-operators
                -- are normalised out of the syntax tree by altering the Sigil
                -- of the type they act on / zilinc, mdimeglio
                | TUnbox   t
                | TBang    t
                -- Will be inserted before typechecking
                | TRPar RecParName Banged (RecContext t)
                -- The context for a recursive type, i.e. a mapping from
                -- Used for both field names in records and tag names in variants
                | TTake (Maybe [FieldName]) t
                | TPut  (Maybe [FieldName]) t
                | TLayout l t
                | TBuffer Integer [(FieldName, t)]
                deriving (Show, Functor, Data, Eq, Ord, Foldable, Traversable)

-- A few commonly used typed
u8   = TCon "U8"   [] Unboxed
u32  = TCon "U32"  [] Unboxed
bool = TCon "Bool" [] Unboxed

data Polytype t = PT [(TyVarName, Kind)] [(DLVarName, t)] t
  deriving (Data, Eq, Show, Functor, Foldable, Traversable, Ord)

numOfArgs (PT x _ _) = length x

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


data LocExpr = LocExpr { posOfE :: SourcePos, exprOfLE :: Expr LocType LocPatn LocIrrefPatn DataLayoutExpr LocExpr }
             deriving (Data, Eq, Ord, Show)
data LocPatn = LocPatn { posOfP :: SourcePos, patnOfLP :: Pattern LocIrrefPatn }
             deriving (Data, Eq, Ord, Show)
data LocIrrefPatn = LocIrrefPatn { posOfIP :: SourcePos, irpatnOfLIP :: IrrefutablePattern VarName LocIrrefPatn LocExpr }
                  deriving (Data, Eq, Ord, Show)
data LocType = LocType { posOfT :: SourcePos, typeOfLT' :: Type LocExpr DataLayoutExpr LocType }
             | Documentation String LocType
             deriving (Data, Eq, Ord, Show)

typeOfLT (LocType _ t) = t
typeOfLT (Documentation s t) = typeOfLT t

posOfLT (LocType p _) = p
posOfLT (Documentation _ t) = posOfLT t

numTypeVars :: TopLevel t p e -> Int
numTypeVars (FunDef _ pt _) = numOfArgs pt
numTypeVars (AbsDec _ pt)   = numOfArgs pt
numTypeVars (AbsTypeDec _ ts _) = length ts
numTypeVars (TypeDec _ ts _)    = length ts

data RawType = RT { unRT :: Type RawExpr DataLayoutExpr RawType } deriving (Data, Eq, Ord, Show)
data RawExpr = RE { unRE :: Expr RawType RawPatn RawIrrefPatn DataLayoutExpr RawExpr } deriving (Data, Eq, Ord, Show)
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

instance Foldable (Flip (Expr t p ip) e) where  -- l
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip2 (Expr t p) e l) where  -- ip
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip3 (Expr t) e l ip) where  -- p
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip4 Expr e l ip p) where  -- t
  foldMap f a = getConst $ traverse (Const . f) a

instance Foldable (Flip (IrrefutablePattern pv) e) where  -- ip
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip2 IrrefutablePattern e ip) where  -- pv
  foldMap f a = getConst $ traverse (Const . f) a


instance Foldable (Flip (Type e) t) where  -- l
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip2 Type t l) where  -- e
  foldMap f a = getConst $ traverse (Const . f) a

instance Foldable (Flip (TopLevel t) e) where
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip2 TopLevel p e) where
  foldMap f a = getConst $ traverse (Const . f) a

instance Traversable (Flip Alt e) where  -- p
  traverse f (Flip alt) = Flip <$> bitraverse f pure alt

instance Traversable (Flip (Binding t p) e) where  -- ip
  traverse f (Flip  b) = Flip  <$> quadritraverse pure pure f pure b
instance Traversable (Flip2 (Binding t) e ip) where  -- p
  traverse f (Flip2 b) = Flip2 <$> quadritraverse pure f pure pure b
instance Traversable (Flip3 Binding e ip p) where  -- t
  traverse f (Flip3 b) = Flip3 <$> quadritraverse f pure pure pure b

instance Traversable (Flip (Expr t p ip) e) where  -- l
  traverse f (Flip  e) = Flip  <$> pentatraverse pure pure pure f pure e
instance Traversable (Flip2 (Expr t p) e l) where  -- ip
  traverse f (Flip2 e) = Flip2 <$> pentatraverse pure pure f pure pure e
instance Traversable (Flip3 (Expr t) e l ip) where  -- p
  traverse f (Flip3 e) = Flip3 <$> pentatraverse pure f pure pure pure e
instance Traversable (Flip4 Expr e l ip p) where  -- t
  traverse f (Flip4 e) = Flip4 <$> pentatraverse f pure pure pure pure e

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

instance Traversable (Flip (Type e) t) where  -- l
  traverse f (Flip (TCon n ts s))        = Flip <$> (TCon n ts <$> traverse (traverse f) s)
  traverse _ (Flip (TVar v b u))         = pure $ Flip (TVar v b u)
  traverse _ (Flip (TFun t1 t2))         = pure $ Flip (TFun t1 t2)
  traverse f (Flip (TRecord rp fs s))    = Flip <$> (TRecord rp fs <$> traverse (traverse f) s)
  traverse _ (Flip (TVariant alts))      = pure $ Flip (TVariant alts)
  traverse _ (Flip (TTuple ts))          = pure $ Flip (TTuple ts)
  traverse _ (Flip (TUnit))              = pure $ Flip (TUnit)
  traverse _ (Flip (TBuffer n fs))       = pure $ Flip (TBuffer n fs)
#ifdef BUILTIN_ARRAYS
  traverse f (Flip (TArray t e s tkns))  = Flip <$> (TArray t e <$> traverse (traverse f) s <*> pure tkns)
  traverse _ (Flip (TATake idxs t))      = pure $ Flip (TATake idxs t)
  traverse _ (Flip (TAPut  idxs t))      = pure $ Flip (TAPut  idxs t)
#endif
#ifdef REFINEMENT_TYPES
  traverse _ (Flip (TRefine v t e))      = pure $ Flip (TRefine v t e)
#endif
  traverse _ (Flip (TUnbox t))           = pure $ Flip (TUnbox t)
  traverse _ (Flip (TBang t))            = pure $ Flip (TBang t)
  traverse _ (Flip (TRPar n b rc))       = pure $ Flip (TRPar n b rc)
  traverse _ (Flip (TTake fs t))         = pure $ Flip (TTake fs t)
  traverse _ (Flip (TPut  fs t))         = pure $ Flip (TPut  fs t)
  traverse f (Flip (TLayout l t))        = Flip <$> (TLayout <$> f l <*> pure t)

instance Traversable (Flip2 Type t l) where  -- e
  traverse _ (Flip2 (TCon n ts s))        = pure $ Flip2 (TCon n ts s)
  traverse _ (Flip2 (TVar v b u))         = pure $ Flip2 (TVar v b u)
  traverse _ (Flip2 (TFun t1 t2))         = pure $ Flip2 (TFun t1 t2)
  traverse _ (Flip2 (TRecord rp fs s))    = pure $ Flip2 (TRecord rp fs s)
  traverse _ (Flip2 (TVariant alts))      = pure $ Flip2 (TVariant alts)
  traverse _ (Flip2 (TTuple ts))          = pure $ Flip2 (TTuple ts)
  traverse _ (Flip2 (TUnit))              = pure $ Flip2 (TUnit)
  traverse _ (Flip2 (TBuffer n fs))       = pure $ Flip2 (TBuffer n fs)
#ifdef BUILTIN_ARRAYS
  traverse f (Flip2 (TArray t e s tkns))  = Flip2 <$> (TArray t <$> f e <*> pure s <*> traverse (firstM f) tkns)
  traverse f (Flip2 (TATake idxs t))      = Flip2 <$> (TATake <$> traverse f idxs <*> pure t)
  traverse f (Flip2 (TAPut  idxs t))      = Flip2 <$> (TAPut  <$> traverse f idxs <*> pure t)
#endif
#ifdef REFINEMENT_TYPES
  traverse f (Flip2 (TRefine v t e))      = Flip2 <$> (TRefine v t <$> f e)
#endif
  traverse _ (Flip2 (TUnbox t))           = pure $ Flip2 (TUnbox t)
  traverse _ (Flip2 (TBang t))            = pure $ Flip2 (TBang t)
  traverse _ (Flip2 (TRPar n b rc))       = pure $ Flip2 (TRPar n b rc)
  traverse _ (Flip2 (TTake fs t))         = pure $ Flip2 (TTake fs t)
  traverse _ (Flip2 (TPut  fs t))         = pure $ Flip2 (TPut  fs t)
  traverse _ (Flip2 (TLayout l t))        = pure $ Flip2 (TLayout l t)

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

instance Functor (Flip (Expr t p ip) e) where  -- l
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip2 (Expr t p) e l) where  -- ip
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip3 (Expr t) e l ip) where  -- p
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip4 Expr e l ip p) where  -- t
  fmap f x = runIdentity (traverse (Identity . f) x)

instance Functor (Flip (IrrefutablePattern pv) e) where  -- ip
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip2 IrrefutablePattern e ip) where  -- pv
  fmap f x = runIdentity (traverse (Identity . f) x)

instance Functor (Flip (Type e) t) where  -- l
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip2 Type t l) where  -- e
  fmap f x = runIdentity (traverse (Identity . f) x)

instance Functor (Flip (TopLevel t) e) where
  fmap f x = runIdentity (traverse (Identity . f) x)
instance Functor (Flip2 TopLevel e p) where
  fmap f x = runIdentity (traverse (Identity . f) x)


instance Bifunctor Alt where
  bimap f g = runIdentity . bitraverse (Identity . f) (Identity . g)
instance Bifoldable Alt where
  bifoldMap f g = getConst . bitraverse (Const . f) (Const . g)
instance Bitraversable Alt where
  bitraverse f g (Alt p l e) = Alt <$> f p <*> pure l <*> g e


instance Quadritraversable Binding where
  quadritraverse fa fb fc fd (Binding ip mt e vs) = Binding <$> fc ip <*> traverse fa mt <*> fd e <*> pure vs
  quadritraverse fa fb fc fd (BindingAlts p mt e vs alts) = BindingAlts <$> fb p <*> traverse fa mt <*> fd e <*> pure vs <*> traverse (bitraverse fb fd) alts

instance Pentatraversable Expr where
  pentatraverse fa fb fc fd fe (PrimOp op es)      = PrimOp op <$> traverse fe es
  pentatraverse fa fb fc fd fe (Var v)             = pure $ Var v
  pentatraverse fa fb fc fd fe (Match e vs as)     = Match <$> fe e <*> pure vs <*> traverse (bitraverse fb fe) as
  pentatraverse fa fb fc fd fe (TLApp fn ts ls n)  = TLApp fn <$> traverse (traverse fa) ts <*> traverse (traverse fd) ls <*> pure n
  pentatraverse fa fb fc fd fe (Con n es)          = Con n <$> traverse fe es
  pentatraverse fa fb fc fd fe (Seq e1 e2)         = Seq <$> fe e1 <*> fe e2
  pentatraverse fa fb fc fd fe (Lam ip mt e)       = Lam <$> fc ip <*> traverse fa mt <*> fe e
  pentatraverse fa fb fc fd fe (App e1 e2 inf)     = App <$> fe e1 <*> fe e2 <*> pure inf
  pentatraverse fa fb fc fd fe (Comp e1 e2)        = Comp <$> fe e1 <*> fe e2
  pentatraverse fa fb fc fd fe (LamC ip mt e vs)   = LamC <$> fc ip <*> traverse fa mt <*> fe e <*> pure vs
  pentatraverse fa fb fc fd fe (AppC e1 e2)        = AppC <$> fe e1 <*> fe e2
  pentatraverse fa fb fc fd fe (If e vs e1 e2)     = If <$> fe e <*> pure vs <*> fe e1 <*> fe e2
  pentatraverse fa fb fc fd fe (MultiWayIf alts e) = MultiWayIf <$> traverse (liftA unrotate3 . bitraverse fe fe . Rotate3) alts <*> fe e
  pentatraverse fa fb fc fd fe (Member e f)        = Member <$> fe e <*> pure f
  pentatraverse fa fb fc fd fe (Unitel)            = pure $ Unitel
  pentatraverse fa fb fc fd fe (IntLit    n)       = pure $ IntLit    n
  pentatraverse fa fb fc fd fe (BoolLit   b)       = pure $ BoolLit   b
  pentatraverse fa fb fc fd fe (CharLit   c)       = pure $ CharLit   c
  pentatraverse fa fb fc fd fe (StringLit s)       = pure $ StringLit s
#ifdef BUILTIN_ARRAYS
  pentatraverse fa fb fc fd fe (ArrayLit es)       = ArrayLit <$> traverse fe es
  pentatraverse fa fb fc fd fe (ArrayIndex e1 e2)  = ArrayIndex <$> fe e1 <*> fe e2
  pentatraverse fa fb fc fd fe (ArrayMap2 p es) = ArrayMap2 <$> bitraverse (bothM fc) fe p <*> bothM fe es
  pentatraverse fa fb fc fd fe (ArrayPut e es)     = ArrayPut <$> fe e <*> traverse (bothM fe) es
#endif
  pentatraverse fa fb fc fd fe (Tuple es)          = Tuple <$> traverse fe es
  pentatraverse fa fb fc fd fe (UnboxedRecord fs)  = UnboxedRecord <$> traverse (traverse fe) fs
  pentatraverse fa fb fc fd fe (Let bs e)          = Let <$> traverse (quadritraverse fa fb fc fe) bs <*> fe e
  pentatraverse fa fb fc fd fe (Put e fs)          = Put <$> fe e <*> traverse (traverse (traverse fe)) fs
  pentatraverse fa fb fc fd fe (Upcast e)          = Upcast <$> fe e
  pentatraverse fa fb fc fd fe (Annot e t)         = Annot <$> fe e <*> fa t
  pentatraverse fa fb fc fd fe (Buffer n es)       = Buffer n <$> traverse (traverse fe) es

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
fvIP (RIP (PUnboxedRecord mfs)) = foldMap (fvIP . snd) (Compose mfs)
fvIP (RIP (PTake pv mfs)) = pv : foldMap (fvIP . snd) (Compose mfs)
#ifdef BUILTIN_ARRAYS
fvIP (RIP (PArray ips)) = foldMap fvIP ips
fvIP (RIP (PArrayTake pv hs)) = __todo "fvIP: PArrayTake unimplemented" -- TODO?
#endif
fvIP _ = []

fvE :: RawExpr -> [VarName]
fvE (RE (Var v)) = [v]
fvE (RE (Match e _ alts)) = fvE e ++ foldMap fvA alts
fvE (RE (TLApp v ts _ _)) = v : foldMap (foldMap fvT) ts
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
fvT (RT (TVar {})) = []
fvT (RT (TFun t1 t2)) = fvT t1 ++ fvT t2
fvT (RT (TRecord _ fs _)) = foldMap (fvT . fst . snd) fs
fvT (RT (TVariant alts)) = foldMap (foldMap fvT . fst) alts
fvT (RT (TTuple ts)) = foldMap fvT ts
fvT (RT (TUnit)) = []
fvT (RT (TRPar _ _ rc)) = __fixme [] -- FIXME: check this
#ifdef BUILTIN_ARRAYS
fvT (RT (TArray t e _ tkns)) = fvT t ++ fvE e ++ foldMap (fvE . fst) tkns
fvT (RT (TATake idxs t)) = fvT t ++ foldMap fvE idxs
fvT (RT (TAPut  idxs t)) = fvT t ++ foldMap fvE idxs
#endif
#ifdef REFINEMENT_TYPES
fvT (RT (TRefine v t e)) = fvT t ++ filter (/= v) (fvE e)
#endif
fvT (RT (TUnbox   t)) = fvT t
fvT (RT (TBang    t)) = fvT t
fvT (RT (TTake  _ t)) = fvT t
fvT (RT (TPut   _ t)) = fvT t
fvT (RT (TLayout _ t)) = fvT t
fvT (RT (TBuffer _ fs)) = foldMap (fvT . snd) fs

fcA :: Alt v RawExpr -> [TagName]
fcA (Alt _ _ e) = fcE e

fcB :: Binding RawType RawPatn RawIrrefPatn RawExpr -> [TagName]
fcB (Binding _ t e _) = foldMap fcT t ++ fcE e
fcB (BindingAlts _ t e _ alts) = foldMap fcT t ++ fcE e ++ foldMap fcA alts

fcE :: RawExpr -> [TagName]
fcE (RE (Let bs e)) = fcE e ++ foldMap fcB bs
fcE (RE (Match e _ as)) = fcE e ++ foldMap fcA as
fcE (RE (TLApp _ ts _ _)) = foldMap fcT (Compose ts)
fcE (RE (Annot e t)) = fcE e ++ fcT t
fcE (RE e) = foldMap fcE e

fcT :: RawType -> [TagName]
fcT (RT (TCon n ts _)) = n : foldMap fcT ts
#ifdef BUILTIN_ARRAYS
fcT (RT (TArray t e _ tkns)) = fcT t ++ fcE e ++ foldMap (fcE . fst) tkns
fcT (RT (TATake idxs t)) = foldMap fcE idxs ++ fcT t
fcT (RT (TAPut  idxs t)) = foldMap fcE idxs ++ fcT t
#endif
#ifdef REFINEMENT_TYPES
fcT (RT (TRefine _ t e)) = fcT t ++ fcE e
#endif
fcT (RT t) = foldMap fcT t

tvT :: RawType -> [TyVarName]
tvT (RT (TCon _ ts _)) = foldMap tvT ts
tvT (RT (TVar v _ _)) = [v]
tvT (RT (TFun t1 t2)) = tvT t1 ++ tvT t2
tvT (RT (TRecord _ fs _)) = foldMap (tvT . fst . snd) fs
tvT (RT (TVariant alts)) = foldMap (foldMap tvT . fst) alts
tvT (RT (TTuple ts)) = foldMap tvT ts
tvT (RT (TUnit)) = []
tvT (RT (TRPar _ _ m)) = __fixme $ foldMap (foldMap tvT) m -- FIXME: check this
#ifdef BUILTIN_ARRAYS
tvT (RT (TArray t e _ tkns)) = tvT t ++ tvE e ++ foldMap (tvE . fst) tkns
tvT (RT (TATake idxs t)) = tvT t ++ foldMap tvE idxs
tvT (RT (TAPut  idxs t)) = tvT t ++ foldMap tvE idxs
#endif
#ifdef REFINEMENT_TYPES
tvT (RT (TRefine _ t e)) = tvT t ++ tvE e
#endif
tvT (RT (TUnbox   t)) = tvT t
tvT (RT (TBang    t)) = tvT t
tvT (RT (TTake  _ t)) = tvT t
tvT (RT (TPut   _ t)) = tvT t
tvT (RT (TLayout _ t)) = tvT t
tvT (RT (TBuffer _ fs)) = foldMap (tvT . snd) fs

tvE :: RawExpr -> [TyVarName]
tvE (RE (PrimOp op es))     = foldMap tvE es
tvE (RE (Var v))            = []
tvE (RE (Match e v alts))   = tvE e ++ foldMap tvA alts
tvE (RE (TLApp v ts _ nt))  = foldMap (foldMap tvT) ts
tvE (RE (Con n es))         = foldMap tvE es
tvE (RE (Seq e e'))         = tvE e ++ tvE e'
tvE (RE (Lam  ip mt e))     = foldMap tvT mt ++ tvE e
tvE (RE (LamC ip mt e vs))  = foldMap tvT mt ++ tvE e
tvE (RE (App  e e' i))      = tvE e ++ tvE e'
tvE (RE (Comp f g))         = tvE f ++ tvE g
tvE (RE (AppC e e'))        = tvE e ++ tvE e'
tvE (RE (If c vs e e'))     = tvE c ++ tvE e ++ tvE e'
tvE (RE (MultiWayIf es el)) = foldMap (\(e1,_,_,e2) -> tvE e1 ++ tvE e2) es ++ tvE el
tvE (RE (Member e f))       = tvE e
tvE (RE Unitel)             = []
tvE (RE (IntLit l))         = []
tvE (RE (BoolLit l))        = []
tvE (RE (CharLit l))        = []
tvE (RE (StringLit l))      = []
#ifdef BUILTIN_ARRAYS
tvE (RE (ArrayLit es))      = foldMap tvE es
tvE (RE (ArrayIndex e i))   = tvE e ++ tvE i
tvE (RE (ArrayMap2 (as,fn) (e1,e2))) = foldMap tvE [fn,e1,e2]
tvE (RE (ArrayPut arr ivs)) = tvE arr ++ foldMap (\(i,v) -> foldMap tvE [i,v]) ivs
#endif
tvE (RE (Tuple es))         = foldMap tvE es
tvE (RE (UnboxedRecord es)) = foldMap (foldMap tvE) es
tvE (RE (Let bs e))         = foldMap tvB bs ++ tvE e
tvE (RE (Put e es))         = tvE e ++ foldMap (foldMap $ foldMap tvE) es
tvE (RE (Upcast e))         = tvE e
tvE (RE (Annot e t))        = tvE e ++ tvT t
tvE (RE (Buffer n es))      = foldMap (tvE . snd) es

tvB :: Binding RawType p ip RawExpr -> [TyVarName]
tvB (Binding _ mt e _) = foldMap tvT mt ++ tvE e
tvB (BindingAlts _ mt e _ alts) = foldMap tvT mt ++ tvE e ++ foldMap tvA alts

tvA :: Alt p RawExpr -> [TyVarName]
tvA (Alt _ _ e) = tvE e

lvT :: RawType -> [DLVarName]
lvT (RT (TLayout l _)) = lvL l
lvT (RT (TFun t1 t2)) = lvT t1 ++ lvT t2
lvT (RT (TRecord _ fs _)) = foldMap (lvT . fst . snd) fs
lvT (RT (TVariant alts)) = foldMap (foldMap lvT . fst) alts
lvT (RT (TTuple ts)) = foldMap lvT ts
lvT (RT (TRPar _ _ rc)) = __fixme [] -- FIXME: check this
#ifdef BUILTIN_ARRAYS
lvT (RT (TArray t _ _ _)) = lvT t
lvT (RT (TATake _ t)) = lvT t
lvT (RT (TAPut  _ t)) = lvT t
#endif
lvT (RT (TUnbox   t)) = lvT t
lvT (RT (TBang    t)) = lvT t
lvT (RT (TTake  _ t)) = lvT t
lvT (RT (TPut   _ t)) = lvT t
lvT (RT (TBuffer _ fs)) = foldMap (lvT . snd) fs
lvT (RT _) = []

lvL :: DataLayoutExpr -> [DLVarName]
lvL (DLVar n) = [n]
lvL (DLOffset e _) = lvL e
lvL (DLRecord fs) = foldMap (\(_, _, x) -> lvL x) fs
lvL (DLVariant t alt) = lvL t <> foldMap (\(_, _, _, x) -> lvL x) alt
#ifdef BUILTIN_ARRAYS
lvL (DLArray e _) = lvL e
#endif
lvL (DLRepRef _ s) = concatMap lvL s
lvL _ = []

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
dvE (RE (TLApp _ ts _ _)) = foldMap dvT (Compose ts)
dvE (RE (Annot e t)) = dvE e ++ dvT t
dvE (RE e) = foldMap dvE e

allRepRefs :: DataLayoutExpr -> [RepName]
allRepRefs (DL d) = allRepRefs' d
  where
    allRepRefs' (Prim _) = []
    allRepRefs' (Record fs) = concatMap (allRepRefs . thd3) fs
    allRepRefs' (Variant tag cs) = allRepRefs tag ++ concatMap (\(_,_,_,e) -> allRepRefs e) cs
#ifdef BUILTIN_ARRAYS
    allRepRefs' (Array e _) = allRepRefs e
#endif
    allRepRefs' (Offset e _) = allRepRefs e
    allRepRefs' (RepRef n s) = [n] ++ concatMap allRepRefs s
    allRepRefs' (LVar _) = []
    allRepRefs' Ptr = []


-- -----------------------------------------------------------------------------

stripLocT :: LocType -> RawType
stripLocT = RT . fmap stripLocT . fffmap stripLocE . typeOfLT

stripLocP :: LocPatn -> RawPatn
stripLocP = RP . fmap stripLocIP . patnOfLP

stripLocIP :: LocIrrefPatn -> RawIrrefPatn
stripLocIP = RIP . ffmap stripLocIP . fmap stripLocE . irpatnOfLIP

stripLocE :: LocExpr -> RawExpr
stripLocE = RE . fffffmap stripLocT . ffffmap stripLocP . fffmap stripLocIP . fmap stripLocE . exprOfLE

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
rawToLocT l (RT t) = LocType l (fmap (rawToLocT l) $ fffmap (rawToLocE l) t)

rawToLocP :: SourcePos -> RawPatn -> LocPatn
rawToLocP l (RP p) = LocPatn l (fmap (rawToLocIP l) p)

rawToLocIP :: SourcePos -> RawIrrefPatn -> LocIrrefPatn
rawToLocIP l (RIP ip) = LocIrrefPatn l (ffmap (rawToLocIP l) $ fmap (rawToLocE l) ip)

rawToLocE :: SourcePos -> RawExpr -> LocExpr
rawToLocE l (RE e) = LocExpr l ( fffffmap (rawToLocT  l)
                               $ ffffmap  (rawToLocP  l)
                               $ fffmap   (rawToLocIP l)
                               $ fmap    (rawToLocE  l) e)


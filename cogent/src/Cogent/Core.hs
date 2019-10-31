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

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{- LANGUAGE DeriveDataTypeable -}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{- LANGUAGE InstanceSigs -}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
#if __GLASGOW_HASKELL__ < 709
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-missing-signatures #-}

module Cogent.Core
  ( module Cogent.Core
  , module Cogent.Dargent.Core
  ) where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Dargent.Allocation (BitRange)
import Cogent.Dargent.Core
import Cogent.PrettyPrint hiding (associativity, primop)
import Cogent.Util
import Data.Nat (Nat(Zero, Suc))
import qualified Data.Nat as Nat
import Data.Vec hiding (splitAt, length, zipWith, zip, unzip)
import qualified Data.Vec as Vec

import Control.Arrow hiding ((<+>))
-- import Data.Data hiding (Refl)
import Data.Function ((&))
import Data.IntMap as IM (IntMap, null, filter, keys)
#if __GLASGOW_HASKELL__ < 709
import Data.Traversable(traverse)
#endif
import Text.PrettyPrint.ANSI.Leijen as L hiding (tupled, indent, (<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as L ((<$>))

data Type t v a ty e
  = TVar (Fin t)
  | TVarBang (Fin t)
  | TCon TypeName [ty t v a] (Sigil ()) -- Layout will be nothing for abstract types
  | TFun (ty t v a) (ty t v a)
  | TPrim PrimInt
  | TString
  | TSum [(TagName, (ty t v a, Bool))]  -- True means taken (since 2.0.4)
  | TProduct (ty t v a) (ty t v a)
  | TRecord [(FieldName, (ty t v a, Bool))] (Sigil (DataLayout BitRange))
    -- True means taken, Layout will be nothing for abstract types
  | TUnit
#ifdef BUILTIN_ARRAYS
  | TArray (ty t v a) ArraySize (Sigil (DataLayout BitRange)) (Maybe (e t v a))  -- the hole
                 -- \ ^^^ use Int for now
    -- XXX | ^^^ (UntypedExpr t 'Zero VarName)  -- stick to UntypedExpr to be simple / zilinc
    -- The sigil specifies the layout of the element
#endif
  deriving (Show, Eq, Ord)

data SupposedlyMonoType v a ty e = forall (t :: Nat). SMT (Type t v a ty e)

isTVar :: Type t v a ty e -> Bool
isTVar (TVar _) = True
isTVar _ = False

isTFun :: Type t v a ty e -> Bool
isTFun (TFun {}) = True
isTFun _ = False

isUnboxed :: Type t v a ty e -> Bool
isUnboxed (TCon _ _ Unboxed) = True
isUnboxed (TRecord _ Unboxed) =  True
#ifdef BUILTIN_ARRAYS
isUnboxed (TArray _ _ Unboxed _) = True
#endif
isUnboxed _ = False

data FunNote = NoInline | InlineMe | MacroCall | InlinePlease  -- order is important, larger value has stronger precedence
             deriving (Bounded, Eq, Ord, Show)

data Expr t v a ty e
  = Variable (Fin v, a)
  | Fun CoreFunName [ty t v a] FunNote  -- here do we want to keep partial application and infer again? / zilinc
  | Op Op [e t v a]
  | App (e t v a) (e t v a)
  | Con TagName (e t v a) (ty t v a)
  | Unit
  | ILit Integer PrimInt
  | SLit String
#ifdef BUILTIN_ARRAYS
  | ALit [e t v a]
  | ArrayIndex (e t v a) (e t v a)
  | Pop (a, a) (e t v a) (e t ('Suc ('Suc v)) a)
  | Singleton (e t v a)  -- extracting the element out of a singleton array
  | ArrayMap2 ((a, a), e t ('Suc ('Suc v)) a) (e t v a, e t v a)
  | ArrayTake (a, a) (e t v a) (e t v a) (e t ('Suc ('Suc v)) a)
          -- \ ^^^ The first is the array, and the second is the taken object
  | ArrayPut (e t v a) (e t v a) (e t v a)
#endif
  | Let a (e t v a) (e t ('Suc v) a)
  | LetBang [(Fin v, a)] a (e t v a) (e t ('Suc v) a)
  | Tuple (e t v a) (e t v a)
  | Struct [(FieldName, e t v a)]  -- unboxed record
  | If (e t v a) (e t v a) (e t v a)   -- technically no longer needed as () + () == Bool
  | Case (e t v a) TagName (Likelihood, a, e t ('Suc v) a) (Likelihood, a, e t ('Suc v) a)
  | Esac (e t v a)
  | Split (a, a) (e t v a) (e t ('Suc ('Suc v)) a)
  | Member (e t v a) FieldIndex
  | Take (a, a) (e t v a) FieldIndex (e t ('Suc ('Suc v)) a)
     -- \ ^^^ The first is the record, and the second is the taken field
  | Put (e t v a) FieldIndex (e t v a)
  | Promote (ty t v a) (e t v a)  -- only for guiding the tc. rep. unchanged.
  | Cast (ty t v a) (e t v a)  -- only for integer casts. rep. changed
deriving instance (Show a, Show (e t v a), Show (e t ('Suc v) a), Show (e t ('Suc ('Suc v)) a), Show (ty t v a))
  => Show (Expr t v a ty e)
deriving instance (Eq a, Eq (e t v a), Eq (e t ('Suc v) a), Eq (e t ('Suc ('Suc v)) a), Eq (ty t v a))
  => Eq  (Expr t v a ty e)
deriving instance (Ord a, Ord (e t v a), Ord (e t ('Suc v) a), Ord (e t ('Suc ('Suc v)) a), Ord (ty t v a))
  => Ord (Expr t v a ty e)
  -- constraint no smaller than header, thus UndecidableInstances

data UntypedExpr t v a = E  (Expr t v a UntypedType UntypedExpr) deriving (Show, Eq, Ord)
data TypedExpr   t v a = TE { exprType :: Type t v a TypedType TypedExpr , exprExpr :: Expr t v a TypedType TypedExpr }
                       deriving (Show, Eq, Ord)

data UntypedType t v a = T  (Type t v a UntypedType UntypedExpr) deriving (Show, Eq, Ord)
data TypedType   t v a = TT (Type t v a TypedType   TypedExpr  ) deriving (Show, Eq, Ord)

data FunctionType t v a ty = forall t. FT (Vec t Kind) (ty t v a) (ty t v a)
instance Show (FunctionType t v a ty) where
  show _ = undefined

data Attr = Attr { inlineDef :: Bool, fnMacro :: Bool } deriving (Eq, Ord, Show)

#if __GLASGOW_HASKELL__ < 803
instance Monoid Attr where
  mempty = Attr False False
  (Attr a1 a2) `mappend` (Attr a1' a2') = Attr (a1 || a1') (a2 || a2')
#else
instance Semigroup Attr where
  Attr a1 a2 <> Attr a1' a2' = Attr (a1 || a1') (a2 || a2')
instance Monoid Attr where
  mempty = Attr False False
#endif


data Definition ty e a
  = forall t. (Pretty a, Pretty (e t ('Suc 'Zero) a))
           => FunDef  Attr FunName (Vec t (TyVarName, Kind)) (ty t 'Zero a) (ty t 'Zero a) (e t ('Suc 'Zero) a)
  | forall t. (Pretty a, Pretty (e t ('Suc 'Zero) a))
           => AbsDecl Attr FunName (Vec t (TyVarName, Kind)) (ty t 'Zero a) (ty t 'Zero a)
  | forall t. (Pretty a, Pretty (e t ('Suc 'Zero) a))
           => TypeDef TypeName (Vec t TyVarName) (Maybe (ty t 'Zero a))
deriving instance Show a => Show (Definition TypedType   TypedExpr   a)
deriving instance Show a => Show (Definition UntypedType UntypedExpr a)

type CoreConst e = (VarName, e 'Zero 'Zero VarName)

getDefinitionId :: Definition ty e a -> String
getDefinitionId (FunDef  _ fn _ _ _ _) = fn
getDefinitionId (AbsDecl _ fn _ _ _  ) = fn
getDefinitionId (TypeDef tn _ _    ) = tn

getFuncId :: Definition ty e a -> Maybe FunName
getFuncId (FunDef  _ fn _ _ _ _) = Just fn
getFuncId (AbsDecl _ fn _ _ _  ) = Just fn
getFuncId _ = Nothing

getTypeVarNum :: Definition ty e a -> Int
getTypeVarNum (FunDef  _ _ tvs _ _ _) = Nat.toInt $ Vec.length tvs
getTypeVarNum (AbsDecl _ _ tvs _ _  ) = Nat.toInt $ Vec.length tvs
getTypeVarNum (TypeDef _ tvs _    ) = Nat.toInt $ Vec.length tvs

isDefinitionId :: String -> Definition ty e a -> Bool
isDefinitionId n d = n == getDefinitionId d

isFuncId :: CoreFunName -> Definition ty e a -> Bool
isFuncId n (FunDef  _ fn _ _ _ _) = unCoreFunName n == fn
isFuncId n (AbsDecl _ fn _ _ _  ) = unCoreFunName n == fn
isFuncId _ _ = False

isAbsFun :: Definition ty e a -> Bool
isAbsFun (AbsDecl {}) = True
isAbsFun _ = False

isConFun :: Definition ty e a -> Bool
isConFun (FunDef {}) = True
isConFun _ = False

isTypeDef :: Definition ty e a -> Bool
isTypeDef (TypeDef {}) = True
isTypeDef _ = False

isAbsTyp :: Definition ty e a -> Bool
isAbsTyp (TypeDef _ _ Nothing) = True
isAbsTyp _ = False

traverseE :: (Applicative f) => (forall t v. e1 t v a -> f (e2 t v a)) -> Expr t v a ty e1 -> f (Expr t v a ty e2)
traverseE f (Variable v)         = pure $ Variable v
traverseE f (Fun fn tys nt)      = pure $ Fun fn tys nt
traverseE f (Op opr es)          = Op opr <$> traverse f es
traverseE f (App e1 e2)          = App <$> f e1 <*> f e2
traverseE f (Con cn e t)         = Con cn <$> f e <*> pure t
traverseE f (Unit)               = pure $ Unit
traverseE f (ILit i pt)          = pure $ ILit i pt
traverseE f (SLit s)             = pure $ SLit s
#ifdef BUILTIN_ARRAYS
traverseE f (ALit es)            = ALit <$> traverse f es
traverseE f (ArrayIndex e i)     = ArrayIndex <$> f e <*> f i
traverseE f (Pop as e1 e2)       = Pop as <$> f e1 <*> f e2
traverseE f (Singleton e)        = Singleton <$> f e
traverseE f (ArrayMap2 ae es)    = ArrayMap2 <$> secondM f ae <*> bothM f es
traverseE f (ArrayTake as arr fld e) = ArrayTake as <$> f arr <*> f fld <*> f e
traverseE f (ArrayPut arr fld e) = ArrayPut <$> f arr <*> f fld <*> f e
#endif
traverseE f (Let a e1 e2)        = Let a <$> f e1 <*> f e2
traverseE f (LetBang vs a e1 e2) = LetBang vs a <$> f e1 <*> f e2
traverseE f (Tuple e1 e2)        = Tuple <$> f e1 <*> f e2
traverseE f (Struct fs)          = Struct <$> traverse (traverse f) fs
traverseE f (If e1 e2 e3)        = If <$> f e1 <*> f e2 <*> f e3
traverseE f (Case e tn (l1,a1,e1) (l2,a2,e2)) = Case <$> f e <*> pure tn <*> ((l1, a1,) <$> f e1)  <*> ((l2, a2,) <$> f e2)
traverseE f (Esac e)             = Esac <$> (f e)
traverseE f (Split a e1 e2)      = Split a <$> (f e1) <*> (f e2)
traverseE f (Member rec fld)     = Member <$> (f rec) <*> pure fld
traverseE f (Take a rec fld e)   = Take a <$> (f rec) <*> pure fld <*> (f e)
traverseE f (Put rec fld v)      = Put <$> (f rec) <*> pure fld <*> (f v)
traverseE f (Promote ty e)       = Promote ty <$> (f e)
traverseE f (Cast ty e)          = Cast ty <$> (f e)

-- pre-order fold over Expr wrapper
foldEPre :: (Monoid b) => (forall t v. e1 t v a -> Expr t v a ty e1) -> (forall t v. e1 t v a -> b) -> e1 t v a -> b
foldEPre unwrap f e = case unwrap e of
  Variable{}          -> f e
  Fun{}               -> f e
  (Op _ es)           -> mconcat $ f e : map (foldEPre unwrap f) es
  (App e1 e2)         -> mconcat [f e, foldEPre unwrap f e1, foldEPre unwrap f e2]
  (Con _ e1 _)        -> f e `mappend` foldEPre unwrap f e1
  Unit                -> f e
  ILit {}             -> f e
  SLit {}             -> f e
#ifdef BUILTIN_ARRAYS
  ALit es             -> mconcat $ f e : map (foldEPre unwrap f) es
  ArrayIndex e i      -> mconcat [f e, f i]
  Pop as e1 e2        -> mconcat [f e1, f e2]
  Singleton e         -> f e
  ArrayMap2 (_,e) (e1,e2) -> mconcat [f e, f e1, f e2]
  ArrayTake _ arr fld e   -> mconcat [f arr, f fld, f e]
  ArrayPut    arr fld e   -> mconcat [f arr, f fld, f e]
#endif
  (Let _ e1 e2)       -> mconcat [f e, foldEPre unwrap f e1, foldEPre unwrap f e2]
  (LetBang _ _ e1 e2) -> mconcat [f e, foldEPre unwrap f e1, foldEPre unwrap f e2]
  (Tuple e1 e2)       -> mconcat [f e, foldEPre unwrap f e1, foldEPre unwrap f e2]
  (Struct fs)         -> mconcat $ f e : map (foldEPre unwrap f . snd) fs
  (If e1 e2 e3)       -> mconcat [f e, foldEPre unwrap f e1, foldEPre unwrap f e2, foldEPre unwrap f e3]
  (Case e1 _ (_,_,e2) (_,_,e3)) -> mconcat $ [f e, foldEPre unwrap f e1, foldEPre unwrap f e2, foldEPre unwrap f e3]
  (Esac e1)           -> f e `mappend` foldEPre unwrap f e1
  (Split _ e1 e2)     -> mconcat [f e, foldEPre unwrap f e1, foldEPre unwrap f e2]
  (Member e1 _)       -> f e `mappend` foldEPre unwrap f e1
  (Take _ e1 _ e2)    -> mconcat [f e, foldEPre unwrap f e1, foldEPre unwrap f e2]
  (Put e1 _ e2)       -> mconcat [f e, foldEPre unwrap f e1, foldEPre unwrap f e2]
  (Promote _ e1)      -> f e `mappend` foldEPre unwrap f e1
  (Cast _ e1)         -> f e `mappend` foldEPre unwrap f e1

fmapE :: (forall t v. e1 t v a -> e2 t v a) -> Expr t v a ty e1 -> Expr t v a ty e2
fmapE f (Variable v)         = Variable v
fmapE f (Fun fn tys nt)      = Fun fn tys nt
fmapE f (Op opr es)          = Op opr (map f es)
fmapE f (App e1 e2)          = App (f e1) (f e2)
fmapE f (Con cn e t)         = Con cn (f e) t
fmapE f (Unit)               = Unit
fmapE f (ILit i pt)          = ILit i pt
fmapE f (SLit s)             = SLit s
#ifdef BUILTIN_ARRAYS
fmapE f (ALit es)            = ALit (map f es)
fmapE f (ArrayIndex e i)     = ArrayIndex (f e) (f i)
fmapE f (ArrayMap2 (as,e) (e1,e2)) = ArrayMap2 (as, f e) (f e1, f e2)
fmapE f (Pop a e1 e2)        = Pop a (f e1) (f e2)
fmapE f (Singleton e)        = Singleton (f e)
fmapE f (ArrayTake as arr fld e) = ArrayTake as (f arr) (f fld) (f e)
fmapE f (ArrayPut arr fld e) = ArrayPut (f arr) (f fld) (f e)
#endif
fmapE f (Let a e1 e2)        = Let a (f e1) (f e2)
fmapE f (LetBang vs a e1 e2) = LetBang vs a (f e1) (f e2)
fmapE f (Tuple e1 e2)        = Tuple (f e1) (f e2)
fmapE f (Struct fs)          = Struct (map (second f) fs)
fmapE f (If e1 e2 e3)        = If (f e1) (f e2) (f e3)
fmapE f (Case e tn (l1,a1,e1) (l2,a2,e2)) = Case (f e) tn (l1, a1, f e1) (l2, a2, f e2)
fmapE f (Esac e)             = Esac (f e)
fmapE f (Split a e1 e2)      = Split a (f e1) (f e2)
fmapE f (Member rec fld)     = Member (f rec) fld
fmapE f (Take a rec fld e)   = Take a (f rec) fld (f e)
fmapE f (Put rec fld v)      = Put (f rec) fld (f v)
fmapE f (Promote ty e)       = Promote ty (f e)
fmapE f (Cast ty e)          = Cast ty (f e)

ffmapE :: (forall t v. ty1 t v a -> ty2 t v a) -> Expr t v a ty1 e -> Expr t v a ty2 e
ffmapE f (Variable v)        = Variable v
ffmapE _ _                   = undefined   -- TODO

fmapT :: (forall t v. e1 t v a -> e2 t v a) -> Type t v a ty e1 -> Type t v a ty e2
fmapT f (TVar x) = TVar x
fmapT _ _        = undefined  -- TODO

ffmapT :: (forall t v. ty1 t v a -> ty2 t v a) -> Type t v a ty1 e -> Type t v a ty2 e
ffmapT f (TVar x) = TVar x
ffmapT f _        = undefined  -- TODO

untypeE :: TypedExpr t v a -> UntypedExpr t v a
untypeE (TE _ e) = E $ ffmapE untypeT $ fmapE untypeE e

untypeT :: TypedType t v a -> UntypedType t v a
untypeT (TT t) = T $ fmapT untypeT t

untypeD :: Definition TypedType TypedExpr a -> Definition UntypedType UntypedExpr a
untypeD (FunDef  attr fn ts ti to e) = FunDef  attr fn ts ti to (untypeE e)
untypeD (AbsDecl attr fn ts ti to  ) = AbsDecl attr fn ts ti to
untypeD (TypeDef tn ts mt) = TypeDef tn ts mt

instance (Functor (e t v), Functor (e t ('Suc v)), Functor (e t ('Suc ('Suc v))))
  => Functor (Flip2 (Expr t v) e ty) where  -- map over @a@
  fmap f (Flip2 (Variable v)         )      = Flip2 $ Variable (second f v)
  fmap f (Flip2 (Fun fn tys nt)      )      = Flip2 $ Fun fn tys nt
  fmap f (Flip2 (Op opr es)          )      = Flip2 $ Op opr (map (fmap f) es)
  fmap f (Flip2 (App e1 e2)          )      = Flip2 $ App (fmap f e1) (fmap f e2)
  fmap f (Flip2 (Con cn e t)         )      = Flip2 $ Con cn (fmap f e) t
  fmap f (Flip2 (Unit)               )      = Flip2 $ Unit
  fmap f (Flip2 (ILit i pt)          )      = Flip2 $ ILit i pt
  fmap f (Flip2 (SLit s)             )      = Flip2 $ SLit s
#ifdef BUILTIN_ARRAYS
  fmap f (Flip2 (ALit es)            )      = Flip2 $ ALit (map (fmap f) es)
  fmap f (Flip2 (ArrayIndex e i)     )      = Flip2 $ ArrayIndex (fmap f e) (fmap f i)
  fmap f (Flip2 (ArrayMap2 (as,e) (e1,e2))) = Flip2 $ ArrayMap2 (both f as, fmap f e) (fmap f e1, fmap f e2)
  fmap f (Flip2 (Pop as e1 e2)       )      = Flip2 $ Pop (both f as) (fmap f e1) (fmap f e2)
  fmap f (Flip2 (Singleton e)        )      = Flip2 $ Singleton (fmap f e)
  fmap f (Flip2 (ArrayTake as arr fld e))   = Flip2 $ ArrayTake (both f as) (fmap f arr) (fmap f fld) (fmap f e)
  fmap f (Flip2 (ArrayPut     arr fld e))   = Flip2 $ ArrayPut (fmap f arr) (fmap f fld) (fmap f e)
#endif
  fmap f (Flip2 (Let a e1 e2)        )      = Flip2 $ Let (f a) (fmap f e1) (fmap f e2)
  fmap f (Flip2 (LetBang vs a e1 e2) )      = Flip2 $ LetBang (map (second f) vs) (f a) (fmap f e1) (fmap f e2)
  fmap f (Flip2 (Tuple e1 e2)        )      = Flip2 $ Tuple (fmap f e1) (fmap f e2)
  fmap f (Flip2 (Struct fs)          )      = Flip2 $ Struct (map (second $ fmap f) fs)
  fmap f (Flip2 (If e1 e2 e3)        )      = Flip2 $ If (fmap f e1) (fmap f e2) (fmap f e3)
  fmap f (Flip2 (Case e tn (l1,a1,e1) (l2,a2,e2))) = Flip2 $ Case (fmap f e) tn (l1, f a1, fmap f e1) (l2, f a2, fmap f e2)
  fmap f (Flip2 (Esac e)             )      = Flip2 $ Esac (fmap f e)
  fmap f (Flip2 (Split a e1 e2)      )      = Flip2 $ Split (both f a) (fmap f e1) (fmap f e2)
  fmap f (Flip2 (Member rec fld)     )      = Flip2 $ Member (fmap f rec) fld
  fmap f (Flip2 (Take a rec fld e)   )      = Flip2 $ Take (both f a) (fmap f rec) fld (fmap f e)
  fmap f (Flip2 (Put rec fld v)      )      = Flip2 $ Put (fmap f rec) fld (fmap f v)
  fmap f (Flip2 (Promote ty e)       )      = Flip2 $ Promote ty (fmap f e)
  fmap f (Flip2 (Cast ty e)          )      = Flip2 $ Cast ty (fmap f e)

instance Functor (TypedExpr t v) where
  fmap f (TE t e) = TE t $ ffmap f e


-- instance Functor (Definition TypedExpr) where
--   fmap f (FunDef  attr fn ts ti to e) = FunDef  attr fn ts ti to (fmap f e)
--   fmap f (AbsDecl attr fn ts ti to)   = AbsDecl attr fn ts ti to
--   fmap f (TypeDef tn ts mt)      = TypeDef tn ts mt
--
-- stripNameTD :: Definition TypedExpr VarName -> Definition TypedExpr ()
-- stripNameTD = fmap $ const ()


-- /////////////////////////////////////////////////////////////////////////////
-- Core-lang pretty-printing

primop = blue . (pretty :: Op -> Doc)
fieldIndex = magenta . string . ('.':) . show

-- NOTE: the precedence levels are somewhat different to those of the surface lang / zilinc

instance Prec (Expr t v a ty e) where
  prec (Op opr [_,_]) = prec (associativity opr)
  prec (ILit {}) = 0
  prec (SLit {}) = 0
#ifdef BUILTIN_ARRAYS
  prec (ALit {}) = 0
#endif
  prec (Variable {}) = 0
  prec (Fun {}) = 0
  prec (App {}) = 1
  prec (Tuple {}) = 0
  prec (Con {}) = 0
  prec (Esac {}) = 0
  prec (Member {}) = 0
  prec (Take {}) = 0
  prec (Put {}) = 1
  prec (Promote {}) = 0
  prec (Cast {}) = 0
  prec _ = 100

instance Prec (TypedExpr t v a) where
  prec (TE _ e) = prec e

instance Prec (UntypedExpr t v a) where
  prec (E e) = prec e

prettyV = dullblue  . string . ("_v" ++) . show . finInt
prettyT = dullgreen . string . ("_t" ++) . show . finInt

instance Pretty a => Pretty (TypedExpr t v a) where
  pretty (TE t e) | not __cogent_fshow_types_in_pretty = pretty e
                  | otherwise = parens (pretty e <+> symbol ":" <+> pretty t)

instance Pretty a => Pretty (UntypedExpr t v a) where
  pretty (E e) = pretty e

instance (Pretty a, Prec (e t v a), Pretty (e t v a), Pretty (e t ('Suc v) a), Pretty (e t ('Suc ('Suc v)) a),
          Pretty (ty t v a))
         => Pretty (Expr t v a ty e) where
  pretty (Op opr [a,b])
     | LeftAssoc  l <- associativity opr = prettyPrec (l+1) a <+> primop opr <+> prettyPrec l b
     | RightAssoc l <- associativity opr = prettyPrec l a <+> primop opr <+> prettyPrec (l+1)  b
     | NoAssoc    l <- associativity opr = prettyPrec l a <+> primop opr <+> prettyPrec l  b
  pretty (Op opr [e]) = primop opr <+> prettyPrec 1 e
  pretty (Op opr es)  = primop opr <+> tupled (map pretty es)
  pretty (ILit i pt) = literal (string $ show i) <+> symbol "::" <+> pretty pt
  pretty (SLit s) = literal $ string s
#ifdef BUILTIN_ARRAYS
  pretty (ALit es) = array $ map pretty es
  pretty (ArrayIndex arr idx) = prettyPrec 2 arr <+> symbol "@" <+> prettyPrec 2 idx
  pretty (ArrayMap2 ((v1,v2),f) (e1,e2)) = keyword "map2" <+>
                                           parens (symbol "\\" <> pretty v1 <+> pretty v2 <+> symbol "=>" <+> pretty f) <+>
                                           prettyPrec 1 e1 <+> prettyPrec 1 e2
  pretty (Pop (v1,v2) e1 e2) = align (keyword "pop" <+> pretty v1 <> symbol ":@" <> pretty v2 <+> symbol "=" <+> pretty e1 L.<$>
                                keyword "in"  <+> pretty e2)
  pretty (Singleton e) = keyword "singleton" <+> parens (pretty e)
  pretty (ArrayPut arr i e) = prettyPrec 1 arr <+> symbol "@" <> record [symbol "@" <> pretty i <+> symbol "=" <+> pretty e]
#endif
  pretty (Variable x) = pretty (snd x) L.<> angles (prettyV $ fst x)
  pretty (Fun fn ins nt) = pretty nt L.<> funname (unCoreFunName fn) <+> pretty ins
  pretty (App a b) = prettyPrec 2 a <+> prettyPrec 1 b
  pretty (Let a e1 e2) = align (keyword "let" <+> pretty a <+> symbol "=" <+> pretty e1 L.<$>
                                keyword "in" <+> pretty e2)
  pretty (LetBang bs a e1 e2) = align (keyword "let!" <+> tupled (map (prettyV . fst) bs) <+> pretty a <+> symbol "=" <+> pretty e1 L.<$>
                                       keyword "in" <+> pretty e2)
  pretty (Unit) = tupled []
  pretty (Tuple e1 e2) = tupled (map pretty [e1, e2])
  pretty (Struct fs) = symbol "#" L.<> record (map (\(n,e) -> fieldname n <+> symbol "=" <+> pretty e) fs)
  pretty (Con tn e t) = parens (tagname tn <+> prettyPrec 1 e) <+> symbol "::" <+> pretty t
  pretty (If c t e) = group . align $ (keyword "if" <+> pretty c
                                       L.<$> indent (keyword "then" </> align (pretty t))
                                       L.<$> indent (keyword "else" </> align (pretty e)))
  pretty (Case e tn (l1,v1,a1) (l2,v2,a2)) = align (keyword "case" <+> pretty e <+> keyword "of"
                                                  L.<$> indent (tagname tn <+> pretty v1 <+> pretty l1 <+> align (pretty a1))
                                                  L.<$> indent (pretty v2 <+> pretty l2 <+> align (pretty a2)))
  pretty (Esac e) = keyword "esac" <+> parens (pretty e)
  pretty (Split (v1,v2) e1 e2) = align (keyword "split" <+> parens (pretty v1 <> comma <> pretty v2) <+> symbol "=" <+> pretty e1 L.<$>
                                  keyword "in" <+> pretty e2)
  pretty (Member x f) = prettyPrec 1 x L.<> symbol "." L.<> fieldIndex f
  pretty (Take (a,b) rec f e) = align (keyword "take" <+> tupled [pretty a, pretty b] <+> symbol "="
                                                      <+> prettyPrec 1 rec <+> record (fieldIndex f:[]) L.<$>
                                       keyword "in" <+> pretty e)
  pretty (Put rec f v) = prettyPrec 1 rec <+> record [fieldIndex f <+> symbol "=" <+> pretty v]
  pretty (Promote t e) = prettyPrec 1 e <+> symbol ":^:" <+> pretty t
  pretty (Cast t e) = prettyPrec 1 e <+> symbol ":::" <+> pretty t

instance Pretty FunNote where
  pretty NoInline = empty
  pretty InlineMe = comment "{-# INLINE #-}" <+> empty
  pretty MacroCall = comment "{-# FNMACRO #-}" <+> empty
  pretty InlinePlease = comment "inline" <+> empty

instance Pretty (Type t v a ty e) where
  pretty (TVar v) = prettyT v
  pretty (TVarBang v) = prettyT v L.<> typesymbol "!"
  pretty (TPrim pt) = pretty pt
  pretty (TString) = typename "String"
  pretty (TUnit) = typename "()"
  pretty (TProduct t1 t2) = tupled (map pretty [t1, t2])
  pretty (TSum alts) = variant (map (\(n,(t,b)) -> tagname n L.<> prettyTaken b <+> pretty t) alts)
  pretty (TFun t1 t2) = prettyT' t1 <+> typesymbol "->" <+> pretty t2
     where prettyT' e@(TFun {}) = parens (pretty e)
           prettyT' e           = pretty e
  pretty (TRecord fs s) = record (map (\(f,(t,b)) -> fieldname f <+> symbol ":" L.<> prettyTaken b <+> pretty t) fs)
                          <> pretty s
  pretty (TCon tn [] s) = typename tn <> pretty s
  pretty (TCon tn ts s) = typename tn <> pretty s <+> typeargs (map pretty ts)
#ifdef BUILTIN_ARRAYS
  pretty (TArray t l s mhole) = (pretty t <> brackets (pretty l) <+> pretty s) &
    (case mhole of Nothing -> id; Just hole -> (<+> keyword "take" <+> parens (pretty hole)))
#endif

prettyTaken :: Bool -> Doc
prettyTaken True  = symbol "*"
prettyTaken False = empty


#if __GLASGOW_HASKELL__ < 709
instance Pretty (TyVarName, Kind) where
#else
instance {-# OVERLAPPING #-} Pretty (TyVarName, Kind) where
#endif
  pretty (v,k) = pretty v L.<> typesymbol ":<" L.<> pretty k

instance Pretty a => Pretty (Vec t a) where
  pretty Nil = empty
  pretty (Cons x Nil) = pretty x
  pretty (Cons x xs) = pretty x L.<> string "," <+> pretty xs

instance Pretty (Definition ty e a) where
  pretty (FunDef _ fn ts t rt e) = funname fn <+> symbol ":" <+> brackets (pretty ts) L.<> symbol "." <+>
                                   parens (pretty t) <+> symbol "->" <+> parens (pretty rt) <+> symbol "=" L.<$>
                                   pretty e
  pretty (AbsDecl _ fn ts t rt) = funname fn <+> symbol ":" <+> brackets (pretty ts) L.<> symbol "." <+>
                                  parens (pretty t) <+> symbol "->" <+> parens (pretty rt)
  pretty (TypeDef tn ts Nothing) = keyword "type" <+> typename tn <+> pretty ts
  pretty (TypeDef tn ts (Just t)) = keyword "type" <+> typename tn <+> pretty ts <+>
                                    symbol "=" <+> pretty t



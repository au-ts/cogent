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
{-# LANGUAGE DeriveGeneric #-}
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
import Data.Binary (Binary)
-- import Data.Data hiding (Refl)
import Data.Function ((&))
import Data.IntMap as IM (IntMap, null, filter, keys)
#if __GLASGOW_HASKELL__ < 709
import Data.Traversable(traverse)
#endif
import GHC.Generics (Generic)
import Text.PrettyPrint.ANSI.Leijen as L hiding (tupled, indent, (<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as L ((<$>))

data Type t v a e
  = TVar (Fin t)
  | TVarBang (Fin t)
  | TVarUnboxed (Fin t)
  | TCon TypeName [Type t v a e] (Sigil ()) -- Layout will be nothing for abstract types
  | TFun (Type t v a e) (Type t v a e)
  | TPrim PrimInt
  | TString
  | TSum [(TagName, (Type t v a e, Bool))]  -- True means taken (since 2.0.4)
  | TProduct (Type t v a e) (Type t v a e)
  | TRecord [(FieldName, (Type t v a e, Bool))] (Sigil (DataLayout BitRange))
    -- True means taken, Layout will be nothing for abstract types
  | TUnit
#ifdef BUILTIN_ARRAYS
  | TArray (Type t v a e) ArraySize (Sigil (DataLayout BitRange)) (Maybe (e t v a))  -- the hole
                 -- \ ^^^ use Int for now
    -- XXX | ^^^ (UntypedExpr t 'Zero VarName)  -- stick to UntypedExpr to be simple / zilinc
    -- The sigil specifies the layout of the element
#endif
  deriving (Show, Eq, Ord)

deriving instance Generic (Type 'Zero)

instance Binary (Type 'Zero)

data SupposedlyMonoType a = forall (t :: Nat) (v :: Nat). SMT (DType t v a)

isTVar :: Type t v a e -> Bool
isTVar (TVar _) = True
isTVar _ = False

isTFun :: Type t v a e -> Bool
isTFun (TFun {}) = True
isTFun _ = False

isUnboxed :: Type t v a e -> Bool
isUnboxed (TCon _ _ Unboxed) = True
isUnboxed (TRecord _ Unboxed) =  True
#ifdef BUILTIN_ARRAYS
isUnboxed (TArray _ _ Unboxed _) = True
#endif
isUnboxed _ = False

data FunNote = NoInline | InlineMe | MacroCall | InlinePlease  -- order is important, larger value has stronger precedence
             deriving (Bounded, Eq, Ord, Show)

data Expr t v a e
  = Variable (Fin v, a)
  | Fun CoreFunName [DType t v a] FunNote  -- here do we want to keep partial application and infer again? / zilinc
  | Op Op [e t v a]
  | App (e t v a) (e t v a)
  | Con TagName (e t v a) (DType t v a)
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
-- \ vvv constraint no smaller than header, thus UndecidableInstances
  | Promote (DType t v a) (e t v a)  -- only for guiding the tc. rep. unchanged.
  | Cast (DType t v a) (e t v a)  -- only for integer casts. rep. changed
deriving instance (Show a, Show (e t v a), Show (e t ('Suc v) a), Show (e t ('Suc ('Suc v)) a))
  => Show (Expr t v a e)
deriving instance (Eq a, Eq (e t v a), Eq (e t ('Suc v) a), Eq (e t ('Suc ('Suc v)) a))
  => Eq  (Expr t v a e)
deriving instance (Ord a, Ord (e t v a), Ord (e t ('Suc v) a), Ord (e t ('Suc ('Suc v)) a))
  => Ord (Expr t v a e)

type DType t v a = Type t v a UntypedExpr

data UntypedExpr t v a = E  (Expr t v a UntypedExpr) deriving (Show, Eq, Ord)
data TypedExpr   t v a = TE { exprType :: DType t v a , exprExpr :: Expr t v a TypedExpr }
                       deriving (Show, Eq, Ord)

data FunctionType v a = forall t. FT (Vec t Kind) (DType t v a) (DType t v a)
deriving instance Show a => Show (FunctionType v a)

data Attr = Attr { inlineDef :: Bool, fnMacro :: Bool } deriving (Eq, Ord, Show, Generic)

instance Binary Attr

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


data Definition e a
  = forall t. (Pretty a, Pretty (e t ('Suc 'Zero) a))
           => FunDef  Attr FunName (Vec t (TyVarName, Kind)) (DType t 'Zero a) (DType t 'Zero a) (e t ('Suc 'Zero) a)
  | forall t. (Pretty a, Pretty (e t ('Suc 'Zero) a))
           => AbsDecl Attr FunName (Vec t (TyVarName, Kind)) (DType t 'Zero a) (DType t 'Zero a)
  | forall t. (Pretty a, Pretty (e t ('Suc 'Zero) a))
           => TypeDef TypeName (Vec t TyVarName) (Maybe (DType t 'Zero a))
deriving instance Show a => Show (Definition TypedExpr   a)
deriving instance Show a => Show (Definition UntypedExpr a)

type CoreConst e = (VarName, e 'Zero 'Zero VarName)

getDefinitionId :: Definition e a -> String
getDefinitionId (FunDef  _ fn _ _ _ _) = fn
getDefinitionId (AbsDecl _ fn _ _ _  ) = fn
getDefinitionId (TypeDef tn _ _    ) = tn

getFuncId :: Definition e a -> Maybe FunName
getFuncId (FunDef  _ fn _ _ _ _) = Just fn
getFuncId (AbsDecl _ fn _ _ _  ) = Just fn
getFuncId _ = Nothing

getTypeVarNum :: Definition e a -> Int
getTypeVarNum (FunDef  _ _ tvs _ _ _) = Nat.toInt $ Vec.length tvs
getTypeVarNum (AbsDecl _ _ tvs _ _  ) = Nat.toInt $ Vec.length tvs
getTypeVarNum (TypeDef _ tvs _    ) = Nat.toInt $ Vec.length tvs

isDefinitionId :: String -> Definition e a -> Bool
isDefinitionId n d = n == getDefinitionId d

isFuncId :: CoreFunName -> Definition e a -> Bool
isFuncId n (FunDef  _ fn _ _ _ _) = unCoreFunName n == fn
isFuncId n (AbsDecl _ fn _ _ _  ) = unCoreFunName n == fn
isFuncId _ _ = False

isAbsFun :: Definition e a -> Bool
isAbsFun (AbsDecl {}) = True
isAbsFun _ = False

isConFun :: Definition e a -> Bool
isConFun (FunDef {}) = True
isConFun _ = False

isTypeDef :: Definition e a -> Bool
isTypeDef (TypeDef {}) = True
isTypeDef _ = False

isAbsTyp :: Definition e a -> Bool
isAbsTyp (TypeDef _ _ Nothing) = True
isAbsTyp _ = False



insertIdxAtUntypedExpr :: Fin ('Suc v) -> UntypedExpr t v a -> UntypedExpr t ('Suc v) a
insertIdxAtUntypedExpr cut (E e) = E $ insertIdxAtE cut insertIdxAtUntypedExpr e

insertIdxAtTypedExpr :: Fin ('Suc v) -> TypedExpr t v a -> TypedExpr t ('Suc v) a
insertIdxAtTypedExpr cut (TE t e) = TE (insertIdxAtT cut t) (insertIdxAtE cut insertIdxAtTypedExpr e)

insertIdxAtE :: Fin ('Suc v)
             -> (forall v. Fin ('Suc v) -> e t v a -> e t ('Suc v) a)
             -> (Expr t v a e -> Expr t ('Suc v) a e)
insertIdxAtE cut f (Variable v) = Variable $ first (liftIdx cut) v
insertIdxAtE cut f (Fun fn ts nt) = Fun fn (fmap (insertIdxAtT cut) ts) nt
insertIdxAtE cut f (Op opr es) = Op opr $ map (f cut) es
insertIdxAtE cut f (App e1 e2) = App (f cut e1) (f cut e2)
insertIdxAtE cut f (Con tag e t) = Con tag (f cut e) (insertIdxAtT cut t)
insertIdxAtE cut f (Unit) = Unit
insertIdxAtE cut f (ILit n pt) = ILit n pt
insertIdxAtE cut f (SLit s) = SLit s
#ifdef BUILTIN_ARRAYS
insertIdxAtE cut f (ALit es) = ALit $ map (f cut) es
insertIdxAtE cut f (ArrayIndex e l) = ArrayIndex (f cut e) (f cut l)
insertIdxAtE cut f (Pop a e1 e2) = Pop a (f cut e1) (f (FSuc (FSuc cut)) e2)
insertIdxAtE cut f (Singleton e) = Singleton (f cut e)
insertIdxAtE cut f (ArrayPut arr i e) = ArrayPut (f cut arr) (f cut i) (f cut e)
#endif
insertIdxAtE cut f (Let a e1 e2) = Let a (f cut e1) (f (FSuc cut) e2)
insertIdxAtE cut f (LetBang vs a e1 e2) = LetBang (map (first $ liftIdx cut) vs) a (f cut e1) (f (FSuc cut) e2)
insertIdxAtE cut f (Tuple e1 e2) = Tuple (f cut e1) (f cut e2)
insertIdxAtE cut f (Struct fs) = Struct $ map (second $ f cut) fs
insertIdxAtE cut f (If c e1 e2) = If (f cut c) (f cut e1) (f cut e2)
insertIdxAtE cut f (Case c tag (l1,a1,alt) (l2,a2,alts)) =
  Case (f cut c) tag (l1, a1, f (FSuc cut) alt) (l2, a2, f (FSuc cut) alts)
insertIdxAtE cut f (Esac e) = Esac (f cut e)
insertIdxAtE cut f (Split a e1 e2) = Split a (f cut e1) (f (FSuc (FSuc cut)) e2)
insertIdxAtE cut f (Member e fld) = Member (f cut e) fld
insertIdxAtE cut f (Take a rec fld e) = Take a (f cut rec) fld (f (FSuc (FSuc cut)) e)
insertIdxAtE cut f (Put rec fld e) = Put (f cut rec) fld (f cut e)
insertIdxAtE cut f (Promote ty e) = Promote (insertIdxAtT cut ty) (f cut e)
insertIdxAtE cut f (Cast ty e) = Cast (insertIdxAtT cut ty) (f cut e)

insertIdxAtT :: Fin ('Suc v) -> Type t v a UntypedExpr -> Type t ('Suc v) a UntypedExpr
insertIdxAtT cut (TVar v) = TVar v
insertIdxAtT cut (TVarBang v) = TVarBang v
insertIdxAtT cut (TCon tn ts s) = TCon tn (fmap (insertIdxAtT cut) ts) s
insertIdxAtT cut (TFun t1 t2) = TFun (insertIdxAtT cut t1) (insertIdxAtT cut t2)
insertIdxAtT cut (TPrim pt) = TPrim pt
insertIdxAtT cut (TString) = TString
insertIdxAtT cut (TSum alts) = TSum (fmap (second $ first $ insertIdxAtT cut) alts)
insertIdxAtT cut (TProduct t1 t2) = TProduct (insertIdxAtT cut t1) (insertIdxAtT cut t2)
insertIdxAtT cut (TRecord fs s) = TRecord (fmap (second $ first $ insertIdxAtT cut) fs) s
#ifdef BUILTIN_ARRAYS
insertIdxAtT cut (TArray t l s mh) = TArray (insertIdxAtT cut t) l s (fmap (insertIdxAtUntypedExpr cut) mh)
#endif


-- pre-order fold over Expr wrapper
foldEPre :: (Monoid b) => (forall t v. e1 t v a -> Expr t v a e1) -> (forall t v. e1 t v a -> b) -> e1 t v a -> b
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

fmapT :: (forall t v. e1 t v a -> e2 t v a) -> Type t v a e1 -> Type t v a e2
fmapT f (TVar v)             = TVar v
fmapT f (TVarBang v)         = TVarBang v
fmapT f (TCon tn ts s)       = TCon tn (fmap (fmapT f) ts) s
fmapT f (TFun t1 t2)         = TFun (fmapT f t1) (fmapT f t2)
fmapT f (TPrim pt)           = TPrim pt
fmapT f (TString)            = TString
fmapT f (TSum alts)          = TSum (fmap (second $ first $ fmapT f) alts)
fmapT f (TProduct t1 t2)     = TProduct (fmapT f t1) (fmapT f t2)
fmapT f (TRecord fs s)       = TRecord (fmap (second $ first $ fmapT f) fs) s
fmapT f (TUnit)              = TUnit
#ifdef BUILTIN_ARRAYS
fmapT f (TArray t l s mh)    = TArray (fmapT f t) l s (fmap f mh)
#endif

fmapE :: (forall t v. e1 t v a -> e2 t v a) -> Expr t v a e1 -> Expr t v a e2
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


untypeE :: TypedExpr t v a -> UntypedExpr t v a
untypeE (TE _ e) = E $ fmapE untypeE e

untypeD :: Definition TypedExpr a -> Definition UntypedExpr a
untypeD (FunDef  attr fn ts ti to e) = FunDef  attr fn ts ti to (untypeE e)
untypeD (AbsDecl attr fn ts ti to  ) = AbsDecl attr fn ts ti to
untypeD (TypeDef tn ts mt) = TypeDef tn ts mt


instance Functor (Flip (Type t v) e) where  -- map over @a@
  fmap f _ = undefined


instance (Functor (e t v), Functor (e t ('Suc v)), Functor (e t ('Suc ('Suc v))))
  => Functor (Flip (Expr t v) e) where  -- map over @a@
  fmap f (Flip (Variable v)         )      = Flip $ Variable (second f v)
  fmap f (Flip (Fun fn tys nt)      )      = Flip $ Fun fn (fmap (ffmap f) tys) nt
  fmap f (Flip (Op opr es)          )      = Flip $ Op opr (map (fmap f) es)
  fmap f (Flip (App e1 e2)          )      = Flip $ App (fmap f e1) (fmap f e2)
  fmap f (Flip (Con cn e t)         )      = Flip $ Con cn (fmap f e) (ffmap f t)
  fmap f (Flip (Unit)               )      = Flip $ Unit
  fmap f (Flip (ILit i pt)          )      = Flip $ ILit i pt
  fmap f (Flip (SLit s)             )      = Flip $ SLit s
#ifdef BUILTIN_ARRAYS
  fmap f (Flip (ALit es)            )      = Flip $ ALit (map (fmap f) es)
  fmap f (Flip (ArrayIndex e i)     )      = Flip $ ArrayIndex (fmap f e) (fmap f i)
  fmap f (Flip (ArrayMap2 (as,e) (e1,e2))) = Flip $ ArrayMap2 (both f as, fmap f e) (fmap f e1, fmap f e2)
  fmap f (Flip (Pop as e1 e2)       )      = Flip $ Pop (both f as) (fmap f e1) (fmap f e2)
  fmap f (Flip (Singleton e)        )      = Flip $ Singleton (fmap f e)
  fmap f (Flip (ArrayTake as arr fld e))   = Flip $ ArrayTake (both f as) (fmap f arr) (fmap f fld) (fmap f e)
  fmap f (Flip (ArrayPut     arr fld e))   = Flip $ ArrayPut (fmap f arr) (fmap f fld) (fmap f e)
#endif
  fmap f (Flip (Let a e1 e2)        )      = Flip $ Let (f a) (fmap f e1) (fmap f e2)
  fmap f (Flip (LetBang vs a e1 e2) )      = Flip $ LetBang (map (second f) vs) (f a) (fmap f e1) (fmap f e2)
  fmap f (Flip (Tuple e1 e2)        )      = Flip $ Tuple (fmap f e1) (fmap f e2)
  fmap f (Flip (Struct fs)          )      = Flip $ Struct (map (second $ fmap f) fs)
  fmap f (Flip (If e1 e2 e3)        )      = Flip $ If (fmap f e1) (fmap f e2) (fmap f e3)
  fmap f (Flip (Case e tn (l1,a1,e1) (l2,a2,e2))) = Flip $ Case (fmap f e) tn (l1, f a1, fmap f e1) (l2, f a2, fmap f e2)
  fmap f (Flip (Esac e)             )      = Flip $ Esac (fmap f e)
  fmap f (Flip (Split a e1 e2)      )      = Flip $ Split (both f a) (fmap f e1) (fmap f e2)
  fmap f (Flip (Member rec fld)     )      = Flip $ Member (fmap f rec) fld
  fmap f (Flip (Take a rec fld e)   )      = Flip $ Take (both f a) (fmap f rec) fld (fmap f e)
  fmap f (Flip (Put rec fld v)      )      = Flip $ Put (fmap f rec) fld (fmap f v)
  fmap f (Flip (Promote ty e)       )      = Flip $ Promote (ffmap f ty) (fmap f e)
  fmap f (Flip (Cast ty e)          )      = Flip $ Cast (ffmap f ty) (fmap f e)

instance Functor (TypedExpr t v) where
  fmap f (TE t e) = TE (ffmap f t) (ffmap f e)


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

instance Prec (Expr t v a e) where
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

instance (Pretty a, Prec (e t v a), Pretty (e t v a), Pretty (e t ('Suc v) a), Pretty (e t ('Suc ('Suc v)) a))
         => Pretty (Expr t v a e) where
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

instance (Pretty (e t v a)) => Pretty (Type t v a e) where
  pretty (TVar v) = prettyT v
  pretty (TVarBang v) = prettyT v L.<> typesymbol "!"
  pretty (TVarUnboxed v) = typesymbol "#" <> prettyT v
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

instance Pretty (Definition e a) where
  pretty (FunDef _ fn ts t rt e) = funname fn <+> symbol ":" <+> brackets (pretty ts) L.<> symbol "." <+>
                                   parens (pretty t) <+> symbol "->" <+> parens (pretty rt) <+> symbol "=" L.<$>
                                   pretty e
  pretty (AbsDecl _ fn ts t rt) = funname fn <+> symbol ":" <+> brackets (pretty ts) L.<> symbol "." <+>
                                  parens (pretty t) <+> symbol "->" <+> parens (pretty rt)
  pretty (TypeDef tn ts Nothing) = keyword "type" <+> typename tn <+> pretty ts
  pretty (TypeDef tn ts (Just t)) = keyword "type" <+> typename tn <+> pretty ts <+>
                                    symbol "=" <+> pretty t



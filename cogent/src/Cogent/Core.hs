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
import Data.Fin
import Data.Nat (Nat(Zero, Suc), natToInt)
import qualified Data.Nat as Nat
import Data.Vec hiding (splitAt, length, zipWith, zip, unzip)
import qualified Data.Vec as Vec
import qualified Data.Map as M

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

data Type t b
  = TVar (Fin t)
  | TVarBang (Fin t)
  | TVarUnboxed (Fin t)
  | TCon TypeName [Type t b] (Sigil ()) -- Layout will be nothing for abstract types
  | TFun (Type t b) (Type t b)
  | TPrim PrimInt
  | TString
  | TSum [(TagName, (Type t b, Bool))]  -- True means taken (since 2.0.4)
  | TProduct (Type t b) (Type t b)
  | TRecord RecursiveParameter [(FieldName, (Type t b, Bool))] (Sigil (DataLayout BitRange))
    -- True means taken, Layout will be nothing for abstract types
  | TUnit
  | TRPar     RecParName (RecContext (Type t b))
  | TRParBang RecParName (RecContext (Type t b))
-- #ifdef BUILTIN_ARRAYS
  | TArray (Type t b) (LExpr t b) (Sigil (DataLayout BitRange)) (Maybe (LExpr t b))  -- the hole
  | TRefine (Type t b) (LExpr t b)
-- #endif
    -- The sigil specifies the layout of the element
  | TBuffer Integer (DType t b)
  deriving (Show, Eq, Ord, Functor)

data DType t b
  = DRecord [(FieldName, DType t b)]
  | DArray FieldName (DType t b)
  | Type (Type t b)
  deriving (Show, Eq, Ord, Functor)

deriving instance Generic b => Generic (Type 'Zero b)
deriving instance Generic b => Generic (DType 'Zero b)

instance (Generic b, Binary b) => Binary (Type 'Zero b)
instance (Generic b, Binary b) => Binary (DType 'Zero b)


data SupposedlyMonoType b = forall (t :: Nat) (v :: Nat). SMT (Type t b)

isTVar :: Type t b -> Bool
isTVar (TVar _) = True
isTVar _ = False

isTFun :: Type t b -> Bool
isTFun (TFun {}) = True
isTFun _ = False

isTRecord :: Type t b -> Bool
isTRecord (TRecord {}) = True
isTRecord _ = False

recordHasLayout :: Type t b -> Bool
recordHasLayout (TRecord _ _ (Boxed _ Layout{})) = True
recordHasLayout _ = False

-- ASSUME: input in a record type
recordFields :: Type t b -> [FieldName]
recordFields (TRecord _ fs _) = map fst fs
recordFields _ = __impossible "recordsFields: not a record type"

isUnboxed :: Type t b -> Bool
isUnboxed (TCon _ _ Unboxed) = True
isUnboxed (TRecord _ _ Unboxed) =  True
#ifdef BUILTIN_ARRAYS
isUnboxed (TArray _ _ Unboxed _) = True
#endif
#ifdef REFINEMENT_TYPES
isUnboxed (TRefine t _) = isUnboxed t
#endif
isUnboxed _ = False

unroll :: RecParName -> RecContext (Type t b) -> Type t b
unroll v (Just ctxt) = erp (Just ctxt) (ctxt M.! v)
  where
    -- Embed rec pars
    erp :: RecContext (Type t b) -> Type t b -> Type t b
    erp c (TCon n ts s) = TCon n (map (erp c) ts) s
    erp c (TFun t1 t2) = TFun (erp c t1) (erp c t2)
    erp c (TSum r) = TSum $ map (\(a,(t,b)) -> (a, (erp c t, b))) r
    erp c (TProduct t1 t2) = TProduct (erp c t1) (erp c t2)
    erp (Just c) t@(TRecord rp fs s) =
      let c' = case rp of Rec v -> M.insert v t c; _ -> c
      in TRecord rp (map (\(a,(t,b)) -> (a, (erp (Just c') t, b))) fs) s
    -- Context must be Nothing at this point
    erp c (TRPar v Nothing) = TRPar v c
#ifdef BUILTIN_ARRAYS
    erp c (TArray t e s h) = TArray (erp c t) e s h
#endif
    erp _ t = t
unroll v _ = __impossible "unroll in core given an empty context - this usually means a recursive parameter was not unrolled before being used"

data FunNote = NoInline | InlineMe | MacroCall | InlinePlease  -- order is important, larger value has stronger precedence
             deriving (Bounded, Eq, Ord, Show)

data Expr t v a b e
  = Variable (Fin v, a)
  | Fun CoreFunName [Type t b] [DataLayout BitRange] FunNote  -- here do we want to keep partial application and infer again? / zilinc
  | Op Op [e t v a b]
  | App (e t v a b) (e t v a b)
  | Con TagName (e t v a b) (Type t b)
  | Unit
  | ILit Integer PrimInt
  | SLit String
#ifdef BUILTIN_ARRAYS
  | ALit [e t v a b]
  | ArrayIndex (e t v a b) (e t v a b)
  | Pop (a, a) (e t v a b) (e t ('Suc ('Suc v)) a b)
  | Singleton (e t v a b)  -- extracting the element out of a singleton array
  | ArrayMap2 ((a, a), e t ('Suc ('Suc v)) a b) (e t v a b, e t v a b)
  | ArrayTake (a, a) (e t v a b) (e t v a b) (e t ('Suc ('Suc v)) a b)
          -- \ ^^^ The first is the taken object, and the second is the array
  | ArrayPut (e t v a b) (e t v a b) (e t v a b)
#endif
  | Let a (e t v a b) (e t ('Suc v) a b)
  | LetBang [(Fin v, a)] a (e t v a b) (e t ('Suc v) a b)
  | Tuple (e t v a b) (e t v a b)
  | Struct [(FieldName, e t v a b)]  -- unboxed record
  | If (e t v a b) (e t v a b) (e t v a b)   -- technically no longer needed as () + () == Bool
  | Case (e t v a b) TagName (Likelihood, a, e t ('Suc v) a b) (Likelihood, a, e t ('Suc v) a b)
  | Esac (e t v a b)
  | Split (a, a) (e t v a b) (e t ('Suc ('Suc v)) a b)
  | Member (e t v a b) FieldIndex
  | Take (a, a) (e t v a b) FieldIndex (e t ('Suc ('Suc v)) a b)
     -- \ ^^^ The first is the taken field, and the second is the record
  | Put (e t v a b) FieldIndex (e t v a b)
  | Promote (Type t b) (e t v a b)  -- only for guiding the tc. rep. unchanged.
  | Cast (Type t b) (e t v a b)  -- only for integer casts. rep. changed
  | Buffer Integer [(FieldName, e t v a b)]
-- \ vvv constraint no smaller than header, thus UndecidableInstances
deriving instance (Show a, Show b, Show (e t v a b), Show (e t ('Suc v) a b), Show (e t ('Suc ('Suc v)) a b))
  => Show (Expr t v a b e)
deriving instance (Eq a, Eq b, Eq (e t v a b), Eq (e t ('Suc v) a b), Eq (e t ('Suc ('Suc v)) a b))
  => Eq  (Expr t v a b e)
deriving instance (Ord a, Ord b, Ord (e t v a b), Ord (e t ('Suc v) a b), Ord (e t ('Suc ('Suc v)) a b))
  => Ord (Expr t v a b e)

-- NOTE: We leave these logic expressions here even when the --builtin-arrays
-- flag is off. The reason is that, without it, the type class instance
-- derivings don't work. It's very mysterious to me. / zilinc
data LExpr t b
  = LVariable (Nat, b)
  | LFun CoreFunName [Type t b] [DataLayout BitRange]
  | LOp Op [LExpr t b]
  | LApp (LExpr t b) (LExpr t b)
  | LCon TagName (LExpr t b) (Type t b)
  | LUnit
  | LILit Integer PrimInt
  | LSLit String
  | LLet b (LExpr t b) (LExpr t b)
  | LLetBang [(Nat, b)] b (LExpr t b) (LExpr t b)
  | LTuple (LExpr t b) (LExpr t b)
  | LStruct [(FieldName, LExpr t b)]  -- unboxed record
  | LIf (LExpr t b) (LExpr t b) (LExpr t b)   -- technically no longer needed as () + () == Bool
  | LCase (LExpr t b) TagName (b, LExpr t b) (b, LExpr t b)
  | LEsac (LExpr t b)
  | LSplit (b, b) (LExpr t b) (LExpr t b)
  | LMember (LExpr t b) FieldIndex
  | LTake (b, b) (LExpr t b) FieldIndex (LExpr t b)
     -- \ ^^^ The first is the record, and the second is the taken field
  | LPut (LExpr t b) FieldIndex (LExpr t b)
  | LPromote (Type t b) (LExpr t b)  -- only for guiding the tc. rep. unchanged.
  | LCast (Type t b) (LExpr t b)
  deriving (Show, Eq, Ord, Functor, Generic)

instance (Binary b, Generic b) => Binary (LExpr 'Zero b)

#ifdef BUILTIN_ARRAYS
exprToLExpr :: (a -> b)
            -> ((a -> b) -> e t v a b -> LExpr t b)
            -> ((a -> b) -> e t ('Suc v) a b -> LExpr t b)
            -> ((a -> b) -> e t ('Suc ('Suc v)) a b -> LExpr t b)
            -> Expr t v a b e -> LExpr t b
exprToLExpr fab f f1 f2 = \case
  Variable v         -> LVariable (second fab $ first finNat v)
  Fun fn ts ls nt    -> LFun fn ts ls
  Op opr es          -> LOp opr (map f' es)
  App e1 e2          -> LApp (f' e1) (f' e2)
  Con cn e t         -> LCon cn (f' e) t
  Unit               -> LUnit
  ILit i pt          -> LILit i pt
  SLit s             -> LSLit s
  ALit {}            -> __impossible "array expressions in types not allowed"
  ArrayIndex {}      -> __impossible "array expressions in types not allowed"
  ArrayMap2 {}       -> __impossible "array expressions in types not allowed"
  Pop {}             -> __impossible "array expressions in types not allowed"
  Singleton {}       -> __impossible "array expressions in types not allowed"
  ArrayTake {}       -> __impossible "array expressions in types not allowed"
  ArrayPut {}        -> __impossible "array expressions in types not allowed"
  Let a e1 e2        -> LLet (fab a) (f' e1) (f1' e2)
  LetBang vs a e1 e2 -> LLetBang (map (second fab . first finNat) vs) (fab a) (f' e1) (f1' e2)
  Tuple e1 e2        -> LTuple (f' e1) (f' e2)
  Struct fs          -> LStruct (map (second f') fs)
  If e1 e2 e3        -> LIf (f' e1) (f' e2) (f' e3)
  Case e tn (l1,a1,e1) (l2,a2,e2) -> LCase (f' e) tn (fab a1, f1' e1) (fab a2, f1' e2)
  Esac e             -> LEsac (f' e)
  Split a e1 e2      -> LSplit (both fab a) (f' e1) (f2' e2)
  Member rec fld     -> LMember (f' rec) fld
  Take a rec fld e   -> LTake (both fab a) (f' rec) fld (f2' e)
  Put rec fld v      -> LPut (f' rec) fld (f' v)
  Promote ty e       -> LPromote ty (f' e)
  Cast ty e          -> LCast ty (f' e)
 where
  f'  = f  fab
  f1' = f1 fab
  f2' = f2 fab

texprToLExpr :: (a -> b) -> TypedExpr t v a b -> LExpr t b
texprToLExpr f (TE _ e) = exprToLExpr f texprToLExpr texprToLExpr texprToLExpr e

uexprToLExpr :: (a -> b) -> UntypedExpr t v a b -> LExpr t b
uexprToLExpr f (E e) = exprToLExpr f uexprToLExpr uexprToLExpr uexprToLExpr e
#endif

data UntypedExpr t v a b = E  (Expr t v a b UntypedExpr) deriving (Show, Eq, Ord)
data TypedExpr   t v a b = TE { exprType :: Type t b , exprExpr :: Expr t v a b TypedExpr }
                         deriving (Show, Eq, Ord)

data FunctionType b = forall t l. FT (Vec t Kind) (Vec l (Type t b)) (Type t b) (Type t b)
deriving instance Show a => Show (FunctionType a)

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


data Definition e a b
  = forall t l. (Pretty a, Pretty b, Pretty (e t ('Suc 'Zero) a b))
             => FunDef  Attr FunName (Vec t (TyVarName, Kind)) (Vec l (DLVarName, Type t b)) (Type t b) (Type t b) (e t ('Suc 'Zero) a b)
  | forall t l. AbsDecl Attr FunName (Vec t (TyVarName, Kind)) (Vec l (DLVarName, Type t b)) (Type t b) (Type t b)
  | forall t. TypeDef TypeName (Vec t TyVarName) (Maybe (Type t b))
deriving instance (Show a, Show b) => Show (Definition TypedExpr   a b)
deriving instance (Show a, Show b) => Show (Definition UntypedExpr a b)

type CoreConst e = (VarName, e 'Zero 'Zero VarName VarName)

getDefinitionId :: Definition e a b -> String
getDefinitionId (FunDef  _ fn _ _ _ _ _) = fn
getDefinitionId (AbsDecl _ fn _ _ _ _  ) = fn
getDefinitionId (TypeDef tn _ _    ) = tn

getFuncId :: Definition e a b -> Maybe FunName
getFuncId (FunDef  _ fn _ _ _ _ _) = Just fn
getFuncId (AbsDecl _ fn _ _ _ _  ) = Just fn
getFuncId _ = Nothing

getTypeVarNum :: Definition e a b -> Int
getTypeVarNum (FunDef  _ _ tvs _ _ _ _) = Nat.toInt $ Vec.length tvs
getTypeVarNum (AbsDecl _ _ tvs _ _ _  ) = Nat.toInt $ Vec.length tvs
getTypeVarNum (TypeDef _ tvs _        ) = Nat.toInt $ Vec.length tvs

getLayoutVarNum :: Definition e a b -> Int
getLayoutVarNum (FunDef  _ _ _ lvs _ _ _) = Nat.toInt $ Vec.length lvs
getLayoutVarNum (AbsDecl _ _ _ lvs _ _  ) = Nat.toInt $ Vec.length lvs
getLayoutVarNum (TypeDef _ _ _          ) = 0

isDefinitionId :: String -> Definition e a b -> Bool
isDefinitionId n d = n == getDefinitionId d

isFuncId :: CoreFunName -> Definition e a b -> Bool
isFuncId n (FunDef  _ fn _ _ _ _ _) = unCoreFunName n == fn
isFuncId n (AbsDecl _ fn _ _ _ _  ) = unCoreFunName n == fn
isFuncId _ _ = False

isAbsFun :: Definition e a b -> Bool
isAbsFun (AbsDecl {}) = True
isAbsFun _ = False

isConFun :: Definition e a b -> Bool
isConFun (FunDef {}) = True
isConFun _ = False

isTypeDef :: Definition e a b -> Bool
isTypeDef (TypeDef {}) = True
isTypeDef _ = False

isAbsTyp :: Definition e a b -> Bool
isAbsTyp (TypeDef _ _ Nothing) = True
isAbsTyp _ = False

insertIdxAtType :: Nat -> Type t b -> Type t b
insertIdxAtType cut t = __fixme t

insertIdxAtUntypedExpr :: Fin ('Suc v) -> UntypedExpr t v a b -> UntypedExpr t ('Suc v) a b
insertIdxAtUntypedExpr cut (E e) = E $ insertIdxAtE cut insertIdxAtUntypedExpr e

insertIdxAtTypedExpr :: Fin ('Suc v) -> TypedExpr t v a b -> TypedExpr t ('Suc v) a b
insertIdxAtTypedExpr cut (TE t e) = TE (insertIdxAtType (finNat cut) t) (insertIdxAtE cut insertIdxAtTypedExpr e)

insertIdxAtE :: Fin ('Suc v)
             -> (forall v. Fin ('Suc v) -> e t v a b -> e t ('Suc v) a b)
             -> (Expr t v a b e -> Expr t ('Suc v) a b e)
insertIdxAtE cut f (Variable v) = Variable $ first (liftIdx cut) v
insertIdxAtE cut f (Fun fn ts ls nt) = Fun fn ts ls nt
insertIdxAtE cut f (Op opr es) = Op opr $ map (f cut) es
insertIdxAtE cut f (App e1 e2) = App (f cut e1) (f cut e2)
insertIdxAtE cut f (Con tag e t) = Con tag (f cut e) t
insertIdxAtE cut f (Unit) = Unit
insertIdxAtE cut f (ILit n pt) = ILit n pt
insertIdxAtE cut f (SLit s) = SLit s
#ifdef BUILTIN_ARRAYS
insertIdxAtE cut f (ALit es) = ALit $ map (f cut) es
insertIdxAtE cut f (ArrayIndex e l) = ArrayIndex (f cut e) (f cut l)
insertIdxAtE cut f (Pop a e1 e2) = Pop a (f cut e1) (f (FSuc (FSuc cut)) e2)
insertIdxAtE cut f (Singleton e) = Singleton (f cut e)
insertIdxAtE cut f (ArrayPut arr i e) = ArrayPut (f cut arr) (f cut i) (f cut e)
insertIdxAtE cut f (ArrayTake (o, ca) pa i e) = ArrayTake (o, ca) (f cut pa) (f cut i) (f (FSuc (FSuc cut)) e)
#endif
insertIdxAtE cut f (Let a e1 e2) = Let a (f cut e1) (f (FSuc cut) e2)
insertIdxAtE cut f (LetBang vs a e1 e2) = LetBang (map (first $ liftIdx cut) vs) a (f cut e1) (f (FSuc cut) e2)
insertIdxAtE cut f (Tuple e1 e2) = Tuple (f cut e1) (f cut e2)
insertIdxAtE cut f (Struct fs) = Struct $ map (second $ f cut) fs
insertIdxAtE cut f (If c e1 e2) = If (f cut c) (f cut e1) (f cut e2)
insertIdxAtE cut f (Case c tag (l1,a1,alt) (l2,a2,alts)) = Case (f cut c) tag (l1, a1, f (FSuc cut) alt) (l2, a2, f (FSuc cut) alts)
insertIdxAtE cut f (Esac e) = Esac (f cut e)
insertIdxAtE cut f (Split a e1 e2) = Split a (f cut e1) (f (FSuc (FSuc cut)) e2)
insertIdxAtE cut f (Member e fld) = Member (f cut e) fld
insertIdxAtE cut f (Take a rec fld e) = Take a (f cut rec) fld (f (FSuc (FSuc cut)) e)
insertIdxAtE cut f (Put rec fld e) = Put (f cut rec) fld (f cut e)
insertIdxAtE cut f (Promote ty e) = Promote ty (f cut e)
insertIdxAtE cut f (Cast ty e) = Cast ty (f cut e)
insertIdxAtE cut f (Buffer n fs) = Buffer n $ map (second $ f cut) fs


-- pre-order fold over Expr wrapper
foldEPre :: (Monoid m)
         => (forall t v. e1 t v a b -> Expr t v a b e1)
         -> (forall t v. e1 t v a b -> m)
         -> e1 t v a b
         -> m
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
  (Buffer _ fs)       -> mconcat $ f e : map (foldEPre unwrap f . snd) fs


fmapE :: (forall t v. e1 t v a b -> e2 t v a b) -> Expr t v a b e1 -> Expr t v a b e2
fmapE f (Variable v)         = Variable v
fmapE f (Fun fn ts ls nt)    = Fun fn ts ls nt
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
fmapE f (Buffer n fs)        = Buffer n (map (second f) fs)


untypeE :: TypedExpr t v a b -> UntypedExpr t v a b
untypeE (TE _ e) = E $ fmapE untypeE e

untypeD :: Definition TypedExpr a b -> Definition UntypedExpr a b
untypeD (FunDef  attr fn ts ls ti to e) = FunDef  attr fn ts ls ti to (untypeE e)
untypeD (AbsDecl attr fn ts ls ti to  ) = AbsDecl attr fn ts ls ti to
untypeD (TypeDef tn ts mt) = TypeDef tn ts mt

instance (Functor (e t v a),
          Functor (e t ('Suc v) a),
          Functor (e t ('Suc ('Suc v)) a))
       => Functor (Flip (Expr t v a) e) where  -- map over @b@
  fmap f (Flip (Variable v)         )      = Flip $ Variable v
  fmap f (Flip (Fun fn ts ls nt)    )      = Flip $ Fun fn (fmap (fmap f) ts) ls nt
  fmap f (Flip (Op opr es)          )      = Flip $ Op opr (fmap (fmap f) es)
  fmap f (Flip (App e1 e2)          )      = Flip $ App (fmap f e1) (fmap f e2)
  fmap f (Flip (Con cn e t)         )      = Flip $ Con cn (fmap f e) (fmap f t)
  fmap f (Flip (Unit)               )      = Flip $ Unit
  fmap f (Flip (ILit i pt)          )      = Flip $ ILit i pt
  fmap f (Flip (SLit s)             )      = Flip $ SLit s
#ifdef BUILTIN_ARRAYS
  fmap f (Flip (ALit es)            )      = Flip $ ALit (fmap (fmap f) es)
  fmap f (Flip (ArrayIndex e i)     )      = Flip $ ArrayIndex (fmap f e) (fmap f i)
  fmap f (Flip (ArrayMap2 (as,e) (e1,e2))) = Flip $ ArrayMap2 (as, fmap f e) (fmap f e1, fmap f e2)
  fmap f (Flip (Pop as e1 e2)       )      = Flip $ Pop as (fmap f e1) (fmap f e2)
  fmap f (Flip (Singleton e)        )      = Flip $ Singleton (fmap f e)
  fmap f (Flip (ArrayTake as arr fld e))   = Flip $ ArrayTake as (fmap f arr) (fmap f fld) (fmap f e)
  fmap f (Flip (ArrayPut     arr fld e))   = Flip $ ArrayPut (fmap f arr) (fmap f fld) (fmap f e)
#endif
  fmap f (Flip (Let a e1 e2)        )      = Flip $ Let a (fmap f e1) (fmap f e2)
  fmap f (Flip (LetBang vs a e1 e2) )      = Flip $ LetBang vs a (fmap f e1) (fmap f e2)
  fmap f (Flip (Tuple e1 e2)        )      = Flip $ Tuple (fmap f e1) (fmap f e2)
  fmap f (Flip (Struct fs)          )      = Flip $ Struct (map (second $ fmap f) fs)
  fmap f (Flip (If e1 e2 e3)        )      = Flip $ If (fmap f e1) (fmap f e2) (fmap f e3)
  fmap f (Flip (Case e tn (l1,a1,e1) (l2,a2,e2))) = Flip $ Case (fmap f e) tn (l1, a1, fmap f e1) (l2, a2, fmap f e2)
  fmap f (Flip (Esac e)             )      = Flip $ Esac (fmap f e)
  fmap f (Flip (Split a e1 e2)      )      = Flip $ Split a (fmap f e1) (fmap f e2)
  fmap f (Flip (Member rec fld)     )      = Flip $ Member (fmap f rec) fld
  fmap f (Flip (Take a rec fld e)   )      = Flip $ Take a (fmap f rec) fld (fmap f e)
  fmap f (Flip (Put rec fld v)      )      = Flip $ Put (fmap f rec) fld (fmap f v)
  fmap f (Flip (Promote ty e)       )      = Flip $ Promote (fmap f ty) (fmap f e)
  fmap f (Flip (Cast ty e)          )      = Flip $ Cast (fmap f ty) (fmap f e)
  fmap f (Flip (Buffer n fs)        )      = Flip $ Buffer n (map (second $ fmap f) fs)

instance (Functor (Flip (e t v) b),
          Functor (Flip (e t ('Suc v)) b),
          Functor (Flip (e t ('Suc ('Suc v))) b))
       => Functor (Flip2 (Expr t v) e b) where  -- map over @a@
  fmap f (Flip2 (Variable v)         )      = Flip2 $ Variable (second f v)
  fmap f (Flip2 (Fun fn ts ls nt)    )      = Flip2 $ Fun fn ts ls nt
  fmap f (Flip2 (Op opr es)          )      = Flip2 $ Op opr (fmap (ffmap f) es)
  fmap f (Flip2 (App e1 e2)          )      = Flip2 $ App (ffmap f e1) (ffmap f e2)
  fmap f (Flip2 (Con cn e t)         )      = Flip2 $ Con cn (ffmap f e) t
  fmap f (Flip2 (Unit)               )      = Flip2 $ Unit
  fmap f (Flip2 (ILit i pt)          )      = Flip2 $ ILit i pt
  fmap f (Flip2 (SLit s)             )      = Flip2 $ SLit s
#ifdef BUILTIN_ARRAYS
  fmap f (Flip2 (ALit es)            )      = Flip2 $ ALit (fmap (ffmap f) es)
  fmap f (Flip2 (ArrayIndex e i)     )      = Flip2 $ ArrayIndex (ffmap f e) (ffmap f i)
  fmap f (Flip2 (ArrayMap2 (as,e) (e1,e2))) = Flip2 $ ArrayMap2 (both f as, ffmap f e) (ffmap f e1, ffmap f e2)
  fmap f (Flip2 (Pop as e1 e2)       )      = Flip2 $ Pop (both f as) (ffmap f e1) (ffmap f e2)
  fmap f (Flip2 (Singleton e)        )      = Flip2 $ Singleton (ffmap f e)
  fmap f (Flip2 (ArrayTake as arr fld e))   = Flip2 $ ArrayTake (both f as) (ffmap f arr) (ffmap f fld) (ffmap f e)
  fmap f (Flip2 (ArrayPut     arr fld e))   = Flip2 $ ArrayPut (ffmap f arr) (ffmap f fld) (ffmap f e)
#endif
  fmap f (Flip2 (Let a e1 e2)        )      = Flip2 $ Let (f a) (ffmap f e1) (ffmap f e2)
  fmap f (Flip2 (LetBang vs a e1 e2) )      = Flip2 $ LetBang (map (second f) vs) (f a) (ffmap f e1) (ffmap f e2)
  fmap f (Flip2 (Tuple e1 e2)        )      = Flip2 $ Tuple (ffmap f e1) (ffmap f e2)
  fmap f (Flip2 (Struct fs)          )      = Flip2 $ Struct (map (second $ ffmap f) fs)
  fmap f (Flip2 (If e1 e2 e3)        )      = Flip2 $ If (ffmap f e1) (ffmap f e2) (ffmap f e3)
  fmap f (Flip2 (Case e tn (l1,a1,e1) (l2,a2,e2))) = Flip2 $ Case (ffmap f e) tn (l1, f a1, ffmap f e1) (l2, f a2, ffmap f e2)
  fmap f (Flip2 (Esac e)             )      = Flip2 $ Esac (ffmap f e)
  fmap f (Flip2 (Split a e1 e2)      )      = Flip2 $ Split (both f a) (ffmap f e1) (ffmap f e2)
  fmap f (Flip2 (Member rec fld)     )      = Flip2 $ Member (ffmap f rec) fld
  fmap f (Flip2 (Take a rec fld e)   )      = Flip2 $ Take (both f a) (ffmap f rec) fld (ffmap f e)
  fmap f (Flip2 (Put rec fld v)      )      = Flip2 $ Put (ffmap f rec) fld (ffmap f v)
  fmap f (Flip2 (Promote ty e)       )      = Flip2 $ Promote ty (ffmap f e)
  fmap f (Flip2 (Cast ty e)          )      = Flip2 $ Cast ty (ffmap f e)
  fmap f (Flip2 (Buffer n fs)        )      = Flip2 $ Buffer n (map (second $ ffmap f) fs)

instance Functor (Flip (TypedExpr t v) b) where  -- over @a@
  fmap f (Flip (TE t e)) = Flip $ TE t (fffmap f e)


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

instance Prec (Expr t v a b e) where
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

instance Prec (TypedExpr t v a b) where
  prec (TE _ e) = prec e

instance Prec (UntypedExpr t v a b) where
  prec (E e) = prec e

#ifdef BUILTIN_ARRAYS
instance Prec (LExpr t b) where
  prec (LOp opr [_,_]) = prec (associativity opr)
  prec (LILit {}) = 0
  prec (LSLit {}) = 0
  prec (LVariable {}) = 0
  prec (LFun {}) = 0
  prec (LApp {}) = 1
  prec (LTuple {}) = 0
  prec (LCon {}) = 0
  prec (LEsac {}) = 0
  prec (LMember {}) = 0
  prec (LTake {}) = 0
  prec (LPut {}) = 1
  prec (LPromote {}) = 0
  prec (LCast {}) = 0
  prec _ = 100
#endif

prettyV = dullblue  . string . ("_v" ++) . show . finInt
prettyT = dullgreen . string . ("_t" ++) . show . finInt

instance (Pretty a, Pretty b) => Pretty (TypedExpr t v a b) where
  pretty (TE t e) | not __cogent_fshow_types_in_pretty = pretty e
                  | otherwise = parens (pretty e <+> symbol ":" <+> pretty t)

instance (Pretty a, Pretty b) => Pretty (UntypedExpr t v a b) where
  pretty (E e) = pretty e

instance (Pretty a, Pretty b, Prec (e t v a b), Pretty (e t v a b), Pretty (e t ('Suc v) a b), Pretty (e t ('Suc ('Suc v)) a b))
         => Pretty (Expr t v a b e) where
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
  pretty (ArrayTake (o, ca) pa i e) = align (keyword "take" <+> pretty ca <+> symbol "@" <> record [symbol "@" <> pretty i <+>
                                             symbol "=" <+> pretty o] <+> symbol "=" <+> (prettyPrec 1 pa) L.<$> keyword "in" <+> pretty e)
#endif
  pretty (Variable x) = pretty (snd x) L.<> angles (prettyV $ fst x)
  pretty (Fun fn ts ls nt) = pretty nt L.<> funname (unCoreFunName fn) <+> pretty ts <+> pretty ls
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
  pretty (Buffer n fs)
    | length fs == 0 = initial <+> symbol "(" <> symbol ")"
    | otherwise = initial <+> symbol "#" L.<> record (map (\(n, e) -> fieldname n <+> symbol "=" <+> pretty e) fs)
    where
      initial = keyword "Buffer" <+> pretty n

instance Pretty FunNote where
  pretty NoInline = empty
  pretty InlineMe = comment "{-# INLINE #-}" <+> empty
  pretty MacroCall = comment "{-# FNMACRO #-}" <+> empty
  pretty InlinePlease = comment "inline" <+> empty

instance (Pretty b) => Pretty (Type t b) where
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
  pretty (TRecord rp fs s) = pretty rp <+> record (map (\(f,(t,b)) -> fieldname f <+> symbol ":" L.<> prettyTaken b <+> pretty t) fs)
                          <> pretty s
  pretty (TCon tn [] s) = typename tn <> pretty s
  pretty (TCon tn ts s) = typename tn <> pretty s <+> typeargs (map pretty ts)
  pretty (TRPar v m) = keyword "rec" <+> typevar v
#ifdef BUILTIN_ARRAYS
  pretty (TArray t l s mhole) = (pretty t <> brackets (pretty l) <+> pretty s) &
    (case mhole of Nothing -> id; Just hole -> (<+> keyword "take" <+> parens (pretty hole)))
#endif
#ifdef REFINEMENT_TYPES
  pretty (TRefine t p) = braces (pretty t <+> symbol "|" <+> pretty p)
#endif
  pretty (TBuffer n dt) = keyword "Buffer" <+> brackets (string $ show n) <+> pretty dt

typeToDType :: Type t b -> DType t b
typeToDType (TRecord _ fs _) = DRecord (map (\(f, (t, b)) -> (f, typeToDType t)) fs)
-- typeToDType (TArray t le s mle) = DArray (typeToDType t) le s mle
typeToDType t = Type t

-- dTypetoType :: DType t b -> Type t b
-- dTypetoType (DRecord fs) = TRecord NonRec (map (\(f, (t, b)) -> (f, (dTypetoType t, b))) fs) Unboxed
-- dTypetoType (DArray t le s mle) = TArray (dTypetoType t) le s mle
-- dTypetoType (Type t) = t

instance (Pretty b) => Pretty (DType t b) where
  pretty (DRecord fs) = typesymbol "#" <> record (map (\(f, t) -> fieldname f <+> symbol ":" <+> pretty t) fs)
  pretty (DArray f dt) = keyword "DArray" <+> fieldname f <+> pretty dt
  pretty (Type t) = pretty t

prettyTaken :: Bool -> Doc
prettyTaken True  = symbol "*"
prettyTaken False = empty

#ifdef BUILTIN_ARRAYS
instance (Pretty b) => Pretty (LExpr t b) where
  pretty (LOp opr [a,b])
     | LeftAssoc  l <- associativity opr = prettyPrec (l+1) a <+> primop opr <+> prettyPrec l b
     | RightAssoc l <- associativity opr = prettyPrec l a <+> primop opr <+> prettyPrec (l+1)  b
     | NoAssoc    l <- associativity opr = prettyPrec l a <+> primop opr <+> prettyPrec l  b
  pretty (LOp opr [e]) = primop opr <+> prettyPrec 1 e
  pretty (LOp opr es)  = primop opr <+> tupled (map pretty es)
  pretty (LILit i pt) = literal (string $ show i) <+> symbol "::" <+> pretty pt
  pretty (LSLit s) = literal $ string s
  pretty (LVariable x) = pretty (snd x) L.<> angles (L.int . natToInt $ fst x)
  pretty (LFun fn ts ls) = funname (unCoreFunName fn) <+> pretty ts <+> pretty ls
  pretty (LApp a b) = prettyPrec 2 a <+> prettyPrec 1 b
  pretty (LLet a e1 e2) = align (keyword "let" <+> pretty a <+> symbol "=" <+> pretty e1 L.<$>
                                keyword "in" <+> pretty e2)
  pretty (LLetBang bs a e1 e2) = align (keyword "let!" <+> tupled (map (L.int . natToInt . fst) bs) <+> pretty a <+> symbol "=" <+> pretty e1 L.<$>
                                       keyword "in" <+> pretty e2)
  pretty (LUnit) = tupled []
  pretty (LTuple e1 e2) = tupled (map pretty [e1, e2])
  pretty (LStruct fs) = symbol "#" L.<> record (map (\(n,e) -> fieldname n <+> symbol "=" <+> pretty e) fs)
  pretty (LCon tn e t) = parens (tagname tn <+> prettyPrec 1 e) <+> symbol "::" <+> pretty t
  pretty (LIf c t e) = group . align $ (keyword "if" <+> pretty c
                                       L.<$> indent (keyword "then" </> align (pretty t))
                                       L.<$> indent (keyword "else" </> align (pretty e)))
  pretty (LCase e tn (v1,a1) (v2,a2)) = align (keyword "case" <+> pretty e <+> keyword "of"
                                               L.<$> indent (tagname tn <+> pretty v1 <+> symbol "->" <+> align (pretty a1))
                                               L.<$> indent (pretty v2 <+> symbol "->" <+> align (pretty a2)))
  pretty (LEsac e) = keyword "esac" <+> parens (pretty e)
  pretty (LSplit (v1,v2) e1 e2) = align (keyword "split" <+> parens (pretty v1 <> comma <> pretty v2) <+> symbol "=" <+> pretty e1 L.<$>
                                  keyword "in" <+> pretty e2)
  pretty (LMember x f) = prettyPrec 1 x L.<> symbol "." L.<> fieldIndex f
  pretty (LTake (a,b) rec f e) = align (keyword "take" <+> tupled [pretty a, pretty b] <+> symbol "="
                                                      <+> prettyPrec 1 rec <+> record (fieldIndex f:[]) L.<$>
                                       keyword "in" <+> pretty e)
  pretty (LPut rec f v) = prettyPrec 1 rec <+> record [fieldIndex f <+> symbol "=" <+> pretty v]
  pretty (LPromote t e) = prettyPrec 1 e <+> symbol ":^:" <+> pretty t
  pretty (LCast t e) = prettyPrec 1 e <+> symbol ":::" <+> pretty t
#endif


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

instance (Pretty a, Pretty b) => Pretty (Definition e a b) where
  pretty (FunDef _ fn ts ls t rt e) = funname fn <+> symbol ":" <+> brackets (pretty ts) <+> braces (pretty ls) L.<> symbol "." <+>
                                      parens (pretty t) <+> symbol "->" <+> parens (pretty rt) <+> symbol "=" L.<$>
                                      pretty e
  pretty (AbsDecl _ fn ts ls t rt) = funname fn <+> symbol ":" <+> brackets (pretty ts) <+> braces (pretty ls) L.<> symbol "." <+>
                                     parens (pretty t) <+> symbol "->" <+> parens (pretty rt)
  pretty (TypeDef tn ts Nothing) = keyword "type" <+> typename tn <+> pretty ts
  pretty (TypeDef tn ts (Just t)) = keyword "type" <+> typename tn <+> pretty ts <+>
                                    symbol "=" <+> pretty t



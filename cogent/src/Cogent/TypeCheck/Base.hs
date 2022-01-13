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
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Cogent.TypeCheck.Base where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Dargent.Allocation
import Cogent.Dargent.TypeCheck
import Cogent.Surface
import Cogent.TypeCheck.ARow hiding (all, null)
import Cogent.TypeCheck.Row (Entry, Row)
import qualified Cogent.TypeCheck.Row as Row
-- import Cogent.TypeCheck.Util
import Cogent.Util

import Control.Applicative (liftA)
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Writer hiding (Alt)
import Control.Monad.Reader
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Data (Data)
import Data.Foldable (all)
import Data.Maybe (fromJust, isJust)
import Data.Either (either, isLeft, lefts, rights)
import Data.Functor.Const
import Data.Functor.Identity
import qualified Data.IntMap as IM
import Data.List (nub, (\\))
import qualified Data.Map as M
import Data.Maybe (maybeToList)
#if __GLASGOW_HASKELL__ < 803
import Data.Monoid ((<>))
#endif
import Data.List (sortOn)
import qualified Data.Sequence as Seq
-- import qualified Data.Set as S
import Text.Parsec.Pos
import Lens.Micro
import Lens.Micro.TH
import Lens.Micro.Mtl

import Debug.Trace

-- -----------------------------------------------------------------------------
-- Typecheck errors, warnings and context
-- -----------------------------------------------------------------------------


data TypeError = FunctionNotFound VarName
               | TooManyTypeArguments FunName (Polytype TCType)
               | TooManyLayoutArguments FunName (Polytype TCType)
               | NotInScope FuncOrVar VarName
               | DuplicateVariableInPattern VarName  -- (Pattern TCName)
               | DifferingNumberOfConArgs TagName Int Int
               -- | DuplicateVariableInIrrefPattern VarName (IrrefutablePattern TCName)
               | UnknownTypeVariable VarName
               | UnknownTypeConstructor TypeName
               | TypeArgumentMismatch TypeName Int Int
               | TypeMismatch TCType TCType
               | RequiredTakenField FieldName TCType
               | TypeNotShareable TCType Metadata
               | TypeNotEscapable TCType Metadata
               | TypeNotDiscardable TCType Metadata
               | PatternsNotExhaustive TCType [TagName]
               | UnsolvedConstraint Constraint (IM.IntMap VarOrigin)
               | RecordWildcardsNotSupported
               | NotAFunctionType TCType
               | DuplicateRecordFields [FieldName]
               | DuplicateTypeVariable [VarName]
               | SuperfluousTypeVariable [VarName]
               | DuplicateLayoutVariable [DLVarName]
               | SuperfluousLayoutVariable [DLVarName]
               | TypeVariableNotDeclared [TyVarName]
               | LayoutVariableNotDeclared [DLVarName]
               | TakeFromNonRecordOrVariant (Maybe [FieldName]) TCType
               | PutToNonRecordOrVariant    (Maybe [FieldName]) TCType
               | TakeNonExistingField FieldName TCType
               | PutNonExistingField  FieldName TCType
               | RecursiveUnboxedRecord RecursiveParameter (Sigil (Maybe DataLayoutExpr)) -- A record that is unboxed yet has a recursive parameter
               | DiscardWithoutMatch TagName
               | RequiredTakenTag TagName
#ifdef BUILTIN_ARRAYS
               | ArithConstraintsUnsatisfiable [TCSExpr] String
               | TakeElementsFromNonArrayType [TCSExpr] TCType
               | PutElementsToNonArrayType [TCSExpr] TCType
#endif
               | CustTyGenIsPolymorphic LocType
               | CustTyGenIsSynonym LocType
               | TypeWarningAsError TypeWarning
               | DataLayoutError DataLayoutTcError
               | LayoutOnNonRecordOrCon TCType
               | LayoutDoesNotMatchType TCDataLayout TCType
               | TypesNotFit TCType TCType
               | LayoutsNotCompatible TCDataLayout TCDataLayout
               | OtherTypeError String
               deriving (Eq, Show, Ord)

isWarnAsError :: TypeError -> Bool
isWarnAsError (TypeWarningAsError _) = True
isWarnAsError _ = False

data TypeWarning = UnusedLocalBind VarName
                 | TakeTakenField  FieldName TCType
                 | PutUntakenField FieldName TCType
                 deriving (Eq, Show, Ord)

type TcLog = Either TypeError TypeWarning
type ContextualisedTcLog = ([ErrorContext], TcLog)  -- high-level context at the end of the list

-- FIXME: More fine-grained context is appreciated. e.g., only show alternatives that don't unify / zilinc
data ErrorContext = InExpression LocExpr TCType
                  | InType SourcePos RawType
                  | InPattern LocPatn
                  | InIrrefutablePattern LocIrrefPatn
                  | ThenBranch | ElseBranch
                  | NthBranch Int  -- MultiWayIf
                  | SolvingConstraint Constraint
                  | NthAlternative Int LocPatn
                  | InDefinition SourcePos (TopLevel LocType LocPatn LocExpr)
                  | AntiquotedType LocType
                  | AntiquotedExpr LocExpr
                  | InAntiquotedCDefn VarName  -- C function or type name
                  | CustomisedCodeGen LocType
                  deriving (Eq, Show)

instance Ord ErrorContext where
  compare _ _ = EQ

isCtxConstraint :: ErrorContext -> Bool
isCtxConstraint (SolvingConstraint _) = True
isCtxConstraint _ = False

data VarOrigin = ExpressionAt SourcePos
               | TermInType RawExpr RawType SourcePos
               | TypeOfExpr RawExpr [VarName] SourcePos
               | TypeOfPatn RawPatn SourcePos
               | TypeOfIrrefPatn RawIrrefPatn SourcePos
               | ImplicitTypeApp SourcePos
               | ImplicitLayoutApp SourcePos
               | TypeHole SourcePos
               | LayoutHole SourcePos
               | UnifyingRows (Row TCType) (Row TCType)
               | SinkFloat TCType TCType TCType      -- SinkFloat t1 t2 t3: s/f t1 to t2 due to t3
               | SinkFloatRow Int (Row TCType) TCType TCType  -- SinkFloat2 x r t1 t2: s/f x to r when comparing t1 and t2
               | SinkFloatEntry (Entry TCType) TCType TCType
               | SinkFloatSigil TCType TCType
               | BoundOf TCType TCType Bound
               | EqualIn TCExpr TCExpr TCType TCType
               | BlockedByType RawType SourcePos
               | BlockedByLayout DataLayoutExpr SourcePos
               | OtherOrigin String
               deriving (Eq, Show, Ord)


-- -----------------------------------------------------------------------------
-- Constraints, metadata
-- -----------------------------------------------------------------------------


data Metadata = Reused { varName :: VarName, boundAt :: SourcePos, usedAt :: Seq.Seq SourcePos }
              | Unused { varName :: VarName, boundAt :: SourcePos }
              | UnusedInOtherBranch { varName :: VarName, boundAt :: SourcePos, usedAt :: Seq.Seq SourcePos }
              | UnusedInThisBranch  { varName :: VarName, boundAt :: SourcePos, usedAt :: Seq.Seq SourcePos }
              | Suppressed
              | UsedInMember { fieldName :: FieldName }
#ifdef BUILTIN_ARRAYS
              | UsedInArrayIndexing
              | MultipleArrayTakePut
#endif
              | UsedInLetBang
              | TypeParam { functionName :: FunName, typeVarName :: TyVarName }
              -- | LayoutParam { expression :: TCExpr, layoutVarName :: DLVarName }
              | ImplicitlyTaken
              | Constant { constName :: ConstName }
              deriving (Eq, Show, Ord)

(>:) = flip (:<)

data Constraint' t l = (:<) t t
                     | (:=:) t t
                     | (:&) (Constraint' t l) (Constraint' t l)
                     | Upcastable t t
                     | Share t Metadata
                     | Drop t Metadata
                     | Escape t Metadata
                     | (:~) l t
                     | (:~<) l l
                     | (:~~) t t  -- t1 :~~ t2 means that t1 can fit in any layout that t2 can fit in
                     | LayoutOk t
                     | (:@) (Constraint' t l) ErrorContext
                     | Unsat TypeError
                     | SemiSat TypeWarning
                     | Sat
                     | Exhaustive t [RawPatn]
                     | UnboxedNotRecursive t
                     | NotReadOnly TCSigil
                     | Solved t
                     | IsPrimType t
#ifdef BUILTIN_ARRAYS
                     | Arith (SExpr t l)
                     | (:==:) (SExpr t l) (SExpr t l)  -- arithmetically equal
                     | (:->) (Constraint' t l) (Constraint' t l)
#endif
                     deriving (Eq, Show, Ord)

type Constraint = Constraint' TCType TCDataLayout


arithTCType :: TCType -> Bool
arithTCType (T (TCon n [] Unboxed)) | n `elem` ["U8", "U16", "U32", "U64", "Bool"] = True
arithTCType (U _) = False
arithTCType _ = False

arithTCExpr :: TCExpr -> Bool
arithTCExpr (TE _ (PrimOp _ es) _) | length es `elem` [1,2] = all arithTCExpr es
arithTCExpr (TE _ (Var _      ) _) = True
arithTCExpr (TE _ (IntLit _   ) _) = True
arithTCExpr (TE _ (BoolLit _  ) _) = True
arithTCExpr (TE _ (Upcast e   ) _) = arithTCExpr e
arithTCExpr (TE _ (Annot e _  ) _) = arithTCExpr e
arithTCExpr _ = False

#ifdef BUILTIN_ARRAYS
splitArithConstraints :: Constraint -> ([TCSExpr], Constraint)
splitArithConstraints (c1 :& c2)
  = let (e1,c1') = splitArithConstraints c1
        (e2,c2') = splitArithConstraints c2
     in (e1 <> e2, c1' <> c2')
splitArithConstraints (c :@ ctx)
  = let (e,c') = splitArithConstraints c
     in (e, c' :@ ctx)
splitArithConstraints (Arith e)  = ([e], Sat)
splitArithConstraints c          = ([], c)

andTCSExprs :: [TCSExpr] -> TCSExpr
andTCSExprs [] = SE (T bool) (BoolLit True)
andTCSExprs (e:es) = SE (T bool) (PrimOp "&&" [e, andTCSExprs es])

implTCSExpr :: TCSExpr -> TCSExpr -> TCSExpr
implTCSExpr e1 e2 = SE (T bool) (PrimOp "||" [notTCSExpr e1, e2])

notTCSExpr :: TCSExpr -> TCSExpr
notTCSExpr e = SE (T bool) (PrimOp "not" [e])
#endif

#if __GLASGOW_HASKELL__ < 803
instance Monoid (Constraint' x y) where
  mempty = Sat
  mappend Sat x = x
  mappend x Sat = x
  -- mappend (Unsat r) x = Unsat r
  -- mappend x (Unsat r) = Unsat r
  mappend x y = x :& y
#else
instance Semigroup (Constraint' x y) where
  Sat <> x = x
  x <> Sat = x
  x <> y = x :& y
instance Monoid (Constraint' x y) where
  mempty = Sat
#endif

instance Bifunctor Constraint' where
  bimap f g (t1 :<  t2)        = (f t1) :<  (f t2)
  bimap f g (t1 :=: t2)        = (f t1) :=: (f t2)
  bimap f g (c1 :&  c2)        = (bimap f g c1) :& (bimap f g c2)
  bimap f g (Upcastable t1 t2) = Upcastable (f t1) (f t2)
  bimap f g (Share t m)        = Share (f t) m
  bimap f g (Drop t m)         = Drop (f t) m
  bimap f g (Escape t m)       = Escape (f t) m
  bimap f g (l  :~  t)         = (g l) :~ (f t)
  bimap f g (l1 :~< l2)        = (g l1) :~< (g l2)
  bimap f g (t1 :~~ t2)        = (f t1) :~~ (f t2)
  bimap f g (c  :@  e)         = (bimap f g c) :@ e
  bimap f g (Exhaustive t ps)  = Exhaustive (f t) ps
  bimap f g (Solved t)         = Solved (f t)
  bimap f g (IsPrimType t)     = IsPrimType (f t)
#ifdef BUILTIN_ARRAYS
  bimap f g (Arith se)         = Arith (bimap f g se)
  bimap f g (e1 :==: e2)       = bimap f g e1 :==: bimap f g e2
  bimap f g (c1 :-> c2)        = (bimap f g c1) :-> (bimap f g c2)
#endif
  bimap f g Sat                = Sat
  bimap f g (SemiSat w)        = SemiSat w
  bimap f g (Unsat e)          = Unsat e

instance Bifoldable Constraint' where
  bifoldMap f g cs = getConst $ bitraverse (Const . f) (Const . g) cs

instance Bitraversable Constraint' where
  bitraverse f g (t1 :<  t2)        = (:<)  <$> f t1 <*> f t2
  bitraverse f g (t1 :=: t2)        = (:=:) <$> f t1 <*> f t2
  bitraverse f g (c1 :&  c2)        = (:&)  <$> bitraverse f g c1 <*> bitraverse f g c2
  bitraverse f g (Upcastable t1 t2) = Upcastable <$> f t1 <*> f t2
  bitraverse f g (Share t m)        = Share <$> f t <*> pure m
  bitraverse f g (Drop t m)         = Drop  <$> f t <*> pure m
  bitraverse f g (Escape t m)       = Escape <$> f t <*> pure m
  bitraverse f g (LayoutOk t)       = LayoutOk <$> f t
  bitraverse f g (l  :~  t)         = (:~)  <$> g l <*> f t
  bitraverse f g (l1 :~< l2)        = (:~<) <$> g l1 <*> g l2
  bitraverse f g (t1 :~~ t2)        = (:~~) <$> f t1 <*> f t2
  bitraverse f g (c  :@  e)         = (:@)  <$> bitraverse f g c <*> pure e
  bitraverse f g (Exhaustive t ps)  = Exhaustive <$> f t <*> pure ps
  bitraverse f g (Solved t)         = Solved <$> f t
  bitraverse f g (IsPrimType t)     = IsPrimType <$> f t
  bitraverse f g (UnboxedNotRecursive t) = UnboxedNotRecursive <$> f t
  bitraverse f g (NotReadOnly s)    = pure $ NotReadOnly s
#ifdef BUILTIN_ARRAYS
  bitraverse f g (Arith se)         = Arith <$> bitraverse f g se
  bitraverse f g (e1 :==: e2)       = (:==:) <$> bitraverse f g e1 <*> bitraverse f g e2
  bitraverse f g (c1 :-> c2)        = (:->) <$> bitraverse f g c1 <*> bitraverse f g c2
#endif
  bitraverse f g Sat                = pure Sat
  bitraverse f g (SemiSat w)        = pure $ SemiSat w
  bitraverse f g (Unsat e)          = pure $ Unsat e

kindToConstraint :: Kind -> TCType -> Metadata -> Constraint
kindToConstraint k t m = (if canEscape  k then Escape t m else Sat)
                      <> (if canDiscard k then Drop   t m else Sat)
                      <> (if canShare   k then Share  t m else Sat)

layoutMatchConstraint :: TCType -> TCDataLayout -> Constraint
layoutMatchConstraint t l = l :~ t

warnToConstraint :: Bool -> TypeWarning -> Constraint
warnToConstraint f w | f = SemiSat w
                     | otherwise = Sat

-- -----------------------------------------------------------------------------
-- Types for constraint generation and solving
-- -----------------------------------------------------------------------------

type TCSigil = Either (Sigil (Maybe TCDataLayout)) Int

data TCType         = T (Type TCSExpr TCDataLayout TCType)
                    | U Int  -- unifier
                    | R RP (Row TCType) TCSigil
                    | V (Row TCType)
#ifdef BUILTIN_ARRAYS
                    | A TCType TCSExpr TCSigil (Either (Maybe TCSExpr) Int)
#endif
                    | Synonym TypeName [TCType]
                    deriving (Show, Eq, Ord)

data SExpr t l      = SE { getTypeSE :: t, getExprSE :: Expr t (TPatn t l) (TIrrefPatn t l) l (SExpr t l) }
                    | SU t Int
                    deriving (Show, Eq, Ord)

data RP = Mu RecParName | None | UP Int
          deriving (Show, Eq, Ord)

coerceRP :: RecursiveParameter -> RP
coerceRP (Rec v) = Mu v
coerceRP NonRec  = None

unCoerceRP :: RP -> RecursiveParameter
unCoerceRP (Mu v) = Rec v
unCoerceRP None   = NonRec
unCoerceRP (UP i) = __impossible $ "Tried to coerce unification parameter (?" ++ show i ++ ") in core recursive type to surface recursive type"

sameRecursive :: RP -> RP -> Bool
sameRecursive (Mu _) (Mu _) = True
sameRecursive None    None = True
sameRecursive _ _ = False

unroll :: VarName -> Banged -> RecContext TCType -> TCType
unroll v b (Just ctxt) =
    ifBang b $ embedRecPar' (Just ctxt) (ctxt M.! v)
  where
    embedRecPar' ctxt (T (TRPar v b Nothing)) = T (TRPar v b ctxt)
    embedRecPar' ctxt (T t) = T $ fmap (embedRecPar' ctxt) t
    embedRecPar' (Just ctxt) t@(R rp r s) = let ctxt' = (case rp of (Mu v) -> M.insert v t ctxt; _ -> ctxt)
                                    in R rp (fmap (embedRecPar' $ Just ctxt') r) s
    embedRecPar' ctxt (V r) = V $ fmap (embedRecPar' ctxt) r
    embedRecPar' ctxt (Synonym t ts) = Synonym t $ map (embedRecPar' ctxt) ts
    embedRecPar' ctxt t = t



typeOfSE :: SExpr t l -> t
typeOfSE (SE t _) = t
typeOfSE (SU t _) = t

type TCSExpr = SExpr TCType TCDataLayout

instance Bifunctor SExpr where
  bimap f g (SE t e) = SE (f t) (fffffmap f $ ffffmap (bimap f g) $ fffmap (bimap f g) $ ffmap g $ fmap (bimap f g) e)
  bimap f g (SU t x) = SU (f t) x
instance Bifoldable SExpr where
  bifoldMap f g e = getConst $ bitraverse (Const . f) (Const . g) e
instance Bitraversable SExpr where
  bitraverse f g (SE t e) = SE <$> f t <*> pentatraverse f (bitraverse f g) (bitraverse f g) g (bitraverse f g) e
  bitraverse f g (SU t x) = SU <$> f t <*> pure x

ifBang :: Banged -> TCType -> TCType
ifBang True t = T (TBang t)
ifBang _    t = t

data FuncOrVar = MustFunc | MustVar | FuncOrVar deriving (Eq, Ord, Show)

funcOrVar :: TCType -> FuncOrVar
funcOrVar (U _) = FuncOrVar
funcOrVar (T (TVar  {})) = FuncOrVar
funcOrVar (T (TUnbox _)) = FuncOrVar
funcOrVar (T (TBang  _)) = FuncOrVar
funcOrVar (T (TFun {})) = MustFunc
funcOrVar _ = MustVar

data TExpr t l = TE { getTypeTE :: t, getExpr :: Expr t (TPatn t l) (TIrrefPatn t l) l (TExpr t l), getLocTE :: SourcePos }
deriving instance (Eq   t, Eq   l) => Eq   (TExpr t l)
deriving instance (Ord  t, Ord  l) => Ord  (TExpr t l)
deriving instance (Show t, Show l) => Show (TExpr t l)
deriving instance (Data t, Data l) => Data (TExpr t l)

data TPatn t l = TP { getPatn :: Pattern (TIrrefPatn t l), getLocTP :: SourcePos }
deriving instance (Eq   t, Eq   l) => Eq   (TPatn t l)
deriving instance (Ord  t, Ord  l) => Ord  (TPatn t l)
deriving instance (Show t, Show l) => Show (TPatn t l)
deriving instance (Data t, Data l) => Data (TPatn t l)

data TIrrefPatn t l = TIP { getIrrefPatn :: IrrefutablePattern (VarName, t) (TIrrefPatn t l) (TExpr t l), getLocTIP :: SourcePos }
deriving instance (Eq   t, Eq   l) => Eq   (TIrrefPatn t l)
deriving instance (Ord  t, Ord  l) => Ord  (TIrrefPatn t l)
deriving instance (Show t, Show l) => Show (TIrrefPatn t l)
deriving instance (Data t, Data l) => Data (TIrrefPatn t l)

instance Bifunctor TExpr where
  bimap f g (TE t e l) = TE (f t) (fffffmap f $ ffffmap (bimap f g) $ fffmap (bimap f g) $ ffmap g $ fmap (bimap f g) e) l
instance Bifunctor TPatn where
  bimap f g (TP p l) = TP (fmap (bimap f g) p) l
instance Bifunctor TIrrefPatn where
  bimap f g (TIP ip l) = TIP (fffmap (second f) $ ffmap (bimap f g) $ fmap (bimap f g) ip) l

instance Bitraversable TExpr where
  bitraverse f g (TE t e l) = TE <$> f t <*> pentatraverse f (bitraverse f g) (bitraverse f g) g (bitraverse f g) e <*> pure l
instance Bitraversable TPatn where
  bitraverse f g (TP p l) = TP <$> traverse (bitraverse f g) p <*> pure l
instance Bitraversable TIrrefPatn where
  bitraverse f g (TIP ip l) = TIP <$> tritraverse (secondM f) (bitraverse f g) (bitraverse f g) ip <*> pure l

instance Bifoldable TExpr where
  bifoldMap f g = getConst . bitraverse (Const . f) (Const . g)
instance Bifoldable TPatn where
  bifoldMap f g = getConst . bitraverse (Const . f) (Const . g)
instance Bifoldable TIrrefPatn where
  bifoldMap f g = getConst . bitraverse (Const . f) (Const . g)


instance Functor (TExpr t) where  -- over l
  fmap f e = bimap id f e
instance Functor (TPatn t) where  -- over l
  fmap f p = bimap id f p
instance Functor (TIrrefPatn l) where  -- over l
  fmap f ip = bimap id f ip

instance Traversable (TExpr t) where  -- over l
  traverse f = bitraverse pure f
instance Traversable (TPatn t) where  -- over l
  traverse f = bitraverse pure f
instance Traversable (TIrrefPatn t) where  -- over l
  traverse f = bitraverse pure f

instance Foldable (TExpr t) where  -- over l
  foldMap f = bifoldMap mempty f
instance Foldable (TPatn t) where  -- over l
  foldMap f = bifoldMap mempty f
instance Foldable (TIrrefPatn t) where  -- over l
  foldMap f = bifoldMap mempty f


instance Functor (Flip TExpr l) where  -- over t
  fmap f (Flip e)  = Flip $ bimap f id e
instance Functor (Flip TPatn l) where  -- over t
  fmap f (Flip p)  = Flip $ bimap f id p
instance Functor (Flip TIrrefPatn l) where  -- over t
  fmap f (Flip ip) = Flip $ bimap f id ip

instance Traversable (Flip TExpr l) where  -- over t
  traverse f (Flip e)  = Flip <$> bitraverse f pure e
instance Traversable (Flip TPatn l) where  -- over t
  traverse f (Flip p)  = Flip <$> bitraverse f pure p
instance Traversable (Flip TIrrefPatn l) where  -- over t
  traverse f (Flip ip) = Flip <$> bitraverse f pure ip

instance Foldable (Flip TExpr l) where  -- over t
  foldMap f (Flip e)  = bifoldMap f mempty e
instance Foldable (Flip TPatn l) where  -- over t
  foldMap f (Flip p)  = bifoldMap f mempty p
instance Foldable (Flip TIrrefPatn l) where  -- over t
  foldMap f (Flip ip) = bifoldMap f mempty ip

type TCName = (VarName, TCType)
type TCExpr = TExpr TCType TCDataLayout
type TCPatn = TPatn TCType TCDataLayout
type TCIrrefPatn = TIrrefPatn TCType TCDataLayout

data DepType = DT { unDT :: Type RawTypedExpr DataLayoutExpr DepType } deriving (Data, Eq, Ord, Show)

type TypedName = (VarName, DepType)
type TypedExpr = TExpr DepType DataLayoutExpr
type TypedPatn = TPatn DepType DataLayoutExpr
type TypedIrrefPatn = TIrrefPatn DepType DataLayoutExpr

type RawTypedExpr = TExpr RawType DataLayoutExpr
type RawTypedPatn = TPatn RawType DataLayoutExpr
type RawTypedIrrefPatn = TIrrefPatn RawType DataLayoutExpr

-- --------------------------------
-- And their conversion functions
-- --------------------------------

-- Precondition: No unification variables left in the type
toLocType :: SourcePos -> TCType -> LocType
toLocType l (T x) = LocType l (fmap (toLocType l) $ ffmap toDLExpr $ fffmap (toLocExpr toLocType toDLExpr . toTCExpr) x)
toLocType l _ = __impossible "toLocType: unification variable found"

toLocExpr :: (SourcePos -> t -> LocType) -> (l -> DataLayoutExpr) -> TExpr t l -> LocExpr
toLocExpr f g (TE t e l) = LocExpr l $ fffffmap (f l)
                                     . ffffmap (toLocPatn f g)
                                     . fffmap (toLocIrrefPatn f g)
                                     . ffmap g
                                     . fmap (toLocExpr f g) $ e

toLocPatn :: (SourcePos -> t -> LocType) -> (l -> DataLayoutExpr) -> TPatn t l -> LocPatn
toLocPatn f g (TP p l) = LocPatn l (fmap (toLocIrrefPatn f g) p)

toLocIrrefPatn :: (SourcePos -> t -> LocType) -> (l -> DataLayoutExpr) -> TIrrefPatn t l -> LocIrrefPatn
toLocIrrefPatn f g (TIP p l) = LocIrrefPatn l (fffmap fst $ ffmap (toLocIrrefPatn f g) $ fmap (toLocExpr f g) p)

toTypedExpr :: TCExpr -> TypedExpr
toTypedExpr = ffmap toDepType . fmap toDLExpr

toTypedAlts :: [Alt TCPatn TCExpr] -> [Alt TypedPatn TypedExpr]
toTypedAlts = fmap (ffmap (ffmap toDepType . fmap toDLExpr) . fmap toTypedExpr)

toDepType :: TCType -> DepType
toDepType (T x) = DT (fffmap (ffmap toRawType . fmap toDLExpr . toTCExpr) $ ffmap toDLExpr $ fmap toDepType x)
toDepType _ = __impossible "toDepType: unification variable found"

toRawType :: TCType -> RawType
toRawType (T x) = RT (fffmap (toRawExpr' . toTCExpr) $ ffmap toDLExpr $ fmap toRawType x)
toRawType _ = __impossible "toRawType: unification variable found"

toRawType' :: DepType -> RawType
toRawType' (DT t) = RT (fffmap toRawExpr'' $ fmap toRawType' t)

-- This function although is partial, it should be ok, as we statically know that
-- we won't run into those undefined cases. / zilinc
rawToDepType :: RawType -> DepType
rawToDepType (RT t) = DT $ go t
  where go :: Type RawExpr DataLayoutExpr RawType -> Type RawTypedExpr DataLayoutExpr DepType
        go t = let f = rawToDepType
                in case t of
                     TCon tn ts s    -> TCon tn (fmap f ts) s
                     TVar v b u      -> TVar v b u
                     TRecord rp fs s -> TRecord rp (fmap (second $ first f) fs) s
                     TVariant alts   -> TVariant (fmap (first $ fmap f) alts)
                     TTuple ts       -> TTuple $ fmap f ts
                     TUnit           -> TUnit
                     TUnbox t        -> TUnbox $ f t
                     TBang t         -> TBang $ f t
                     TTake mfs t     -> TTake mfs $ f t
                     TPut mfs t      -> TPut mfs $ f t
                     TLayout l t     -> TLayout l $ f t
                     _               -> __impossible "rawToDepType: we don't allow higher-order refinement types"

toRawTypedExpr :: TypedExpr -> RawTypedExpr
toRawTypedExpr (TE t e l) = TE (toRawType' t)
                               (fffffmap toRawType' $ ffffmap (ffmap toRawType') $ fffmap (ffmap toRawType') $ fmap (ffmap toRawType') e) l

toRawExpr'' :: RawTypedExpr -> RawExpr
toRawExpr'' (TE _ e _) = RE (ffffmap toRawPatn' $ fffmap toRawIrrefPatn' $ fmap toRawExpr'' e)

toRawExpr' :: TCExpr -> RawExpr
toRawExpr' = toRawExpr . toTypedExpr

toRawExpr :: TypedExpr -> RawExpr
toRawExpr = toRawExpr'' . toRawTypedExpr

toTCSExpr :: TCExpr -> TCSExpr
toTCSExpr (TE t e l) = SE t (fmap toTCSExpr e)

toTCExpr :: TCSExpr -> TCExpr
toTCExpr (SE t e) = TE t (fmap toTCExpr e) noPos
toTCExpr (SU _ x) = __impossible $ "toTCExpr: unification term variable ?" ++ show x ++ " found"

toRawPatn :: TypedPatn -> RawPatn
toRawPatn (TP p _) = RP (fmap toRawIrrefPatn p)

toRawPatn' :: RawTypedPatn -> RawPatn
toRawPatn' (TP p _) = RP (fmap toRawIrrefPatn' p)

toRawIrrefPatn :: TypedIrrefPatn -> RawIrrefPatn
toRawIrrefPatn (TIP ip _) = RIP (fffmap fst $ ffmap toRawIrrefPatn $ fmap toRawExpr ip)

toRawIrrefPatn' :: RawTypedIrrefPatn -> RawIrrefPatn
toRawIrrefPatn' (TIP ip _) = RIP (fffmap fst $ ffmap toRawIrrefPatn' $ fmap toRawExpr'' ip)


-- -----------------------------------------------------------------------------
-- Monads for the typechecker, and their states
-- -----------------------------------------------------------------------------


type TypeDict = [(TypeName, ([VarName], Maybe TCType))]  -- `Nothing' for abstract types

data TcState = TcState { _knownFuns    :: M.Map FunName (Polytype TCType)
                       , _knownTypes   :: TypeDict
                       , _knownConsts  :: M.Map VarName (TCType, TCExpr, SourcePos)
                       , _knownDataLayouts :: NamedDataLayouts
                       }

makeLenses ''TcState

#if __GLASGOW_HASKELL__ < 803
instance Monoid TcState where
  mempty = TcState mempty mempty mempty mempty
  TcState x1 x2 x3 x4 `mappend` TcState y1 y2 y3 y4 = TcState (x1 <> y1) (x2 <> y2) (x3 <> y3) (x4 <> y4)
#else
instance Semigroup TcState where
  TcState x1 x2 x3 x4 <> TcState y1 y2 y3 y4 = TcState (x1 <> y1) (x2 <> y2) (x3 <> y3) (x4 <> y4)
instance Monoid TcState where
  mempty = TcState mempty mempty mempty mempty
#endif


data TcLogState = TcLogState { _errLog :: [ContextualisedTcLog]
                             , _errCtx :: [ErrorContext]
                             }
makeLenses ''TcLogState

#if __GLASGOW_HASKELL__ < 803
instance Monoid TcLogState where
  mempty = TcLogState mempty mempty
  TcLogState l1 c1 `mappend` TcLogState l2 c2 = TcLogState (l1 <> l2) (c1 <> c2)
#else
instance Semigroup TcLogState where
  TcLogState l1 c1 <> TcLogState l2 c2 = TcLogState (l1 <> l2) (c1 <> c2)
instance Monoid TcLogState where
  mempty = TcLogState mempty mempty
#endif


runTc :: TcState -> TcM a -> IO ((Maybe a, TcLogState), TcState)
runTc s ma = flip runStateT s
             . fmap (second $ over errLog adjustErrors)
             . flip runStateT (TcLogState [] [])
             . runMaybeT
             $ ma
  where
    adjustErrors = (if __cogent_freverse_tc_errors then reverse else id) . adjustContexts
    adjustContexts = map (first noConstraints)
    noConstraints = if __cogent_ftc_ctx_constraints then id else filter (not . isCtxConstraint)


type TcM a = MaybeT (StateT TcLogState (StateT TcState IO)) a
type TcConsM lcl a = StateT  lcl (StateT TcState IO) a
type TcErrM  err a = ExceptT err (StateT TcState IO) a
type TcBaseM     a =              StateT TcState IO  a


-- -----------------------------------------------------------------------------
-- Error logging functions and exception handling
-- -----------------------------------------------------------------------------


withTcConsM :: lcl -> TcConsM lcl a -> TcM a
withTcConsM lcl ma = lift . lift $ evalStateT ma lcl

logErr :: [ErrorContext] -> TypeError -> TcM ()
logErr ctx e = logTc =<< ((\c -> (ctx++c, Left e)) <$> lift (use errCtx))

logErrExit :: TypeError -> TcM a
logErrExit e = logErr [] e >> exitErr

-- Even -Werror is enabled, we don't exit. Errors will be collected and thrown at the end.
logWarn :: TypeWarning -> TcM ()
logWarn w = case __cogent_warning_switch of
                Flag_w -> return ()
                Flag_Wwarn  -> logTc =<< ((, Right $ w                   ) <$> lift (use errCtx))
                Flag_Werror -> logTc =<< ((, Left  $ TypeWarningAsError w) <$> lift (use errCtx))

logTc :: ContextualisedTcLog -> TcM ()
logTc l = lift $ errLog %= (++[l])

exitErr :: TcM a
exitErr = MaybeT $ return Nothing

exitOnErr :: TcM a -> TcM a
exitOnErr ma = do a <- ma
                  log <- lift $ use errLog
                  if not (any isLeft $ map snd log) then return a else exitErr


-- -----------------------------------------------------------------------------
-- Functions operating on types. Type wellformedness checks
-- -----------------------------------------------------------------------------


substType :: [(VarName, TCType)] -> TCType -> TCType
substType vs (U x) = U x
substType vs (V x) = V (fmap (substType vs) x)
substType vs (R rp x s) = R rp (fmap (substType vs) x) s
#ifdef BUILTIN_ARRAYS
substType vs (A t l s tkns) = A (substType vs t) l s tkns
#endif
substType vs (Synonym n ts) = Synonym n (fmap (substType vs) ts)
substType vs (T (TVar v b u)) | Just x <- lookup v vs
  = case (b,u) of
      (False, False) -> x
      (True , False) -> T (TBang x)
      (_    , True ) -> T (TUnbox x)
substType vs (T t) = T (fmap (substType vs) t)

substLayoutL :: [(DLVarName, TCDataLayout)] -> TCDataLayout -> TCDataLayout
substLayoutL vs (TLVar n) | Just x <- lookup n vs = x
substLayoutL vs (TLRecord fs) = TLRecord $ (\(x,y,z) -> (x,y,substLayoutL vs z)) <$> fs
substLayoutL vs (TLVariant e fs) = TLVariant e $ (\(x,y,z,v) -> (x,y,z,substLayoutL vs v)) <$> fs
#ifdef BUILTIN_ARRAYS
substLayoutL vs (TLArray e l p) = TLArray (substLayoutL vs e) l p
#endif
substLayoutL vs (TLOffset e s) = TLOffset (substLayoutL vs e) s
substLayoutL vs (TLAfter e f) = TLAfter (substLayoutL vs e) f
substLayoutL vs (TLRepRef n es) = TLRepRef n $ fmap (substLayoutL vs) es 
substLayoutL vs l = l

substLayout :: [(DLVarName, TCDataLayout)] -> TCType -> TCType
substLayout vs (T (TLayout l t)) = T (TLayout (substLayoutL vs l) t)
substLayout vs (T t) = T (fmap (substLayout vs) t)
substLayout vs (U x) = U x
substLayout vs (V x) = V $ substLayout vs <$> x
substLayout vs (R rp x s) = R rp (substLayout vs <$> x) (first (fmap (fmap (substLayoutL vs))) s)
#ifdef BUILTIN_ARRAYS
substLayout vs (A t l s tkns) = A (substLayout vs t) l (bimap (fmap (fmap (substLayoutL vs))) id s) tkns
#endif
substLayout vs (Synonym n ts) = Synonym n $ substLayout vs <$> ts

flexOf (U x) = Just x
flexOf (T (TTake _ t))   = flexOf t
flexOf (T (TPut  _ t))   = flexOf t
flexOf (T (TLayout _ t)) = flexOf t
flexOf (T (TBang  t))    = flexOf t
flexOf (T (TUnbox t))    = flexOf t
#ifdef BUILTIN_ARRAYS
flexOf (T (TATake _ t))  = flexOf t
flexOf (T (TAPut  _ t))  = flexOf t
#endif
flexOf _ = Nothing

isSynonym :: RawType -> TcBaseM Bool
isSynonym (RT (TCon c _ _)) = lookup c <$> use knownTypes >>= \case
  Nothing -> __impossible "isSynonym: type not in scope"
  Just (vs,Just _ ) -> return True
  Just (vs,Nothing) -> return False
isSynonym (RT t) = foldM (\b a -> (b ||) <$> isSynonym a) False t

isIntType :: RawType -> Bool
isIntType (RT (TCon cn ts s)) | cn `elem` words "U8 U16 U32 U64", null ts, s == Unboxed = True
isIntType _ = False

isVariantType :: RawType -> Bool
isVariantType (RT (TVariant _)) = True
isVariantType _ = False

isMonoType :: RawType -> Bool
isMonoType (RT (TVar {})) = False
isMonoType (RT t) = all isMonoType t


-- TODO: not yet counting the higher-rank types / zilinc
unifVars :: TCType -> [Int]
unifVars (U v) = [v]
unifVars (Synonym n ts) = concatMap unifVars ts
unifVars (V r) =
  maybeToList (Row.var r) ++ concatMap unifVars (Row.payloads r)
unifVars (R rp r s) =
  maybeToList (Row.var r) ++ concatMap unifVars (Row.payloads r) ++ rights [s]
    ++ case rp of UP i -> [i]; _ -> []
#ifdef BUILTIN_ARRAYS
unifVars (A t l s tkns) = unifVars t ++ rights [s] ++ rights [tkns]
#endif
unifVars (T x) = foldMap unifVars x

unifLVars :: TCDataLayout -> [Int]
unifLVars (TLU n) = [n]
unifLVars (TLRecord ps) = concatMap unifLVars (thd3 <$> ps)
unifLVars (TLVariant t ps) = unifLVars t <> concatMap unifLVars ((\(_,_,_,a) -> a) <$> ps)
#ifdef BUILTIN_ARRAYS
unifLVars (TLArray e _ _) = unifLVars e
#endif
unifLVars (TLOffset e _) = unifLVars e
unifLVars (TLAfter e _) = unifLVars e
unifLVars (TLEndian e _) = unifLVars e
unifLVars _ = []

unifLVarsS :: TCSigil -> [Int]
unifLVarsS (Left (Boxed _ (Just l))) = unifLVars l
unifLVarsS _ = []

unifLVarsT :: TCType -> [Int]
unifLVarsT (Synonym _ ts) = concatMap unifLVarsT ts
unifLVarsT (R _ r s) = unifLVarsS s <> nub (concatMap unifLVarsT $ Row.payloads r)
unifLVarsT (V r) = nub (concatMap unifLVarsT $ Row.payloads r)
#ifdef BUILTIN_ARRAYS
unifLVarsT (A t _ s _) = unifLVarsT t <> unifLVarsS s
#endif
unifLVarsT (T x) = foldMap unifLVarsT x

#ifdef BUILTIN_ARRAYS
unifVarsE :: TCSExpr -> [Int]
unifVarsE (SE t e) = unifVars t ++ foldMap unifVarsE e
                                ++ fffoldMap (ffoldMap unifVars) e
                                ++ ffffoldMap (ffoldMap unifVars) e
                                ++ fffffoldMap unifVars e
unifVarsE (SU t _) = unifVars t

unknowns :: TCType -> [Int]
unknowns (U _) = []
unknowns (Synonym n ts) = concatMap unknowns ts
unknowns (V r) = concatMap unknowns (Row.payloads r)
unknowns (R _ r s) = concatMap unknowns (Row.payloads r)
unknowns (A t l s tkns) = unknowns t ++ unknownsE l ++ bifoldMap (foldMap unknownsE) (const mempty) tkns
unknowns (T x) = foldMap unknowns x

unknownsE :: SExpr t l -> [Int]
unknownsE (SU _ x) = [x]
unknownsE (SE _ e) = foldMap unknownsE e

isKnown :: SExpr t l -> Bool
isKnown (SU _ _) = False
isKnown (SE _ e) = all isKnown e

isTrivialSE :: TCSExpr -> Bool
isTrivialSE (SU {})  = False
isTrivialSE (SE t e) = go e
  where go (Var {})   = False
        go (Con {})   = False
        go (Match {}) = False
        go (Lam {})   = False
        go (LamC {})  = False
        go (Let {})   = False
        go e          = all isTrivialSE e

simpleTE :: TExpr t l -> Bool
simpleTE (TE _ e _) = case e of
                 ArrayLit   {} -> False
                 ArrayIndex {} -> False
                 ArrayMap2  {} -> False
                 ArrayPut   {} -> False
                 _             -> all simpleTE e

#endif

-- What's the spec of this function? / zilinc
rigid :: TCType -> Bool
rigid (U {}) = False
rigid (T (TBang {})) = False
rigid (T (TTake {})) = False
rigid (T (TPut {})) = False
rigid (T (TLayout {})) = False
rigid (Synonym {}) = False  -- why? / zilinc
rigid (R _ r _) = not $ Row.justVar r
rigid (V r) = not $ Row.justVar r
#ifdef BUILTIN_ARRAYS
rigid (A t l _ _) = True  -- rigid t && null (unknownsE l) -- FIXME: is it correct? / zilinc
#endif
rigid _ = True

floppy :: TCType -> Bool
floppy = not . rigid


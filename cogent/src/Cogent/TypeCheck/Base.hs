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
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Cogent.TypeCheck.Base where

import Cogent.Dargent.Allocation
import Cogent.Dargent.TypeCheck ( NamedDataLayouts
                                , DataLayoutTcError
                                , tcDataLayoutExpr
                                , evalSize
                                )
import Cogent.Dargent.Core      ( DataLayout (..)
                                , DataLayout'(..)
                                )

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Surface
import Cogent.TypeCheck.ARow hiding (all, null)
import Cogent.TypeCheck.Row (Row)
import qualified Cogent.TypeCheck.Row as Row
-- import Cogent.TypeCheck.Util
import Cogent.Util

import Control.Applicative (liftA)
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Writer hiding (Alt)
import Control.Monad.Reader
import Data.Bifunctor (bimap, first, second)
import Data.Bitraversable (bitraverse)
import Data.Data (Data)
import Data.Foldable (all)
import Data.Maybe (fromJust, isJust)
import Data.Either (either, isLeft)
import Data.Functor.Const
import Data.Functor.Identity
import qualified Data.IntMap as IM
import Data.List (nub, (\\))
import qualified Data.Map as M
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
               | TakeFromNonRecordOrVariant (Maybe [FieldName]) TCType
               | PutToNonRecordOrVariant    (Maybe [FieldName]) TCType
               | TakeNonExistingField FieldName TCType
               | PutNonExistingField  FieldName TCType
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
               | LayoutDoesNotMatchType DataLayoutExpr TCType
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
               | BoundOf TCType TCType Bound
               | EqualIn TCExpr TCExpr TCType TCType
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
              | ImplicitlyTaken
              | Constant { constName :: ConstName }
              deriving (Eq, Show, Ord)

(>:) = flip (:<)

data Constraint' t = (:<) t t
                   | (:=:) t t
                   | (:&) (Constraint' t) (Constraint' t)
                   | Upcastable t t
                   | Share t Metadata
                   | Drop t Metadata
                   | Escape t Metadata
                   | (:@) (Constraint' t) ErrorContext
                   | Unsat TypeError
                   | SemiSat TypeWarning
                   | Sat
                   | Exhaustive t [RawPatn]
                   | Solved t
#ifdef BUILTIN_ARRAYS
                   | Arith (SExpr t)
                   | (:->) (Constraint' t) (Constraint' t)
#endif
                   deriving (Eq, Show, Ord, Functor, Foldable, Traversable)

type Constraint = Constraint' TCType

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
splitArithConstraints (Arith e ) = ([e], Sat)
splitArithConstraints c          = ([], c)

andTCSExprs :: [TCSExpr] -> TCSExpr
andTCSExprs [] = SE (T bool) (BoolLit True)
andTCSExprs (e:es) = SE (T bool) (PrimOp "&&" [e, andTCSExprs es])
#endif

#if __GLASGOW_HASKELL__ < 803	
instance Monoid (Constraint' x) where	
  mempty = Sat	
  mappend Sat x = x	
  mappend x Sat = x	
  -- mappend (Unsat r) x = Unsat r	
  -- mappend x (Unsat r) = Unsat r	
  mappend x y = x :& y	
#else
instance Semigroup (Constraint' x) where
  Sat <> x = x
  x <> Sat = x
  x <> y = x :& y
instance Monoid (Constraint' x) where
  mempty = Sat
#endif

kindToConstraint :: Kind -> TCType -> Metadata -> Constraint
kindToConstraint k t m = (if canEscape  k then Escape t m else Sat)
                      <> (if canDiscard k then Drop   t m else Sat)
                      <> (if canShare   k then Share  t m else Sat)

warnToConstraint :: Bool -> TypeWarning -> Constraint
warnToConstraint f w | f = SemiSat w
                     | otherwise = Sat

-- -----------------------------------------------------------------------------
-- Types for constraint generation and solving
-- -----------------------------------------------------------------------------

data TCType         = T (Type TCSExpr TCType)
                    | U Int  -- unifier
                    | R (Row TCType) (Either (Sigil (Maybe DataLayoutExpr)) Int)
                    | V (Row TCType)
#ifdef BUILTIN_ARRAYS
                    | A TCType TCSExpr (Either (Sigil (Maybe DataLayoutExpr)) Int) (Maybe TCSExpr)
#endif
                    | Synonym TypeName [TCType]
                    deriving (Show, Eq, Ord)

data SExpr t        = SE { getTypeSE :: t, getExprSE :: Expr t (TPatn t) (TIrrefPatn t) (SExpr t) }
                    | SU t Int
                    deriving (Show, Eq, Ord)

typeOfSE :: SExpr t -> t
typeOfSE (SE t _) = t
typeOfSE (SU t _) = t

type TCSExpr = SExpr TCType

instance Functor SExpr where
  fmap f (SE t e) = SE (f t) (ffffmap f $ fffmap (fmap f) $ ffmap (fmap f) $ fmap (fmap f) e)
  fmap f (SU t x) = SU (f t) x
instance Foldable SExpr where
  foldMap f e = getConst $ traverse (Const . f) e
instance Traversable SExpr where
  traverse f (SE t e) = SE <$> f t <*> quadritraverse f (traverse f) (traverse f) (traverse f) e
  traverse f (SU t x) = SU <$> f t <*> pure x

data FuncOrVar = MustFunc | MustVar | FuncOrVar deriving (Eq, Ord, Show)

funcOrVar :: TCType -> FuncOrVar
funcOrVar (U _) = FuncOrVar
funcOrVar (T (TVar  {})) = FuncOrVar
funcOrVar (T (TUnbox _)) = FuncOrVar
funcOrVar (T (TBang  _)) = FuncOrVar
funcOrVar (T (TFun {})) = MustFunc
funcOrVar _ = MustVar

data TExpr      t = TE { getTypeTE :: t, getExpr :: Expr t (TPatn t) (TIrrefPatn t) (TExpr t), getLocTE :: SourcePos }
deriving instance Eq   t => Eq   (TExpr t)
deriving instance Ord  t => Ord  (TExpr t)
deriving instance Show t => Show (TExpr t)
deriving instance Data t => Data (TExpr t)

data TPatn      t = TP { getPatn :: Pattern (TIrrefPatn t), getLocTP :: SourcePos }
deriving instance Eq   t => Eq   (TPatn t)
deriving instance Ord  t => Ord  (TPatn t)
deriving instance Show t => Show (TPatn t)
deriving instance Data t => Data (TPatn t)

data TIrrefPatn t = TIP { getIrrefPatn :: IrrefutablePattern (VarName, t) (TIrrefPatn t) (TExpr t), getLocTIP :: SourcePos }
deriving instance Eq   t => Eq   (TIrrefPatn t)
deriving instance Ord  t => Ord  (TIrrefPatn t)
deriving instance Show t => Show (TIrrefPatn t)
deriving instance Data t => Data (TIrrefPatn t)

instance Functor TExpr where
  fmap f (TE t e l) = TE (f t) (ffffmap f $ fffmap (fmap f) $ ffmap (fmap f) $ fmap (fmap f) e) l  -- Hmmm!
instance Functor TPatn where
  fmap f (TP p l) = TP (fmap (fmap f) p) l
instance Functor TIrrefPatn where
  fmap f (TIP ip l) = TIP (fffmap (second f) $ ffmap (fmap f) $ fmap (fmap f) ip) l

instance Traversable TExpr where
  traverse f e = undefined
instance Traversable TPatn where
  traverse f (TP p l) = TP <$> traverse (traverse f) p <*> pure l
instance Traversable TIrrefPatn where
  traverse f (TIP ip l) = TIP <$> tritraverse f ip <*> pure l
    where tritraverse :: Applicative f
                      => (a -> f b)
                      -> IrrefutablePattern (VarName, a) (TIrrefPatn a) (TExpr a)
                      -> f (IrrefutablePattern (VarName, b) (TIrrefPatn b) (TExpr b))
          tritraverse f (PVar v)            = PVar <$> traverse f v
          tritraverse f (PTuple ips)        = PTuple <$> traverse (traverse f) ips
          tritraverse f (PUnboxedRecord fs) = PUnboxedRecord <$> traverse (traverse (traverse (traverse f))) fs
          tritraverse f (PUnderscore)       = pure $ PUnderscore
          tritraverse f (PUnitel)           = pure $ PUnitel
          tritraverse f (PTake pv fs)       = PTake <$> traverse f pv <*> traverse (traverse (traverse (traverse f))) fs
#ifdef BUILTIN_ARRAYS
          tritraverse f (PArray ips)        = PArray <$> traverse (traverse f) ips
          tritraverse f (PArrayTake pv is)  = PArrayTake <$> traverse f pv <*> traverse (bitraverse (traverse f) (traverse f)) is
#endif


instance Foldable TExpr where
  foldMap f e  = getConst $ traverse (Const . f) e
instance Foldable TPatn where
  foldMap f p  = getConst $ traverse (Const . f) p
instance Foldable TIrrefPatn where
  foldMap f ip = getConst $ traverse (Const . f) ip

type TCName = (VarName, TCType)
type TCExpr = TExpr TCType
type TCPatn = TPatn TCType
type TCIrrefPatn = TIrrefPatn TCType

data DepType = DT { unDT :: Type RawTypedExpr DepType } deriving (Data, Eq, Ord, Show)

type TypedName = (VarName, DepType)
type TypedExpr = TExpr DepType
type TypedPatn = TPatn DepType
type TypedIrrefPatn = TIrrefPatn DepType

type RawTypedExpr = TExpr RawType
type RawTypedPatn = TPatn RawType
type RawTypedIrrefPatn = TIrrefPatn RawType

-- --------------------------------
-- And their conversion functions
-- --------------------------------

-- Precondition: No unification variables left in the type
toLocType :: SourcePos -> TCType -> LocType
toLocType l (T x) = LocType l (fmap (toLocType l) $ ffmap (toLocExpr toLocType . toTCExpr) x)
toLocType l _ = __impossible "toLocType: unification variable found"

toLocExpr :: (SourcePos -> t -> LocType) -> TExpr t -> LocExpr
toLocExpr f (TE t e l) = LocExpr l (ffffmap (f l) $ fffmap (toLocPatn f) $ ffmap (toLocIrrefPatn f) $ fmap (toLocExpr f) e)

toLocPatn :: (SourcePos -> t -> LocType) -> TPatn t -> LocPatn
toLocPatn f (TP p l) = LocPatn l (fmap (toLocIrrefPatn f) p)

toLocIrrefPatn :: (SourcePos -> t -> LocType) -> TIrrefPatn t -> LocIrrefPatn
toLocIrrefPatn f (TIP p l) = LocIrrefPatn l (fffmap fst $ ffmap (toLocIrrefPatn f) $ fmap (toLocExpr f) p)

toTypedExpr :: TCExpr -> TypedExpr
toTypedExpr = fmap toDepType

toTypedAlts :: [Alt TCPatn TCExpr] -> [Alt TypedPatn TypedExpr]
toTypedAlts = fmap (ffmap (fmap toDepType) . fmap toTypedExpr)

toDepType :: TCType -> DepType
toDepType (T x) = DT (ffmap (fmap toRawType . toTCExpr) $ fmap toDepType x)
toDepType _ = __impossible "toDepType: unification variable found"

toRawType :: TCType -> RawType
toRawType (T x) = RT (ffmap (toRawExpr' . toTCExpr) $ fmap toRawType x)
toRawType _ = __impossible "toRawType: unification variable found"

toRawType' :: DepType -> RawType
toRawType' (DT t) = RT (ffmap toRawExpr'' $ fmap toRawType' t)

-- This function although is partial, it should be ok, as we statically know that 
-- we won't run into those undefined cases. / zilinc
rawToDepType :: RawType -> DepType
rawToDepType (RT t) = DT $ go t
  where go :: Type RawExpr RawType -> Type RawTypedExpr DepType
        go t = let f = rawToDepType
                in case t of
                     TCon tn ts s  -> TCon tn (fmap f ts) s
                     TVar v b      -> TVar v b
                     TRecord fs s  -> TRecord (fmap (second $ first f) fs) s
                     TVariant alts -> TVariant (fmap (first $ fmap f) alts)
                     TTuple ts     -> TTuple $ fmap f ts
                     TUnit         -> TUnit
                     TUnbox t      -> TUnbox $ f t
                     TBang t       -> TBang $ f t
                     TTake mfs t   -> TTake mfs $ f t
                     TPut mfs t    -> TPut mfs $ f t
                     TLayout l t   -> TLayout l $ f t
                     _             -> __impossible $ "rawToDepType: we don't allow higher-order refinement types"

toRawTypedExpr :: TypedExpr -> RawTypedExpr
toRawTypedExpr (TE t e l) = TE (toRawType' t) (ffffmap toRawType' $ fffmap (fmap toRawType') $ ffmap (fmap toRawType') $ fmap (fmap toRawType') e) l

toRawExpr'' :: RawTypedExpr -> RawExpr
toRawExpr'' (TE _ e _) = RE (fffmap toRawPatn' $ ffmap toRawIrrefPatn' $ fmap toRawExpr'' e)

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

logErr :: TypeError -> TcM ()
logErr e = logTc =<< ((,Left e) <$> lift (use errCtx))

logErrExit :: TypeError -> TcM a
logErrExit e = logErr e >> exitErr

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
substType vs (R x s) = R (fmap (substType vs) x) s
#ifdef BUILTIN_ARRAYS
substType vs (A t l s tkns) = A (substType vs t) l s tkns
#endif
substType vs (Synonym n ts) = Synonym n (fmap (substType vs) ts)
substType vs (T (TVar v False )) | Just x <- lookup v vs = x
substType vs (T (TVar v True  )) | Just x <- lookup v vs = T (TBang x)
substType vs (T t) = T (fmap (substType vs) t)

-- only for error reporting
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
unifVars (V r)
  | Just x <- Row.var r = [x] ++ concatMap unifVars (Row.allTypes r)
  | otherwise = concatMap unifVars (Row.allTypes r)
unifVars (R r s)
  | Just x <- Row.var r = [x] ++ concatMap unifVars (Row.allTypes r)
                       ++ case s of Left s -> []
                                    Right y -> [y]
  | otherwise = concatMap unifVars (Row.allTypes r)
                       ++ case s of Left s -> []
                                    Right y -> [y]
#ifdef BUILTIN_ARRAYS
unifVars (A t l s tkns) = unifVars t ++ (case s of Left s -> []; Right y -> [y])
#endif
unifVars (T x) = foldMap unifVars x

#ifdef BUILTIN_ARRAYS
unknowns :: TCType -> [Int]
unknowns (U _) = []
unknowns (Synonym n ts) = concatMap unknowns ts
unknowns (V r) = concatMap unknowns (Row.allTypes r)
unknowns (R r s) = concatMap unknowns (Row.allTypes r)
unknowns (A t l s tkns) = unknowns t ++ unknownsE l ++ foldMap unknownsE tkns
unknowns (T x) = foldMap unknowns x

unknownsE :: SExpr t -> [Int]
unknownsE (SU _ x) = [x]
unknownsE (SE _ e) = foldMap unknownsE e

isKnown :: SExpr t -> Bool
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
#endif

-- What's the spec of this function? / zilinc
rigid :: TCType -> Bool
rigid (U {}) = False
rigid (T (TBang {})) = False
rigid (T (TTake {})) = False
rigid (T (TPut {})) = False
rigid (T (TLayout {})) = False
rigid (Synonym {}) = False  -- why? / zilinc
rigid (R r _) = not $ Row.justVar r
rigid (V r) = not $ Row.justVar r
#ifdef BUILTIN_ARRAYS
rigid (A t l _ _) = True  -- rigid t && null (unknownsE l) -- FIXME: is it correct? / zilinc
#endif
rigid _ = True

--
-- Dargent
--

isTypeLayoutExprCompatible :: NamedDataLayouts -> TCType -> DataLayoutExpr -> Bool
isTypeLayoutExprCompatible env (T (TCon n [] Boxed{})) DLPtr = True
isTypeLayoutExprCompatible env (T (TCon n [] Unboxed)) (DLPrim rs) =
  let s  = evalSize rs
      s' = (case n of
            "U8"  -> 8
            "U16" -> 16
            "U32" -> 32
            "U64" -> 64
            "Bool" -> 1)
   in s' <= s
isTypeLayoutExprCompatible env (T (TRecord fs1 Boxed{})) DLPtr = True
isTypeLayoutExprCompatible env (T (TRecord fs1 Unboxed)) (DLRecord fs2) =
  all
    (\((n1,(t,_)),(n2,_,l)) -> n1 == n2 && isTypeLayoutExprCompatible env t l)
    (zip (sortOn fst fs1) (sortOn fst3 fs2))
isTypeLayoutExprCompatible env (T (TTuple fs1)) (DLRecord fs2) =
  all (\(t,(_,_,l)) -> isTypeLayoutExprCompatible env t l) (zip fs1 fs2)
isTypeLayoutExprCompatible env (T (TVariant ts1)) (DLVariant _ ts2) =
  all
    (\((n1,(ts,_)),(n2,_,_,l)) ->
      n1 == n2 && isTypeLayoutExprCompatible env (tuplise ts) l)
    (zip (M.assocs ts1) (sortOn fst4 ts2))
  where
    tuplise [] = T TUnit
    tuplise [t] = t
    tuplise ts = T (TTuple ts)
#ifdef BUILTIN_ARRAYS
isTypeLayoutExprCompatible env (T (TArray t _ (Boxed {}) _)) DLPtr = True
isTypeLayoutExprCompatible env (T (TArray t _ Unboxed _)) (DLArray l _) = isTypeLayoutExprCompatible env t l
#endif
isTypeLayoutExprCompatible env t (DLOffset l _) = isTypeLayoutExprCompatible env t (DL l)
isTypeLayoutExprCompatible env t (DLRepRef n)   =
  case M.lookup n env of
    Just (l, _) -> isTypeLayoutExprCompatible env t l
    Nothing     -> False  -- TODO(dargent): this really shoud be an exceptional state
isTypeLayoutExprCompatible _ t l = trace ("t = " ++ show t ++ "\nl = " ++ show l) False


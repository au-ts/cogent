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

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Cogent.TypeCheck.Base where

import qualified Cogent.Common.Repr as R
import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.ReprCheck as R
import Cogent.Surface
-- import Cogent.TypeCheck.Util
import Cogent.Util

import Control.Arrow (second)
import Control.Lens hiding (Context, (:<))
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Writer hiding (Alt)
import Data.Either (either, isLeft)
import qualified Data.IntMap as IM
import Data.List (nub, (\\))
import qualified Data.Map as M
#if __GLASGOW_HASKELL__ < 803
import Data.Monoid ((<>))
#endif
import qualified Data.Sequence as Seq
-- import qualified Data.Set as S
import Text.Parsec.Pos


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
               | TypeMismatch (TypeFragment TCType) (TypeFragment TCType)
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
               | TakeFromNonRecordOrVariant (Maybe [FieldName]) TCType
               | PutToNonRecordOrVariant    (Maybe [FieldName]) TCType
               | TakeNonExistingField FieldName TCType
               | PutNonExistingField  FieldName TCType
               | DiscardWithoutMatch TagName
               | RequiredTakenTag TagName
               | ArithConstraintsUnsatisfiable [SExpr] String
               | CustTyGenIsPolymorphic TCType
               | CustTyGenIsSynonym TCType
               | TypeWarningAsError TypeWarning
               | RepError R.RepError
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
               | BoundOf (TypeFragment TCType) (TypeFragment TCType) Bound
               | EqualIn SExpr SExpr TCType TCType
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
              | UsedInArrayIndexing
              | UsedInLetBang
              | TypeParam { functionName :: VarName, typeVarName :: VarName }
              | ImplicitlyTaken
              | Constant { varName :: VarName }
              deriving (Eq, Show, Ord)

data Constraint = (:<) (TypeFragment TCType) (TypeFragment TCType)
                | (:&) Constraint Constraint
                | Upcastable TCType TCType
                | Share TCType Metadata
                | Drop TCType Metadata
                | Escape TCType Metadata
                | (:@) Constraint ErrorContext
                | Unsat TypeError
                | SemiSat TypeWarning
                | Sat
                | Exhaustive TCType [RawPatn]
                | Arith SExpr
                deriving (Eq, Show, Ord)

#if __GLASGOW_HASKELL__ < 803
instance Monoid Constraint where
  mempty = Sat
  mappend Sat x = x
  mappend x Sat = x
  -- mappend (Unsat r) x = Unsat r
  -- mappend x (Unsat r) = Unsat r
  mappend x y = x :& y
#else
instance Semigroup Constraint where
  Sat <> x = x
  x <> Sat = x
  x <> y = x :& y
instance Monoid Constraint where
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


data TypeFragment t = F t
                    | FRecord [(FieldName, (t, Taken))]
                    | FVariant (M.Map TagName ([t], Taken))
                    deriving (Eq, Show, Functor, Foldable, Traversable, Ord)

data TCType       = T (Type SExpr TCType)
                  | U Int  -- unifier
                  deriving (Show, Eq, Ord)

data SExpr        = SE (Expr RawType RawPatn RawIrrefPatn SExpr)
                  | SU Int
                  deriving (Show, Eq, Ord)

data FuncOrVar = MustFunc | MustVar | FuncOrVar deriving (Eq, Ord, Show)

funcOrVar :: TCType -> FuncOrVar
funcOrVar (U _) = FuncOrVar
funcOrVar (T (TVar  {})) = FuncOrVar
funcOrVar (T (TUnbox _)) = FuncOrVar
funcOrVar (T (TBang  _)) = FuncOrVar
funcOrVar (T (TFun {})) = MustFunc
funcOrVar _ = MustVar

data TExpr      t = TE { getTypeTE :: t, getExpr :: Expr t (TPatn t) (TIrrefPatn t) (TExpr t), getLocTE :: SourcePos }
deriving instance Show t => Show (TExpr t)

data TPatn      t = TP { getPatn :: Pattern (TIrrefPatn t), getLocTP :: SourcePos }
deriving instance Eq   t => Eq   (TPatn t)
deriving instance Ord  t => Ord  (TPatn t)
deriving instance Show t => Show (TPatn t)

data TIrrefPatn t = TIP { getIrrefPatn :: IrrefutablePattern (VarName, t) (TIrrefPatn t), getLocTIP :: SourcePos }
deriving instance Eq   t => Eq   (TIrrefPatn t)
deriving instance Ord  t => Ord  (TIrrefPatn t)
deriving instance Show t => Show (TIrrefPatn t)

instance Functor TExpr where
  fmap f (TE t e l) = TE (f t) (ffffmap f $ fffmap (fmap f) $ ffmap (fmap f) $ fmap (fmap f) e) l  -- Hmmm!
instance Functor TPatn where
  fmap f (TP p l) = TP (fmap (fmap f) p) l
instance Functor TIrrefPatn where
  fmap f (TIP ip l) = TIP (ffmap (second f) $ fmap (fmap f) ip) l

type TCName = (VarName, TCType)
type TCExpr = TExpr TCType
type TCPatn = TPatn TCType
type TCIrrefPatn = TIrrefPatn TCType

type TypedName = (VarName, RawType)
type TypedExpr = TExpr RawType
type TypedPatn = TPatn RawType
type TypedIrrefPatn = TIrrefPatn RawType


-- --------------------------------
-- And their convertion functions
-- --------------------------------

toTCType :: RawType -> TCType
toTCType (RT x) = T (fmap toTCType $ ffmap toSExpr x)

toSExpr :: RawExpr -> SExpr
toSExpr (RE e) = SE (fmap toSExpr e)

tcToSExpr :: TCExpr -> SExpr
tcToSExpr = toSExpr . toRawExpr . toTypedExpr

-- Precondition: No unification variables left in the type
toLocType :: SourcePos -> TCType -> LocType
toLocType l (T x) = LocType l (fmap (toLocType l) $ ffmap (rawToLocE l . toRawExpr') x)
toLocType l _ = error "panic: unification variable found"

toLocExpr :: (SourcePos -> t -> LocType) -> TExpr t -> LocExpr
toLocExpr f (TE t e l) = LocExpr l (ffffmap (f l) $ fffmap (toLocPatn f) $ ffmap (toLocIrrefPatn f) $ fmap (toLocExpr f) e)

toLocPatn :: (SourcePos -> t -> LocType) -> TPatn t -> LocPatn
toLocPatn f (TP p l) = LocPatn l (fmap (toLocIrrefPatn f) p)

toLocIrrefPatn :: (SourcePos -> t -> LocType) -> TIrrefPatn t -> LocIrrefPatn
toLocIrrefPatn f (TIP p l) = LocIrrefPatn l (ffmap fst $ fmap (toLocIrrefPatn f) p)

toTypedExpr :: TCExpr -> TypedExpr
toTypedExpr = fmap toRawType

toTypedAlts :: [Alt TCPatn TCExpr] -> [Alt TypedPatn TypedExpr]
toTypedAlts = fmap (ffmap (fmap toRawType) . fmap (fmap toRawType))

toRawType :: TCType -> RawType
toRawType (T x) = RT (ffmap toRawExpr' $ fmap toRawType x)
toRawType _ = error "panic: unification variable found"

toRawExpr' :: SExpr -> RawExpr
toRawExpr' (SE e) = RE (fmap toRawExpr' e)
toRawExpr' _ = __impossible "toRawExpr': unification variable found"

toRawExpr :: TypedExpr -> RawExpr
toRawExpr (TE t e _) = RE (fffmap toRawPatn . ffmap toRawIrrefPatn . fmap toRawExpr $ e)

toRawPatn :: TypedPatn -> RawPatn
toRawPatn (TP p _) = RP (fmap toRawIrrefPatn p)

toRawIrrefPatn :: TypedIrrefPatn -> RawIrrefPatn
toRawIrrefPatn (TIP ip _) = RIP (ffmap fst $ fmap toRawIrrefPatn ip)



-- -----------------------------------------------------------------------------
-- Monads for the typechecker, and their states
-- -----------------------------------------------------------------------------


type TypeDict = [(TypeName, ([VarName], Maybe TCType))]  -- `Nothing' for abstract types

data TcState = TcState { _knownFuns    :: M.Map FunName (Polytype TCType)
                       , _knownTypes   :: TypeDict
                       , _knownConsts  :: M.Map VarName (TCType, TCExpr, SourcePos)
                       , _knownReps    :: M.Map RepName (R.Allocation, RepData)
                       }

makeLenses ''TcState

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
                Flag_Wwarn  -> logTc =<< ((, Right $ w) <$> lift (use errCtx))
                Flag_Werror -> logTc =<< ((, Left  $ TypeWarningAsError w) <$> lift (use errCtx))

logTc :: ContextualisedTcLog -> TcM ()
logTc l = lift $ errLog %= (++[l])

exitErr :: TcM a
exitErr = MaybeT $ return Nothing

exitOnErr :: TcM a -> TcM a
exitOnErr ma = do a <- ma
                  log <- lift $ use errLog
                  if null (filter isLeft $ map snd log) then return a else exitErr


-- -----------------------------------------------------------------------------
-- Functions operating on types. Type wellformedness checks
-- -----------------------------------------------------------------------------


substType :: [(VarName, TCType)] -> TCType -> TCType
substType vs (U x) = U x
substType vs (T (TVar v False )) | Just x <- lookup v vs = x
substType vs (T (TVar v True  )) | Just x <- lookup v vs = T (TBang x)
substType vs (T t) = T (fmap (substType vs) t)

-- Check for type well-formedness
validateType :: [VarName] -> RawType -> TcM TCType
validateType vs t = either (\e -> logErr e >> exitErr) return =<< lift (lift $ runExceptT $ validateType' vs t)

-- don't log erros, but instead return them
validateType' :: [VarName] -> RawType -> TcErrM TypeError TCType
validateType' vs (RT t) = do
  ts <- use knownTypes
  case t of
    TVar v _    | v `notElem` vs         -> throwE (UnknownTypeVariable v)
    TCon t as _ | Nothing <- lookup t ts -> throwE (UnknownTypeConstructor t)
                | Just (vs, _) <- lookup t ts
                , provided <- length as
                , required <- length vs
                , provided /= required
               -> throwE (TypeArgumentMismatch t provided required)
    TRecord fs _ | fields  <- map fst fs
                 , fields' <- nub fields
                -> if fields' == fields
                   then T <$> (mmapM (return . toSExpr) <=< mapM (validateType' vs)) t
                   else throwE (DuplicateRecordFields (fields \\ fields'))
    -- TArray te l -> check l >= 0  -- TODO!!!
    _ -> T <$> (mmapM (return . toSExpr) <=< mapM (validateType' vs)) t

validateTypes' :: (Traversable t) => [VarName] -> t RawType -> TcErrM TypeError (t TCType)
validateTypes' vs rs = mapM (validateType' vs) rs


-- Remove a pattern from a type, for case expressions.
removeCase :: LocPatn -> TCType -> TCType
removeCase (LocPatn _ (PIrrefutable _)) _ = (T (TVariant M.empty))
removeCase (LocPatn _ (PIntLit  _))     x = x
removeCase (LocPatn _ (PCharLit _))     x = x
removeCase (LocPatn _ (PBoolLit _))     x = x
removeCase (LocPatn _ (PCon t _))       x = (T (TTake (Just [t]) x))

flexOf (U x) = Just x
flexOf (T (TTake _ t))  = flexOf t
flexOf (T (TPut  _ t))  = flexOf t
flexOf (T (TBang  t))   = flexOf t
flexOf (T (TUnbox t))   = flexOf t
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
isMonoType (RT t) = getAll $ foldMap (All . isMonoType) t


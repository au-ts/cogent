--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE TemplateHaskell, DeriveFunctor, DeriveTraversable #-}
module Cogent.TypeCheck.Base where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Surface
import Cogent.Util

import Control.Lens hiding (Context, (:<))
import Control.Monad.Except
import Control.Monad.State
import Data.List (nub, (\\))
import qualified Data.Map as M
import qualified Data.IntMap as IM
-- import qualified Data.Set as S
import Data.Monoid ((<>))
import Text.Parsec.Pos


data TypeError = FunctionNotFound VarName
               | TooManyTypeArguments FunName (Polytype TCType)
               | NotInScope VarName
               | DuplicateVariableInPattern VarName (Pattern TCName)
               | DifferingNumberOfConArgs TagName Int Int
               | DuplicateVariableInIrrefPattern VarName (IrrefutablePattern TCName)
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
               | TakeFromNonRecord (Maybe [FieldName]) TCType
               | PutToNonRecord (Maybe [FieldName]) TCType
               | RemoveCaseFromNonVariant (Pattern TCName) TCType
               | DiscardWithoutMatch TagName
               | RequiredTakenTag TagName
               | TypeWarningAsError TypeWarning
               deriving (Eq, Show, Ord)

data TypeWarning = UnusedLocalBind VarName
                 deriving (Eq, Show, Ord)

type TypeEW = Either TypeError TypeWarning

-- FIXME: More fine-grained context is appreciated. e.g., only show alternatives that don't unify / zilinc
data ErrorContext = InExpression LocExpr TCType
                  | ThenBranch | ElseBranch
                  | SolvingConstraint Constraint
                  | NthAlternative Int (Pattern VarName)
                  | InDefinition SourcePos (TopLevel LocType VarName LocExpr)
                  | AntiquotedType LocType
                  | AntiquotedExpr LocExpr
                  deriving (Eq, Show)

data Bound = GLB | LUB deriving (Eq, Ord)
data VarOrigin = ExpressionAt SourcePos
               | BoundOf (TypeFragment TCType) (TypeFragment TCType) Bound
               deriving (Eq, Show, Ord)

flexOf (U x) = Just x
flexOf (T (TTake _ v)) = flexOf v
flexOf (T (TPut  _ v)) = flexOf v
flexOf (T (TBang v))   = flexOf v
flexOf (T (TUnbox v))  = flexOf v
flexOf _ = Nothing

instance Show Bound where
  show GLB = "lower bound"
  show LUB = "upper bound"

instance Ord ErrorContext where
  compare _ _ = EQ 

isCtxConstraint :: ErrorContext -> Bool
isCtxConstraint (SolvingConstraint _) = True
isCtxConstraint _ = False

-- high-level context at the end of the list
type ContextualisedEW = ([ErrorContext], TypeEW)

data TypeFragment a = F a
                    | FRecord [(FieldName, (a, Taken))]
                    | FVariant (M.Map TagName ([a], Taken))
                    deriving (Eq, Show, Functor, Foldable, Traversable, Ord)

data TCType = T (Type TCType)
            | U Int  -- unifier
            deriving (Show, Eq, Ord)

data TExpr t = TE { getType :: t, getExpr :: Expr t (VarName, t) (TExpr t), getLoc :: SourcePos }
             deriving (Show)

instance Functor TExpr where
  fmap f (TE t e p) = TE (f t) (fffmap f $ ffmap (fmap f) $ fmap (fmap f) e) p

type TCName = (VarName, TCType)
type TCExpr = TExpr TCType

type TypedName = (VarName, RawType)
type TypedExpr = TExpr RawType

toTCType :: RawType -> TCType
toTCType (RT x) = T (fmap toTCType x)

toLocExpr :: (SourcePos -> t -> LocType) -> TExpr t -> LocExpr
toLocExpr f (TE t e p) = LocExpr p (fffmap (f p) $ fmap (toLocExpr f) $ ffmap fst $ e)

toTypedExpr :: TCExpr -> TypedExpr
toTypedExpr = fmap toRawType

toTypedAlts :: [Alt TCName TCExpr] -> [Alt TypedName TypedExpr]
toTypedAlts = fmap (fmap (fmap toRawType) . ffmap (fmap toRawType))

-- Precondition: No unification variables left in the type
toLocType :: SourcePos -> TCType -> LocType
toLocType l (T x) = LocType l (fmap (toLocType l) x)
-- toLocType l (RemoveCase p t) = error "panic: removeCase found"
toLocType l _ = error "panic: unification variable found"
toRawType :: TCType -> RawType
toRawType (T x) = RT (fmap toRawType x)
-- toRawType (RemoveCase p t) = error "panic: removeCase found"
toRawType _ = error "panic: unification variable found"

toRawExp :: TypedExpr -> RawExpr
toRawExp (TE t e p) = RE (ffmap fst . fmap toRawExp $ e)

data Metadata = Reused { varName :: VarName, boundAt :: SourcePos, usedAt :: SourcePos }
              | Unused { varName :: VarName, boundAt :: SourcePos }
              | UnusedInOtherBranch { varName :: VarName, boundAt :: SourcePos, usedAt :: SourcePos }
              | UnusedInThisBranch  { varName :: VarName, boundAt :: SourcePos, usedAt :: SourcePos }
              | Suppressed
              | UsedInMember { fieldName :: FieldName }
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
                | Exhaustive TCType [Pattern TCName]
                deriving (Eq, Show, Ord)

instance Monoid Constraint where
  mempty = Sat
  mappend Sat x = x
  mappend x Sat = x
  -- mappend (Unsat r) x = Unsat r
  -- mappend x (Unsat r) = Unsat r
  mappend x y = x :& y

warnToConstraint :: Bool -> TypeWarning -> Constraint
warnToConstraint f w 
  | f = case __cogent_warning_switch of
          Flag_w -> Sat
          Flag_Wwarn -> SemiSat w
          Flag_Werror -> Unsat (TypeWarningAsError w)
  | otherwise = Sat

isWarnAsError :: ContextualisedEW -> Bool
isWarnAsError (_, Left (TypeWarningAsError _)) = True
isWarnAsError _ = False

data TCState = TCS { _knownFuns    :: M.Map FunName (Polytype TCType)
                   , _knownTypes   :: TypeDict
                   , _knownConsts  :: M.Map VarName (TCType, SourcePos)
                   }

type TypeDict = [(TypeName, ([VarName], Maybe TCType))]  -- `Nothing' for abstract types

makeLenses ''TCState

type TC = StateT TCState IO

kindToConstraint :: Kind -> TCType -> Metadata -> Constraint
kindToConstraint k t m = (if canEscape  k then Escape t m else Sat)
                      <> (if canDiscard k then Drop   t m else Sat)
                      <> (if canShare   k then Share  t m else Sat)

substType :: [(VarName, TCType)] -> TCType -> TCType
substType vs (U x) = U x
-- substType vs (RemoveCase p x) = RemoveCase (fmap (fmap (substType vs)) p) (substType vs x)
substType vs (T (TVar v False )) | Just x <- lookup v vs = x
substType vs (T (TVar v True  )) | Just x <- lookup v vs = T (TBang x)
substType vs (T t) = T (fmap (substType vs) t)

validateType :: [VarName] -> RawType -> ExceptT TypeError TC TCType
validateType vs (RT t) = do
  ts <- use knownTypes
  case t of
    TVar v _    | v `notElem` vs         -> throwError (UnknownTypeVariable v)
    TCon t as _ | Nothing <- lookup t ts -> throwError (UnknownTypeConstructor t)
                | Just (vs, _) <- lookup t ts
                , provided <- length as
                , required <- length vs
                , provided /= required
               -> throwError (TypeArgumentMismatch t provided required)
    TRecord ts _ | tags <- map fst ts
                 , tags' <- nub tags
                -> if tags' == tags then T <$> traverse (validateType vs) t
                   else throwError (DuplicateRecordFields (tags \\ tags'))
    _ -> T <$> traverse (validateType vs) t

-- Remove a pattern from a type, for case expressions.
removeCase :: Pattern x -> TCType -> TCType
removeCase (PIrrefutable _) _ = (T (TVariant M.empty))
removeCase (PIntLit _)      x = x
removeCase (PCharLit _)     x = x
removeCase (PBoolLit _)     x = x
removeCase (PCon t _)       x = (T (TTake (Just [t]) x))

forFlexes :: (Int -> TCType) -> TCType -> TCType
forFlexes f (U x) = f x
-- forFlexes f (RemoveCase p t) = let
--     p' = fmap (fmap (forFlexes f)) p
--     t' = forFlexes f t
--   in case removeCase p' t' of
--      Just t' -> t'
--      Nothing -> RemoveCase p' t'
forFlexes f (T x) = T (fmap (forFlexes f) x)


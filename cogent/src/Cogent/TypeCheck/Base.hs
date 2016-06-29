--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE TemplateHaskell #-}
module COGENT.TypeCheck.Base where

import COGENT.Common.Syntax
import COGENT.Util
import COGENT.Surface
import COGENT.Common.Types

import Control.Monad.State
import Control.Lens hiding (Context, (:<))
import Text.Parsec.Pos
import Data.Monoid ((<>))
import Control.Monad.Except

import qualified Data.Map as M

data TypeError = FunctionNotFound VarName
               | TooManyTypeArguments FunName (Polytype RawType)
               | NotInScope VarName
               | DuplicateVariableInPattern VarName (Pattern TCTypedName)
               | DuplicateVariableInIrrefPattern VarName (IrrefutablePattern TCTypedName)
               | UnknownTypeVariable VarName
               | UnknownTypeConstructor TypeName
               | TypeArgumentMismatch TypeName Int Int
               | TypeMismatch TCType TCType
               | RequiredTakenField FieldName TCType
               | TypeNotShareable TCType Metadata
               | TypeNotEscapable TCType Metadata
               | TypeNotDiscardable TCType Metadata
               | PatternsNotExhaustive TCType [TagName]
               | UnsolvedConstraint Constraint
               deriving (Show)


-- FIXME: More fine-grained context is appreciated. e.g., only show alternatives that don't unify / zilinc
data ErrorContext = InExpression LocExpr TCType
                  | ThenBranch | ElseBranch
                  | InExpressionOfType LocExpr RawType
                  | NthAlternative Int (Pattern VarName)
                  | InDefinition SourcePos (TopLevel LocType VarName LocExpr)
                  | AntiquotedType LocType
                  | AntiquotedExpr LocExpr
                  deriving (Show)

type TCTypedName = (VarName, TCType)

data TCType = T (Type TCType) | U Int | RemoveCase (Pattern TCTypedName) TCType deriving (Show, Eq)

data TExpr t = TE { getType :: t, getExpr :: Expr t (VarName, t) (TExpr t) }
             deriving (Show)


type TypedName = (VarName, RawType)

instance Functor TExpr where
  fmap f (TE t e) = TE (f t) (fffmap f $ ffmap (fmap f) $ fmap (fmap f) e)

type TypedExpr = TExpr RawType
type TCExpr    = TExpr TCType

toTCType :: RawType -> TCType
toTCType (RT x) = T (fmap toTCType x)

-- Precondition: No unification variables left in the type
toRawType :: TCType -> RawType
toRawType (T x) = RT (fmap toRawType x)
toRawType _ = error "panic: unification variable found"

data Metadata = Reused { varName :: VarName, boundAt :: SourcePos, usedAt :: SourcePos }
              | Unused { varName :: VarName, boundAt :: SourcePos}
              | UnusedInOtherBranch { varName :: VarName, boundAt :: SourcePos, usedAt :: SourcePos}
              | UnusedInThisBranch  { varName :: VarName, boundAt :: SourcePos, usedAt :: SourcePos}
              | Suppressed
              | UsedInMember { fieldName :: FieldName }
              | UsedInLetBang
              | TypeParam { functionName :: VarName, typeVarName :: VarName }
              | ImplicitlyTaken
              deriving (Show)

data Constraint = (:<) TCType TCType
                | (:<~) TCType TCType
                | (:&) Constraint Constraint
                | Share TCType Metadata
                | Drop TCType Metadata
                | Escape TCType Metadata
                | (:@) Constraint ErrorContext
                | Unsat TypeError
                | Sat
                | Exhaustive TCType [Pattern TCTypedName]
                deriving (Show)

instance Monoid Constraint where
  mempty = Sat
  mappend Sat x = x
  mappend x Sat = x
  mappend (Unsat r) x = Unsat r
  mappend x (Unsat r) = Unsat r
  mappend x y = x :& y

data TCState = TCS { _knownFuns    :: M.Map VarName (Polytype RawType)
                   , _knownTypes   :: [(TypeName, ([VarName], Maybe RawType))]  -- `Nothing' for abstract types
                   }

makeLenses ''TCState

type TC = State TCState

kindToConstraint :: Kind -> TCType -> Metadata -> Constraint
kindToConstraint k t m = (if canEscape  k then Escape t m else Sat)
                      <> (if canDiscard k then Drop   t m else Sat)
                      <> (if canShare   k then Share  t m else Sat)


substType :: [(VarName, TCType)] -> TCType -> TCType
substType vs (U x) = U x
substType vs (RemoveCase p x) = RemoveCase (fmap (fmap (substType vs)) p) (substType vs x)
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
    _ -> T <$> traverse (validateType vs) t

validateType' :: [VarName] -> RawType -> TC (Either TypeError TCType)
validateType' vs r = runExceptT (validateType vs r)

validateTypes' :: [VarName] -> [RawType] -> TC (Either TypeError [TCType])
validateTypes' vs rs = runExceptT (traverse (validateType vs) rs)


forFlexes :: (Int -> TCType) -> TCType -> TCType
forFlexes f (U x) = f x
forFlexes f (RemoveCase p t) = RemoveCase (fmap (fmap (forFlexes f)) p) (forFlexes f t)
forFlexes f (T x) = T (fmap (forFlexes f) x)

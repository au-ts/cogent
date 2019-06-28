-- |
-- Module      : Minigent.Syntax
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- Contains type definitions for all the syntax used in the compiler:
-- for types, expressions, constraints and so on.
--
-- It expects to be imported unqualified.
{-# LANGUAGE PatternSynonyms #-}
module Minigent.Syntax
  ( -- * Names
    -- | All names in the syntax tree are represented with 'String'.
    VarName
  , FunName
  , ConName
  , AbsTypeName
  , FieldName
  , -- * Types
    Type (..)
  , Sigil (..)
  , PrimType (..)
  , -- ** Entries and Rows
    Row (..)
  , Entry (..)
  , Taken
  , -- * Constraints
    Constraint (..)
  , pattern (:>)
  , -- * Expressions
    Expr (..)
  , Op (..)
  , PrimValue (..)
  , -- * Toplevels and Polytypes
    RawTopLevel (..)
  , PolyType (..)
  ) where


import qualified Data.Map as M

-- | Binary and Unary Operators
data Op
  = Plus | Times | Minus | Divide | Mod
  | Less | Greater | LessEqual | GreaterEqual
  | Equal | NotEqual
  | And | Or | Not
  deriving (Show, Eq)

type FieldName = String
type VarName = String
type ConName = String
type FunName = String
type AbsTypeName = String

-- | A field or alternative is marked /taken/ if it is unpacked with a 'Take' expression
--   or matched on with a 'Case' expression. 
type Taken = Bool
-- | An entry is either a record field or a variant alternative, consisting of a field or
--   constructor name, a type, and whether or not the field or alternative is taken.
data Entry = Entry String Type Taken -- Used for both Record and Variant
     deriving (Show, Eq)

-- | Primitive types are represented using machine word types.
data PrimType = Unit | Bool | U8 | U16 | U32 | U64
     deriving (Show, Eq)

-- | Sigils, used in boxed records and abstract types, indicate whether a type is an
--   unboxed data structure, a boxed read-only data structure, or a boxed read/write
--   data structure which must be linearly typed.
--
--   Unification variables may also stand for sigils during type inference.
data Sigil
  = Unboxed | ReadOnly | Writable
  | UnknownSigil VarName -- ^ Used only for type inference.
  deriving (Show, Eq)


-- | A row is the contents of either a record or variant type. Each 'Entry' in the
--   row corresponds to a field or alternative in the type. In addition, during type
--   inference a row may also contain a unification variable to stand for further
--   entries that are not yet known.
data Row
  = Row
    { rowEntries :: M.Map FieldName Entry
    , rowVar :: Maybe VarName -- ^ Used only in type inference.
    } deriving (Show, Eq)

-- | A type, which may contain unification variables or type operators.
data Type
  = PrimType PrimType
  | Record (Maybe VarName) Row Sigil -- ^ A recursive parameter, field entry list and sigil
  | AbsType AbsTypeName Sigil [Type]
  | Variant Row
  | TypeVar VarName -- ^ Refers to a rigid type variable bound with a forall.
  | TypeVarBang VarName -- ^ A 'TypeVar' with 'Bang' applied.
  | Function Type Type
  -- used in type inference:
  | UnifVar VarName -- ^ Stands for an unknown type
  | Bang Type -- ^ Eliminated by type normalisation.
  deriving (Show, Eq)

-- | Used for literals.
data PrimValue = BoolV Bool | IntV Integer | UnitV
     deriving (Show, Eq)

-- | Basic minicogent expressions.
data Expr
  = PrimOp Op [Expr]  -- ^ Primitive operators with one or two arguments.
  | Literal PrimValue -- ^ Basic primitive type literals.
  | Var VarName       -- ^ Variables, identified by name. Shadowing is allowed.
  | Con ConName Expr  -- ^ A variant constructor applied to an argument.
  | TypeApp FunName [Type] -- ^ A function applied to zero or more type arguments.
  | Sig Expr Type     -- ^ An explicit type annotation. Added to all expressions by type inference.
  | Apply Expr Expr   -- ^ Function application.
  | Struct [(FieldName, Expr)] -- ^ Unboxed record literals.
  | If Expr Expr Expr -- ^ Ordinary conditionals. Condition, then, else.
  | Let VarName Expr Expr -- ^ A let expression. Not that @let@ doesn't imply type generalisation.
  | LetBang [VarName] VarName Expr Expr -- ^ Like let, but allows for observers to be made of the
                                        --   given variables.
  | Take VarName FieldName VarName Expr Expr -- ^ A take expression, the first 'VarName' denotes
                                             --   the name of the remaining record, the second
                                             --   is the name for the contents of the taken field.
                                             --   The first expression is the record to take from,
                                             --   and the second expression is the scope of the
                                             --   two new variables.
  | Put Expr FieldName Expr -- ^ A put expression. The first expression is the incomplete record
                            --   with the given field taken. The second expression evaluates to
                            --   a compatible value that can be placed inside the incomplete
                            --   record and then returned.
  | Member Expr FieldName -- ^ Extracting a field from a (non-linear) record.
  | Case Expr ConName VarName Expr VarName Expr
    -- ^ A refutable case expression where the first expression is
    --   the scrutinee to match on. After that, the first 'VarName' and 'Expr' denote the variable
    --   name bound and expression to run if the given scrutinee matches the given constructor.
    --   The second 'VarName' and 'Expr' are likewise for the default, fallback case. In this
    --   case, the variable bound will have the same type as the scrutinee, only with the constructor
    --   marked as 'Taken'.
  | Esac Expr ConName VarName Expr
    -- ^ An irrefutable pattern match expression. Here, the scrutinee must provably
    --   match the provided constructor.
  | Roll Expr   -- Recursive type rolling
  | Unroll Expr -- Recursive type unravelling
  deriving (Show, Eq)

infixr 0 :&:

-- | Constraints used for type inference.
data Constraint
  = Constraint :&: Constraint -- ^ Conjunction.
  | Type :< Type -- ^ Subtyping. Antisymmetry gives type equality constraints.
  | Type :=: Type -- ^ Type equality.
  | Integer :<=: Type -- ^ The 'fits in' relation, that says a given literal fits in the given
                      --   type. Only satisfiable if the type is a numeric type.
  | Share Type     -- ^ The given type can be duplicated or shared freely
  | Drop Type      -- ^ The given type can go out of scope without being used
  | Escape Type    -- ^ The given type can be safely bound in a 'LetBang' expression
  | Exhausted Type -- ^ The given type is a variant type where all entries are 'Taken'.
  | Sat            -- ^ Trivially true.
  | Unsat          -- ^ Trivially false.
  deriving (Show, Eq)

pattern (:>) t1 t2 = t2 :< t1

-- | A polymorphic type, used for top-level bindings only.
--   Given a list of type variable names, constraints on those type variables (right now,
--   only 'Share', 'Drop' and 'Escape' constraints are supported), and a list of recursive (mu) parameters.
data PolyType = Forall [VarName] [Constraint] Type
     deriving (Show, Eq)

-- | A top level declaration is either a type signature for a function
--   or a definition for a function.
data RawTopLevel
  = TypeSig FunName PolyType -- ^ @f : t@
  | Equation FunName VarName Expr -- ^ @f x = e@
  deriving (Show, Eq)

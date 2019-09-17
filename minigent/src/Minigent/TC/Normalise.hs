-- |
-- Module      : Minigent.TC.Normalise
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- The normalise rewrite for types, which applies type operators.
--
-- May be used qualified or unqualified.
module Minigent.TC.Normalise (normaliseConstraints) where
import Data.List (nub)
import Minigent.Syntax
import Minigent.Syntax.Utils
import Minigent.Syntax.Utils.Rewrite
import qualified Minigent.Syntax.Utils.Row as Row

bangRW :: Rewrite Type
bangRW = rewrite $ \t -> case t of
    Bang (Function t1 t2)  -> Just (Function t1 t2)
    Bang (AbsType n s ts)  -> Just (AbsType n (bangSigil s) (map Bang ts))
    Bang (TypeVar a)       -> Just (TypeVarBang a)
    Bang (TypeVarBang a)   -> Just (TypeVarBang a)
    Bang (PrimType t)      -> Just (PrimType t)
    Bang (Variant r)  | rowVar r == Nothing
      -> Just (Variant (Row.mapEntries (entryTypes Bang) r))
    Bang (Record _ r s) | rowVar r == Nothing, s == ReadOnly || s == Writable || s == Unboxed
      -> Just (Record undefined (Row.mapEntries (entryTypes Bang) r) (bangSigil s))
    _                      -> Nothing
  where
    bangSigil Writable = ReadOnly
    bangSigil x        = x


-- | Normalise all types within a set of constraints
normaliseConstraints :: [Constraint] -> [Constraint]
normaliseConstraints = nub . map (constraintTypes (normaliseType bangRW))

-- |
-- Module      : Minigent.Syntax.Utils
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- This module provides various miscellaneous utility functions for querying
-- and manipulating syntax.
--
-- It expects to be imported unqualified.
module Minigent.Syntax.Utils
  ( -- * Operators
    operators
  , -- ** Operator categories
    -- | The various syntactic precendence categories of binary operators
    prodOps
  , sumOps
  , compOps
  , boolOps
  , -- * Constraints
    flattenConstraint
  , conjunction
  , constraintTypes
  , -- * Types
    -- ** Applying rewrites
    traverseType
  , normaliseType
  , sameRecursive
  , unroll
  , mapRecPars
  , -- ** Rewrites
    substUV
  , substRowV
  , substSigilV
  , substTV
  , substUVs
  , substTVs
  , substRecPar
  , -- ** Queries for type inference
    fits
  , unorderedType
  , typeUVs
  , typeVariables
  , recursiveParameterNames
  , rigid
  , rootUnifVar
  , -- * Entries
    entryTypes
  , -- * Sigils
    sigilsCompatible
  , -- * Expressions
    exprTypes
  , -- * Fresh Unification Variables
    unifVars
  , withUnifVars
  , -- * Field manipulation
    updateField
  )
where

import           Minigent.Syntax
import           Minigent.Fresh
import qualified Minigent.Syntax.Utils.Rewrite as RW
import qualified Minigent.Syntax.Utils.Row     as Row


import           Control.Applicative
import           Control.Monad                  ( guard )
import           Data.Maybe                     ( fromMaybe
                                                , maybeToList
                                                , isNothing
                                                )

import qualified Data.Stream                   as S
import qualified Data.Map                      as M

-- | Returns true iff the given argument type is not subject to subtyping. That is, if @a :\< b@
--   (subtyping) is equivalent to @a :=: b@ (equality), then this function returns true.
--
--   At least for now, this returns true for all types but variants, records and functions.
unorderedType :: Type -> Bool
unorderedType (Record{}  ) = False
unorderedType (Variant{} ) = False
unorderedType (Function{}) = False
unorderedType t            = rigid t

-- | Return all of the unification type variables inside a type.
typeUVs :: Type -> [VarName]
typeUVs (UnifVar v) = [v]
typeUVs (Record n r s) = concatMap (\(Entry _ t _) -> typeUVs t) (Row.entries r)
                    ++ maybe [] pure (rowVar r)
                    ++ (case s of UnknownSigil     s' -> [s']; _ -> [])
                    ++ (case n of UnknownParameter n' -> [n']; _ -> [])
typeUVs (Variant r)  = concatMap (\(Entry _ t _) -> typeUVs t) (Row.entries r)
                    ++ maybe [] pure (rowVar r)
typeUVs (AbsType _ _ ts) = concatMap typeUVs ts
typeUVs (Function t1 t2) = typeUVs t1 ++ typeUVs t2
typeUVs (Bang t        ) = typeUVs t
typeUVs _                = []

-- | Return all of the (rigid, non-unification) type variables in a type. Does not include mu variables
typeVariables :: Type -> [VarName]
typeVariables t = typeVariables' t []
 where
    -- Ensures recursive parameters are not included in type variables
  typeVariables' :: Type -> [VarName] -> [VarName]
  typeVariables' (TypeVar     v) mvs = if elem v mvs then [] else [v]
  typeVariables' (TypeVarBang v) mvs = if elem v mvs then [] else [v]
  typeVariables' (Record mt r _) mvs = concatMap
    (\(Entry _ t _) -> typeVariables' t ((case mt of Rec x -> [x]; _ -> []) ++ mvs))
    (Row.entries r)
  typeVariables' (Variant r) mvs      = concatMap (\(Entry _ t _) -> typeVariables' t mvs) (Row.entries r)
  typeVariables' (AbsType _ _ ts) mvs = concatMap (\x -> typeVariables' x mvs) ts
  typeVariables' (Function t1 t2) mvs = typeVariables' t1 mvs ++ typeVariables' t2 mvs
  typeVariables' (Bang t        ) mvs = typeVariables' t mvs
  typeVariables' _                _   = []

recursiveParameterNames :: Type -> [VarName]
recursiveParameterNames (Record mt r _) = case mt of Rec x -> [x]; _ -> []
  ++ concatMap (\(Entry _ t _) -> recursiveParameterNames t) (Row.entries r)
recursiveParameterNames (Variant r) =
  concatMap (\(Entry _ t _) -> recursiveParameterNames t) (Row.entries r)
recursiveParameterNames (AbsType _ _ ts) = concatMap recursiveParameterNames ts
recursiveParameterNames (Function t1 t2) = recursiveParameterNames t1 ++ recursiveParameterNames t2
recursiveParameterNames (Bang t        ) = recursiveParameterNames t
recursiveParameterNames _                = []


-- | Returns @True@ unless the given type is a unification variable or a type operator
--   applied to a unification variable.
rigid :: Type -> Bool
rigid (UnifVar _)  = False
rigid (Bang _)     = False
rigid (Record _ r _) = not $ Row.justVar r
rigid (Variant r)  = not $ Row.justVar r
rigid _            = True

-- | Return the unification variable in a non-rigid type.
--   If the type is rigid, then returns @Nothing@.
rootUnifVar :: Type -> Maybe VarName
rootUnifVar (UnifVar n   ) = Just n
rootUnifVar (Bang    n   ) = rootUnifVar n
rootUnifVar (Variant r   ) = rowVar r
rootUnifVar (Record _ r s) = rowVar r
rootUnifVar _              = Nothing

-- | A table of all operators, mapping string representations
--   to their 'Op' values.
operators :: [(String, Op)]
operators =
  [ ("+" , Plus)
  , ("*" , Times)
  , ("-" , Minus)
  , ("/" , Divide)
  , ("%" , Mod)
  , ("<" , Less)
  , (">" , Greater)
  , ("==", Equal)
  , ("/=", NotEqual)
  , ("<=", LessEqual)
  , (">=", GreaterEqual)
  , ("&&", And)
  , ("||", Or)
  , ("~" , Not)
  ]

prodOps, sumOps, compOps, boolOps :: [Op]
prodOps = [Times, Divide, Mod]
sumOps = [Plus, Minus]
compOps = [Equal, NotEqual, Greater, Less, GreaterEqual, LessEqual]
boolOps = [And, Or, Not]

-- | Given a constraint, flatten it out to remove all conjunctions,
--   returning a list of conjunction-free constraints.
flattenConstraint :: Constraint -> [Constraint]
flattenConstraint (a :&: b) = flattenConstraint a ++ flattenConstraint b
flattenConstraint x         = [x]

-- | Given a list of constraints, combine them into one constraint
--   using constraint conjunction.
conjunction :: [Constraint] -> Constraint
conjunction = foldr (:&:) Sat

-- | Given a function that acts on 'Type' values, produce a function
--   that acts on the type inside 'Entry' values.
entryTypes :: (Type -> Type) -> Entry -> Entry
entryTypes func (Entry f t k) = Entry f (func t) k

-- | Given a function that acts on 'Type' values, produce a function
--   that acts on the types inside 'Constraint' values.
constraintTypes :: (Type -> Type) -> Constraint -> Constraint
constraintTypes func constraint = go constraint
  where
    go (c1 :&: c2)             = go c1 :&: go c2
    go (i :<=: t)              = i :<=: func t
    go (Share     t)           = Share     (func t)
    go (Drop      t)           = Drop      (func t)
    go (Escape    t)           = Escape    (func t)
    go (Exhausted t)           = Exhausted (func t)
    go (t1  :<  t2 )           = func t1 :< func t2
    go (t1  :=: t2 )           = func t1 :=: func t2
    go (Solved t)              = Solved $ func t
    go (UnboxedNoRecurse rp s) = UnboxedNoRecurse rp s
    go Sat                     = Sat
    go Unsat                   = Unsat


-- | Given a function that acts on 'Type' values, produce a function
--   that acts on the types inside an 'Expr'.
exprTypes :: (Type -> Type) -> Expr -> Expr
exprTypes func expr = go expr
 where
  go (TypeApp f  ts     ) = TypeApp f (map func ts)
  go (Sig     e  t      ) = Sig (go e) (func t)
  go (PrimOp  o  es     ) = PrimOp o (map go es)
  go (Con     n  e      ) = Con n (go e)
  go (Apply   e1 e2     ) = Apply (go e1) (go e2)
  go (Struct fs         ) = Struct (map (fmap go) fs)
  go (If  e e1 e2       ) = If (go e) (go e1) (go e2)
  go (Let v e1 e2       ) = Let v (go e1) (go e2)
  go (LetBang vs v e1 e2) = LetBang vs v (go e1) (go e2)
  go (Take r f v e1 e2  ) = Take r f v (go e1) (go e2)
  go (Put e1 f e2       ) = Put (go e1) f (go e2)
  go (Member e f        ) = Member (go e) f
  go (Case e k x e1 y e2) = Case (go e) k x (go e1) y (go e2)
  go (Esac e k x e1     ) = Esac (go e) k x (go e1)
  go e                    = e

-- | Given a 'RW.Rewrite' on types, apply it over every subterm in a type, i.e. recursively applying
--   the rewrite to every subterm.
--
--   If the rewrite succeeds on a subterm, the rewrite is not run again on the result. Therefore,
--   this is guaranteed to terminate.
--
--   This could be accomplished with a datatype generics library but is overkill in this case I
--   think.
traverseType :: (RW.Rewrite Type) -> Type -> Type
traverseType func ty = case RW.run func ty of
  Just t' -> t'
  Nothing -> case ty of
    Record n es s ->
      Record n (Row.mapEntries (entryTypes (traverseType func)) es) s
    AbsType n s ts -> AbsType n s (map (traverseType func) ts)
    Variant es -> Variant (Row.mapEntries (entryTypes (traverseType func)) es)
    Function t1 t2 -> Function (traverseType func t1) (traverseType func t2)
    Bang t         -> Bang (traverseType func t)
    _              -> ty

-- | Given a 'RW.Rewrite' on types, apply it over every subterm in a type, i.e. recursively applying
--   the rewrite to every subterm.
--
--   If the rewrite succeeds on a subterm, the rewrite *is* run again on the result. Therefore,
--   the rewrite must be a reduction or this function will not terminate.
--
--   If this function terminates, the result is guaranteed not to contain any further reducible
--   subterm.
normaliseType :: (RW.Rewrite Type) -> Type -> Type
normaliseType func ty =
  let t' = fromMaybe ty (RW.run func ty)
  in
    case t' of
      Record n es s ->
        Record n (Row.mapEntries (entryTypes (normaliseType func)) es) s
      AbsType n s ts -> AbsType n s (map (normaliseType func) ts)
      Variant es ->
        Variant (Row.mapEntries (entryTypes (normaliseType func)) es)
      Function t1 t2 ->
        Function (normaliseType func t1) (normaliseType func t2)
      Bang t -> Bang (normaliseType func t)
      _      -> t'


-- | Checks if two recursive parameter bindings are the same type
sameRecursive :: RecPar -> RecPar -> Bool
sameRecursive (Rec _) (Rec _) = True
sameRecursive None    None    = True
sameRecursive _       _       = False

-- | Unrolls a recursive parameter to the record it references
unroll :: RecParName -> RecContext -> Type
unroll n (Just ctxt) = mapRecPars (Just ctxt)  (ctxt M.! n)
unroll _ _ = error "Impossible: cannot unroll a recursive parameter with an empty context"

-- | Given a context, changes all recursive parameter references from TypeVar to RecPar according to the context
mapRecPars :: RecContext -> Type -> Type
mapRecPars ctxt (AbsType n s ts)   = AbsType n s $ map (mapRecPars ctxt) ts
mapRecPars ctxt (Variant row)      = Variant $ Row.mapEntries (\(Entry n t tk) -> Entry n (mapRecPars ctxt t) tk) row
mapRecPars ctxt (Bang t)           = Bang $ mapRecPars ctxt t
mapRecPars ctxt (RecPar n Nothing    ) = RecPar n ctxt
mapRecPars ctxt (RecParBang n Nothing) = RecParBang n ctxt
mapRecPars ctxt (RecPar n _    ) = error "Impossible: mapRecPars found a recursive parameter with a context inside a context"
mapRecPars ctxt (RecParBang n _) = error "Impossible: mapRecPars found a recursive parameter (banged) with a context inside a context"
mapRecPars (Just ctxt) r@(Record par row s) = 
  Record par (Row.mapEntries (\(Entry n t tk) -> Entry n (mapRecPars (addRecPar par) t) tk) row) s
  where addRecPar p = Just $ case p of
                        Rec v -> (M.insert v r ctxt)
                        _ -> ctxt
mapRecPars ctxt (Function a b) = Function (mapRecPars ctxt a) (mapRecPars ctxt b)
mapRecPars _ t = t



-- | A rewrite that substitutes a given unification type variable for a type term in a type.
substUV :: (VarName, Type) -> RW.Rewrite Type
substUV (x, t) = RW.rewrite $
  \t' -> case t' of
    (UnifVar v) | x == v -> Just t
    _                    -> Nothing

-- | A rewrite that substitutes a given unification row variable for a row in a type.
substRowV :: (VarName, Row) -> RW.Rewrite Type
substRowV (x, (Row m' q)) = RW.rewrite $
  \t' -> case t' of
    Variant (Row m (Just v)) | x == v -> Just (Variant (Row (M.union m m') q))
    Record n (Row m (Just v)) s | x == v ->
      Just (Record n (Row (M.union m m') q) s)
    _ -> Nothing

-- | A rewrite that substitutes a given unification sigil variable for a sigil in a type.
substSigilV :: (VarName, Sigil) -> RW.Rewrite Type
substSigilV (x, s) = RW.rewrite $
  \t' -> case t' of
    Record n r (UnknownSigil v) | x == v -> Just (Record n r s)
    _ -> Nothing

-- | A rewrite that substitutes a rigid type variable for a type term in a type.
substTV :: (VarName, Type) -> RW.Rewrite Type
substTV (x, t) = RW.rewrite $
  \t' -> case t' of
    (TypeVar v) | x == v     -> Just t
    (TypeVarBang v) | x == v -> Just (Bang t)
    _                        -> Nothing

-- | A rewrite that substitutes the unkown recursive parameter on a boxed record for a parameter
substRecPar :: (VarName, RecPar) -> RW.Rewrite Type
substRecPar (v1, v2) = RW.rewrite $
  \t' -> case t' of
    Record (UnknownParameter n) r s | n == v1 -> 
      Just (Record v2 r s)
    _ -> Nothing

-- | A convenience that allows multiple substitutions to type variables to be made simulatenously.
substTVs :: [(VarName, Type)] -> RW.Rewrite Type
substTVs = foldMap substTV

-- | A convenience that allows multiple substitutions to unification type variables to be made
--   simulatenously.
substUVs :: [(VarName, Type)] -> RW.Rewrite Type
substUVs = foldMap substUV

-- | Just 'traverseType' composed with 'substTVs'
traverseSubstTVs :: [(VarName, Type)] -> Type -> Type
traverseSubstTVs = traverseType . substTVs


-- | Returns @True@ iff the given integer fits within the given primitive type without overflow.
fits :: Integer -> PrimType -> Bool
fits i U8  = i >= 0 && i <= 255
fits i U16 = i >= 0 && i <= 65535
fits i U32 = i >= 0 && i <= 4294967295
fits i U64 = i >= 0 && i <= 18446744073709551615
fits _ _   = False

-- | Returns @True@ if the two inputs are equal, or if either of them are an unknown sigil
--   variable (morally, in this case the two inputs could be made equal by unification).
sigilsCompatible :: Sigil -> Sigil -> Bool
sigilsCompatible (UnknownSigil{}) y                = True
sigilsCompatible x                (UnknownSigil{}) = True
sigilsCompatible x                y                = x == y

-- | Run a 'Fresh' computation with 'unifVars' as the source of fresh names.
withUnifVars :: Monad m => FreshT VarName m a -> m a
withUnifVars fr = evalFreshT unifVars fr

-- | A stream of greek unification variable names.
unifVars :: S.Stream VarName
unifVars = S.fromList names
  where
    names = [ g:n | n <- nums, g <- "𝛂𝛃𝛄𝛅𝛆𝛇𝛈𝛉𝛊𝛋𝛍𝛎𝛏𝛑𝛖𝛗𝛘𝛙" ]
    nums = "":map show [1 :: Integer ..]

updateField :: Eq a => a -> b -> [(a,b)] -> [(a,b)]
updateField a0 b0 ((a1,b1):fs)
  | a0 == a1 = (a0,b0) : fs
  | otherwise = (a1,b1) : updateField a0 b0 fs
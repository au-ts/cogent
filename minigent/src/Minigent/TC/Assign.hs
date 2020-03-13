-- |
-- Module      : Minigent.TC.Assign
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- A module for solver assignments to unification variables.
--
-- May be imported unqualified.
module Minigent.TC.Assign
  ( Assign (..) 
  , substAssign
  , substsToMaps
  , substConstraint'
  ) where 

import Minigent.Syntax
import Minigent.Syntax.Utils

import Data.Maybe (fromMaybe)
import qualified Data.Map as M

import qualified Minigent.Syntax.Utils.Row as Row
import qualified Minigent.Syntax.Utils.Rewrite as Rewrite

-- | An assignment to a unification variable.
data Assign = TyAssign VarName Type
            | RowAssign VarName Row
            | SigilAssign VarName Sigil
            | RecParAssign VarName RecPar
            deriving (Show)

-- | Apply an assignment to a unification variable to a type.
substAssign :: Assign -> Rewrite.Rewrite Type
substAssign (TyAssign v t) = substUV (v, t)
substAssign (RowAssign v t) = substRowV (v, t)
substAssign (SigilAssign v t) = substSigilV (v, t)
substAssign (RecParAssign v1 v2) = substRecPar (v1, v2)

-- Assumes: that substitutions do not substitute for variables in other given substitutions
substsToMaps :: [Assign] -> (M.Map VarName Type, M.Map VarName RecPar, M.Map VarName Row, M.Map VarName Sigil)
substsToMaps [] = (M.empty, M.empty, M.empty, M.empty)
substsToMaps (TyAssign v t : substs) =
  let (munif, mrp, mrow, ms) = substsToMaps substs
   in (M.insert v t munif, mrp, mrow, ms)
substsToMaps (RowAssign v r : substs) =
  let (munif, mrp, mrow, ms) = substsToMaps substs
      r' = substRow' munif mrp mrow ms r
   in (munif, mrp, M.insert v r' mrow, ms)
substsToMaps (SigilAssign v s : substs) =
  let (munif, mrp, mrow, ms) = substsToMaps substs
   in (munif, mrp, mrow, M.insert v s ms)
substsToMaps (RecParAssign v rp : substs) =
  let (munif, mrp, mrow, ms) = substsToMaps substs
   in (munif, M.insert v rp mrp, mrow, ms)


substAssign' :: M.Map VarName Type -> 
                M.Map VarName RecPar ->
                M.Map VarName Row ->
                M.Map VarName Sigil ->
                Assign -> Assign
substAssign' munif mrp mrow ms = go
 where
  go (TyAssign     v t ) = TyAssign v $ substType' munif mrp mrow ms t
  go (RowAssign    v r ) = RowAssign v $ substRow' munif mrp mrow ms r
  go (SigilAssign  v s ) = SigilAssign v $ substSigil' ms s
  go (RecParAssign v rp) = RecParAssign v $ substRecPar' mrp rp

substConstraint' :: M.Map VarName Type -> 
                    M.Map VarName RecPar ->
                    M.Map VarName Row ->
                    M.Map VarName Sigil ->
                    Constraint -> Constraint
substConstraint' munif mrp mrow ms = go
 where
  go (c1 :&: c2)             = go c1 :&: go c2
  go (i :<=: t)              = i :<=: substTy t
  go (Share     t)           = Share $ substTy t
  go (Drop      t)           = Drop $ substTy t
  go (Escape    t)           = Escape $ substTy t
  go (Exhausted t)           = Exhausted $ substTy t
  go (t1  :<  t2 )           = substTy t1 :< substTy t2
  go (t1  :=: t2 )           = substTy t1 :=: substTy t2
  go (Solved t)              = Solved $ substTy t
  go (UnboxedNoRecurse rp s) = UnboxedNoRecurse (substRecPar' mrp rp) (substSigil' ms s)
  go Sat                     = Sat
  go Unsat                   = Unsat

  substTy = substType' munif mrp mrow ms

substType' :: M.Map VarName Type -> 
              M.Map VarName RecPar ->
              M.Map VarName Row ->
              M.Map VarName Sigil ->
              Type -> Type
substType' munif mrp mrow ms = go
 where
  go (PrimType pt) = PrimType pt
  go (Record rp r s) =
    let rp' = substRecPar' mrp rp
        r' = substRow' munif mrp mrow ms r
        s' = substSigil' ms s
     in Record rp' r' s'
  go (AbsType n s ts) =
    let s' = substSigil' ms s
        ts' = map go ts
     in  AbsType n s' ts'
  go (Variant r) = Variant $ substRow' munif mrp mrow ms r
  go (TypeVar v)      = TypeVar v
  go (TypeVarBang v)  = TypeVarBang v
  go (RecPar p c)     = RecPar p c
  go (RecParBang p c) = RecParBang p c
  go (Function t1 t2) = Function (go t1) (go t2)
  go t@(UnifVar v)    = fromMaybe t $ munif M.!? v
  go (Bang t)         = Bang $ go t

substRecPar' :: M.Map VarName RecPar -> RecPar -> RecPar
substRecPar' mrp rp@(UnknownParameter v) = fromMaybe rp $ mrp M.!? v
substRecPar' _ rp = rp

substSigil' :: M.Map VarName Sigil -> Sigil -> Sigil
substSigil' ms s@(UnknownSigil v) = fromMaybe s $ ms M.!? v
substSigil' _ s = s

substRow' :: M.Map VarName Type ->
             M.Map VarName RecPar ->
             M.Map VarName Row ->
             M.Map VarName Sigil ->
             Row -> Row
substRow' munif mrp mrow ms (Row m0 rvar) =
  let m1 = M.map (\(Entry n t tk) -> Entry n (substType' munif mrp mrow ms t) tk) m0
   in case rvar of
        (Just v) | Just (Row m' v') <- mrow M.!? v
                 -> Row (M.union m' m1) v'
        rvar     -> Row m1 rvar

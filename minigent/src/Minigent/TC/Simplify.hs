-- |
-- Module      : Minigent.TC.Simplify
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- The simplify phase of the solver.
--
-- May be used qualified or unqualified.
module Minigent.TC.Simplify where

import Minigent.Syntax
import Minigent.Syntax.Utils
import qualified Minigent.Syntax.Utils.Row     as Row
import qualified Minigent.Syntax.Utils.Rewrite as Rewrite

import Control.Monad
import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Foldable (toList)

import Minigent.Syntax.PrettyPrint
import Debug.Trace 

-- | Rewrite a set of constraints, removing all trivially satisfiable constraints
--   and breaking down large constraints into smaller ones.
simplify :: [Constraint] -> Rewrite.Rewrite [Constraint]
simplify axs = Rewrite.pickOne $ \c -> -- trace ("About to simpliy:\n" ++ debugPrettyConstraints [c]) $ 
  case c of
  c | c `elem` axs                    -> Just []
  Sat                                 -> Just []
  c1 :&: c2                           -> Just [c1,c2]
  Drop   (PrimType _)                 -> Just []
  Share  (PrimType _)                 -> Just []
  Escape (PrimType _)                 -> Just []
  Drop   (Function _ _)               -> Just []
  Share  (Function _ _)               -> Just []
  Escape (Function _ _)               -> Just []
  Drop   (TypeVarBang _)              -> Just []
  Share  (TypeVarBang _)              -> Just []
  Drop   (RecParBang _ _)             -> Just []
  Share  (RecParBang _ _)             -> Just []
  -- TODO: Drop/Share RecParBang?
  Share  (Variant es)                 -> guard (rowVar es == Nothing)
                                      >> Just (map Share  (Row.untakenTypes es))
  Drop   (Variant es)                 -> guard (rowVar es == Nothing)
                                      >> Just (map Drop   (Row.untakenTypes es))
  Escape (Variant es)                 -> guard (rowVar es == Nothing)
                                      >> Just (map Escape (Row.untakenTypes es))
  Share  (AbsType n s ts)             -> guard (s == ReadOnly || s == Unboxed)
                                      >> Just (map Share  ts)
  Drop   (AbsType n s ts)             -> guard (s == ReadOnly || s == Unboxed)
                                      >> Just (map Drop   ts)
  Escape (AbsType n s ts)             -> guard (s == Writable || s == Unboxed)
                                      >> Just (map Escape ts)
  Share  (Record n es s)              -> guard (s == ReadOnly || s == Unboxed)
                                      >> guard (rowVar es == Nothing)
                                      >> Just (map Share (Row.untakenTypes es))
  Drop   (Record n es s)              -> guard (s == ReadOnly || s == Unboxed)
                                      >> guard (rowVar es == Nothing)
                                      >> Just (map Drop (Row.untakenTypes es))
  Escape (Record n es s)              -> guard (s == Writable || s == Unboxed)
                                      >> guard (rowVar es == Nothing)
                                      >> Just (map Escape (Row.untakenTypes es))
  Exhausted (Variant es)              -> guard (null (Row.untakenTypes es) && rowVar es == Nothing)
                                      >> Just []
  i :<=: PrimType t                   -> guard (fits i t) >> Just []

  Function t1 t2 :< Function r1 r2    -> Just [r1 :< t1, t2 :< r2]
  Function t1 t2 :=: Function r1 r2   -> Just [r1 :=: t1, t2 :=: r2]

  Variant r1     :< Variant r2        ->
    if Row.null r1 && Row.null r2 then Just []
    else if Row.null r1 && null (Row.entries r2)
         || Row.null r2 && null (Row.entries r1)  
         then Just [Variant r1 :=: Variant r2]
    else do
    let commons  = Row.common r1 r2
        (ls, rs) = unzip commons
    guard (not (null commons))
    guard (untakenLabels ls `S.isSubsetOf` untakenLabels rs)
    let (r1',r2') = Row.withoutCommon r1 r2
        cs = map (\(Entry _ t _, Entry _ t' _) -> t :< t') commons
        c   = Variant r1' :< Variant r2'
    Just (c:cs)

  Record n1 r1 s1  :< Record n2 r2 s2 ->
    if Row.null r1 && Row.null r2 && s1 == s2 && n1 == n2 then Just []
    else if Row.null r1 && null (Row.entries r2)
         || Row.null r2 && null (Row.entries r1)  
         then Just [Record n1 r1 s1 :=: Record n2 r2 s2]
    else do
    let commons  = Row.common r1 r2
        (ls, rs) = unzip commons
    guard (not (null commons))
    guard (untakenLabels rs `S.isSubsetOf` untakenLabels ls)
    let (r1',r2') = Row.withoutCommon r1 r2
        cs = map (\(Entry _ t _, Entry _ t' _) -> t :< t') commons
        ds = map Drop (Row.typesFor (untakenLabels ls S.\\ untakenLabels rs) r1)
        c  = Record n1 r1' s1 :< Record n2 r2' s2
    Just (c:cs ++ ds)

  RecPar n ctxt :< RecPar n' ctxt' ->  guard (ctxt M.! n == ctxt M.! n') >> Just []
  RecPar n ctxt :=: RecPar n' ctxt' -> guard (ctxt M.! n == ctxt M.! n') >> Just []

  RecPar n ctxt :< t  -> Just [mapRecPars ctxt (ctxt M.! n) :< t]
  t :< RecPar n ctxt  -> Just [t :< mapRecPars ctxt (ctxt M.! n)]
  RecPar n ctxt :=: t -> Just [mapRecPars ctxt (ctxt M.! n) :=: t]
  t :=: RecPar n ctxt -> Just [t :=: mapRecPars ctxt (ctxt M.! n)]

  t :< t'  -> guard (unorderedType t || unorderedType t') >> Just [t :=: t']

  AbsType n s ts :=: AbsType n' s' ts' -> guard (n == n' && s == s') >> Just (zipWith (:=:) ts ts')

  Variant r1     :=: Variant r2        ->
    if Row.null r1 && Row.null r2 then Just []
    else if Row.justVar r1 && Row.justVar r2 && r1 == r2 
         then Just [Solved (Variant r1)]
    else do
    let commons  = Row.common r1 r2
        (ls, rs) = unzip commons
    guard (not (null commons))
    guard (untakenLabels ls == untakenLabels rs)
    let (r1',r2') = Row.withoutCommon r1 r2
        cs = map (\(Entry _ t _, Entry _ t' _) -> t :=: t') commons
        c   = Variant r1' :=: Variant r2'
    Just (c:cs)

  Record n1 r1 s1   :=: Record n2 r2 s2 ->
    if Row.null r1 && Row.null r2 && s1 == s2 && n1 == n2 then Just []
    else if Row.justVar r1 && Row.justVar r2 && s1 == s2 && r1 == r2 && n1 == n2
         then Just [Solved (Record n1 r1 s1)]
    else do
    let commons  = Row.common r1 r2
        (ls, rs) = unzip commons
    guard (not (null commons))
    guard (untakenLabels rs == untakenLabels ls)
    let (r1',r2') = Row.withoutCommon r1 r2
        cs = map (\(Entry _ t _, Entry _ t' _) -> t :=: t') commons
        c   = Record n1 r1' s1 :=: Record n2 r2' s2
    Just (c:cs)
    
  t :=: t' -> guard (t == t') >> if typeUVs t == [] then Just [] 
                                                    else Just [Solved t] 
  Solved t -> guard (typeUVs t == []) >> Just []

  -- If an unboxed record has no recursive parameter, sat
  UnboxedNoRecurse (Record None _ Unboxed) -> Just [Sat]
  -- If a boxed record, sat
  UnboxedNoRecurse (Record _ _ c) | (c == ReadOnly || c == Writable) -> Just [Sat]

  _ -> Nothing

  

  where

    untakenLabels :: [Entry] -> S.Set FieldName
    untakenLabels = S.fromList . mapMaybe (\(Entry l _ t) -> guard (not t) >> pure l)

module Cogent.TypeCheck.Solver.Simplify where 

import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
import Cogent.TypeCheck.Solver.Goal 
import Cogent.TypeCheck.Solver.Monad
import qualified Cogent.TypeCheck.Row as Row
import Cogent.Surface
import Cogent.TypeCheck.Base 
import Cogent.Common.Types
import Cogent.Common.Syntax
import Lens.Micro
import Control.Monad
import Data.Maybe
import Data.List (elemIndex)
import Control.Applicative
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Class (lift)
import qualified Data.Set as S
import qualified Data.Map as M

onGoal :: (Constraint -> Maybe [Constraint]) -> Goal -> Maybe [Goal]
onGoal f g = fmap (map (derivedGoal g)) (f (g ^. goal))

unsat :: TypeError -> Maybe [Constraint]
unsat x = Just [Unsat x]
elseDie :: Bool -> TypeError -> Maybe [Constraint]
elseDie b e = (guard b >> Just []) <|> unsat e 

simplify :: [(TyVarName, Kind)] -> Rewrite.Rewrite [Goal]
simplify axs = Rewrite.pickOne $ onGoal $ \c -> case c of 
  Sat      -> Just []
  c1 :& c2 -> Just [c1,c2]

  Drop   t@(T (TVar v False)) m
    | Just k <- lookup v axs -> 
        canDiscard k `elseDie` TypeNotDiscardable t m
  Share  t@(T (TVar v False)) m
    | Just k <- lookup v axs -> 
        canShare k   `elseDie` TypeNotShareable t m
  Escape t@(T (TVar v False)) m
    | Just k <- lookup v axs -> 
        canEscape k  `elseDie` TypeNotEscapable t m

  Drop     (T (TVar v True)) m -> Just []
  Share    (T (TVar v True)) m -> Just []
  Escape t@(T (TVar v True)) m -> unsat (TypeNotEscapable t m)

  Drop   t@(T (TCon n ts s)) m ->
    not (writable s) `elseDie` TypeNotDiscardable t m
  Share  t@(T (TCon n ts s)) m ->
    not (writable s) `elseDie` TypeNotShareable t m
  Escape t@(T (TCon n ts s)) m ->
    not (readonly s) `elseDie` TypeNotEscapable t m

  Drop   (T (TFun {})) _ -> Just []
  Share  (T (TFun {})) _ -> Just []
  Escape (T (TFun {})) _ -> Just []

  Drop   (T TUnit) _ -> Just []
  Share  (T TUnit) _ -> Just []
  Escape (T TUnit) _ -> Just []

  Drop   (T (TTuple xs)) m -> Just (map (flip Drop   m) xs)
  Share  (T (TTuple xs)) m -> Just (map (flip Share  m) xs)
  Escape (T (TTuple xs)) m -> Just (map (flip Escape m) xs)

  Share  (V r) m
    | isNothing (Row.var r) -> Just (map (flip Share  m) (Row.untakenTypes r))
  Drop   (V r) m
    | isNothing (Row.var r) -> Just (map (flip Drop   m) (Row.untakenTypes r))
  Escape (V r) m
    | isNothing (Row.var r) -> Just (map (flip Escape m) (Row.untakenTypes r))

  Share  (R r (Left s)) m
    | isNothing (Row.var r)
    , not (writable s) -> Just (map (flip Share  m) (Row.untakenTypes r))
  Drop   (R r (Left s)) m
    | isNothing (Row.var r)
    , not (writable s) -> Just (map (flip Drop   m) (Row.untakenTypes r))
  Escape (R r (Left s)) m
    | isNothing (Row.var r)
    , not (readonly s) -> Just (map (flip Escape m) (Row.untakenTypes r))

  Exhaustive t ps | any isIrrefutable ps -> Just []
  Exhaustive (V r) []
    | isNothing (Row.var r) ->
      null (Row.untakenTypes r) 
        `elseDie` PatternsNotExhaustive (V r) (Row.untakenLabels r) 
  Exhaustive (V r) (RP (PCon t _):ps) 
    | isNothing (Row.var r) -> 
      Just [Exhaustive (V (Row.take t r)) ps]
  
  Exhaustive tau@(T (TCon "Bool" [] Unboxed)) [RP (PBoolLit t), RP (PBoolLit f)] 
    -> (not (t && f) && (t || f)) `elseDie` PatternsNotExhaustive tau []

  Upcastable (T (TCon n [] Unboxed)) (T (TCon m [] Unboxed))
    | Just n' <- elemIndex n primTypeCons
    , Just m' <- elemIndex m primTypeCons
    , n' <= m' , m /= "String" -> Just []

  -- If both sides of an equality constraint are equal, we can't completely discharge it; we need to make sure all unification variables in the type are instantiated at some point
  t :=: u | t == u ->
    if isSolved t
    then Just []
    else Just [Solved t]

  Solved t | isSolved t -> Just []

  T (TFun t1 t2) :=: T (TFun r1 r2) -> Just [r1 :=: t1, t2 :=: r2]
  T (TFun t1 t2) :<  T (TFun r1 r2) -> Just [r1 :<  t1, t2 :<  r2]

  T (TTuple ts) :<  T (TTuple us) | length ts == length us -> Just (zipWith (:< ) ts us)
  T (TTuple ts) :=: T (TTuple us) | length ts == length us -> Just (zipWith (:=:) ts us)

  V r1 :< V r2 | Row.null r1 && Row.null r2 -> Just []
               | Just (r1',r2') <- extractVariableEquality r1 r2 -> Just [V r1' :=: V r2']
               | otherwise -> do 
    let commons  = Row.common r1 r2
        (ls, rs) = unzip commons
    guard (not (null commons))
    guard (untakenLabelsSet ls `S.isSubsetOf` untakenLabelsSet rs)
    let (r1',r2') = Row.withoutCommon r1 r2
        cs = map (\ ((_, e),(_,e')) -> fst e :< fst e') commons
        c   = V r1' :< V r2'
    Just (c:cs)
    
  V r1 :=: V r2 | Row.null r1 && Row.null r2 -> Just []
                | otherwise -> do 
    let commons  = Row.common r1 r2
        (ls, rs) = unzip commons
    guard (not (null commons))
    guard (untakenLabelsSet ls == untakenLabelsSet rs)
    let (r1',r2') = Row.withoutCommon r1 r2
        cs = map (\ ((_, e),(_,e')) -> fst e :=: fst e') commons
        c   = V r1' :=: V r2'
    Just (c:cs)

  R r1 s1 :< R r2 s2 | Row.null r1 && Row.null r2 && s1 == s2 -> Just []
                     | Just (r1',r2') <- extractVariableEquality r1 r2 -> Just [R r1' s1 :=: R r2' s2]
                     | otherwise -> do
    let commons  = Row.common r1 r2
        (ls, rs) = unzip commons
    guard (not (null commons))
    guard (untakenLabelsSet rs `S.isSubsetOf` untakenLabelsSet ls)
    let (r1',r2') = Row.withoutCommon r1 r2
        cs = map (\ ((_, e),(_,e')) -> fst e :< fst e') commons
        ds = map (flip Drop ImplicitlyTaken) $ Row.typesFor (untakenLabelsSet ls S.\\ untakenLabelsSet rs) r1
        c  = R r1' s1 :< R r2' s2
    Just (c:cs ++ ds)

  R r1 s1 :=: R r2 s2 | Row.null r1 && Row.null r2 && s1 == s2 -> Just []
                      | otherwise -> do
    let commons  = Row.common r1 r2
        (ls, rs) = unzip commons
    guard (not (null commons))
    guard (untakenLabelsSet rs == untakenLabelsSet ls)
    let (r1',r2') = Row.withoutCommon r1 r2
        cs = map (\ ((_, e),(_,e')) -> fst e :=: fst e') commons
        ds = map (flip Drop ImplicitlyTaken) $ Row.typesFor (untakenLabelsSet ls S.\\ untakenLabelsSet rs) r1
        c  = R r1' s1 :=: R r2' s2
    Just (c:cs ++ ds)


  T t1 :< x | unorderedType t1 -> Just [T t1 :=: x]
  x :< T t2 | unorderedType t2 -> Just [x :=: T t2]

  (T (TCon n ts s)) :=: (T (TCon n' us s'))
    | s == s', n == n' -> Just (zipWith (:=:) ts us)

  T t1 :=: T t2 | t1 == t2 -> Just []

  _ -> Nothing

unorderedType :: Type e t -> Bool 
unorderedType (TRecord {}) = False
unorderedType (TVariant {}) = False
unorderedType (TTuple {}) = False
unorderedType (TFun {}) = False
unorderedType (TUnbox {}) = False
unorderedType (TBang {}) = False
unorderedType (TTake {}) = False
unorderedType (TPut {}) = False
#ifdef BUILTIN_ARRAYS
unorderedType (TArray {}) = False
#endif
unorderedType _ = True 



untakenLabelsSet :: [Entry TCType] -> S.Set FieldName
untakenLabelsSet = S.fromList . mapMaybe (\(l, (_,t)) -> guard (not t) >> pure l)
isIrrefutable :: RawPatn -> Bool
isIrrefutable (RP (PIrrefutable _)) = True
isIrrefutable _ = False

-- | Check if the variable parts must be equal.
-- Returns true iff the two rows have the same keys, but one of the variables is Nothing and the other is a Just
extractVariableEquality :: Row.Row t -> Row.Row t -> Maybe (Row.Row t, Row.Row t)
extractVariableEquality (Row.Row m1 v1) (Row.Row m2 v2)
 | (isJust v1 && isNothing v2) || (isNothing v1 && isJust v2)
 , M.null m1
 , M.null m2
 = Just (Row.Row M.empty v1, Row.Row M.empty v2)
 | otherwise
 = Nothing

isSolved :: TCType -> Bool
isSolved t = unifVars t == []

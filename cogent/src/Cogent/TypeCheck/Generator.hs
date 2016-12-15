--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

module Cogent.TypeCheck.Generator
  ( runCG
  , CG
  , cg
  , cgAlts
  ) where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import qualified Cogent.Context as C
import Cogent.PrettyPrint (prettyC)
import Cogent.Surface
import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Util
import Cogent.Util hiding (Warning)

import Control.Arrow (first, second)
import Control.Lens hiding (Context, (:<))
import Control.Monad.Except
import Control.Monad.State
import Data.Functor.Compose
import qualified Data.Map as M
import qualified Data.IntMap as IM
import Data.Maybe (catMaybes, isNothing, isJust)
import Data.Monoid ((<>))
import Text.Parsec.Pos
import Text.PrettyPrint.ANSI.Leijen hiding ((<>), (<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as L


data CGState = CGS { _tc :: TCState
                   , _context :: C.Context TCType
                   , _flexes :: Int
                   , _knownTypeVars :: [VarName]
                   , _flexOrigins :: IM.IntMap VarOrigin
                   }

makeLenses ''CGState

type CG = StateT CGState IO

runCG :: C.Context TCType -> [TyVarName] -> CG a -> TC (a, Int, IM.IntMap VarOrigin)
runCG g vs a = do
  x <- get
  (r, CGS x' _ f _ os) <- lift $ runStateT a (CGS x g 0 vs mempty)
  put x'
  return (r,f,os)

fresh :: (?loc :: SourcePos) => CG TCType
fresh = fresh' (ExpressionAt ?loc)
  where
    fresh' :: VarOrigin -> CG TCType
    fresh' ctx = do
      i <- flexes <<%= succ
      flexOrigins %= IM.insert i ctx
      return $ U i

cgMany :: (?loc :: SourcePos) => [LocExpr] -> CG ([TCType], Constraint, [TCExpr])
cgMany es = do
  let each (ts,c,es') e = do
        alpha    <- fresh 
        (c', e') <- cg e alpha
        return (alpha:ts, c <> c', e':es')
  (ts, c', es') <- foldM each ([], Sat, []) es
  return (reverse ts, c', reverse es')

cg :: LocExpr -> TCType -> CG (Constraint, TCExpr)
cg x@(LocExpr l e) t = do
  let ?loc = l
  (c, e') <- cg' e t
  return (c :@ InExpression x t, TE t e' l)

cg' :: (?loc :: SourcePos) => Expr LocType VarName LocExpr -> TCType -> CG (Constraint, Expr TCType TCName TCExpr)
cg' (PrimOp o [e1, e2]) t
  | o `elem` words "+ - * / % .&. .|. .^. >> <<"
  = do (c1, e1') <- cg e1 t
       (c2, e2') <- cg e2 t
       return (integral t <> c1 <> c2, PrimOp o [e1', e2'] )
  | o `elem` words "&& ||"
  = do (c1, e1') <- cg e1 t
       (c2, e2') <- cg e2 t
       return (F (T (TCon "Bool" [] Unboxed)) :< F t <> c1 <> c2, PrimOp o [e1', e2'] )
  | o `elem` words "== /= >= <= > <"
  = do alpha <- fresh
       (c1, e1') <- cg e1 alpha
       (c2, e2') <- cg e2 alpha
       let c  = F (T (TCon "Bool" [] Unboxed)) :< F t
           c' = integral alpha
       return (c <> c' <> c1 <> c2, PrimOp o [e1', e2'] )
cg' (PrimOp o [e]) t
  | o == "complement"  = do
      (c, e') <- cg e t
      return (integral t :& c, PrimOp o [e'])
  | o == "not"         = do
      (c, e') <- cg e t
      return (F (T (TCon "Bool" [] Unboxed)) :< F t :& c, PrimOp o [e'])
cg' (PrimOp o _) t = error "impossible"
cg' (Var n) t = do
  ctx <- use context
  let e = Var n
  traceTC "gen" (text "cg for variable" <+> pretty n L.<$> text "of type" <+> pretty t)
  case C.lookup n ctx of
    -- Variable not found, see if the user meant a function.
    Nothing ->
      use (tc.knownFuns.at n) >>= \case
        Just _  -> cg' (TypeApp n [] NoInline) t
        Nothing -> return (Unsat (NotInScope n), e)

    -- Variable used for the first time, mark the use, and continue
    Just (t', p, Nothing) -> do
      context %= C.use n ?loc
      let c = F t' :< F t
      traceTC "gen" (text "variable" <+> pretty n <+> text "used for the first time" <> semi
               L.<$> text "generate constraint" <+> prettyC c)
      return (c, e)

    -- Variable already used before, emit a Share constraint.
    Just (t', p, Just l)  -> do
      traceTC "gen" (text "variable" <+> pretty n <+> text "used before" <> semi
               L.<$> text "generate constraint" <+> prettyC (F t' :< F t) <+> text "and share constraint")
      return (Share t' (Reused n p l) <> F t' :< F t, e)

cg' (Upcast e) t = do
  alpha <- fresh
  (c1, e1') <- cg e alpha
  let c = (integral alpha) <> Upcastable alpha t <> c1
  return (c, Upcast e1')

-- cg' (Widen e) t = do
--   alpha <- fresh
--   (c1, e1') <- cg e alpha
--   let c = (T (TVariant M.empty) :<~ alpha) <> (alpha :<~ t) <> c1
--   return (c, Widen e1')

cg' (BoolLit b) t = do
  let c = F (T (TCon "Bool" [] Unboxed)) :< F t
      e = BoolLit b
  return (c,e)

cg' (CharLit l) t = do
  let c = F (T (TCon "U8" [] Unboxed)) :< F t
      e = CharLit l
  return (c,e)

cg' (StringLit l) t = do
  let c = F (T (TCon "String" [] Unboxed)) :< F t
      e = StringLit l
  return (c,e)

cg' Unitel t = do
  let c = F (T TUnit) :< F t
      e = Unitel
  return (c,e)

cg' (IntLit i) t = do
  let minimumBitwidth | i < u8MAX      = "U8"
                      | i < u16MAX     = "U16"
                      | i < u32MAX     = "U32"
                      | otherwise      = "U64"
      c = Upcastable (T (TCon minimumBitwidth [] Unboxed)) t
      e = IntLit i
  return (c,e)

cg' (App e1 e2) t = do
  alpha     <- fresh
  (c1, e1') <- cg e1 (T (TFun alpha t))
  (c2, e2') <- cg e2 alpha

  let c = c1 <> c2
      e = App e1' e2'
  traceTC "gen" (text "cg for funapp:" <+> prettyE e)
  return (c,e)

cg' (Con k es) t = do
  (ts, c', es') <- cgMany es

  let e = Con k es'
      c = FVariant (M.fromList [(k, (ts, False))]) :< F t
  traceTC "gen" (text "cg for constructor:" <+> prettyE e
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (c' <> c,e)

cg' (Tuple es) t = do
  (ts, c', es') <- cgMany es

  let e = Tuple es'
      c = F (T (TTuple ts)) :< F t
  traceTC "gen" (text "cg for tuple:" <+> prettyE e
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (c' <> c,e)

cg' (UnboxedRecord fes) t = do
  let (fs, es) = unzip fes
  (ts, c', es') <- cgMany es

  let e = UnboxedRecord (zip fs es')
      r = T (TRecord (zip fs (map (, False) ts)) Unboxed)
      c = F r :< F t
  traceTC "gen" (text "cg for unboxed record:" <+> prettyE e
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (c' <> c,e)

cg' (Seq e1 e2) t = do
  alpha <- fresh
  (c1, e1') <- cg e1 alpha
  (c2, e2') <- cg e2 t

  let e = Seq e1' e2'
      c = c1 <> Drop alpha Suppressed <> c2
  return (c, e)

cg' (TypeApp f as i) t = do
  tvs <- use knownTypeVars
  (c,as') <- zoom tc (validateTypes' tvs (fmap stripLocT $ Compose as)) >>= \case
    Left e -> return (Unsat e, [])
    Right ts -> return (Sat, getCompose ts)
  use (tc.knownFuns.at f) >>= \case

    Just (PT vs tau) -> let
        match :: [(TyVarName, Kind)] -> [Maybe TCType] -> CG ([(TyVarName, TCType)], Constraint)
        match [] []    = return ([], Sat)
        match [] (_:_) = return ([], Unsat (TooManyTypeArguments f (PT vs tau)))
        match vs []    = fresh >>= match vs . return . Just
        match (v:vs) (Nothing:as) = fresh >>= \a -> match (v:vs) (Just a:as)
        match ((v,k):vs) (Just a:as) = do
          (ts, c) <- match vs as
          return ((v,a):ts, kindToConstraint k a (TypeParam f v) <> c)
      in do
        (ts,c') <- match vs as'

        let c = F (substType ts tau) :< F t
            e = TypeApp f (map (Just . snd) ts) i
        traceTC "gen" (text "cg for typeapp:" <+> prettyE e
                 L.<$> text "of type" <+> pretty t <> semi
                 L.<$> text "type signature is" <+> pretty (PT vs tau) <> semi
                 L.<$> text "generate constraint" <+> prettyC c)
        return (c' <> c, e)

    Nothing -> do
      let e = TypeApp f as' i
          c = Unsat (FunctionNotFound f)
      return (c, e)

cg' (Member e f) t = do
  alpha <- fresh
  (c', e') <- cg e alpha

  let e = Member e' f
      x = FRecord [(f, (t, False))]
      c = F alpha :< x <> Share alpha (UsedInMember f)
  traceTC "gen" (text "cg for member:" <+> prettyE e
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (c' <> c, e)

cg' (If e1 bs e2 e3) t = do
  (c1, e1') <- letBang bs (cg e1) (T (TCon "Bool" [] Unboxed))
  (c, [(c2, e2'), (c3, e3')]) <- parallel' [(ThenBranch, cg e2 t), (ElseBranch, cg e3 t)]
  let e = If e1' bs e2' e3'
  traceTC "gen" (text "cg for if:" <+> prettyE e)
  return (c1 <> c <> c2 <> c3, e)

cg' (Put e ls) t | not (any isNothing ls) = do
  alpha <- fresh
  let (fs, es) = unzip (catMaybes ls)
  (c', e') <- cg e alpha  -- (T (TTake (Just fs) t))
  (ts, cs, es') <- cgMany es

  let c1 = F (T (TPut (Just fs) alpha)) :< F t
      c2 = F alpha :< FRecord (zip fs (map (,True) ts))
      e = Put e' (map Just (zip fs es'))
  traceTC "gen" (text "cg for put:" <+> prettyE e
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint:" <+> prettyC c1 <+> text "and" <+> prettyC c2)
  return (c1 <> c' <> cs <> c2, e)

  | otherwise = first (<> Unsat RecordWildcardsNotSupported) <$> cg' (Put e (filter isJust ls)) t

cg' (Let bs e) t = do
  (c, bs', (c', e')) <- withBindings bs (cg e t)
  return (c <> c', Let bs' e')

cg' (Match e bs alts) top = do
  alpha <- fresh
  (c', e') <- letBang bs (cg e) alpha
  (c'', alts') <- cgAlts alts top alpha

  let c = c' :& c''
      e = Match e' bs alts'
  return (c, e)

integral :: TCType -> Constraint
integral a = Upcastable (T (TCon "U8" [] Unboxed)) a

dropConstraintFor :: M.Map VarName (C.Row TCType) -> Constraint
dropConstraintFor m = foldMap (\(i, (t,x,p)) -> maybe (Drop t (Unused i x)) (const Sat) p) $ M.toList m

cgAlts :: (?loc :: SourcePos) => [Alt VarName LocExpr] -> TCType -> TCType -> CG (Constraint, [Alt TCName TCExpr])
cgAlts alts top alpha = do
  let
    altPattern (Alt p _ _) = p

    f (Alt p like e) t = do
      (s, c, p') <- matchA p t
      context %= C.addScope s
      (c', e') <- cg e top
      rs <- context %%= C.dropScope
      let unused = flip foldMap (M.toList rs) $ \(v,(_,_,mp)) ->
            case mp of Nothing -> warnToConstraint __cogent_wunused_local_binds (UnusedLocalBind v); _ -> Sat
      return (removeCase p t, (c <> c' <> dropConstraintFor rs <> unused, Alt p' like e'))

    jobs = map (\(n, alt) -> (NthAlternative n (altPattern alt), f alt)) (zip [1..] alts)

  (c'', blob) <- parallel jobs alpha

  let (cs, alts') = unzip blob
      c = mconcat (Exhaustive alpha (map altPattern alts'):c'':cs)
  return (c, alts')

matchA :: (?loc :: SourcePos)
       => Pattern VarName -> TCType
       -> CG (M.Map VarName (C.Row TCType), Constraint, Pattern TCName)

matchA (PIrrefutable i) t = do
  (s, c, i') <- match i t
  return (s, c, PIrrefutable i')

matchA (PCon k is) t = do
  (vs, blob) <- unzip <$> forM is (\i -> do alpha <- fresh; (alpha,) <$> match i alpha)
  let (ss, cs, is') = (map fst3 blob, map snd3 blob, map thd3 blob)
      p' = PCon k is'
      co = case overlapping ss of
             Left (v:vs) -> Unsat $ DuplicateVariableInPattern v p'
             _           -> Sat
      c = F t :< FVariant (M.fromList [(k, (vs, False))]) 
  traceTC "gen" (text "match constructor pattern:" <+> pretty p'
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (M.unions ss, co <> mconcat cs <> c, p')

matchA (PIntLit i) t = do
  let minimumBitwidth | i < u8MAX      = "U8"
                      | i < u16MAX     = "U16"
                      | i < u32MAX     = "U32"
                      | otherwise      = "U64"
      c = Upcastable (T (TCon minimumBitwidth [] Unboxed)) t
  return (M.empty, c, PIntLit i)

matchA (PBoolLit b) t =
  return (M.empty, F t :< F (T (TCon "Bool" [] Unboxed)), PBoolLit b)

matchA (PCharLit c) t =
  return (M.empty, F t :< F (T (TCon "U8" [] Unboxed)), PCharLit c)

match :: (?loc :: SourcePos)
      => IrrefutablePattern VarName -> TCType
      -> CG (M.Map VarName (C.Row TCType), Constraint, IrrefutablePattern TCName)

match (PVar x) t = do
  let p = PVar (x,t)
  traceTC "gen" (text "match var pattern:" <+> pretty p
           L.<$> text "of type" <+> pretty t)
  return (M.fromList [(x, (t,?loc,Nothing))], Sat, p)

match (PUnderscore) t = 
  let c = dropConstraintFor (M.singleton "_" (t, ?loc, Nothing))
   in return (M.empty, c, PUnderscore)

match (PUnitel) t = return (M.empty, F t :< F (T TUnit), PUnitel)

match (PTuple ps) t = do
   (vs, blob) <- unzip <$> mapM (\p -> do v <- fresh; (v,) <$> match p v) ps
   let (ss, cs, ps') = (map fst3 blob, map snd3 blob, map thd3 blob)
       p' = PTuple ps'
       co = case overlapping ss of
              Left (v:vs) -> Unsat $ DuplicateVariableInIrrefPattern v p'
              _           -> Sat
       c = F t :< F (T (TTuple vs))
   traceTC "gen" (text "match tuple pattern:" <+> pretty p'
            L.<$> text "of type" <+> pretty t <> semi
            L.<$> text "generate constraint" <+> prettyC c)
   return (M.unions ss, co <> mconcat cs <> c, p')

match (PUnboxedRecord fs) t | not (any isNothing fs) = do
   let (ns, ps) = unzip (catMaybes fs)
   (vs, blob) <- unzip <$> mapM (\p -> do v <- fresh; (v,) <$> match p v) ps
   let (ss, cs, ps') = (map fst3 blob, map snd3 blob, map thd3 blob)
       t' = FRecord (zip ns (map (,False) vs))
       d  = Drop (T (TTake (Just ns) t)) Suppressed
       p' = PUnboxedRecord (map Just (zip ns ps'))
       c = F t :< t'
       co = case overlapping ss of
              Left (v:vs) -> Unsat $ DuplicateVariableInIrrefPattern v p'
              _           -> Sat
   traceTC "gen" (text "match unboxed record:" <+> pretty p'
            L.<$> text "of type" <+> pretty t <> semi
            L.<$> text "generate constraint" <+> prettyC c
            L.<$> text "non-overlapping, and linearity constraints")
   return (M.unions ss, co <> mconcat cs <> c <> d, p')

   | otherwise = second3 (:& Unsat RecordWildcardsNotSupported) <$> match (PUnboxedRecord (filter isJust fs)) t

match (PTake r fs) t | not (any isNothing fs) = do
   let (ns, ps) = unzip (catMaybes fs)
   (vs, blob) <- unzip <$> mapM (\p -> do v <- fresh; (v,) <$> match p v) ps
   let (ss, cs, ps') = (map fst3 blob, map snd3 blob, map thd3 blob)
       c = F t :< FRecord (zip ns (map (,False) vs))
       s  = M.fromList [(r, (u, ?loc, Nothing))]
       u  = T (TTake (Just ns) t)
       p' = PTake (r,u) (map Just (zip ns ps'))
       co = case overlapping (s:ss) of
              Left (v:vs) -> Unsat $ DuplicateVariableInIrrefPattern v p'
              _           -> Sat
   traceTC "gen" (text "match take pattern:" <+> pretty p'
            L.<$> text "of type" <+> pretty t <> semi
            L.<$> text "generate constraint:" <+> prettyC c
            L.<$> text "and non-overlapping constraints")
   return (M.unions (s:ss), co <> mconcat cs <> c, p')

   | otherwise = second3 (:& Unsat RecordWildcardsNotSupported) <$> match (PTake r (filter isJust fs)) t

withBindings :: (?loc::SourcePos)
  => [Binding LocType VarName LocExpr]
  -> CG a -> CG (Constraint, [Binding TCType TCName TCExpr], a)
withBindings [] a = (Sat, [],) <$> a
withBindings (Binding pat tau e bs : xs) a = do
  alpha <- fresh
  (c1, e') <- letBang bs (cg e) alpha
  (ct, alpha') <- case tau of
    Nothing -> return (Sat, alpha)
    Just tau' -> do
      tvs <- use knownTypeVars
      zoom tc (validateType' tvs (stripLocT tau')) >>= \case
        Left e -> return (Unsat e, alpha)
        Right t -> return (F alpha :< F t, t)
  (s, cp, pat') <- match pat alpha'
  context %= C.addScope s
  (c', xs', r) <- withBindings xs a
  rs <- context %%= C.dropScope
  let unused = flip foldMap (M.toList rs) $ \(v,(_,_,mp)) -> case mp of Nothing -> warnToConstraint __cogent_wunused_local_binds (UnusedLocalBind v); _ -> Sat
      c = ct <> c1 <> c' <> cp <> dropConstraintFor rs <> unused
      b' = Binding pat' (fmap (const alpha) tau) e' bs
  traceTC "gen" (text "bound expression" <+> pretty e' <+> text "with banged" <+> pretty bs
           L.<$> text "of type" <+> pretty alpha <> semi
           L.<$> text "generate constraint" <+> prettyC c1 <> semi
           L.<$> text "constraint for ascribed type:" <+> prettyC ct)
  return (c, b':xs', r)

parallel' :: [(ErrorContext, CG (Constraint, a))] -> CG (Constraint, [(Constraint, a)])
parallel' ls = parallel (map (second (\a _ -> ((), ) <$> a)) ls) ()

parallel :: [(ErrorContext, acc -> CG (acc, (Constraint, a)))] -> acc -> CG (Constraint, [(Constraint, a)])
parallel []       acc = return (Sat, [])
parallel [(ct,x)] acc = (Sat,) . return . first (:@ ct) . snd <$> x acc
parallel ((ct,x):xs) acc = do
  ctx  <- use context
  (acc', x') <- second (first (:@ ct)) <$> x acc
  ctx1 <- use context
  context .= ctx
  (c', xs') <- parallel xs acc'
  ctx2 <- use context
  let (ctx', ls, rs) = C.merge ctx1 ctx2
  context .= ctx'
  let cls = foldMap (\(n, (t, p, Just p')) -> Drop t (UnusedInOtherBranch n p p')) ls
      crs = foldMap (\(n, (t, p, Just p')) -> Drop t (UnusedInThisBranch  n p p')) rs
  return (c' <> ((cls <> crs) :@ ct) , x':xs')

letBang :: (?loc :: SourcePos) => [VarName] -> (TCType -> CG (Constraint, TCExpr)) -> TCType -> CG (Constraint, TCExpr)
letBang [] x t = x t
letBang bs x t = do
  c <- foldMap id <$> mapM validateVariable bs
  ctx <- use context
  let (ctx', undo) = C.mode ctx bs (\(t,p,p') -> (T (TBang t), p, Just ?loc))
  context .= ctx'
  (c', e) <- x t
  context %= undo
  let c'' = Escape t UsedInLetBang
  traceTC "gen" (text "let!" <+> pretty bs <+> text "when cg for expression" <+> pretty e
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c'')
  return (c <> c' <> c'', e)

validateVariable :: VarName -> CG Constraint
validateVariable v = do
  x <- use context
  return $ if C.contains x v then Sat else Unsat (NotInScope v)

prettyE :: Expr TCType TCName TCExpr -> Doc
prettyE = pretty


validateType' :: [VarName] -> RawType -> TC (Either TypeError TCType)
validateType' vs r = runExceptT (validateType vs r)

validateTypes' :: (Traversable t) => [VarName] -> t RawType -> TC (Either TypeError (t TCType))
validateTypes' vs rs = runExceptT (traverse (validateType vs) rs)


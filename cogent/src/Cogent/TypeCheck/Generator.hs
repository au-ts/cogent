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

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

module Cogent.TypeCheck.Generator
  ( runCG
  , CG
  , cg
  , cgFunDef
  , freshTVar
  , validateType
  ) where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import qualified Cogent.Context as C
import Cogent.PrettyPrint (prettyC)
import Cogent.Surface
import Cogent.TypeCheck.Base hiding (validateType)
import Cogent.TypeCheck.Util
import Cogent.Util hiding (Warning)
import qualified Cogent.TypeCheck.Row as Row

import Control.Arrow (first, second)
import Control.Monad.State
import Control.Monad.Trans.Except
import Data.Foldable (fold)
import Data.Functor.Compose
import Data.List (nub, (\\))
import qualified Data.Map as M
import qualified Data.IntMap as IM
import Data.Maybe (catMaybes, isNothing, isJust)
import Data.Monoid ((<>))
import qualified Data.Sequence as Seq
import Text.Parsec.Pos
import Text.PrettyPrint.ANSI.Leijen hiding ((<>), (<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as L
import Lens.Micro.TH
import Lens.Micro
import Lens.Micro.Mtl
-- import Debug.Trace

data GenState = GenState { _context :: C.Context TCType
                         , _knownTypeVars :: [TyVarName]
                         , _flexes :: Int
                         , _flexOrigins :: IM.IntMap VarOrigin
                         }

makeLenses ''GenState

type CG a = TcConsM GenState a

runCG :: C.Context TCType -> [TyVarName] -> CG a -> TcM (a, Int, IM.IntMap VarOrigin)
runCG g vs ma = do
  (a, GenState _ _ f os) <- withTcConsM (GenState g vs 0 mempty) ((,) <$> ma <*> get)
  return (a,f,os)


-- -----------------------------------------------------------------------------
-- Type-level constraints
-- -----------------------------------------------------------------------------

validateType :: RawType -> CG (Constraint, TCType)
validateType rt@(RT t) = do
  vs <- use knownTypeVars
  ts <- lift $ use knownTypes
  case t of
    TVar v _ | v `notElem` vs -> return (Unsat $ UnknownTypeVariable v, toTCType rt)
    TCon t as _ | Nothing <- lookup t ts -> return (Unsat $ UnknownTypeConstructor t, toTCType rt)
                | Just (vs, _) <- lookup t ts
                , provided <- length as
                , required <- length vs
                , provided /= required
               -> return (Unsat $ TypeArgumentMismatch t provided required, toTCType rt)
                |  Just (vs, Just x) <- lookup t ts
               -> second (Synonym t) <$> fmapFoldM validateType as  
    TRecord fs s | fields  <- map fst fs
                 , fields' <- nub fields
                -> let toRow (T (TRecord fs s)) = R (Row.fromList fs) (Left (fmap (const ()) s)) 
                   in if fields' == fields
                   then second (toRow . T . ffmap toSExpr) <$> fmapFoldM validateType t
                   else return (Unsat $ DuplicateRecordFields (fields \\ fields'), toTCType rt)
    TVariant fs  -> do let tuplize [] = T TUnit
                           tuplize [x] = x 
                           tuplize xs  = T (TTuple xs)
                       (c, TVariant fs') <- second (ffmap toSExpr) <$> fmapFoldM validateType t 
                       pure (c, V (Row.fromMap (fmap (first tuplize) fs')))
#ifdef BUILTIN_ARRAYS
    TArray te l -> do let l' = toSExpr l
                          cl = Arith (SE $ PrimOp ">" [l', SE $ IntLit 0])
                      (c,te') <- validateType te
                      return (c <> cl, T $ TArray te' l')
#endif
    _ -> second (T . ffmap toSExpr) <$> fmapFoldM validateType t 

validateTypes :: (Traversable t) => t RawType -> CG (Constraint, t TCType)
validateTypes = fmapFoldM validateType

-- -----------------------------------------------------------------------------
-- Term-level constraints
-- -----------------------------------------------------------------------------

cgFunDef :: (?loc :: SourcePos) => [Alt LocPatn LocExpr] -> TCType -> CG (Constraint, [Alt TCPatn TCExpr])
cgFunDef alts t = do
  alpha1 <- freshTVar
  alpha2 <- freshTVar
  (c, alts') <- cgAlts alts alpha2 alpha1
  return (c <> (T (TFun alpha1 alpha2)) :< t, alts')

-- cgAlts alts out_type in_type
-- NOTE the order of arguments!
cgAlts :: [Alt LocPatn LocExpr] -> TCType -> TCType -> CG (Constraint, [Alt TCPatn TCExpr])
cgAlts alts top alpha = do
  let
    altPattern (Alt p _ _) = p

    f (Alt p l e) t = do
      (s, c, p',t') <- matchA p t
      context %= C.addScope s
      (c', e') <- cg e top
      rs <- context %%= C.dropScope
      let unused = flip foldMap (M.toList rs) $ \(v,(_,_,us)) ->
            case us of Seq.Empty -> warnToConstraint __cogent_wunused_local_binds (UnusedLocalBind v); _ -> Sat
      return (t', (c <> c' <> dropConstraintFor rs <> unused, Alt p' l e'))

    jobs = map (\(n, alt) -> (NthAlternative n (altPattern alt), f alt)) (zip [1..] alts)

  (c'', blob) <- parallel jobs alpha

  let (cs, alts') = unzip blob
      c = mconcat (Exhaustive alpha (map (toRawPatn . altPattern) $ toTypedAlts alts'):c'':cs)
  return (c, alts')


-- -----------------------------------------------------------------------------
-- Expression constraints
-- -----------------------------------------------------------------------------

cgMany :: (?loc :: SourcePos) => [LocExpr] -> CG ([TCType], Constraint, [TCExpr])
cgMany es = do
  let each (ts,c,es') e = do
        alpha    <- freshTVar
        (c', e') <- cg e alpha
        return (alpha:ts, c <> c', e':es')
  (ts, c', es') <- foldM each ([], Sat, []) es  -- foldM is the same as foldlM
  return (reverse ts, c', reverse es')


cg :: LocExpr -> TCType -> CG (Constraint, TCExpr)
cg x@(LocExpr l e) t = do
  let ?loc = l
  (c, e') <- cg' e t
  return (c :@ InExpression x t, TE t e' l)

cg' :: (?loc :: SourcePos) => Expr LocType LocPatn LocIrrefPatn LocExpr -> TCType -> CG (Constraint, Expr TCType TCPatn TCIrrefPatn TCExpr)
cg' (PrimOp o [e1, e2]) t
  | o `elem` words "+ - * / % .&. .|. .^. >> <<"
  = do (c1, e1') <- cg e1 t
       (c2, e2') <- cg e2 t
       return (integral t <> c1 <> c2, PrimOp o [e1', e2'] )
  | o `elem` words "&& ||"
  = do (c1, e1') <- cg e1 t
       (c2, e2') <- cg e2 t
       return (T (TCon "Bool" [] Unboxed) :=: t <> c1 <> c2, PrimOp o [e1', e2'] )
  | o `elem` words "== /= >= <= > <"
  = do alpha <- freshTVar
       (c1, e1') <- cg e1 alpha
       (c2, e2') <- cg e2 alpha
       let c  = T (TCon "Bool" [] Unboxed) :=: t
           c' = integral alpha
       return (c <> c' <> c1 <> c2, PrimOp o [e1', e2'] )
cg' (PrimOp o [e]) t
  | o == "complement"  = do
      (c, e') <- cg e t
      return (integral t :& c, PrimOp o [e'])
  | o == "not"         = do
      (c, e') <- cg e t
      return (T (TCon "Bool" [] Unboxed) :=: t :& c, PrimOp o [e'])
cg' (PrimOp _ _) _ = __impossible "cg': unimplemented primops"
cg' (Var n) t = do
  let e = Var n  -- it has a different type than the above `Var n' pattern
  ctx <- use context
  traceTc "gen" (text "cg for variable" <+> pretty n L.<$> text "of type" <+> pretty t)
  case C.lookup n ctx of
    -- Variable not found, see if the user meant a function.
    Nothing ->
      lift (use $ knownFuns.at n) >>= \case
        Just _  -> cg' (TypeApp n [] NoInline) t
        Nothing -> return (Unsat (NotInScope (funcOrVar t) n), e)

    -- Variable used for the first time, mark the use, and continue
    Just (t', _, Seq.Empty) -> do
      context %= C.use n ?loc
      let c = t' :< t
      traceTc "gen" (text "variable" <+> pretty n <+> text "used for the first time" <> semi
               L.<$> text "generate constraint" <+> prettyC c)
      return (c, e)

    -- Variable already used before, emit a Share constraint.
    Just (t', p, us)  -> do
      context %= C.use n ?loc
      traceTc "gen" (text "variable" <+> pretty n <+> text "used before" <> semi
               L.<$> text "generate constraint" <+> prettyC (t' :< t) <+> text "and share constraint")
      return (Share t' (Reused n p us) <> t' :< t, e)

cg' (Upcast e) t = do
  alpha <- freshTVar
  (c1, e1') <- cg e alpha
  let c = integral alpha <> Upcastable alpha t <> c1
  return (c, Upcast e1')

cg' (BoolLit b) t = do
  let c = T (TCon "Bool" [] Unboxed) :=: t
      e = BoolLit b
  return (c,e)

cg' (CharLit l) t = do
  let c = T (TCon "U8" [] Unboxed) :=: t
      e = CharLit l
  return (c,e)

cg' (StringLit l) t = do
  let c = T (TCon "String" [] Unboxed) :=: t
      e = StringLit l
  return (c,e)

cg' Unitel t = do
  let c = T TUnit :=: t
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

#ifdef BUILTIN_ARRAYS
cg' (ArrayLit es) t = do
  alpha <- freshTVar
  blob <- forM es $ flip cg alpha
  let (cs,es') = unzip blob
      n = SE . IntLit . fromIntegral $ length es
      cz = Arith (SE $ PrimOp ">" [n, SE (IntLit 0)])
  return (mconcat cs <> cz <> F (T $ TArray alpha n) :< F t, ArrayLit es')

cg' (ArrayIndex e i) t = do
  alpha <- freshTVar
  n <- freshEVar
  let ta = T $ TArray alpha n
  (ce, e') <- cg e ta
  (ci, i') <- cg (dummyLocE i) (T $ TCon "U32" [] Unboxed)
  let c = F alpha :< F t <> Share ta UsedInArrayIndexing
        <> Arith (SE (PrimOp "<" [toSExpr i, n]))
        -- <> Arith (SE (PrimOp ">=" [toSExpr i, SE (IntLit 0)]))  -- as we don't have negative values
  traceTc "gen" (text "array indexing" <> colon
                 L.<$> text "index is" <+> pretty i <> semi
                 L.<$> text "bound is" <+> pretty n <> semi
                 L.<$> text "generate constraint" <+> prettyC c)
  return (ce <> ci <> c, ArrayIndex e' i)
#endif 

cg' exp@(Lam pat mt e) t = do
  alpha <- freshTVar
  beta  <- freshTVar
  (ct, alpha') <- case mt of
    Nothing -> return (Sat, alpha)
    Just t' -> do
      tvs <- use knownTypeVars
      lift (runExceptT $ validateType' tvs (stripLocT t')) >>= \case
        Left  e   -> return (Unsat e, alpha)
        Right t'' -> return (alpha :< t'', t'')
  (s, cp, pat') <- match pat alpha'
  let fvs = fvE $ stripLocE (LocExpr noPos $ Lam pat mt e)
  ctx <- use context
  let fvs' = filter (C.contains ctx) fvs  -- including (bad) vars that are not in scope
  context %= C.addScope s
  (ce, e') <- cg e beta
  rs <- context %%= C.dropScope
  let unused = flip foldMap (M.toList rs) $ \(v,(_,_,us)) -> 
        case us of
          Seq.Empty -> warnToConstraint __cogent_wunused_local_binds (UnusedLocalBind v)
          _ -> Sat
      c = ct <> cp <> ce <> (T $ TFun alpha beta) :< t
             <> dropConstraintFor rs <> unused
      lam = Lam  pat' (fmap (const alpha) mt) e'
  unless (null fvs') $ __todo "closures not implemented"
  unless (null fvs') $ context .= ctx
  traceTc "gen" (text "lambda expression" <+> prettyE lam
           L.<$> text "generate constraint" <+> prettyC c <> semi)
  return (c,lam)

cg' (App e1 e2 _) t = do
  alpha     <- freshTVar
  (c1, e1') <- cg e1 (T (TFun alpha t))
  (c2, e2') <- cg e2 alpha

  let c = c1 <> c2
      e = App e1' e2' False
  traceTc "gen" (text "cg for funapp:" <+> prettyE e)
  return (c,e)

cg' (Comp f g) t = do
  alpha1 <- freshTVar
  alpha2 <- freshTVar
  alpha3 <- freshTVar
  
  (c1, f') <- cg f (T (TFun alpha2 alpha3))
  (c2, g') <- cg g (T (TFun alpha1 alpha2))
  let e = Comp f' g'
      c = c1 <> c2 <> (T $ TFun alpha1 alpha3) :< t
  traceTc "gen" (text "cg for comp:" <+> prettyE e)
  return (c,e)

cg' (Con k [e]) t =  do
  alpha <- freshTVar 
  (c', e') <- cg e alpha
  U x <- freshTVar
  let e = Con k [e']
      c = V (Row.incomplete [(k,(alpha,False))] x) :< t
  traceTc "gen" (text "cg for constructor:" <+> prettyE e
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (c' <> c, e)
cg' (Con k []) t = cg' (Con k [LocExpr noPos $ Unitel]) t
cg' (Con k es) t = cg' (Con k [LocExpr noPos $ Tuple es]) t
cg' (Tuple es) t = do
  (ts, c', es') <- cgMany es

  let e = Tuple es'
      c = T (TTuple ts) :< t
  traceTc "gen" (text "cg for tuple:" <+> prettyE e
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (c' <> c, e)

cg' (UnboxedRecord fes) t = do
  let (fs, es) = unzip fes
  (ts, c', es') <- cgMany es

  let e = UnboxedRecord (zip fs es')
      r = R (Row.fromList (zip fs (map (, False) ts))) (Left Unboxed)
      c = r :< t
  traceTc "gen" (text "cg for unboxed record:" <+> prettyE e
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (c' <> c, e)
cg' (Seq e1 e2) t = do
  alpha <- freshTVar
  (c1, e1') <- cg e1 alpha
  (c2, e2') <- cg e2 t

  let e = Seq e1' e2'
      c = c1 <> Drop alpha Suppressed <> c2
  return (c, e)

cg' (TypeApp f as i) t = do
  tvs <- use knownTypeVars
  (ct, getCompose -> as') <- validateTypes (stripLocT <$> Compose as) 
  lift (use $ knownFuns.at f) >>= \case
    Just (PT vs tau) -> let
        match :: [(TyVarName, Kind)] -> [Maybe TCType] -> CG ([(TyVarName, TCType)], Constraint)
        match [] []    = return ([], Sat)
        match [] (_:_) = return ([], Unsat (TooManyTypeArguments f (PT vs tau)))
        match vs []    = freshTVar >>= match vs . return . Just
        match (v:vs) (Nothing:as) = freshTVar >>= \a -> match (v:vs) (Just a:as)
        match ((v,k):vs) (Just a:as) = do
          (ts, c) <- match vs as
          return ((v,a):ts, kindToConstraint k a (TypeParam f v) <> c)
      in do
        (ts,c') <- match vs as'

        let c = substType ts tau :< t
            e = TypeApp f (map (Just . snd) ts) i
        traceTc "gen" (text "cg for typeapp:" <+> prettyE e
                 L.<$> text "of type" <+> pretty t <> semi
                 L.<$> text "type signature is" <+> pretty (PT vs tau) <> semi
                 L.<$> text "generate constraint" <+> prettyC c)
        return (ct <> c' <> c, e)

    Nothing -> do
      let e = TypeApp f as' i
          c = Unsat (FunctionNotFound f)
      return (ct <> c, e)

cg' (Member e f) t =  do
  alpha <- freshTVar
  (c', e') <- cg e alpha
  U rest <- freshTVar
  U sigil <- freshTVar
  let f' = Member e' f
      row = Row.incomplete [(f, (t, False))] rest
      x = R row (Right sigil)
      c = alpha :< x <> Drop (R (Row.take f row) (Right sigil)) (UsedInMember f)
  traceTc "gen" (text "cg for member:" <+> prettyE f'
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (c' <> c, f')
-- FIXME: This is very hacky. But since we don't yet have implications in our
-- constraint system, ... / zilinc
cg' (If e1 bs e2 e3) t = do
  (c1, e1') <- letBang bs (cg e1) (T (TCon "Bool" [] Unboxed))
  (c, [(c2, e2'), (c3, e3')]) <- parallel' [(ThenBranch, cg e2 t), (ElseBranch, cg e3 t)]
  let e = If e1' bs e2' e3'
#ifdef BUILTIN_ARRAYS 
      ((c2',cc2),(c3',cc3)) = if arithTCExpr e1' then
        let (ca2,cc2) = splitArithConstraints c2
            (ca3,cc3) = splitArithConstraints c3
            c2' = Arith (SE $ PrimOp "||" [SE $ PrimOp "not" [tcToSExpr e1'], andSExprs ca2])
            c3' = Arith (SE $ PrimOp "||" [tcToSExpr e1', andSExprs ca3])
         in ((c2',cc2),(c3',cc3))
      else ((c2,Sat),(c3,Sat))
#else
      ((c2',cc2),(c3',cc3)) = ((c2,Sat),(c3,Sat))
#endif
  traceTc "gen" (text "cg for if:" <+> prettyE e)
  return (c1 <> c <> c2' <> c3' <> cc2 <> cc3, e)

cg' (MultiWayIf es el) t = do
  conditions <- forM es $ \(c,bs,_,_) -> letBang bs (cg c) (T (TCon "Bool" [] Unboxed))
  let (cconds, conds') = unzip conditions
      ctxs = map NthBranch [1..length es] ++ [ElseBranch]
  (c,bodies) <- parallel' $ zip ctxs (map (\(_,_,_,e) -> cg e t) es ++ [cg el t])
  let ((ces,es'),(cel,el')) = (unzip $ init bodies, last bodies)
      e' = MultiWayIf (zipWith3 (\(_,bs,l,_) cond' e' -> (cond',bs,l,e')) es conds' es') el'
      c' = c <> mconcat cconds <> mconcat ces <> cel
  traceTc "gen" (text "cg for multiway-if:" <+> prettyE e'
           L.<$> text "generate constraints:" <+> prettyC c')
  return (c',e')

cg' (Put e ls) t | not (any isNothing ls) = do
  alpha <- freshTVar
  let (fs, es) = unzip (catMaybes ls)
  (c', e') <- cg e alpha
  (ts, cs, es') <- cgMany es
  U rest <- freshTVar
  U sigil <- freshTVar
  let row  = R (Row.incomplete (zip fs (map (,True ) ts)) rest) (Right sigil)
      row' = R (Row.incomplete (zip fs (map (,False) ts)) rest) (Right sigil) 
      c1 = row' :< t
      c2 = alpha :< row
      r = Put e' (map Just (zip fs es'))
  traceTc "gen" (text "cg for put:" <+> prettyE r
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint:" <+> prettyC c1 <+> text "and" <+> prettyC c2)
  return (c1 <> c' <> cs <> c2, r)

  | otherwise = first (<> Unsat RecordWildcardsNotSupported) <$> cg' (Put e (filter isJust ls)) t
cg' (Let bs e) t = do
  (c, bs', e') <- withBindings bs e t
  return (c, Let bs' e')

cg' (Match e bs alts) t = do
  alpha <- freshTVar
  (c', e') <- letBang bs (cg e) alpha
  (c'', alts') <- cgAlts alts t alpha

  let c = c' :& c''
      e'' = Match e' bs alts'
  return (c, e'')

cg' (Annot e tau) t = do
  tvs <- use knownTypeVars
  let t' = stripLocT tau
  (c, t'') <- lift (runExceptT $ validateType' tvs t') >>= \case
    Left  e'' -> return (Unsat e'', t)
    Right t'' -> return (t'' :< t, t'')
  (c', e') <- cg e t''
  return (c <> c', Annot e' t'')


-- -----------------------------------------------------------------------------
-- Pattern constraints
-- -----------------------------------------------------------------------------

matchA :: LocPatn -> TCType -> CG (M.Map VarName (C.Assumption TCType), Constraint, TCPatn, TCType)
matchA x@(LocPatn l p) t = do
  let ?loc = l
  (s,c,p',t') <- matchA' p t
  return (s, c :@ InPattern x, TP p' l, t')

matchA' :: (?loc :: SourcePos)
       => Pattern LocIrrefPatn -> TCType
       -> CG (M.Map VarName (C.Assumption TCType), Constraint, Pattern TCIrrefPatn, TCType)

matchA' (PIrrefutable i) t = do
  (s, c, i') <- match i t
  return (s, c, PIrrefutable i', t)

matchA' (PCon k [i]) t = do
  beta <- freshTVar
  (s, c, i') <- match i beta  
  U rest <- freshTVar
  let row = Row.incomplete [(k,(beta,False))] rest
      c' = t :< V row
      row' = Row.incomplete [(k,(beta,True))] rest

  traceTc "gen" (text "match constructor pattern:" <+> pretty (PCon k [i'])
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (s, c <> c', PCon k [i'], V row')
matchA' (PCon k []) t = matchA' (PCon k [LocIrrefPatn ?loc PUnitel]) t
matchA' (PCon k is) t = matchA' (PCon k [LocIrrefPatn ?loc (PTuple is)]) t
matchA' (PIntLit i) t = do
  let minimumBitwidth | i < u8MAX      = "U8"
                      | i < u16MAX     = "U16"
                      | i < u32MAX     = "U32"
                      | otherwise      = "U64"
      c = Upcastable (T (TCon minimumBitwidth [] Unboxed)) t
      -- ^^^ FIXME: I think if we restrict this constraint, then we can possibly get rid of `Upcast' / zilinc
  return (M.empty, c, PIntLit i, t)

matchA' (PBoolLit b) t =
  return (M.empty, t :=: T (TCon "Bool" [] Unboxed), PBoolLit b, t)

matchA' (PCharLit c) t =
  return (M.empty, t :=: T (TCon "U8" [] Unboxed), PCharLit c, t)

match :: LocIrrefPatn -> TCType -> CG (M.Map VarName (C.Assumption TCType), Constraint, TCIrrefPatn)
match x@(LocIrrefPatn l ip) t = do
  let ?loc = l
  (s,c,ip') <- match' ip t
  return (s, c :@ InIrrefutablePattern x, TIP ip' l)

match' :: (?loc :: SourcePos)
      => IrrefutablePattern VarName LocIrrefPatn -> TCType
      -> CG (M.Map VarName (C.Assumption TCType), Constraint, IrrefutablePattern TCName TCIrrefPatn)

match' (PVar x) t = do
  let p = PVar (x,t)
  traceTc "gen" (text "match var pattern:" <+> prettyIP p
           L.<$> text "of type" <+> pretty t)
  return (M.fromList [(x, (t,?loc,Seq.empty))], Sat, p)

match' (PUnderscore) t = 
  let c = dropConstraintFor (M.singleton "_" (t, ?loc, Seq.empty))
   in return (M.empty, c, PUnderscore)

match' (PUnitel) t = return (M.empty, t :< T TUnit, PUnitel)

match' (PTuple ps) t = do
  (vs, blob) <- unzip <$> mapM (\p -> do v <- freshTVar; (v,) <$> match p v) ps
  let (ss, cs, ps') = (map fst3 blob, map snd3 blob, map thd3 blob)
      p' = PTuple ps'
      co = case overlapping ss of
             Left (v:_) -> Unsat $ DuplicateVariableInPattern v  -- p'
             _          -> Sat
      c = t :< T (TTuple vs)
  traceTc "gen" (text "match tuple pattern:" <+> prettyIP p'
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (M.unions ss, co <> mconcat cs <> c, p')

match' (PUnboxedRecord fs) t | not (any isNothing fs) = do
  let (ns, ps) = unzip (catMaybes fs)
  (vs, blob) <- unzip <$> mapM (\p -> do v <- freshTVar; (v,) <$> match p v) ps
  U rest <- freshTVar
  let (ss, cs, ps') = (map fst3 blob, map snd3 blob, map thd3 blob)
      row = Row.incomplete (zip ns (map (,False) vs)) rest
      row' = Row.incomplete (zip ns (map (,True) vs)) rest
      t' = R row (Left Unboxed)
      d  = Drop (R row' (Left Unboxed)) Suppressed
      p' = PUnboxedRecord (map Just (zip ns ps'))
      c = t :< t'
      co = case overlapping ss of
             Left (v:_) -> Unsat $ DuplicateVariableInPattern v  -- p'
             _          -> Sat
  traceTc "gen" (text "match unboxed record:" <+> prettyIP p'
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c
           L.<$> text "non-overlapping, and linearity constraints")
  return (M.unions ss, co <> mconcat cs <> c <> d, p')
  | otherwise = second3 (:& Unsat RecordWildcardsNotSupported) <$> match' (PUnboxedRecord (filter isJust fs)) t

match' (PTake r fs) t | not (any isNothing fs) = do
  let (ns, ps) = unzip (catMaybes fs)
  (vs, blob) <- unzip <$> mapM (\p -> do v <- freshTVar; (v,) <$> match p v) ps
  U rest <- freshTVar
  U sigil <- freshTVar
  let (ss, cs, ps') = (map fst3 blob, map snd3 blob, map thd3 blob)
      s  = M.fromList [(r, (R row' (Right sigil), ?loc, Seq.empty))]
      row = Row.incomplete (zip ns (map (,False) vs)) rest
      row' = Row.incomplete (zip ns (map (,True) vs)) rest
      t' = R row (Right sigil)
      p' = PTake (r, R row' (Right sigil)) (map Just (zip ns ps'))
      c = t :< t'
      co = case overlapping ss of
             Left (v:_) -> Unsat $ DuplicateVariableInPattern v  -- p'
             _          -> Sat
  traceTc "gen" (text "match unboxed record:" <+> prettyIP p'
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c
           L.<$> text "non-overlapping, and linearity constraints")
  return (M.unions (s:ss), co <> mconcat cs <> c, p')
  | otherwise = second3 (:& Unsat RecordWildcardsNotSupported) <$> match' (PTake r (filter isJust fs)) t

#ifdef BUILTIN_ARRAYS
match' (PArray ps) t = do
  alpha <- freshTVar
  blob <- mapM (`match` alpha) ps
  let (ss,cs,ps') = unzip3 blob
      l = SE . IntLit . fromIntegral $ length ps
      c = F t :< F (T $ TArray alpha l)
  return (M.unions ss, mconcat cs <> c, PArray ps')
#endif

-- -----------------------------------------------------------------------------
-- Auxiliaries
-- -----------------------------------------------------------------------------

freshTVar :: (?loc :: SourcePos) => CG TCType
freshTVar = fresh (ExpressionAt ?loc)
  where
    fresh :: VarOrigin -> CG TCType
    fresh ctx = do
      i <- flexes <<%= succ
      flexOrigins %= IM.insert i ctx
      return $ U i

freshEVar :: (?loc :: SourcePos) => CG SExpr
freshEVar = fresh (ExpressionAt ?loc)
  where
    fresh :: VarOrigin -> CG SExpr
    fresh ctx = do
      i <- flexes <<%= succ  -- FIXME: do we need a different variable?
      flexOrigins %= IM.insert i ctx
      return $ SU i
      
integral :: TCType -> Constraint
integral = Upcastable (T (TCon "U8" [] Unboxed))

dropConstraintFor :: M.Map VarName (C.Assumption TCType) -> Constraint
dropConstraintFor = foldMap (\(i, (t,x,us)) -> if null us then Drop t (Unused i x) else Sat) . M.toList

parallel' :: [(ErrorContext, CG (Constraint, a))] -> CG (Constraint, [(Constraint, a)])
parallel' ls = parallel (map (second (\a _ -> ((),) <$> a)) ls) ()

parallel :: [(ErrorContext, acc -> CG (acc, (Constraint, a)))]
         -> acc
         -> CG (Constraint, [(Constraint, a)])
parallel []       _   = return (Sat, [])
parallel [(ct,f)] acc = (Sat,) . return . first (:@ ct) . snd <$> f acc
parallel ((ct,f):xs) acc = do
  ctx  <- use context
  (acc', x) <- second (first (:@ ct)) <$> f acc
  ctx1 <- use context
  context .= ctx
  (c', xs') <- parallel xs acc'
  ctx2 <- use context
  let (ctx', ls, rs) = C.merge ctx1 ctx2
  context .= ctx'
  let cls = foldMap (\(n, (t, p, us@(_ Seq.:<| _))) -> Drop t (UnusedInOtherBranch n p us)) ls
      crs = foldMap (\(n, (t, p, us@(_ Seq.:<| _))) -> Drop t (UnusedInThisBranch  n p us)) rs
  return (c' <> ((cls <> crs) :@ ct), x:xs')



withBindings :: (?loc::SourcePos)
  => [Binding LocType LocPatn LocIrrefPatn LocExpr]
  -> LocExpr -- expression e to be checked with the bindings
  -> TCType  -- the type for e
  -> CG (Constraint, [Binding TCType TCPatn TCIrrefPatn TCExpr], TCExpr)
withBindings [] e top = do
  (c, e') <- cg e top
  return (c, [], e')
withBindings (Binding pat tau e0 bs : xs) e top = do
  alpha <- freshTVar
  (c0, e0') <- letBang bs (cg e0) alpha
  (ct, alpha') <- case tau of
    Nothing -> return (Sat, alpha)
    Just tau' -> do
      tvs <- use knownTypeVars
      lift (runExceptT $ validateType' tvs (stripLocT tau')) >>= \case
        Left  e -> return (Unsat e, alpha)
        Right t -> return (alpha :< t, t)
  (s, cp, pat') <- match pat alpha'
  context %= C.addScope s
  (c', xs', e') <- withBindings xs e top
  rs <- context %%= C.dropScope
  let unused = flip foldMap (M.toList rs) $ \(v,(_,_,us)) -> 
        case us of
          Seq.Empty -> warnToConstraint __cogent_wunused_local_binds (UnusedLocalBind v)
          _ -> Sat
      c = ct <> c0 <> c' <> cp <> dropConstraintFor rs <> unused
      b' = Binding pat' (fmap (const alpha) tau) e0' bs
  traceTc "gen" (text "bound expression" <+> pretty e0' <+> 
                 text "with banged" <+> pretty bs
           L.<$> text "of type" <+> pretty alpha <> semi
           L.<$> text "generate constraint" <+> prettyC c0 <> semi
           L.<$> text "constraint for ascribed type:" <+> prettyC ct)
  return (c, b':xs', e')
withBindings (BindingAlts pat tau e0 bs alts : xs) e top = do
  alpha <- freshTVar
  (c0, e0') <- letBang bs (cg e0) alpha
  (ct, alpha') <- case tau of
    Nothing -> return (Sat, alpha)
    Just tau' -> do
      tvs <- use knownTypeVars
      lift (runExceptT $ validateType' tvs (stripLocT tau')) >>= \case
        Left  e -> return (Unsat e, alpha)
        Right t -> return (alpha :< t, t)
  (calts, alts') <- cgAlts (Alt pat Regular (LocExpr (posOfE e) (Let xs e)) : alts) top alpha'
  let c = c0 <> ct <> calts
      (Alt pat' _ (TE _ (Let xs' e') _)) : altss' = alts'
      b0' = BindingAlts pat' (fmap (const alpha) tau) e0' bs altss'
  return (c, b0':xs', e')

letBang :: (?loc :: SourcePos) => [VarName] -> (TCType -> CG (Constraint, TCExpr)) -> TCType -> CG (Constraint, TCExpr)
letBang [] f t = f t
letBang bs f t = do
  c <- fold <$> mapM validateVariable bs
  ctx <- use context
  let (ctx', undo) = C.mode ctx bs (\(t,p,_) -> (T (TBang t), p, Seq.singleton ?loc))  -- FIXME: shall we also take the old `us'?
  context .= ctx'
  (c', e) <- f t
  context %= undo  -- NOTE: this is NOT equiv. to `context .= ctx'
  let c'' = Escape t UsedInLetBang
  traceTc "gen" (text "let!" <+> pretty bs <+> text "when cg for expression" <+> pretty e
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c'')
  return (c <> c' <> c'', e)

validateVariable :: VarName -> CG Constraint
validateVariable v = do
  x <- use context
  return $ if C.contains x v then Sat else Unsat (NotInScope MustVar v)


-- ----------------------------------------------------------------------------
-- pp for debugging
-- ----------------------------------------------------------------------------

prettyE :: Expr TCType TCPatn TCIrrefPatn TCExpr -> Doc
prettyE = pretty

-- prettyP :: Pattern TCIrrefPatn -> Doc
-- prettyP = pretty

prettyIP :: IrrefutablePattern TCName TCIrrefPatn -> Doc
prettyIP = pretty



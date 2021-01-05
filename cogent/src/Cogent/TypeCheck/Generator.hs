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
  , validateTypes
  , validateLayout
  , validateLayouts
  ) where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import qualified Cogent.Context as C
import Cogent.Dargent.TypeCheck
import Cogent.PrettyPrint (prettyC)
import Cogent.Surface
import Cogent.TypeCheck.ARow as ARow hiding (null)
import Cogent.TypeCheck.Base hiding (validateType)
import Cogent.TypeCheck.Util
import Cogent.Util hiding (Warning)
import Cogent.TypeCheck.Row (mkEntry)
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
import Text.PrettyPrint.ANSI.Leijen hiding ((<>), (<$>), bool)
import qualified Text.PrettyPrint.ANSI.Leijen as L
import Lens.Micro.TH
import Lens.Micro
import Lens.Micro.Mtl

import Debug.Trace

data GenState = GenState { _context :: C.Context TCType
                         , _knownTypeVars :: [TyVarName]
                         , _knownDataLayoutVars :: [DLVarName]
                         , _flexes :: Int
                         , _flexOrigins :: IM.IntMap VarOrigin
                         }

makeLenses ''GenState

type CG a = TcConsM GenState a

runCG :: C.Context TCType -> [TyVarName] -> [DLVarName] -> CG a -> TcM (a, Int, IM.IntMap VarOrigin)
runCG g tvs lvs ma = do
  (a, GenState _ _ _ f os) <- withTcConsM (GenState g tvs lvs 0 mempty) ((,) <$> ma <*> get)
  return (a,f,os)


-- -----------------------------------------------------------------------------
-- Type-level constraints
-- -----------------------------------------------------------------------------

validateType :: (?loc :: SourcePos) => RawType -> CG (Constraint, TCType)
validateType (RT t) = do
  vs <- use knownTypeVars
  ts <- lift $ use knownTypes
  layouts <- lift $ use knownDataLayouts
  lvs <- use knownDataLayoutVars
  traceTc "gen" (text "validate type" <+> pretty t)
  case t of
    TVar v b u  | v `notElem` vs -> freshTVar >>= \t' -> return (Unsat $ UnknownTypeVariable v, t')
                | otherwise -> return (mempty, T $ TVar v b u)

    TCon t as s | Nothing <- lookup t ts -> freshTVar >>= \t' -> return (Unsat $ UnknownTypeConstructor t, t')
                | Just (vs', _) <- lookup t ts
                , provided <- length as
                , required <- length vs'
                , provided /= required
               -> freshTVar >>= \t' -> return (Unsat $ TypeArgumentMismatch t provided required, t')
                | Just (vs, Just x) <- lookup t ts
               -> second (Synonym t) <$> fmapFoldM validateType as
                | otherwise -> do
                  (c, s') <- cgSigil s
                  (cs, t') <- fmapFoldM validateType (TCon t as s')
                  return (c <> cs, T t')

    TRecord rp fs s | fields  <- map fst fs
                    , fields' <- nub fields
                   -> let toRow (T (TRecord rp fs s)) = R (coerceRP rp) (Row.complete $ Row.toEntryList fs) (Left s)
                      in if fields' == fields
                           then do
                             (cs, s') <- cgSigil s
                             (ct, TRecord rp' fs' _) <- fmapFoldM validateType t 
                             return (cs <> ct, toRow . T $ TRecord rp' fs' s')
                           else freshTVar >>= \t' -> return (Unsat $ DuplicateRecordFields (fields \\ fields'), t')
                    | otherwise -> do
                      (c, s') <- cgSigil s
                      (cs, t') <- fmapFoldM validateType (TRecord rp fs s')
                      return (c <> cs, T t')

    TVariant fs  -> do let tuplize [] = T TUnit
                           tuplize [x] = x
                           tuplize xs  = T (TTuple xs)
                       (c, TVariant fs') <- fmapFoldM validateType t
                       pure (c, V (Row.fromMap (fmap (first tuplize) fs')))

#ifdef BUILTIN_ARRAYS
    TArray te l s tkns -> do
      x <- freshEVar (T u32)
      traceTc "gen" (text "unifier for array length" <+> pretty l L.<$> 
                     text "is" <+> pretty x)
      (cl,l') <- cg (rawToLocE ?loc l) (T u32)
      (ctkn,mhole) <- case tkns of
                        [] -> return (Sat, Nothing)
                        [(i,True)] -> do y <- freshEVar (T u32)
                                         traceTc "gen" (text "unifier for array hole" <+> pretty i L.<$>
                                                        text "is" <+> pretty y)
                                         (ci,i') <- cg (rawToLocE ?loc i) (T u32)
                                         let c = Arith (SE (T bool) (PrimOp "==" [toTCSExpr i', y]))
                                              -- <> Arith (SE (T bool) (PrimOp ">=" [y, SE (T u32) (IntLit 0)]))
                                              <> Arith (SE (T bool) (PrimOp "<" [y, x]))
                                         traceTc "gen" (text "cg for array hole" <+> pretty i L.<$>
                                                        text "generate constraint" <+> prettyC (c <> ci))
                                         return (c <> ci, Just y)
                        _  -> return (Unsat $ OtherTypeError "taking more than one element from arrays not supported", Nothing)
      let cl' = Arith (SE (T bool) (PrimOp ">" [x, SE (T u32) (IntLit 0)]))
             <> Arith (SE (T bool) (PrimOp "==" [toTCSExpr l', x]))
      traceTc "gen" (text "cg for array length" <+> pretty x L.<$>
                     text "generate constraint" <+> prettyC (cl <> cl'))
      (cs, s') <- cgSigil s
      (c,te') <- validateType te
      return (cl <> cl' <> ctkn <> cs <> c, A te' x (Left s') (Left mhole))

    TATake es t -> do
      blob <- forM es $ \e -> do
        x <- freshEVar (T u32)
        (ce,e') <- cg (rawToLocE ?loc e) (T u32)
        return (ce <> Arith (SE (T bool) (PrimOp "==" [toTCSExpr e', x])), e', x)
      let (ces,es',xs) = unzip3 blob
      traceTc "gen" (text "cg for @take" <+> parens (prettyList es) L.<$>
                     text "generate constraint" <+> prettyC (mconcat ces))
      (ct,t') <- validateType t
      return (mconcat ces <> ct, T $ TATake xs t')

    TAPut es t -> do
      blob <- forM es $ \e -> do
        x <- freshEVar (T u32)
        (ce,e') <- cg (rawToLocE ?loc e) (T u32)
        return (ce <> Arith (SE (T bool) (PrimOp "==" [toTCSExpr e', x])), e', x)
      let (ces,es',xs) = unzip3 blob
      traceTc "gen" (text "cg for @put" <+> parens (prettyList es) L.<$>
                     text "generate constraint" <+> prettyC (mconcat ces))
      (ct,t') <- validateType t
      return (mconcat ces <> ct, T $ TAPut xs t')
#endif

#ifdef REFINEMENT_TYPES
    TRefine v t e -> do
      (ct,t') <- validateType t
      c <- use context
      context %= C.addScope (M.fromList [(v, (t', ?loc, Seq.empty))])
      (ce,e') <- cg (rawToLocE ?loc e) (T bool)
      rs <- context %%= C.dropScope
      let unused = flip foldMap (M.toList rs) $ \(v,(_,_,us)) ->
            case us of Seq.Empty -> warnToConstraint __cogent_wunused_local_binds (UnusedLocalBind v); _ -> Sat
          c = ct <> ce <> unused
      traceTc "gen" (text "cg for reftype" L.<$>
                     text "generate constraint" <+> prettyC c)
      return (c, T $ TRefine v t' (toTCSExpr e'))
#endif

    TLayout l t -> do
      (cl,l') <- validateLayout l
      (ct,t') <- validateType t
      pure (cl <> ct <> LayoutOk t', T $ TLayout l' t')

    -- vvv The uninteresting cases; but we still have to match each of them to convince the typechecker / zilinc
    TRPar v b ctxt -> (second T) <$> fmapFoldM validateType (TRPar v b ctxt)
    TFun t1 t2 -> (second T) <$> fmapFoldM validateType (TFun t1 t2)
    TTuple ts  -> (second T) <$> fmapFoldM validateType (TTuple ts)
    TUnit -> return (mempty, T TUnit)
    TUnbox t  -> (second T) <$> fmapFoldM validateType (TUnbox t)
    TBang  t  -> (second T) <$> fmapFoldM validateType (TBang  t)
    TTake mfs t -> (second T) <$> fmapFoldM validateType (TTake mfs t)
    TPut  mfs t -> (second T) <$> fmapFoldM validateType (TPut  mfs t)
    -- With (TCon _ _ l), and (TRecord _ l), must check l == Nothing iff it is contained in a TUnbox.
    -- This can't be done in the current setup because validateType' has no context for the type it is validating.
    -- Not implementing this now, because a new syntax for types is needed anyway, which may make this issue redundant.
    -- /mdimeglio
    -- In addition to the above: We have an UnboxedNotRecursive constraint now, which checks something similar 
    -- (that recursive parameters are not used on unboxed records).
    -- We can potentially generalise this constraint to also solve the above issue (or create a similar constraint).
    -- /emmetm


validateTypes :: (?loc :: SourcePos, Traversable t) => t RawType -> CG (Constraint, t TCType)
validateTypes = fmapFoldM validateType

-- --------------------------------------------------------------------------

validateLayout :: DataLayoutExpr -> CG (Constraint, TCDataLayout)
validateLayout = let unsat = Unsat . DataLayoutError in \case
  DLRepRef n s   -> do
    (c, s') <- validateLayouts s
    ls <- lift $ use knownDataLayouts
    let e' = TLRepRef n s'
    case M.lookup n ls of
      Just (vs, exp) | length vs == length s -> return (Wellformed e' <> c, e')
                     | otherwise, en <- length vs, an <- length s
                     -> return (unsat $ dataLayoutArgsNotMatch n en an, e')
      _ -> return (unsat $ unknownDataLayout n, e')
  DLRecord fs    -> do
    (c, s') <- validateLayouts $ fmap thd3 fs
    let expr' = TLRecord $ zipWith (\(a,b,_) c -> (a,b,c)) fs s'
    return (Wellformed expr' <> c, expr')
  DLVariant e fs -> do
    (c, s') <- validateLayouts $ fmap (\(_,_,_,d) -> d) fs
    (tc, e') <- validateLayout e
    let expr' = TLVariant e' $ zipWith (\(a,b,c,_) d -> (a,b,c,d)) fs s'
    return (Wellformed expr' <> c <> tc, expr')
#ifdef BUILTIN_ARRAYS
  DLArray e p    -> do
    (c, e') <- validateLayout e
    return (c, TLArray e' p)
#endif
  -- it should be impossible to have negative prim size
  DLOffset e s   -> do
    (c, e') <- validateLayout e
    return (c, TLOffset e' s)
  DLAfter e f    -> do
    (c, e') <- validateLayout e
    return (c, TLAfter e' f)
  DLPrim n       -> return (Sat, TLPrim n)
  DLVar n        -> do
    lvs <- use knownDataLayoutVars
    if n `elem` lvs
       then return (Sat, TLVar n)
       else return (unsat $ unknownDataLayoutVar n, TLVar n)
  DLPtr          -> return (Sat, TLPtr)

validateLayouts :: Traversable t => t DataLayoutExpr -> CG (Constraint, t TCDataLayout)
validateLayouts = fmapFoldM validateLayout

cgSubstedType :: TCType -> CG Constraint
cgSubstedType (T (TLayout l t)) = cgDataLayout' l
cgSubstedType (T t) = foldMapM cgSubstedType t
cgSubstedType (U x) = pure Sat
cgSubstedType (V x) = foldMapM cgSubstedType x
cgSubstedType (R _ x s) = (<>) <$> foldMapM cgSubstedType x <*> cgSubstedSigil s
#ifdef BUILTIN_ARRAYS
cgSubstedType (A t l s tkns) = (<>) <$> cgSubstedType t <*> cgSubstedSigil s
#endif
cgSubstedType (Synonym n ts) = foldMapM cgSubstedType ts

cgSubstedSigil :: Either (Sigil (Maybe TCDataLayout)) Int -> CG Constraint
cgSubstedSigil (Left (Boxed _ (Just l))) = cgDataLayout' l
cgSubstedSigil _ = pure Sat

cgDataLayout' :: TCDataLayout -> CG Constraint
cgDataLayout' l = return Sat -- FIXME

-- -----------------------------------------------------------------------------
-- Term-level constraints
-- --------------------------------------------------------------------------

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

cg' :: (?loc :: SourcePos) => Expr LocType LocPatn LocIrrefPatn DataLayoutExpr LocExpr -> TCType -> CG (Constraint, Expr TCType TCPatn TCIrrefPatn TCDataLayout TCExpr)
cg' (PrimOp o [e1, e2]) t
  | o `elem` words "+ - * / % .&. .|. .^. >> <<"
  = do (c1, e1') <- cg e1 t
       (c2, e2') <- cg e2 t
       return (integral t <> c1 <> c2, PrimOp o [e1', e2'] )
  | o `elem` words "&& ||"
  = do (c1, e1') <- cg e1 t
       (c2, e2') <- cg e2 t
       return (T bool :=: t <> c1 <> c2, PrimOp o [e1', e2'] )
  | o `elem` words "== /= >= <= > <"
  = do alpha <- freshTVar
       (c1, e1') <- cg e1 alpha
       (c2, e2') <- cg e2 alpha
       let c  = T bool :=: t
           c' = IsPrimType alpha
       return (c <> c' <> c1 <> c2, PrimOp o [e1', e2'] )
cg' (PrimOp o [e]) t
  | o == "complement"  = do
      (c, e') <- cg e t
      return (integral t :& c, PrimOp o [e'])
  | o == "not"         = do
      (c, e') <- cg e t
      return (T bool :=: t :& c, PrimOp o [e'])
cg' (PrimOp _ _) _ = __impossible "cg': unimplemented primops"
cg' (Var n) t = do
  let e = Var n  -- it has a different type than the above `Var n' pattern
  ctx <- use context
  traceTc "gen" (text "cg for variable" <+> pretty n L.<$> text "of type" <+> pretty t)
  case C.lookup n ctx of
    -- Variable not found, see if the user meant a function.
    Nothing ->
      lift (use $ knownFuns.at n) >>= \case
        Just _  -> cg' (TLApp n [] [] NoInline) t
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
  let c = T bool :=: t
      e = BoolLit b
  return (c,e)

cg' (CharLit l) t = do
  let c = T u8 :=: t
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
      n = SE (T u32) (IntLit . fromIntegral $ length es)
      cz = Arith (SE (T bool) (PrimOp ">" [n, SE (T u32) (IntLit 0)]))
  traceTc "gen" (text "cg for array literal length" L.<$>
                 text "generate constraint" <+> prettyC cz L.<$>
                 text "which should always be trivially true")
  beta <- freshVar
  return (mconcat cs <> cz <> (A alpha n (Left Unboxed) (Left Nothing)) :< t, ArrayLit es')

cg' (ArrayIndex e i) t = do
  alpha <- freshTVar        -- element type
  n <- freshEVar (T u32)    -- length
  s <- freshVar             -- sigil
  idx <- freshEVar (T u32)  -- index
  h <- freshVar             -- hole
  let -- XXX | ta = A alpha n (Right s) (Left $ Just idx)  -- this is the biggest type 'e' can ever have -- with a hole
      -- XXX |                                             -- at a location other than 'i'
      ta = A alpha n (Right s) (Left Nothing)  -- For now we disallow holes to appear, due to the lack of symbolic execution
      ta' = A alpha n (Right s) (Right h)
  (ce, e') <- cg e ta'
  (ci, i') <- cg i (T u32)
  let c = alpha :< t
        <> ta' :< ta
        <> Share ta UsedInArrayIndexing
        <> Arith (SE (T bool) (PrimOp "<"  [toTCSExpr i', n  ]))
        -- <> Arith (SE (T bool) (PrimOp "<"  [idx         , n  ]))
        -- <> Arith (SE (T bool) (PrimOp "/=" [toTCSExpr i', idx]))
        -- <> Arith (SE (PrimOp ">=" [toSExpr i, SE (IntLit 0)]))  -- as we don't have negative values
  traceTc "gen" (text "array indexing" <> colon
                 L.<$> text "index is" <+> pretty (stripLocE i) <> semi
                 L.<$> text "upper bound (excl.) is" <+> pretty n <> semi
                 L.<$> text "generate constraint" <+> prettyC c)
  return (ce <> ci <> c, ArrayIndex e' i')

cg' (ArrayMap2 ((p1,p2), fbody) (arr1,arr2)) t = __fixme $ do  -- FIXME: more accurate constraints / zilinc
  alpha1 <- freshTVar
  alpha2 <- freshTVar
  x1 <- freshVar
  x2 <- freshVar
  len1 <- freshEVar (T u32)
  len2 <- freshEVar (T u32)
  (s1,cp1,p1') <- match p1 alpha1
  (s2,cp2,p2') <- match p2 alpha2
  context %= C.addScope (s1 `M.union` s2)  -- domains of s1 and s2 don't overlap
  (cbody, fbody') <- cg fbody (T $ TTuple [alpha1, alpha2])
  -- TODO: also need to check that all other variables `fbody` refers to must be non-linear / zilinc
  rs <- context %%= C.dropScope
  let tarr1 = A alpha1 len1 (Right x1) (Left Nothing)
      tarr2 = A alpha2 len2 (Right x2) (Left Nothing)
  (carr1, arr1') <- cg arr1 tarr1
  (carr2, arr2') <- cg arr2 tarr2
  let unused = flip foldMap (M.toList rs) $ \(v,(_,_,us)) ->
        case us of Seq.Empty -> warnToConstraint __cogent_wunused_local_binds (UnusedLocalBind v); _ -> Sat
      t' = T $ TTuple [tarr1,tarr2]
      e' = ArrayMap2 ((p1',p2'), fbody') (arr1',arr2')
  return (t' :< t <> cp1 <> cp2 <> cbody <> carr1 <> carr2 <> dropConstraintFor rs <> unused, e')

cg' (ArrayPut arr [(idx,v)]) t = do
  alpha <- freshTVar  -- the element type
  sigma <- freshTVar  -- the original array type
  l <- freshEVar (T u32)  -- the length of the array
  s <- freshVar   -- the unifier for the sigil
  (carr,arr') <- cg arr sigma
  (cidx,idx') <- cg idx $ T u32
  (cv,v') <- cg v alpha
  let c = [ A alpha l (Right s) (Left Nothing) :< t
          , sigma :< A alpha l (Right s) (Left . Just $ toTCSExpr idx')
          , carr, cidx, cv
          -- , Arith (SE (T bool) (PrimOp ">=" [idx', SE (IntLit 0)]))
          , Arith (SE (T bool) (PrimOp "<" [toTCSExpr idx', l]))
          ]
  traceTc "gen" (text "cg for array put" L.<$>
                 text "elemenet type is" <+> pretty alpha L.<$>
                 text "array type is" <+> pretty sigma L.<$>
                 text "length is" <+> pretty l L.<$>
                 text "sigil is" <+> pretty s L.<$>
                 text "generate constraint" <+> prettyC (mconcat c))
  return (mconcat c, ArrayPut arr' [(idx',v')])
cg' (ArrayPut arr ivs) t = do
  alpha <- freshTVar  -- the elemenet type
  sigma <- freshTVar  -- the original array type
  l <- freshEVar (T u32)  -- the length of the array
  s <- freshVar  -- sigil
  (carr,arr') <- cg arr sigma
  let (idxs,vs) = unzip ivs
  blob1 <- forM idxs $ \idx -> do
    (cidx,idx') <- cg idx (T u32)
    let c = Arith (SE (T bool) (PrimOp "<" [toTCSExpr idx', l]))
    return (cidx <> c, idx')
  -- TODO: holes distinct from each other / zilinc
  blob2 <- forM vs $ \v -> cg v alpha
  let c = [ A alpha l (Right s) (Left Nothing) :< t
          , sigma :< A alpha l (Right s) (Left Nothing)
          , carr
          , Drop alpha MultipleArrayTakePut
          ] ++ map fst blob1 ++ map fst blob2
  return (mconcat c, ArrayPut arr' (zip (map snd blob1) (map snd blob2)))
#endif

cg' exp@(Lam pat mt e) t = do
  alpha <- freshTVar
  beta  <- freshTVar
  (ct, alpha') <- case mt of
    Nothing -> return (Sat, alpha)
    Just t' -> do
      tvs <- use knownTypeVars
      (ct',t'') <- validateType (stripLocT t')
      return (ct' <> alpha :< t'', t'')
  (s, cp, pat') <- match pat alpha'
  let fvs = fvE $ stripLocE (LocExpr ?loc $ Lam pat mt e)
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
      c = V (Row.incomplete [Row.mkEntry k alpha False] x) :< t
  traceTc "gen" (text "cg for constructor:" <+> prettyE e
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (c' <> c, e)
cg' (Con k []) t = cg' (Con k [LocExpr ?loc $ Unitel]) t
cg' (Con k es) t = cg' (Con k [LocExpr ?loc $ Tuple es]) t
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
      r = R None (Row.complete $ zipWith3 mkEntry fs ts (repeat False)) (Left Unboxed)
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

cg' (TLApp f ts ls i) t = do
  -- tvs <- use knownTypeVars
  (ct, getCompose -> ts') <- validateTypes (stripLocT <$> Compose ts)
  (cl, getCompose -> ls') <- validateLayouts (Compose ls)
  lift (use $ knownFuns.at f) >>= \case
    Just (PT tvs lvs tau) -> do
      let matchT :: [(TyVarName, Kind)] -> [Maybe TCType] -> CG (Constraint, [(TyVarName, TCType)])
          matchT [] [] = pure (Sat, [])
          matchT [] _  = pure (Unsat (TooManyTypeArguments f (PT tvs lvs tau)), [])
          matchT vs [] = freshTVar >>= matchT vs . return . Just
          matchT (v:vs) (Nothing:as) = freshTVar >>= \a -> matchT (v:vs) (Just a:as)
          matchT ((v,k):vs) (Just a:as) = do
            (c, ps) <- matchT vs as
            return (kindToConstraint k a (TypeParam f v) <> c, (v,a):ps)
          matchL :: [(DLVarName, TCType)] -> [Maybe TCDataLayout] -> CG (Constraint, [(DLVarName, TCDataLayout)])
          matchL [] [] = pure (Sat, [])
          matchL [] _  = pure (Unsat $ TooManyLayoutArguments f (PT tvs lvs tau), [])
          matchL ts [] = freshLVar >>= matchL ts . return . Just
          matchL (t':t'') (Nothing:l') = freshLVar >>= matchL (t':t'') . (:l') . Just
          matchL ((v,t):t') (Just l:l') = do
            (c, ps) <- matchL t' l'
            return (c <> layoutMatchConstraint t l, (v, l):ps)
      (cts, tps) <- matchT tvs ts'
      (cls, lps) <- matchL (second (substType tps) <$> lvs) ls'
      let rt = substLayout lps $ substType tps tau
          rc = rt :< t
          re = TLApp f (Just . snd <$> tps) (Just . snd <$> lps) i
      traceTc "gen" (text "cg for tlapp:" <+> prettyE re
               L.<$> text "of type" <+> pretty t <> semi
               L.<$> text "type signature is" <+> pretty (PT tvs lvs tau) <> semi
               L.<$> text "generate constraint" <+> prettyC rc)
      return (ct <> cl <> cts <> cls <> rc, re)
    Nothing -> do
      let e = TLApp f ts' ls' i
          c = Unsat (FunctionNotFound f)
      return (ct <> cl <> c, e)

cg' (Member e f) t =  do
  alpha <- freshTVar
  (c', e') <- cg e alpha
  U rest <- freshTVar
  U sigil <- freshTVar
  rp <- freshRPVar
  let f' = Member e' f
      row = Row.incomplete [Row.mkEntry f t False] rest
      x = R rp row (Right sigil)
      c = alpha :< x <> Drop x (UsedInMember f)
  traceTc "gen" (text "cg for member:" <+> prettyE f'
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (c' <> c, f')

-- FIXME: This is very hacky. But since we don't yet have implications in our
-- constraint system, ... / zilinc
cg' (If e1 bs e2 e3) t = do
  (c1, e1') <- letBang bs (cg e1) (T bool)
  (c, [(c2, e2'), (c3, e3')]) <- parallel' [(ThenBranch, cg e2 t), (ElseBranch, cg e3 t)]
  let e = If e1' bs e2' e3'
#ifdef BUILTIN_ARRAYS
      (c2',c3') = if arithTCExpr e1' then
        let c2' = Arith (toTCSExpr e1') :-> c2
            c3' = Arith (SE (T bool) (PrimOp "not" [toTCSExpr e1'])) :-> c3
         in (c2',c3')
      else (c2,c3)
#else
      (c2',c3') = (c2,c3)
#endif
  traceTc "gen" (text "cg for if:" <+> prettyE e)
  return (c1 <> c <> c2' <> c3', e)

cg' (MultiWayIf es el) t = do
  conditions <- forM es $ \(c,bs,_,_) -> letBang bs (cg c) (T bool)
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
  rp <- freshRPVar
  let row  = R rp (Row.incomplete (zipWith3 mkEntry fs ts (repeat True)) rest) (Right sigil)
      row' = R rp (Row.incomplete (zipWith3 mkEntry fs ts (repeat False)) rest) (Right sigil) 
      c = row' :< t <> alpha :< row <> UnboxedNotRecursive row <>
          NotReadOnly (Right sigil)
      r = Put e' (map Just (zip fs es'))
  traceTc "gen" (text "cg for put:" <+> prettyE r
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint:" <+> prettyC c)
  return (c <> c' <> cs, r)

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
  let tau' = stripLocT tau
  (c, t') <- do (ctau,tau'') <- validateType tau'
                traceTc "gen" (text "cg for type annotation"
                               L.<$> text "generate constraint" <+> prettyC (tau'' :< t)
                               L.<$> text "and others")
                return (ctau <> tau'' :< t, tau'')
  (c', e') <- cg e t'
  return (c <> c', Annot e' t')

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
  let row = Row.incomplete [Row.mkEntry k beta False] rest
      c' = t :< V row
      row' = Row.incomplete [Row.mkEntry k beta True] rest

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
  return (M.empty, t :=: T bool, PBoolLit b, t)

matchA' (PCharLit c) t =
  return (M.empty, t :=: T u8, PCharLit c, t)

match :: LocIrrefPatn -> TCType -> CG (M.Map VarName (C.Assumption TCType), Constraint, TCIrrefPatn)
match x@(LocIrrefPatn l ip) t = do
  let ?loc = l
  (s,c,ip') <- match' ip t
  return (s, c :@ InIrrefutablePattern x, TIP ip' l)

match' :: (?loc :: SourcePos)
       => IrrefutablePattern VarName LocIrrefPatn LocExpr
       -> TCType
       -> CG (M.Map VarName (C.Assumption TCType), Constraint, IrrefutablePattern TCName TCIrrefPatn TCExpr)

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
      row = Row.incomplete (zipWith3 mkEntry ns vs (repeat False)) rest
      row' = Row.incomplete (zipWith3 mkEntry ns vs (repeat True)) rest
      t' = R None row (Left Unboxed)
      d  = Drop (R None row' (Left Unboxed)) Suppressed
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
  rp <- freshRPVar
  let (ss, cs, ps') = (map fst3 blob, map snd3 blob, map thd3 blob)
      s  = M.fromList [(r, (R rp row' (Right sigil), ?loc, Seq.empty))]
      row = Row.incomplete (zipWith3 mkEntry ns vs (repeat False)) rest
      row' = Row.incomplete (zipWith3 mkEntry ns vs (repeat True)) rest
      t' = R rp row (Right sigil)
      p' = PTake (r, R rp row' (Right sigil)) (map Just (zip ns ps'))
      c = t :< t' <> NotReadOnly (Right sigil)
      co = case overlapping (s:ss) of
        Left (v:_) -> Unsat $ DuplicateVariableInPattern v  -- p'
        _          -> Sat
  traceTc "gen" (text "match on take:" <+> prettyIP p'
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c
           L.<$> text "non-overlapping, and linearity constraints")
  return (M.unions (s:ss), co <> mconcat cs <> c, p')
  | otherwise = second3 (:& Unsat RecordWildcardsNotSupported) <$> match' (PTake r (filter isJust fs)) t

#ifdef BUILTIN_ARRAYS
match' (PArray ps) t = do
  alpha <- freshTVar  -- element type
  blob  <- mapM (`match` alpha) ps
  let (ss,cs,ps') = unzip3 blob
      l = SE (T u32) (IntLit . fromIntegral $ length ps) :: TCSExpr -- length of the array
      c = t :< (A alpha l (Left Unboxed) (Left Nothing))
  traceTc "gen" (text "match on array literal pattern" L.<$>
                 text "element type is" <+> pretty alpha L.<$>
                 text "length is" <+> pretty l L.<$>
                 text "generate constraint" <+> prettyC c)
  return (M.unions ss, mconcat cs <> c, PArray ps')

match' (PArrayTake arr [(idx,p)]) t = do
  alpha <- freshTVar  -- array elmt type
  len   <- freshEVar (T u32)  -- array length
  sigil <- freshVar   -- sigil
  (cidx,idx') <- cg idx $ T u32
  (sp,cp,p') <- match p alpha
  let tarr = A alpha len (Right sigil) (Left . Just $ toTCSExpr idx')  -- type of the newly introduced @arr'@ variable
      s = M.fromList [(arr, (tarr, ?loc, Seq.empty))]
      c = [ t :< A alpha len (Right sigil) (Left Nothing)
          -- , Arith (SE (T bool) (PrimOp ">=" [toTCSExpr idx', SE (T u32) (IntLit 0)]))
          , Arith (SE (T bool) (PrimOp "<"  [toTCSExpr idx', len]))
          ]
  traceTc "gen" (text "match on array take" L.<$>
                 text "element type is" <+> pretty alpha L.<$>
                 text "length is" <+> pretty len L.<$>
                 text "sigil is" <+> pretty sigil L.<$>
                 text "generate constraint" <+> prettyC (mconcat c))
  return (s `M.union` sp, cp `mappend` mconcat c, PArrayTake (arr, tarr) [(idx',p')])

match' (PArrayTake arr _) t = __todo "match': taking multiple elements from array is not supported"
#endif

-- -----------------------------------------------------------------------------
-- Auxiliaries
-- -----------------------------------------------------------------------------

cgSigil :: (?loc :: SourcePos) => Sigil (Maybe DataLayoutExpr) -> CG (Constraint, Sigil (Maybe TCDataLayout))
cgSigil = \case
  Unboxed -> return (Sat, Unboxed)
  Boxed b Nothing -> return (Sat, Boxed b Nothing)
  Boxed b (Just l) -> do
    (c, l') <- validateLayout l
    return (c, Boxed b (Just l'))

freshVar :: (?loc :: SourcePos) => CG Int
freshVar = fresh (ExpressionAt ?loc)
  where
    fresh :: VarOrigin -> CG Int
    fresh ctx = do
      i <- flexes <<%= succ
      flexOrigins %= IM.insert i ctx
      return i

freshTVar :: (?loc :: SourcePos) => CG TCType
freshTVar = U  <$> freshVar

freshEVar :: (?loc :: SourcePos) => TCType -> CG TCSExpr
freshEVar t = SU t <$> freshVar

freshLVar :: (?loc :: SourcePos) => CG TCDataLayout
freshLVar = TLU <$> freshVar

freshRPVar :: (?loc :: SourcePos) => CG RP
freshRPVar = UP <$> freshVar
      
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
    Just tau' -> do (ctau',tau'') <- validateType (stripLocT tau')
                    return (ctau' <> alpha :< tau'', tau'')
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
      (ctau,tau'') <- validateType (stripLocT tau')
      return (ctau <> alpha :< tau'', tau'')
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

prettyE :: Expr TCType TCPatn TCIrrefPatn TCDataLayout TCExpr -> Doc
prettyE = pretty

-- prettyP :: Pattern TCIrrefPatn -> Doc
-- prettyP = pretty

prettyIP :: IrrefutablePattern TCName TCIrrefPatn TCExpr -> Doc
prettyIP = pretty



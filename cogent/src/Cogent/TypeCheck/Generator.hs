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
  ) where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import qualified Cogent.Context as C
import Cogent.Dargent.TypeCheck
import Cogent.PrettyPrint (symbol)
import qualified Cogent.PrettyPrint as PP (prettyC)
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
import Data.List (nub, (\\), unzip4)
import qualified Data.Map as M
import qualified Data.IntMap as IM
import Data.Maybe (catMaybes, isNothing, isJust)
import Data.Monoid ((<>))
import qualified Data.Sequence as Seq
import Text.Parsec.Pos
import Text.PrettyPrint.ANSI.Leijen hiding ((<>), (<$>), bool)
import qualified Text.PrettyPrint.ANSI.Leijen as L
import Lens.Micro
import Lens.Micro.Mtl
import Lens.Micro.TH

import Debug.Trace

data GenState = GenState { _context :: C.Context TCType
                         , _knownTypeVars :: [TyVarName]
                         , _knownDataLayoutVars :: [DLVarName]
                         , _flexes :: Int
                         , _flexOrigins :: IM.IntMap VarOrigin
                         , _freshVars :: Int
                         }

makeLenses ''GenState

type CG a = TcConsM GenState a

runCG :: C.Context TCType
      -> [TyVarName]
      -> [DLVarName]
      -> CG a
      -> TcM (a, Int, IM.IntMap VarOrigin, Int)
runCG g tvs lvs ma = 
  withTcConsM (GenState g tvs lvs 0 mempty 0) ((,) <$> ma <*> get) >>=
  \(a, GenState _ _ _ flex os fvar) -> return (a,flex,os,fvar)


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
  let ?isRefType = False
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
                | otherwise -> (second T) <$> fmapFoldM validateType (TCon t as (fmap (fmap toTCDL) s))

    TRecord rp fs s | fields  <- map fst fs
                    , fields' <- nub fields
                   -> let toRow (T (TRecord rp fs s)) = R (coerceRP rp) (Row.complete $ Row.toEntryList fs) (Left s)
                      in if fields' == fields
                         then do
                           (ct, t') <- case s of
                             Boxed _ (Just dlexpr) -> do
                                (cl, l') <- validateLayout dlexpr
                                (ct, t') <- fmapFoldM validateType t
                                return (cl <> ct, t')
                             _ -> fmapFoldM validateType t
                           case t' of
                             TRecord rp' fs' s' -> return (ct, toRow . T $ TRecord rp' fs' (fmap (fmap toTCDL) s'))
                             _ -> freshTVar >>= \t'' -> return (ct, t'')  -- something must have gone wrong; @ct <> cl@ should already contains the unsats / zilinc
                         else freshTVar >>= \t' -> return (Unsat $ DuplicateRecordFields (fields \\ fields'), t')
                    | otherwise -> (second T) <$> fmapFoldM validateType (TRecord rp fs (fmap (fmap toTCDL) s))

    TVariant fs  -> do let tuplize [] = T TUnit
                           tuplize [x] = x
                           tuplize xs  = T (TTuple xs)
                       (c, TVariant fs') <- fmapFoldM validateType t
                       pure (c, V (Row.fromMap (fmap (first tuplize) fs')))

#ifdef REFINEMENT_TYPES
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
      (c,te') <- validateType te
      return (cl <> cl' <> ctkn <> c, A te' x (Left $ fmap (fmap toTCDL) s) (Left mhole))

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

    TRefine v t e -> do
      (ct,t') <- validateType t
      context %= C.addScope (M.fromList [(v, (T (TBang t'), ?loc, Seq.empty))])
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
      let cl = case runExcept $ tcDataLayoutExpr layouts lvs l of
                 Left (e:_) -> Unsat $ DataLayoutError e
                 Right _    -> Sat
      (ct,t') <- validateType t
      let l' = toTCDL l
      pure (cl <> ct <> l' :~ t', T $ TLayout l' t')

    TFun (Just v) t1 t2 -> do
      (c1,t1') <- validateType t1
      context %= C.addScope (M.fromList [(v, (t1', ?loc, Seq.empty))])
      (c2,t2') <- validateType t2
      rs <- context %%= C.dropScope
      let unused = flip foldMap (M.toList rs) $ \(v,(_,_,us)) ->
            case us of Seq.Empty -> warnToConstraint __cogent_wunused_local_binds (UnusedLocalBind v); _ -> Sat
          c = c1 <> c2 <> unused
      traceTc "gen" (text "cg for dep function" L.<$>
                     text "generate constraint" <+> prettyC c)
      return (c, T $ TFun (Just v) t1' t2')


    -- vvv The uninteresting cases; but we still have to match each of them to convince the typechecker / zilinc
    TRPar v b ctxt -> (second T) <$> fmapFoldM validateType (TRPar v b ctxt)
    TFun Nothing t1 t2 -> (second T) <$> fmapFoldM validateType (TFun Nothing t1 t2)
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


validateTypes :: (?loc :: SourcePos, Traversable t)
              => t RawType -> CG (Constraint, t TCType)
validateTypes = fmapFoldM validateType

-- --------------------------------------------------------------------------

validateLayout :: DataLayoutExpr -> CG (Constraint, TCDataLayout)
validateLayout l = do
  ls <- lift $ use knownDataLayouts
  vs <- use knownDataLayoutVars
  let l' = toTCDL l
  case runExcept $ tcDataLayoutExpr ls vs l of
    Left (e:_) -> pure (Unsat $ DataLayoutError e, l')
    Right _    -> pure (Sat, l')

validateLayouts :: Traversable t => t DataLayoutExpr -> CG (Constraint, t TCDataLayout)
validateLayouts = fmapFoldM validateLayout


-- -----------------------------------------------------------------------------
-- Term-level constraints
-- --------------------------------------------------------------------------

cgFunDef :: (?loc :: SourcePos)
         => [Alt LocPatn LocExpr]
         -> TCType
         -> CG (Constraint, [Alt TCPatn TCExpr])
cgFunDef alts t = do
  α1 <- freshTVar
  v <- freshRefVarName freshVars
  α2 <- freshTVar  -- Here we cannot introduce flexes and construct a refinement type.
                   -- E.g., when t is a type var, it would make the {v:?0|?1(v,x)} unable
                   -- to unify. / zilinc
  x <- freshEName
  let ?isRefType = True
  (c, alts') <- cgAlts alts α2 (Just x) α1
  return (c <> (T (TFun (Just x) α1 α2)) :< t, alts')

-- cgAlts alts out_type in_type
-- NOTE the order of arguments!
cgAlts :: (?isRefType :: Bool, ?loc :: SourcePos)
       => [Alt LocPatn LocExpr]
       -> TCType
       -> Maybe VarName
       -> TCType
       -> CG (Constraint, [Alt TCPatn TCExpr])
cgAlts alts top mv alpha = do
  let
    altPattern (Alt p _ _) = p

    f (Alt p l e) mv t = do
      (s, prds, c, p', t') <- matchA p mv t
      context %= C.addScope s
      (c', e') <- cg e top
      let cctx = case mv of
            Nothing -> fmap (\(t,_,occ) -> (t, Seq.length occ)) s
            Just v  -> M.insert v (t,0) $ fmap (\(t,_,occ) -> (t, Seq.length occ)) s
#ifdef REFINEMENT_TYPES
          c'' = (cctx, prds) :|- c'
#else
          c'' = c'
#endif
      rs <- context %%= C.dropScope
      let unused = flip foldMap (M.toList rs) $ \(v,(_,_,us)) ->
            case us of Seq.Empty -> warnToConstraint __cogent_wunused_local_binds (UnusedLocalBind v); _ -> Sat
      return (t', (c <> c'' <> dropConstraintFor rs <> unused, Alt p' l e'))

    jobs = map (\(n, alt) -> (NthAlternative n (altPattern alt), f alt mv))
               (zip [1..] alts)

  (c'', blob) <- parallel jobs alpha

  let (cs, alts') = unzip blob
      c = mconcat (Exhaustive alpha (map (toRawPatn . altPattern) $ toTypedAlts alts'):c'':cs)
  return (c, alts')


-- -----------------------------------------------------------------------------
-- Expression constraints
-- -----------------------------------------------------------------------------

cgMany :: (?loc :: SourcePos, ?isRefType :: Bool)
       => [LocExpr] -> CG ([TCType], Constraint, [TCExpr])
cgMany es = do
  let each (ts,c,es') e = do
        alpha    <- freshTVar
        (c', e') <- cg e alpha
        return (alpha:ts, c <> c', e':es')
  (ts, c', es') <- foldM each ([], Sat, []) es  -- foldM is the same as foldlM
  return (reverse ts, c', reverse es')

cg :: (?isRefType :: Bool) => LocExpr -> TCType -> CG (Constraint, TCExpr)
cg x@(LocExpr l e) t = do
  let ?loc = l
  (c, e') <- cg' e t
  return (c :@ InExpression x t, TE t e' l)

cg' :: (?loc :: SourcePos, ?isRefType :: Bool)
    => Expr LocType LocPatn LocIrrefPatn DataLayoutExpr LocExpr
    -> TCType
    -> CG (Constraint, Expr TCType TCPatn TCIrrefPatn TCDataLayout TCExpr)
cg' (PrimOp o [e1, e2]) t
-- /////////////////////////////////////
-- +, -, *, /, %, .&., .|., .^., >>, <<
-- /////////////////////////////////////
#ifdef REFINEMENT_TYPES
  | o `elem` words "+ - * .&. .|. .^. >> <<" || (o `elem` ["/", "%"] && not __cogent_ftypecheck_undef)
  , ?isRefType
  = do β <- freshTVar
       v <- freshRefVarName freshVars
       (c1, e1') <- cg e1 β
       (c2, e2') <- cg e2 β
       let ϕ = SE (T bool) $ PrimOp "==" [SE β (Var v), SE β (PrimOp o [toTCSExpr e1', toTCSExpr e2'])]
           ρ = T $ TRefine v β ϕ
           c = ρ :< t
       traceTc "gen" (text "[ref-types] cg for primitive op" <+> symbol o L.<$>
                      text "generate constraint" <+> prettyC c)
       return (integral β <> BaseType β <> c <> c1 <> c2, PrimOp o [e1', e2'])
  | o `elem` ["/", "%"]
  , __cogent_ftypecheck_undef
  , ?isRefType
  = do β <- freshTVar
       v <- freshRefVarName freshVars
       (c1, e1') <- cg e1 β
       let nonZeroType = T (TRefine v β (SE (T bool) (PrimOp ">" [SE β (Var v), SE β (IntLit 0)])))
       (c2, e2') <- cg e2 nonZeroType
       let ϕ = SE (T bool) $ PrimOp "==" [SE β (Var v), SE β (PrimOp o [toTCSExpr e1', toTCSExpr e2'])]
           ρ = T $ TRefine v β ϕ
           c = ρ :< t
       traceTc "gen" (text "[ref-types] cg for primitive op (undef check on)" <+> symbol o L.<$>
                      text "generate constraint" <+> prettyC c)
       return (integral β <> BaseType β <> c <> c1 <> c2, PrimOp o [e1', e2']) 
#endif
  | o `elem` words "+ - * / % .&. .|. .^. >> <<"
#ifdef REFINEMENT_TYPES
  , not ?isRefType
#endif
  = do (c1, e1') <- cg e1 t
       (c2, e2') <- cg e2 t
       return (integral t <> c1 <> c2, PrimOp o [e1', e2'])
-- ////////////////////////////////////
--               &&, ||
-- ////////////////////////////////////
#ifdef REFINEMENT_TYPES
  | o `elem` words "&& ||"
  , ?isRefType
  = do v <- freshRefVarName freshVars
       (c1, e1') <- cg e1 (T bool)
       (c2, e2') <- cg e2 (T bool)
       let ϕ = SE (T bool) $ PrimOp o [toTCSExpr e1', toTCSExpr e2']
           ρ = T $ TRefine v (T bool) ϕ
           c = ρ :< t
       traceTc "gen" (text "[ref-types] cg for primitive op" <+> symbol o L.<$>
                      text "generate constraint" <+> prettyC c)
       return (c <> c1 <> c2, PrimOp o [e1', e2'])
#endif
  | o `elem` words "&& ||"
#ifdef REFINEMENT_TYPES
  , not ?isRefType
#endif
  = do (c1, e1') <- cg e1 t
       (c2, e2') <- cg e2 t
       return (T bool :< t <> c1 <> c2, PrimOp o [e1', e2'])
-- ////////////////////////////////////
--            >=, <=, >, <
-- ////////////////////////////////////
#ifdef REFINEMENT_TYPES
  | o `elem` words ">= <= > <"
  , ?isRefType
  = do β <- freshTVar
       v <- freshRefVarName freshVars
       (c1, e1') <- cg e1 β
       (c2, e2') <- cg e2 β
       let ϕ = SE (T bool) $ PrimOp "==" [ SE (T bool) (Var v)
                                         , SE (T bool) (PrimOp o [toTCSExpr e1', toTCSExpr e2']) ]
           ρ = T $ TRefine v (T bool) ϕ
           c = ρ :< t
       traceTc "gen" (text "[ref-types] cg for primitive op" <+> symbol o L.<$>
                      text "generate constraint" <+> prettyC c)
       return (integral β <> BaseType β <> c <> c1 <> c2, PrimOp o [e1', e2'])
#endif
  | o `elem` words ">= <= > <"
#ifdef REFINEMENT_TYPES
  , not ?isRefType
#endif
  = do α <- freshTVar
       (c1, e1') <- cg e1 α
       (c2, e2') <- cg e2 α
       let c  = T bool :< t
           c' = integral α
       return (c <> c' <> c1 <> c2, PrimOp o [e1', e2'])
-- ////////////////////////////////////
--               ==, /=
-- ////////////////////////////////////
#ifdef REFINEMENT_TYPES
  | o `elem` words "== /="
  , ?isRefType
  = do β <- freshTVar
       v <- freshRefVarName freshVars
       (c1, e1') <- cg e1 β
       (c2, e2') <- cg e2 β
       let ϕ = SE (T bool) $ PrimOp "==" [ SE (T bool) (Var v)
                                         , SE (T bool) (PrimOp o [toTCSExpr e1', toTCSExpr e2']) ]
           ρ = T $ TRefine v (T bool) ϕ
           c = ρ :< t
       traceTc "gen" (text "[ref-types] cg for primitive op" <+> symbol o L.<$>
                      text "generate constraint" <+> prettyC c)
       return (PrimType β <> BaseType β <> c <> c1 <> c2, PrimOp o [e1', e2'])
#endif
  | o `elem` words "== /="
#ifdef REFINEMENT_TYPES
  , not ?isRefType
#endif
  = do α <- freshTVar
       (c1, e1') <- cg e1 α
       (c2, e2') <- cg e2 α
       let c  = T bool :< t
           c' = PrimType α
       return (c <> c' <> c1 <> c2, PrimOp o [e1', e2'])

cg' (PrimOp o [e]) t
-- ////////////////////////////////////
--             complement
-- ////////////////////////////////////
#ifdef REFINEMENT_TYPES
  | o == "complement"
  , ?isRefType
  = do β <- freshTVar
       v <- freshRefVarName freshVars
       (ce, e') <- cg e β
       let ρ = SE (T bool) (PrimOp "==" [SE β (Var v), SE β (PrimOp o [toTCSExpr e'])])
           ϕ = T (TRefine v β ρ)
       return (integral β <> BaseType β <> ϕ :< t <> ce, PrimOp o [e'])
#endif
  | o == "complement"
#ifdef REFINEMENT_TYPES
  , not ?isRefType
#endif
  = do (c, e') <- cg e t
       return (integral t :& c, PrimOp o [e'])
-- ////////////////////////////////////
--                 not
-- ////////////////////////////////////
#ifdef REFINEMENT_TYPES
  | o == "not"
  , ?isRefType
  = do v <- freshRefVarName freshVars
       (ce, e') <- cg e (T bool)
       let ϕ = T (TRefine v (T bool) (SE (T bool) $ PrimOp o [toTCSExpr e']))
       return (ϕ :< t <> ce, PrimOp o [e'])
#endif
  | o == "not"
#ifdef REFINEMENT_TYPES
  , not ?isRefType
#endif
  = do (c, e') <- cg e t
       return (T bool :< t :& c, PrimOp o [e'])

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

    Just (t', p, used) -> do
      context %= C.use n ?loc
      -- c <- if ?isRefType then
      --        do beta <- freshTVar
      --           let rho = T $ TRefine refVarName beta (SE (T bool) (PrimOp "==" [SE beta (Var refVarName), SE beta (Var n)]))
      --           return (t' :< t <> rho :< t')
      --      else return $ t' :< t
      let c = t' :< t
      share <- case used of
                 Seq.Empty -> do  -- Variable used for the first time, mark the use, and continue
                   traceTc "gen" (text "variable" <+> pretty n <+> text "used for the first time" <> semi
                            L.<$> text "generate constraint" <+> prettyC c)
                   return Sat
                 us -> do  -- Variable already used before, emit a Share constraint.
                   traceTc "gen" (text "variable" <+> pretty n <+> text "used before" <> semi
                            L.<$> text "generate constraint" <+> prettyC (t' :< t) <+> text "and share constraint")
                   return (Share t' $ Reused n p us)
      return (c <> share, e)

cg' (Upcast e) t = do
  alpha <- freshTVar
  (c1, e1') <- cg e alpha
  let c = integral alpha <> Upcastable alpha t
  traceTc "gen" (text "upcast expression" <+> pretty e <> semi L.<$>
                 text "generate constraint" <+> prettyC c)
  return (c <> c1, Upcast e1')

cg' (BoolLit b) t = do
#ifdef REFINEMENT_TYPES
  c <- if ?isRefType then
         do v <- freshRefVarName freshVars
            let pred = if b then SE (T bool) (Var v)
                            else SE (T bool) (PrimOp "not" [SE (T bool) (Var v)])
            return $ T (TRefine v (T bool) pred) :< t
       else return (T bool :< t)
#else
  let c = T bool :< t
#endif
  let e = BoolLit b
  return (c,e)

cg' (CharLit l) t = do
  let c = T u8 :< t
      e = CharLit l
  return (c,e)

cg' (StringLit l) t = do
  let c = T (TCon "String" [] Unboxed) :< t
      e = StringLit l
  return (c,e)

cg' Unitel t = do
  let c = T TUnit :< t
      e = Unitel
  return (c,e)

cg' (IntLit i) t = do
  let minimumBitwidth | i < u8MAX      = "U8"
                      | i < u16MAX     = "U16"
                      | i < u32MAX     = "U32"
                      | otherwise      = "U64"
      e = IntLit i
#ifdef REFINEMENT_TYPES
  c <- if ?isRefType then
         do beta <- freshTVar
            v <- freshRefVarName freshVars
            let c = T (TRefine v beta (SE (T bool) (PrimOp "==" [SE beta (Var v), SE beta e]))) :< t <>
                    Upcastable (T (TCon minimumBitwidth [] Unboxed)) beta <>
                    BaseType beta
            return c
       else return $ Upcastable (T (TCon minimumBitwidth [] Unboxed)) t
#else
      c = Upcastable (T (TCon minimumBitwidth [] Unboxed)) t
#endif
  traceTc "gen" (text "cg for int literal" <+> integer i L.<$>
                 text "generate constraint" <+> prettyC c)
  return (c,e)

#ifdef REFINEMENT_TYPES
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
  idx <- freshEVar (T u32)  -- index of a potential hole
  h <- freshVar             -- hole
  v <- freshRefVarName freshVars
  let -- NOTE: for now, we just assume that there cannot be a hole, to simplify the constraint solving. / zilinc
      -- XXX | ta = A alpha n (Right s) (Left $ Just idx)  -- this is the biggest type 'e' can ever have---with a hole
      -- XXX |                                             -- at a location other than 'i'
      ta = A alpha n (Right s) (Left Nothing)
      ta' = A alpha n (Right s) (Right h)
      idxInBounds = -- XXX | SE (T bool) (PrimOp "&&"
                    -- XXX |   [ SE (T bool) (PrimOp "<"  [SE (T u32) (Var v), n  ])
                    -- XXX |   , SE (T bool) (PrimOp "/=" [SE (T u32) (Var v), idx])
                    -- XXX |   ])
                    SE (T bool) (PrimOp "<" [SE (T u32) (Var v), n])
  (ce, e') <- cg e ta'
  (ci, i') <- cg i (T $ TRefine v (T u32) idxInBounds)
  let c = alpha :< t
        <> ta' :< ta
        <> Share ta UsedInArrayIndexing
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
  (s1,prds1,cp1,p1') <- match p1 Nothing alpha1  -- FIXME: mv
  (s2,prds2,cp2,p2') <- match p2 Nothing alpha2  -- FIXME: mv
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
  (s, prds, cp, pat') <- match pat Nothing alpha'  -- FIXME: mv
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
#ifdef REFINEMENT_TYPES
      c = ct <> cp <> ((fmap (\(t,_,o) -> (t, Seq.length o)) s, prds) :|- ce)
#else
      c = ct <> cp <> ce
#endif
             <> (T $ TFun Nothing alpha beta) :< t
             <> dropConstraintFor rs <> unused
      lam = Lam  pat' (fmap (const alpha) mt) e'
  unless (null fvs') $ __todo "closures not implemented"
  unless (null fvs') $ context .= ctx
  traceTc "gen" (text "lambda expression" <+> prettyE lam
           L.<$> text "generate constraint" <+> prettyC c <> semi)
  return (c,lam)

cg' (App e1 e2 _) t = do
  alpha     <- freshTVar
  v         <- freshRefVarName freshVars
  (c1, e1') <- cg e1 (T (TFun (Just v) alpha t))
  (c2, e2') <- cg e2 alpha

  let c = c1 <> c2
      e = App e1' e2' False
  traceTc "gen" (text "cg for funapp:" <+> prettyE e)
  return (c,e)

cg' (Comp f g) t = do
  alpha1 <- freshTVar
  alpha2 <- freshTVar
  alpha3 <- freshTVar
  v <- freshRefVarName freshVars

  (c1, f') <- cg f (T (TFun (Just v) alpha2 alpha3))
  (c2, g') <- cg g (T (TFun (Just v) alpha1 alpha2))
  let e = Comp f' g'
      c = c1 <> c2 <> (T $ TFun (Just v) alpha1 alpha3) :< t
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
          matchL ((v,t):t'') (Just l:l') = do
            (c, ps) <- matchL t'' l'
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
#ifdef REFINEMENT_TYPES
      (c2',c3') = if arithTCExpr e1' then
        let c2' = (M.empty, [toTCSExpr e1']) :|- c2
            c3' = (M.empty, [SE (T bool) (PrimOp "not" [toTCSExpr e1'])]) :|- c3
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
#ifdef REFINEMENT_TYPES
      conds'' = fmap toTCSExpr conds'
      poss = scanl1 (\conj c -> andTCSExprs [conj,c]) conds''
      condes = zipWith (\pos c -> andTCSExprs [SE (T bool) (PrimOp "not" [pos]), c]) poss conds''
      condel = SE (T bool) (PrimOp "not" [andTCSExprs conds''])
      c' = c <> mconcat cconds <>
           mconcat (zipWith (\cc ce -> (M.empty,[cc]) :|- ce) condes ces) <>
           ((M.empty,[condel]) :|- cel)
#else
      c' = c <> mconcat cconds <> mconcat ces <> cel
#endif
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
  (c'', alts') <- cgAlts alts t Nothing alpha  -- FIXME: mv

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

matchA :: (?isRefType :: Bool)
       => LocPatn
       -> Maybe VarName
       -> TCType
       -> CG (M.Map VarName (C.Assumption TCType), [TCSExpr], Constraint, TCPatn, TCType)
matchA x@(LocPatn l p) mv t = do
  let ?loc = l
  let me = mv <&> SE t . Var
  (s,prds,c,p',t') <- matchA' p me t
  return (s, prds, c :@ InPattern x, TP p' l, t')

matchA' :: (?loc :: SourcePos, ?isRefType :: Bool)
        => Pattern LocIrrefPatn
        -> Maybe TCSExpr
        -> TCType
        -> CG (M.Map VarName (C.Assumption TCType), [TCSExpr], Constraint, Pattern TCIrrefPatn, TCType)

matchA' (PIrrefutable i) me t = do
  (s, prds, c, i') <- match i me t
  return (s, prds, c, PIrrefutable i', t)

matchA' (PCon k [i]) me t = do
  beta <- freshTVar
  (s, prds, c, i') <- match i Nothing beta
  U rest <- freshTVar
  let row = Row.incomplete [Row.mkEntry k beta False] rest
      c' = t :< V row
      row' = Row.incomplete [Row.mkEntry k beta True] rest

  traceTc "gen" (text "match constructor pattern:" <+> pretty (PCon k [i'])
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (s, prds, c <> c', PCon k [i'], V row')

matchA' (PCon k []) me t = matchA' (PCon k [LocIrrefPatn ?loc PUnitel]) Nothing t
matchA' (PCon k is) me t = matchA' (PCon k [LocIrrefPatn ?loc (PTuple is)]) Nothing t

matchA' (PIntLit i) me t = do
  let minimumBitwidth | i < u8MAX      = "U8"
                      | i < u16MAX     = "U16"
                      | i < u32MAX     = "U32"
                      | otherwise      = "U64"
      c = Upcastable (T (TCon minimumBitwidth [] Unboxed)) t
      -- ^^^ FIXME: I think if we restrict this constraint, then we can possibly get rid of `Upcast' / zilinc
  return (M.empty, [], c, PIntLit i, t)

matchA' (PBoolLit b) me t =
  return (M.empty, [], t :< T bool, PBoolLit b, t)

matchA' (PCharLit c) me t =
  return (M.empty, [], t :< T u8, PCharLit c, t)

match :: (?isRefType :: Bool)
      => LocIrrefPatn
      -> Maybe TCSExpr
      -> TCType
      -> CG (M.Map VarName (C.Assumption TCType), [TCSExpr], Constraint, TCIrrefPatn)
match x@(LocIrrefPatn l ip) me t = do
  let ?loc = l
  (s,prds,c,ip') <- match' ip me t
  return (s, prds, c :@ InIrrefutablePattern x, TIP ip' l)

match' :: (?loc :: SourcePos, ?isRefType :: Bool)
       => IrrefutablePattern VarName LocIrrefPatn LocExpr
       -> Maybe TCSExpr
       -> TCType
       -> CG (M.Map VarName (C.Assumption TCType), [TCSExpr], Constraint, IrrefutablePattern TCName TCIrrefPatn TCExpr)

match' (PVar x) me t = do
  let p = PVar (x,t)
      prds = case me of Just e  -> [SE (T bool) (PrimOp "==" [SE t (Var x), e])]
                        Nothing -> []
  traceTc "gen" (text "match var pattern:" <+> prettyIP p
           L.<$> text "of type" <+> pretty t)
  return (M.fromList [(x, (t,?loc,Seq.empty))], prds, Sat, p)

match' (PUnderscore) me t =
  let c = dropConstraintFor (M.singleton "_" (t, ?loc, Seq.empty))
   in return (M.empty, [], c, PUnderscore)

match' (PUnitel) me t = return (M.empty, [], t :< T TUnit, PUnitel)

match' (PTuple ps) me t = do
  (vs, blob) <- unzip <$> mapM (\p -> do v <- freshTVar; (v,) <$> match p Nothing v) ps
  let (ss, prdss, cs, ps') = unzip4 blob
      p' = PTuple ps'
      co = case overlapping ss of
             Left (v:_) -> Unsat $ DuplicateVariableInPattern v  -- p'
             _          -> Sat
      c = t :< T (TTuple vs)
  traceTc "gen" (text "match tuple pattern:" <+> prettyIP p'
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (M.unions ss, [], co <> mconcat cs <> c, p')

match' (PUnboxedRecord fs) me t | not (any isNothing fs) = do
  let (ns, ps) = unzip (catMaybes fs)
  (vs, blob) <- unzip <$> mapM (\p -> do v <- freshTVar; (v,) <$> match p Nothing v) ps
  U rest <- freshTVar
  let (ss, prdss, cs, ps') = unzip4 blob
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
  return (M.unions ss, concat prdss, co <> mconcat cs <> c <> d, p')
  | otherwise = over _3 (:& Unsat RecordWildcardsNotSupported) <$>
                  match' (PUnboxedRecord (filter isJust fs)) Nothing t

match' (PTake r fs) me t | not (any isNothing fs) = do
  let (ns, ps) = unzip (catMaybes fs)
  (vs, blob) <- unzip <$> mapM (\p -> do v <- freshTVar; (v,) <$> match p Nothing v) ps
  U rest <- freshTVar
  U sigil <- freshTVar
  rp <- freshRPVar
  let (ss, prdss, cs, ps') = unzip4 blob
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
  return (M.unions (s:ss), concat prdss, co <> mconcat cs <> c, p')
  | otherwise = over _3 (:& Unsat RecordWildcardsNotSupported) <$>
                  match' (PTake r (filter isJust fs)) Nothing t

#ifdef REFINEMENT_TYPES
match' (PArray ps) me t = do
  alpha <- freshTVar  -- element type
  blob  <- mapM (\p -> match p Nothing alpha) ps
  let (ss,prdss,cs,ps') = unzip4 blob
      l = SE (T u32) (IntLit . fromIntegral $ length ps) :: TCSExpr -- length of the array
      c = t :< (A alpha l (Left Unboxed) (Left Nothing))
  traceTc "gen" (text "match on array literal pattern" L.<$>
                 text "element type is" <+> pretty alpha L.<$>
                 text "length is" <+> pretty l L.<$>
                 text "generate constraint" <+> prettyC c)
  return (M.unions ss, concat prdss, mconcat cs <> c, PArray ps')

match' (PArrayTake arr [(idx,p)]) me t = do
  alpha <- freshTVar  -- array elmt type
  len   <- freshEVar (T u32)  -- array length
  sigil <- freshVar   -- sigil
  (cidx,idx') <- cg idx $ T u32
  (sp,prds,cp,p') <- match p Nothing alpha
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
  return (s `M.union` sp, prds, cp `mappend` mconcat c, PArrayTake (arr, tarr) [(idx',p')])

match' (PArrayTake arr _) me t = __todo "match': taking multiple elements from array is not supported"
#endif

-- -----------------------------------------------------------------------------
-- Auxiliaries
-- -----------------------------------------------------------------------------


freshVar :: (?loc :: SourcePos) => CG Int
freshVar = fresh (ExpressionAt ?loc)
  where
    fresh :: VarOrigin -> CG Int
    fresh ctx = do
      i <- flexes <<%= succ
      flexOrigins %= IM.insert i ctx
      return i

freshTVar :: (?loc :: SourcePos) => CG TCType
freshTVar = U <$> freshVar

freshEVar :: (?loc :: SourcePos) => TCType -> CG TCSExpr
freshEVar t = SU t <$> freshVar

freshHVar :: (?loc :: SourcePos) => VarName -> [VarName] -> CG TCSExpr
freshHVar v vs = HApp <$> freshVar <*> pure v <*> pure vs


freshLVar :: (?loc :: SourcePos) => CG TCDataLayout
freshLVar = TLU <$> freshVar

freshRPVar :: (?loc :: SourcePos) => CG RP
freshRPVar = UP <$> freshVar

freshEName :: (?loc :: SourcePos) => CG VarName
freshEName = freshVar >>= \i -> return ("_x" ++ show i)

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



withBindings :: (?loc::SourcePos, ?isRefType :: Bool)
  => [Binding LocType LocPatn LocIrrefPatn LocExpr]
  -> LocExpr -- expression e to be checked with the bindings
  -> TCType  -- the type for e
  -> CG (Constraint, [Binding TCType TCPatn TCIrrefPatn TCExpr], TCExpr)
withBindings [] e top = do
  (c, e') <- cg e top
  return (c, [], e')
withBindings (Binding pat mτ e0 bs : xs) e top = do
  α <- freshTVar
  v <- freshRefVarName freshVars
  (c0, e0') <- letBang bs (cg e0) α
  (ct, α') <- case mτ of
    Nothing -> return (Sat, α)
    Just τ  -> do (cτ,τ') <- validateType (stripLocT τ)
                  return (cτ <> α :< τ', τ')
  (s, prds, cp, pat') <- match pat (Just $ SE α (Var v)) α'
  context %= C.addScope s
  (c', xs', e') <- withBindings xs e top
  rs <- context %%= C.dropScope
  let unused = flip foldMap (M.toList rs) $ \(v,(_,_,us)) ->
        case us of
          Seq.Empty -> warnToConstraint __cogent_wunused_local_binds (UnusedLocalBind v)
          _ -> Sat
#ifdef REFINEMENT_TYPES
      c'' = ( M.insert v (α,0) $ fmap (\(t,_,occ) -> (t, Seq.length occ)) s
            , (SE (T bool) (PrimOp "==" [SE α (Var v), toTCSExpr e0'])) : prds
            ) :|- c'
#else
      c'' = c'
#endif
      c = ct <> c0 <> c'' <> cp <> dropConstraintFor rs <> unused
      b' = Binding pat' (fmap (const α) mτ) e0' bs
  traceTc "gen" (text "bound expression" <+> pretty e0' <+>
                 text "with banged" <+> pretty bs
           L.<$> text "of type" <+> pretty α <> semi
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
  (calts, alts') <- cgAlts (Alt pat Regular (LocExpr (posOfE e) (Let xs e)) : alts) top Nothing alpha'  -- FIXME: mv
  let c = c0 <> ct <> calts
      (Alt pat' _ (TE _ (Let xs' e') _)) : altss' = alts'
      b0' = BindingAlts pat' (fmap (const alpha) tau) e0' bs altss'
  return (c, b0':xs', e')

letBang :: (?loc :: SourcePos)
        => [VarName]
        -> (TCType -> CG (Constraint, TCExpr))
        -> TCType
        -> CG (Constraint, TCExpr)
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

-- FIXME: Now we have a context in constraints, do we still need to
-- generate this constraint? / zilinc
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

prettyC :: Constraint -> Doc
prettyC = PP.prettyC

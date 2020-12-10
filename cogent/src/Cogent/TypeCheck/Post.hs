--
-- Copyright 2017, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

module Cogent.TypeCheck.Post (
  postA, postE, postT
) where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Dargent.TypeCheck
import Cogent.PrettyPrint
import Cogent.Surface
import Cogent.TypeCheck.ARow as ARow
import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Util
import qualified Cogent.TypeCheck.Row as Row
import Cogent.Util

import Control.Arrow (first)
import Control.Monad
import Data.Bifunctor
import Data.Word (Word32)
-- import Control.Monad.Except
-- import Control.Monad.Writer hiding (Alt)
import Control.Monad.Trans.Class
import qualified Data.IntMap as IM
import qualified Data.Map as M
import Lens.Micro
import Lens.Micro.Mtl
import Text.PrettyPrint.ANSI.Leijen as P hiding ((<>), (<$>), bool)

-- import Debug.Trace

-- NOTE: this normalisation process largely comes down to normalise types
-- and adding error contexts.


type Post a = TcM a

postT :: TCType -> Post DepType
postT t = do
  d <- lift . lift $ use knownTypes
  traceTc "post" (text "type" <+> pretty t)
  toDepType <$> normaliseT d t

postE :: TCExpr -> Post TypedExpr
postE e = do
  d <- lift . lift $ use knownTypes
  traceTc "post" (text "expression" <+> pretty e)
  toTypedExpr <$> normaliseE d e

postA :: [Alt TCPatn TCExpr] -> Post [Alt TypedPatn TypedExpr]
postA as = do
  d <- lift . lift $ use knownTypes
  traceTc "post" (text "alternative" <+> pretty as)
  toTypedAlts <$> normaliseA d as


normaliseA :: TypeDict -> [Alt TCPatn TCExpr] -> Post [Alt TCPatn TCExpr]
normaliseA d as = traverse (traverse (normaliseE d) >=> ttraverse (normaliseP d)) as

normaliseE :: TypeDict -> TCExpr -> Post TCExpr
normaliseE d te@(TE t e l) = do
  lift $ errCtx %= (ctx:)
  e' <- normaliseE' d e
  t' <- normaliseT  d t
  return $ TE t' e' l
  where
    ctx = InExpression (toLocExpr toLocType te) t
    normaliseE' :: TypeDict
                -> Expr TCType TCPatn TCIrrefPatn TCDataLayout TCExpr
                -> Post (Expr TCType TCPatn TCIrrefPatn TCDataLayout TCExpr)
    normaliseE' d =   traverse (normaliseE d)
                  >=> ttraverse normaliseL
                  >=> tttraverse (normaliseIP d)
                  >=> ttttraverse (normaliseP d)
                  >=> tttttraverse (normaliseT d)

normaliseSE :: TypeDict -> TCSExpr -> Post TCSExpr
normaliseSE d e = toTCSExpr <$> normaliseE d (toTCExpr e)

normaliseL :: TCDataLayout -> Post TCDataLayout
normaliseL l = do
  layouts <- lift . lift $ use knownDataLayouts
  return $ normaliseTCDataLayout layouts l

normaliseP :: TypeDict -> TCPatn -> Post TCPatn
normaliseP d tp@(TP p l) = do
  lift $ errCtx %= (ctx:)
  TP <$> normaliseP' d p <*> pure l
  where ctx = InPattern (toLocPatn toLocType tp)
        normaliseP' :: TypeDict -> Pattern TCIrrefPatn -> Post (Pattern TCIrrefPatn)
        normaliseP' d = traverse (normaliseIP d)

normaliseIP :: TypeDict -> TCIrrefPatn -> Post TCIrrefPatn
normaliseIP d tip@(TIP ip l) = do
  lift $ errCtx %= (ctx:)
  TIP <$> normaliseIP' d ip <*> pure l
  where ctx = InIrrefutablePattern (toLocIrrefPatn toLocType tip)
        normaliseIP' :: TypeDict
                     -> IrrefutablePattern TCName TCIrrefPatn TCExpr
                     -> Post (IrrefutablePattern TCName TCIrrefPatn TCExpr)
        normaliseIP' d = traverse (normaliseE d) >=> ttraverse (normaliseIP d) >=> tttraverse (secondM (normaliseT d))

-- postcondition: only types should remain in the TCType after running (aka 'T' constructors)
normaliseT :: TypeDict -> TCType -> Post TCType
normaliseT d (T (TUnbox t)) = do
   t' <- normaliseT d t
   case t' of
     (T (TCon x ps _))    -> normaliseT d (T (TCon x ps Unboxed))
     (T (TVar v b u))     -> normaliseT d (T (TVar v b True))
     -- Cannot have an unboxed record with a recursive parameter
     (T (TRecord NonRec l _)) -> normaliseT d (T (TRecord NonRec l Unboxed))
#ifdef REFINEMENT_TYPES
     (T (TArray t e _ h)) -> normaliseT d (T (TArray t e Unboxed h))
#endif
     (T o)                -> normaliseT d =<< normaliseT d (T $ fmap (T . TUnbox) o)
     _                    -> __impossible "normaliseT (TUnbox)"

normaliseT d (T (TBang t)) = do
   t' <- normaliseT d t
   case t' of
     (T (TCon x ps s)) -> mapM (normaliseT d . T . TBang) ps >>= \ps' ->
                          normaliseT d (T (TCon x ps' (bangSigil s)))
     (T (TRecord rp l s)) -> mapM ((secondM . firstM) (normaliseT d . T . TBang)) l >>= \l' ->
                             normaliseT d (T (TRecord rp l' (bangSigil s)))
#ifdef REFINEMENT_TYPES
     (T (TArray t e (Boxed False l) h)) -> do
       t' <- normaliseT d $ T $ TBang t
       normaliseT d (T (TArray t' e (Boxed True l) h))
#endif
     (T (TVar v b u))  -> normaliseT d (T (TVar v True u))
     (T (TFun mv a b)) -> T <$> (TFun mv <$> normaliseT d a <*> normaliseT d b)
     (T o)             -> normaliseT d =<< normaliseT d (T $ fmap (T . TBang) o)
     _                 -> __impossible "normaliseT (TBang)"

normaliseT d (T (TTake fs t)) = do
   t' <- normaliseT d t
   case t' of
     (T (TRecord rp l s)) -> takeFields fs l t >>= \r -> normaliseT d (T (TRecord rp r s))
     (T (TVariant ts)) -> takeFields fs (M.toList ts) t' >>= \r -> normaliseT d (T (TVariant (M.fromList r)))
     _                 -> if __cogent_flax_take_put then return t
                                                    else logErrExit (TakeFromNonRecordOrVariant fs t)
 where
   takeFields :: Maybe [FieldName] -> [(FieldName, (a, Bool))] -> TCType -> Post [(FieldName, (a, Bool))]
   takeFields Nothing   fs' _  = return $ map (fmap (fmap (const True))) fs'
   takeFields (Just fs) fs' t' = do
     forM_ fs $ \f -> when (f `notElem` map fst fs') $ logErrExit (TakeNonExistingField f t')
     forM fs' $ \(f,(t,b)) -> do when (f `elem` fs && b && __cogent_wdodgy_take_put) $ logWarn (TakeTakenField f t')
                                 return (f, (t, f `elem` fs || b))

normaliseT d (T (TPut fs t)) = do
   t' <- normaliseT d t
   case t' of
     (T (TRecord rp l s)) -> putFields fs l t >>= \r -> normaliseT d (T (TRecord rp r s))
     (T (TVariant ts)) -> putFields fs (M.toList ts) t' >>= \r -> normaliseT d (T (TVariant (M.fromList r)))
     _                 -> if __cogent_flax_take_put then return t'
                                                    else logErrExit (PutToNonRecordOrVariant fs t)
 where
   putFields :: Maybe [FieldName] -> [(FieldName, (a, Bool))] -> TCType -> Post [(FieldName, (a, Bool))]
   putFields Nothing   fs' _  = return $ map (fmap (fmap (const False))) fs'
   putFields (Just fs) fs' t' = do
     forM_ fs $ \f -> when (f `notElem` map fst fs') $ logErrExit (PutNonExistingField f t')
     forM fs' $ \(f,(t,b)) -> do when (f `elem` fs && not b && __cogent_wdodgy_take_put) $ logWarn (PutUntakenField f t')
                                 return (f, (t,  (f `notElem` fs) && b))

#ifdef REFINEMENT_TYPES
-- TODO: we also need to check that the taken indices are in bounds / zilinc
normaliseT d (T (TATake is t)) = do
  t' <- normaliseT d t
  case t' of
    (T (TArray elt l s [])) -> normaliseT d (T (TArray elt l s $ map (,True) is))
    (T (TArray _ _ _ _)) -> __impossible "normaliseT: TArray can have at most one taken element"
    _ -> logErrExit (TakeElementsFromNonArrayType is t')

normaliseT d (T (TAPut is t)) = do
  -- FIXME: dodgy implementation / zilinc
  t' <- normaliseT d t
  case t' of
    (T (TArray elt l s [])) -> normaliseT d t'  -- no hole. no-op.
    (T (TArray elt l s [(h, True)])) ->  -- one hole
      normaliseT d (T (TArray elt l s []))  -- becomes no hole
    (T (TArray _ _ _ _)) -> __impossible "normaliseT: TArray can have at most one taken element"
    _ -> logErrExit (PutElementsToNonArrayType is t')
#endif

normaliseT d (T (TLayout l t)) = do
  t' <- normaliseT d t
  env <- lift . lift $ use knownDataLayouts
  case t' of
    (T (TRecord rp fs (Boxed p Nothing))) -> do
      let normPartT = normaliseT d . T . TRecord rp fs
      t'' <- normPartT Unboxed
      if isTypeLayoutExprCompatible env t'' l
        then normPartT . Boxed p $ Just l
        else logErrExit (LayoutDoesNotMatchType l t)
    (T (TCon n ts (Boxed p Nothing)))  -> do
      let normPartT = normaliseT d . T . TCon n ts
      t'' <- normPartT Unboxed
      if isTypeLayoutExprCompatible env t'' l
        then normPartT . Boxed p $ Just l
        else logErrExit (LayoutDoesNotMatchType l t)
#ifdef REFINEMENT_TYPES
    (T (TArray telt n (Boxed p Nothing) tkns)) -> do
      let normPartT s = normaliseT d . T $ TArray telt n s tkns
      t'' <- normPartT Unboxed
      if isTypeLayoutExprCompatible env t'' l
        then normPartT . Boxed p $ Just l
        else logErrExit (LayoutDoesNotMatchType l t)
#endif
    _ -> logErrExit (LayoutOnNonRecordOrCon t)

normaliseT d (T (TCon n ts b)) =
  case lookup n d of
    -- In the first case, the sigil `s` should be `Nothing`
    -- because 
    Just (ts', Just b) -> normaliseT d (substType (zip ts' ts) b)
    _ -> do
      ts' <- mapM (normaliseT d) ts
      return $ T (TCon n ts' b)

normaliseT d (T (TRecord rp l s)) = do
  s' <- normaliseS s
  l' <- mapM ((secondM . firstM) (normaliseT d)) l
  return (T (TRecord rp l' s'))

#ifdef REFINEMENT_TYPES
normaliseT d (T (TArray t n s tkns)) = do
  t' <- normaliseT d t
  s' <- normaliseS   s
  return $ T $ TArray t' n s' tkns

normaliseT d (T (TRefine v b p)) = do
  if p == SE (T bool) (BoolLit True) then
     normaliseT d b
  else do
    b' <- normaliseT d b
    p' <- normaliseSE d p
    return $ T (TRefine v b' p')
#endif

normaliseT d (Synonym n ts) = 
  case lookup n d of
    Just (ts', Just b) -> normaliseT d (substType (zip ts' ts) b)
    _ -> __impossible ("normaliseT: unresolved synonym " ++ show n)
normaliseT d (V x) =
  T . TVariant . M.fromList .
  map (\e -> (Row.fname e, ([Row.payload e], Row.taken e))) .
  Row.entries <$> traverse (normaliseT d) x
normaliseT d (R rp x (Left s)) = do
  x' <- map (\e -> (Row.fname e, (Row.payload e, Row.taken e))) . Row.entries <$> traverse (normaliseT d) x
  s' <- normaliseS s
  return $ T $ TRecord (unCoerceRP rp) x' s'
normaliseT d (R _ x (Right s)) =  __impossible ("normaliseT: invalid sigil (?" ++ show s ++ ")")
#ifdef REFINEMENT_TYPES
normaliseT d (A t n (Left s) (Left mhole)) = do
  t' <- normaliseT d t
  s' <- normaliseS s
  let tkns = case mhole of Nothing -> []; Just idx -> [(idx,True)]
  return $ T $ TArray t' n s' tkns
normaliseT d (A t n (Right s) mhole) = __impossible ("normaliseT: invalid sigil (?" ++ show s ++ ")")
normaliseT d (A t n s (Right h)) = __impossible ("normaliseT: invalid hole (?" ++ show h ++ ")")
#endif
normaliseT d (U x) = __impossible ("normaliseT: invalid type (?" ++ show x ++ ")")
normaliseT d (T x) = T <$> traverse (normaliseT d) x

tkNorm :: Either Taken Int -> Taken
tkNorm (Left tk) = tk
tkNorm (Right _) = __impossible "normaliseT: taken variable unsolved at normisation"

-- Normalises the layouts in sigils to remove `DataLayoutRefs`
normaliseS :: Sigil (Maybe TCDataLayout) -> Post (Sigil (Maybe TCDataLayout))
normaliseS sigil = do
  layouts <- lift . lift $ use knownDataLayouts
  return $ normaliseSigil layouts sigil


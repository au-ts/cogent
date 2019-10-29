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
import Cogent.Dargent.TypeCheck (normaliseSigil)
import Cogent.PrettyPrint ()
import Cogent.Surface
import Cogent.TypeCheck.ARow as ARow
import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Util
import qualified Cogent.TypeCheck.Row as Row
import Cogent.Util

import Control.Arrow (first)
import Control.Monad
import Data.Word (Word32)
-- import Control.Monad.Except
-- import Control.Monad.Writer hiding (Alt)
import Control.Monad.Trans.Class
import qualified Data.IntMap as IM
import qualified Data.Map as M
import Lens.Micro
import Lens.Micro.Mtl
import Text.PrettyPrint.ANSI.Leijen as P hiding ((<>), (<$>))

-- import Debug.Trace

-- NOTE: this normalisation process largely comes down to normalise types
-- and adding error contexts.


type Post a = TcM a

postT :: TCType -> Post RawType
postT t = do
  d <- lift . lift $ use knownTypes
  traceTc "post" (text "type" <+> pretty t)
  toRawType <$> normaliseT d t

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
                -> Expr TCType TCPatn TCIrrefPatn TCExpr
                -> Post (Expr TCType TCPatn TCIrrefPatn TCExpr)
    normaliseE' d =   traverse (normaliseE d)
                  >=> ttraverse (normaliseIP d)
                  >=> tttraverse (normaliseP d)
                  >=> ttttraverse (normaliseT d)

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
        normaliseIP' :: TypeDict -> IrrefutablePattern TCName TCIrrefPatn -> Post (IrrefutablePattern TCName TCIrrefPatn)
        normaliseIP' d = traverse (normaliseIP d) >=> ttraverse (secondM (normaliseT d))

normaliseT :: TypeDict -> TCType -> Post TCType
normaliseT d (T (TUnbox t)) = do
   t' <- normaliseT d t
   case t' of
     (T (TCon x ps _)) -> normaliseT d (T (TCon x ps Unboxed))
     (T (TRecord l _)) -> normaliseT d (T (TRecord l Unboxed))
     (T o)             -> normaliseT d =<< normaliseT d (T $ fmap (T . TUnbox) o)
     _                 -> __impossible "normaliseT (TUnbox)"

normaliseT d (T (TBang t)) = do
   t' <- normaliseT d t
   case t' of
     (T (TCon x ps s)) -> mapM (normaliseT d . T . TBang) ps >>= \ps' ->
                          normaliseT d (T (TCon x ps' (bangSigil s)))
     (T (TRecord l s)) -> mapM ((secondM . firstM) (normaliseT d . T . TBang)) l >>= \l' ->
                          normaliseT d (T (TRecord l' (bangSigil s)))
     (T (TVar b _))    -> normaliseT d (T (TVar b True))
     (T (TFun a b))    -> T <$> (TFun <$> normaliseT d a <*> normaliseT d b)
     (T o)             -> normaliseT d =<< normaliseT d (T $ fmap (T . TBang) o)
     _                 -> __impossible "normaliseT (TBang)"

normaliseT d (T (TTake fs t)) = do
   t' <- normaliseT d t
   case t' of
     (T (TRecord l s)) -> takeFields fs l t >>= \r -> normaliseT d (T (TRecord r s))
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
     (T (TRecord l s)) -> putFields fs l t >>= \r -> normaliseT d (T (TRecord r s))
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

#ifdef BUILTIN_ARRAYS
normaliseT d (T (TATake is t)) = do
  t' <- normaliseT d t
  case t' of
    (T (TArray elt l s tkns)) ->
      -- PRECONDITION: @tkns@ should contain entries for all the elements
      let tkns' = map (first $ SE . IntLit . fromIntegral) . IM.toList . takeEntries is . IM.fromList $ map (first evalSExpr) tkns
       in normaliseT d (T (TArray elt l s tkns'))
    _ -> logErrExit (TakeElementsFromNonArrayType is t')
  where
    takeEntries :: [SExpr] -> IM.IntMap Taken -> IM.IntMap Taken
    takeEntries [] tkns = tkns
    takeEntries (i:is) tkns = let i' = evalSExpr i
                                  tkns' = case IM.lookup i' tkns of
                                            Nothing -> __impossible "takeEntries: no entry found"
                                            Just False -> IM.adjust (const True) i' tkns
                                            Just True  -> __impossible "takeEntries: take taken. Will be a warning"
                               in takeEntries is tkns'

normaliseT d (T (TAPut is t)) = do
  t' <- normaliseT d t
  case t' of
    (T (TArray elt l s tkns)) ->
      -- PRECONDITION: @tkns@ should contain entries for all the elements
      let tkns' = map (first $ SE . IntLit . fromIntegral) . IM.toList . putEntries is . IM.fromList $ map (first evalSExpr) tkns
       in normaliseT d (T (TArray elt l s tkns'))
    _ -> logErrExit (PutElementsToNonArrayType is t')
  where
    putEntries :: [SExpr] -> IM.IntMap Taken -> IM.IntMap Taken
    putEntries [] tkns = tkns
    putEntries (i:is) tkns = let i' = evalSExpr i
                                 tkns' = case IM.lookup i' tkns of
                                           Nothing -> __impossible "takeEntries: no entry found"
                                           Just True  -> IM.adjust (const False) i' tkns
                                           Just False -> __impossible "takeEntries: put untaken. Will be a warning"
                              in putEntries is tkns'
#endif

normaliseT d (T (TLayout l t)) = do
  t' <- normaliseT d t
  env <- lift . lift $ use knownDataLayouts
  case t' of
    (T (TRecord fs (Boxed p Nothing))) -> do
      let normPartT = normaliseT d . T . TRecord fs
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
#ifdef BUILTIN_ARRAYS
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

normaliseT d (T (TRecord l s)) = do
  s' <- normaliseS s
  l' <- mapM ((secondM . firstM) (normaliseT d)) l
  return (T (TRecord l' s'))

#ifdef BUILTIN_ARRAYS
normaliseT d (T (TArray t n s tkns)) = do
  t' <- normaliseT d t
  s' <- normaliseS   s
  -- n' <- normaliseE d n
  return $ T $ TArray t' n s' tkns
#endif

normaliseT d (Synonym n ts) = 
  case lookup n d of
    Just (ts', Just b) -> normaliseT d (substType (zip ts' ts) b)
    _ -> __impossible ("normaliseT: unresolved synonym " ++ show n)

normaliseT d (V x) = T . TVariant . M.fromList . Row.toEntryList . fmap (:[]) <$> traverse (normaliseT d) x
normaliseT d (R x (Left s)) = T . flip TRecord s . Row.toEntryList <$> traverse (normaliseT d) x
normaliseT d (R x (Right s)) =  __impossible ("normaliseT: invalid sigil (?" ++ show s ++ ")")
#ifdef BUILTIN_ARRAYS
normaliseT d (A t n (Left s) mhole) = do
  t' <- normaliseT d t
  s' <- normaliseS s
  let tkns = case mhole of Nothing -> []; Just idx -> [(idx,True)]
  return $ T $ TArray t' n s' tkns
normaliseT d (A t n (Right s) mhole) = __impossible ("normaliseT: invalid sigil (?" ++ show s ++ ")")
#endif
normaliseT d (U x) = __impossible ("normaliseT: invalid type (?" ++ show x ++ ")")
normaliseT d (T x) = T <$> traverse (normaliseT d) x


evalSExpr :: SExpr -> Int
evalSExpr (SE (IntLit n)) = fromIntegral n
evalSExpr (SE _) = __todo "Post.evalSExpr"

-- Normalises the layouts in sigils to remove `DataLayoutRefs`
normaliseS :: Sigil (Maybe DataLayoutExpr) -> Post (Sigil (Maybe DataLayoutExpr))
normaliseS sigil = do
  layouts <- lift . lift $ use knownDataLayouts
  return $ normaliseSigil layouts sigil


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
import Cogent.PrettyPrint ()
import Cogent.Surface
import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Util
import Cogent.Util

import Cogent.DataLayout.TypeCheck (normaliseSigil)

-- import Control.Arrow (first)
import Control.Monad
import Lens.Micro
import Lens.Micro.Mtl
-- import Control.Monad.Except
-- import Control.Monad.Writer hiding (Alt)
import Control.Monad.Trans.Class
import qualified Data.Map as M
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


normaliseT d (T (TCon n ts s)) = do
  case lookup n d of
    -- In the first case, the sigil `s` should be `Nothing`
    -- because 
    Just (ts', Just b) -> normaliseT d (substType (zip ts' ts) b)
    _ -> do
      ts' <- mapM (normaliseT d) ts
      s'  <- normaliseS s
      return $ T (TCon n ts' s')

normaliseT d (T (TRecord l s)) = do
  s' <- normaliseS s
  l' <- mapM ((secondM . firstM) (normaliseT d)) l
  return (T (TRecord l' s'))

-- normaliseT d (RemoveCase p t) = do
--   t' <- normaliseT d t
--   p' <- traverse (traverse (normaliseT d)) p
--   case removeCase p' t' of
--     Just t'' -> normaliseT d t''
--     Nothing  -> Left (RemoveCaseFromNonVariant p t)

normaliseT d (U x) = __impossible ("normaliseT: invalid type (?" ++ show x ++ ")")
normaliseT d (T x) = T <$> traverse (normaliseT d) x


-- Normalises the layouts in sigils to remove `DataLayoutRefs`
normaliseS :: Sigil (Maybe DataLayoutExpr) -> Post (Sigil (Maybe DataLayoutExpr))
normaliseS sigil = do
  layouts <- lift . lift $ use knownDataLayouts
  return $ normaliseSigil layouts sigil



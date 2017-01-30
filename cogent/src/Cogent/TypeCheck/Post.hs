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

import Control.Arrow (first)
import Control.Monad
import Control.Lens
import Control.Monad.Except
import Control.Monad.Writer hiding (Alt, censor)
import qualified Data.Map as M
import Text.PrettyPrint.ANSI.Leijen as P hiding ((<>), (<$>))

-- import Debug.Trace

type Post a = ExceptT () (WriterT [ContextualisedEW] TC) a

postT :: [ErrorContext] -> TCType -> Post RawType
postT ctx t = do
  d <- use knownTypes
  traceTC "post" (text "type" <+> pretty t)
  censor (map (first $ (++ctx))) (toRawType <$> normaliseT d t)

postE :: [ErrorContext] -> TCExpr -> Post TypedExpr
postE ctx e = do
  d <- use knownTypes
  traceTC "post" (text "expression" <+> pretty e)
  censor (map (first $ (++ctx))) (toTypedExpr <$> normaliseE d e)

postA :: [ErrorContext] -> [Alt TCPatn TCExpr] -> Post [Alt TypedPatn TypedExpr]
postA ctx as = do
  d <- use knownTypes
  traceTC "post" (text "alternative" <+> pretty as)
  censor (map (first $ (++ctx))) (toTypedAlts <$> normaliseA d as)


normaliseA :: TypeDict -> [Alt TCPatn TCExpr] -> Post [Alt TCPatn TCExpr]
normaliseA d as = traverse (traverse (normaliseE d) >=> ttraverse (normaliseP d)) as

normaliseE :: TypeDict -> TCExpr -> Post TCExpr
normaliseE d te@(TE t e l) = do
  e' <- censor (map (first $ (++ctx))) (normaliseE' d e)
  t' <- censor (map (first $ (++ctx))) (normaliseT  d t)
  return $ TE t' e' l
  where
    ctx = InExpression (toLocExpr toLocType te) t :[]
    normaliseE' :: TypeDict
                -> Expr TCType TCPatn TCIrrefPatn TCExpr
                -> Post (Expr TCType TCPatn TCIrrefPatn TCExpr)
    normaliseE' d =   traverse (normaliseE d)
                  >=> ttraverse (normaliseIP d)
                  >=> tttraverse (normaliseP d)
                  >=> ttttraverse (normaliseT d)

normaliseP :: TypeDict -> TCPatn -> Post TCPatn
normaliseP d tp@(TP p l) = TP <$> censor (map (first $ (++ctx))) (normaliseP' d p) <*> pure l
  where ctx = InPattern (toLocPatn toLocType tp) :[]
        normaliseP' :: TypeDict -> Pattern TCIrrefPatn -> Post (Pattern TCIrrefPatn)
        normaliseP' d = traverse (normaliseIP d)

normaliseIP :: TypeDict -> TCIrrefPatn -> Post TCIrrefPatn
normaliseIP d tip@(TIP ip l) = TIP <$> censor (map (first $ (++ctx))) (normaliseIP' d ip) <*> pure l
  where ctx = InIrrefutablePattern (toLocIrrefPatn toLocType tip) :[]
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
     (T o)             -> normaliseT d =<< normaliseT d (T $ fmap (T . TBang) o)
     _                 -> __impossible "normaliseT (TBang)"

normaliseT d (T (TTake fs t)) = do
   t' <- normaliseT d t
   case t' of
     (T (TRecord l s)) -> takeFields fs l t >>= \r -> normaliseT d (T (TRecord r s))
     (T (TVariant ts)) -> takeFields fs (M.toList ts) t' >>= \r -> normaliseT d (T (TVariant (M.fromList r)))
     e                 -> tell (contextualiseE $ TakeFromNonRecordOrVariant fs t) >> throwError ()
 where
   takeFields :: Maybe [FieldName] -> [(FieldName, (a, Bool))] -> TCType -> Post [(FieldName, (a, Bool))]
   takeFields Nothing   fs' _  = return $ map (fmap (fmap (const True))) fs'
   takeFields (Just fs) fs' t' = do 
     forM fs $ \f -> when (f `notElem` map fst fs') $ tell (contextualiseE (TakeNonExistingField f t')) >> throwError ()
     forM fs' $ \(f,(t,b)) -> do when (f `elem` fs && b && __cogent_wdodgy_take_put) $ tell (contextualiseW (TakeTakenField f t'))
                                 return (f, (t, f `elem` fs || b))

normaliseT d (T (TPut fs t)) = do
   t' <- normaliseT d t
   case t' of
     (T (TRecord l s)) -> putFields fs l t >>= \r -> normaliseT d (T (TRecord r s))
     (T (TVariant ts)) -> putFields fs (M.toList ts) t' >>= \r -> normaliseT d (T (TVariant (M.fromList r)))
     e                 -> tell (contextualiseE $ PutToNonRecordOrVariant fs t) >> throwError ()
 where
   putFields :: Maybe [FieldName] -> [(FieldName, (a, Bool))] -> TCType -> Post [(FieldName, (a, Bool))]
   putFields Nothing   fs' _  = return $ map (fmap (fmap (const False))) fs'
   putFields (Just fs) fs' t' = do
     forM fs $ \f -> when (f `notElem` map fst fs') $ tell (contextualiseE (PutNonExistingField f t')) >> throwError ()
     forM fs' $ \(f,(t,b)) -> do when (f `elem` fs && not b && __cogent_wdodgy_take_put) $ tell (contextualiseW (PutUntakenField f t'))
                                 return (f, (t,  (f `notElem` fs) && b))

normaliseT d (T (TCon n ts b)) = do
  case lookup n d of
    Just (ts', Just b) -> normaliseT d (substType (zip ts' ts) b)
    _ -> mapM (normaliseT d) ts >>= \ts' -> return (T (TCon n ts' b))

-- normaliseT d (RemoveCase p t) = do
--   t' <- normaliseT d t
--   p' <- traverse (traverse (normaliseT d)) p
--   case removeCase p' t' of
--     Just t'' -> normaliseT d t''
--     Nothing  -> Left (RemoveCaseFromNonVariant p t)

normaliseT d (U x) = __impossible ("normaliseT: invalid type (?" ++ show x ++ ")")
normaliseT d (T x) = T <$> traverse (normaliseT d) x

contextualiseE :: TypeError -> [ContextualisedEW]
contextualiseE e = [([], Left e)]

contextualiseW :: TypeWarning -> [ContextualisedEW]
contextualiseW w = [([], Right w)]

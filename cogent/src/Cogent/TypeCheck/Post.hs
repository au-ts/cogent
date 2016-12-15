--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE TupleSections #-}

module Cogent.TypeCheck.Post (
  postA, postE, postT
) where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.PrettyPrint ()
import Cogent.Surface
import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Util
import Cogent.Util

import Control.Monad
import Control.Lens
import Control.Monad.Except
import qualified Data.Map as M
import Text.PrettyPrint.ANSI.Leijen as P hiding ((<$>))

postT :: [ErrorContext] -> TCType -> ExceptT [ContextualisedEW] TC RawType
postT ctx t = do
  d <- use knownTypes
  traceTC "post" (text "type" <+> pretty t)
  withExceptT (pure . (ctx,) . Left) $ ExceptT (return $ fmap toRawType $ normaliseT d t)

postE :: [ErrorContext] -> TCExpr -> ExceptT [ContextualisedEW] TC TypedExpr
postE ctx e = do
  d <- use knownTypes
  traceTC "post" (text "expression" <+> pretty e)
  withExceptT pure $ ExceptT (return $ fmap toTypedExpr $ normaliseE d e)

postA :: [ErrorContext] -> [Alt TCPatn TCExpr] -> ExceptT [ContextualisedEW] TC [Alt TypedPatn TypedExpr]
postA ctx as = do
  d <- use knownTypes
  traceTC "post" (text "alternative" <+> pretty as)
  withExceptT pure $ ExceptT (return $ fmap toTypedAlts $ normaliseA d as)


normaliseA :: TypeDict -> [Alt TCPatn TCExpr] -> Either ContextualisedEW [Alt TCPatn TCExpr]
normaliseA d as = traverse (traverse (normaliseE d) >=> ttraverse (normaliseP d)) as

normaliseE :: TypeDict -> TCExpr -> Either ContextualisedEW TCExpr
normaliseE d te@(TE t e l) = case normaliseE' d e of
  Left (es,c) -> Left (ctx:es, c)
  Right e'    -> case normaliseT d t of
    Left  er -> Left  ([ctx], Left er)
    Right t' -> Right (TE t' e' l)
  where
    ctx = InExpression (toLocExpr toLocType te) t
    normaliseE' :: TypeDict
                -> Expr TCType TCPatn TCIrrefPatn TCExpr
                -> Either ContextualisedEW (Expr TCType TCPatn TCIrrefPatn TCExpr)
    normaliseE' d =   traverse (normaliseE d)
                  >=> ttraverse (normaliseIP d)
                  >=> tttraverse (normaliseP d)
                  >=> ttttraverse (contextualise . normaliseT d)

normaliseP :: TypeDict -> TCPatn -> Either ContextualisedEW TCPatn
normaliseP d tp@(TP p l) = case normaliseP' d p of
    Left (es,c) -> Left (ctx:es, c)
    Right p'    -> Right (TP p' l)
  where ctx = InPattern (toLocPatn toLocType tp)
        normaliseP' :: TypeDict -> Pattern TCIrrefPatn -> Either ContextualisedEW (Pattern TCIrrefPatn)
        normaliseP' d = traverse (normaliseIP d)

normaliseIP :: TypeDict -> TCIrrefPatn -> Either ContextualisedEW TCIrrefPatn
normaliseIP d tip@(TIP ip l) = case normaliseIP' d ip of
    Left (es,c) -> Left (ctx:es, c)
    Right ip'   -> Right (TIP ip' l)
  where ctx = InIrrefutablePattern (toLocIrrefPatn toLocType tip)
        normaliseIP' :: TypeDict -> IrrefutablePattern TCName TCIrrefPatn -> Either ContextualisedEW (IrrefutablePattern TCName TCIrrefPatn)
        normaliseIP' d = traverse (normaliseIP d) >=> ttraverse (secondM (contextualise . normaliseT d))

normaliseT :: TypeDict -> TCType -> Either TypeError TCType
normaliseT d (T (TUnbox t)) = do
   t' <- normaliseT d t
   case t' of
     (T (TCon x ps _)) -> normaliseT d (T (TCon x ps Unboxed))
     (T (TRecord l _)) -> normaliseT d (T (TRecord l Unboxed))
     (T o)             -> normaliseT d =<< normaliseT d (T $ fmap (T . TUnbox) o)
     _                 -> error "Panic: impossible"

normaliseT d (T (TBang t)) = do
   t' <- normaliseT d t
   case t' of
     (T (TCon x ps s)) -> mapM (normaliseT d . T . TBang) ps >>= \ps' ->
                          normaliseT d (T (TCon x ps' (bangSigil s)))
     (T (TRecord l s)) -> mapM ((secondM . firstM) (normaliseT d . T . TBang)) l >>= \l' ->
                          normaliseT d (T (TRecord l' (bangSigil s)))
     (T (TVar b _))    -> normaliseT d (T (TVar b True))
     (T o)             -> normaliseT d =<< normaliseT d (T $ fmap (T . TBang) o)
     _                 -> error "Panic: impossible"

normaliseT d (T (TTake fs t)) = do
   t' <- normaliseT d t
   case t' of
     (T (TRecord l s)) -> normaliseT d (T (TRecord (takeFields fs l) s))
     (T (TVariant ts)) -> normaliseT d (T (TVariant (M.fromList $ takeFields fs $ M.toList ts)))
     _ | Just fs' <- fs, null fs' -> Right t'
     e                 -> Left (TakeFromNonRecord fs t)
 where
   takeFields :: Maybe [FieldName] -> [(FieldName, (a, Bool))] -> [(FieldName, (a, Bool))]
   takeFields Nothing   = map (fmap (fmap (const True)))
   takeFields (Just fs) = map (\(f, (t, b)) -> (f, (t, f `elem` fs || b)))

normaliseT d (T (TPut fs t)) = do
   t' <- normaliseT d t
   case t' of
     (T (TRecord l s)) -> normaliseT d (T (TRecord (putFields fs l) s))
     (T (TVariant ts)) -> normaliseT d (T (TVariant (M.fromList $ putFields fs $ M.toList ts)))
     _ | Just fs' <- fs, null fs'  -> Right t'
     e                 -> Left (PutToNonRecord fs t)
 where
   putFields :: Maybe [FieldName] -> [(FieldName, (a, Bool))] -> [(FieldName, (a, Bool))]
   putFields Nothing   = map (fmap (fmap (const False)))
   putFields (Just fs) = map (\(f, (t, b)) -> (f, (t,  (f `notElem` fs) && b)))

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

normaliseT d (U x) = error ("Panic: invalid type to normaliseT (?" ++ show x ++ ")")
normaliseT d (T x) = T <$> traverse (normaliseT d) x

contextualise :: Either TypeError x -> Either ContextualisedEW x
contextualise (Left e) = Left ([],Left e)
contextualise (Right v) = Right v


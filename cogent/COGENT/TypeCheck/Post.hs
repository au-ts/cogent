{-# LANGUAGE TupleSections #-}
module COGENT.TypeCheck.Post where

import COGENT.TypeCheck.Base
import COGENT.Surface
import COGENT.Common.Syntax
import COGENT.Common.Types
import COGENT.Util
import Control.Monad
import Control.Lens
import Control.Monad.Except

postT :: [ErrorContext] -> TCType -> ExceptT [ContextualisedError] TC RawType
postT ctx t = do
  d <- use knownTypes
  withExceptT (pure . (ctx,)) $ ExceptT (return $ fmap toRawType $ normaliseT d t)

postE :: [ErrorContext] -> TCExpr -> ExceptT [ContextualisedError] TC TypedExpr
postE ctx e = do
  d <- use knownTypes
  withExceptT pure $ ExceptT (return $ fmap toTypedExpr $ normalise d e)


postA :: [ErrorContext] -> [Alt TCTypedName TCExpr] -> ExceptT [ContextualisedError] TC [Alt TypedName TypedExpr]
postA ctx as = do
  d <- use knownTypes
  withExceptT pure $ ExceptT (return $ fmap toTypedAlts $ normaliseA d as)

posttc :: TypeDict -> TCExpr -> Either ContextualisedError TypedExpr
posttc d = fmap toTypedExpr . normalise d



normaliseA :: TypeDict -> [Alt TCTypedName TCExpr] -> Either ContextualisedError [Alt TCTypedName TCExpr]
normaliseA d as = traverse (traverse (normalise d) >=> ttraverse (traverse f)) as
  where f = contextualise . normaliseT d

normalise :: TypeDict -> TCExpr -> Either ContextualisedError TCExpr
normalise d te@(TE t e p) = case normalise' d e of
  Left (es,c) -> Left (ctx:es, c)
  Right e'    -> case normaliseT d t of
    Left er -> Left ([ctx], er)
    Right t' -> Right (TE t' e' p)
  where
    ctx = InExpression (toLocExpr (toLocType) te) t

normaliseT :: TypeDict -> TCType -> Either TypeError TCType
normaliseT d (T (TUnbox t)) = do
   t' <- normaliseT d t
   case t' of
     (T (TCon x ps _)) -> normaliseT d (T (TCon x ps Unboxed))
     (T (TRecord l _)) -> normaliseT d (T (TRecord l Unboxed))
     (T o)             -> normaliseT d (T (fmap (T . TUnbox) o))
     _                 -> error "Panic: impossible"

normaliseT d (T (TBang t)) = do
   t' <- normaliseT d t
   case t' of
     (T (TCon x ps s)) -> normaliseT d (T (TCon x (map (T . TBang) ps) (bangSigil s)))
     (T (TRecord l s)) -> normaliseT d (T (TRecord (map (fmap (_1 %~ T . TBang)) l) (bangSigil s)))
     (T (TVar b _))    -> normaliseT d (T (TVar b True))
     (T o)             -> normaliseT d (T (fmap (T . TBang) o))
     _                 -> error "Panic: impossible"

normaliseT d (T (TTake fs t)) = do
   t' <- normaliseT d t
   case t' of
     (T (TRecord l s)) -> normaliseT d (T (TRecord (takeFields fs l) s))
     _ | Just fs' <- fs, null fs'  -> Right t'
     e                 -> Left (TakeFromNonRecord fs t)
 where
   takeFields :: Maybe [FieldName] -> [(FieldName, (TCType, Bool))] -> [(FieldName, (TCType, Bool))]
   takeFields Nothing   = map (fmap (fmap (const True)))
   takeFields (Just fs) = map (\(f, (t, b)) -> (f, (t, f `elem` fs || b)))

normaliseT d (T (TPut fs t)) = do
   t' <- normaliseT d t
   case t' of
     (T (TRecord l s)) -> normaliseT d (T (TRecord (putFields fs l) s))
     _ | Just fs' <- fs, null fs'  -> Right t'
     e                 -> Left (PutToNonRecord fs t)
 where
   putFields :: Maybe [FieldName] -> [(FieldName, (TCType, Bool))] -> [(FieldName, (TCType, Bool))]
   putFields Nothing   = map (fmap (fmap (const False)))
   putFields (Just fs) = map (\(f, (t, b)) -> (f, (t,  (f `notElem` fs) && b)))

normaliseT d (T (TCon n as b)) = do
  case lookup n d of
    Just (as', Just b) -> normaliseT d (substType (zip as' as) b)
    _ -> return (T (TCon n as b))

normaliseT d (RemoveCase p t) = do
  t' <- normaliseT d t
  p' <- traverse (traverse (normaliseT d)) p
  case removeCase p' t' of
    Just t'' -> normaliseT d t''
    Nothing  -> Left (RemoveCaseFromNonVariant p t)

normaliseT d (U x) = error "Panic: invalid type to normaliseT"
normaliseT d (T x) = T <$> traverse (normaliseT d) x


normalise' :: TypeDict -> Expr TCType (VarName, TCType) (TExpr TCType) -> Either ContextualisedError (Expr TCType (VarName, TCType) (TExpr TCType))
normalise' d =   traverse (normalise d)
             >=> ttraverse (traverse (contextualise . normaliseT d))
             >=> tttraverse (contextualise . normaliseT d)

contextualise :: Either TypeError x -> Either ContextualisedError x
contextualise (Left e) = Left ([],e)
contextualise (Right v) = Right v

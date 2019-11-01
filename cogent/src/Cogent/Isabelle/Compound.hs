--
-- Copyright 2019, Data61
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-
  Compound: taking apart compound expressions, and putting them back together
-}

{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Cogent.Isabelle.Compound
    ( takeFlatCase
    , expDiscardVar
    , discardVar
    )
  where

import Cogent.Common.Syntax
import Cogent.Core
import Cogent.Util (firstM, secondM)

import Control.Applicative
import qualified Data.Map as M
import Data.Maybe
import Prelude as P
import Data.Nat
import Data.Vec

-- | Try to flatten a nested case into a map of alternatives
--
-- A Core program like:
--
-- > Case scrut tag1 (n1, when_tag1)
-- >  (Case (Var 0) tag2 (n2, when_tag2)
-- >    (Let n3 (Esac (Var 0)) when_tag3)
--
-- becomes something like
--
-- > Just (scrut, fromList [(tag1, (n1, when_tag1)), (tag2, (n2, when_tag2)), (tag3, (n3, when_tag3))])
--
takeFlatCase :: TypedExpr t v VarName
             -> Maybe ( TypedExpr t v VarName
                      , M.Map TagName (VarName, TypedExpr t ('Suc v) VarName))
takeFlatCase (TE _ e) = case e of
 -- Take top-level case separately as we need the scrutinee here,
 -- while the nested levels must have a scrutinee of (Var 0).
 (Case escrut tag (_,n1,e1) (_,n2,e2))
  | TSum talts <- exprType escrut
  -> do let m0 = M.singleton tag (n1,e1)
        -- Descend into failure case to match remaining alternatives
        malts <- goAlts n2 e2 m0
        -- Only succeed if we have alternatives for all variant constructors
        case M.size malts == P.length talts of
         True  -> Just (escrut,malts)
         False -> Nothing

 _ -> Nothing

 where
  goAlts :: forall t u. VarName -> TypedExpr t u VarName -> (M.Map TagName (VarName, TypedExpr t u VarName)) -> Maybe (M.Map TagName (VarName, TypedExpr t u VarName))
  -- Match a nested Case on the same scrutinee
  goAlts nscrut (TE _ (Case (TE _ (Variable (FZero, nscrut'))) tag (_, na1,ea1) (_, na2, ea2))) m
   | nscrut == nscrut'
   = do -- The nested case structure binds a lot of variables that all refer to the scrutinee,
        -- because the failure continuation of each nested case has a binding.
        -- To flatten the case, we need all alternatives to have the same environment.
        -- After doing a nested case, the scrutinee variable usually isn't referred to again:
        -- we need to make sure it isn't referred to, and remove it from the context.
        ea1' <- expDiscardVar (FSuc FZero) ea1
        ea2' <- expDiscardVar (FSuc FZero) ea2
        goAlts na2 ea2' (M.insert tag (na1,ea1') m)

  -- Match an Esac
  goAlts nscrut (TE _ (Let nalt (TE _ (Esac (TE tscrut (Variable (FZero, nscrut'))))) erest)) m
   | nscrut == nscrut'
   , TSum alts <- tscrut
   , [tag]     <- map fst $ filter (\(_,(_,b)) -> not b) alts
   = do erest' <- expDiscardVar (FSuc FZero) erest
        Just $ M.insert tag (nalt,erest') m

  goAlts _ _ _
   = Nothing

-- | Try to discard a variable from an expression context
-- If the variable is not mentioned, return an equivalent expression with a smaller context.
-- If the variable is mentioned, return Nothing.
--
-- This function is pretty trivial, but it's a bit tedious because of the de Bruijn indices.
expDiscardVar :: Fin ('Suc v) -> TypedExpr t ('Suc v) a -> Maybe (TypedExpr t v a)
expDiscardVar rm0 (TE t0 e0) = TE <$> typDiscardVar rm0 t0 <*> expDiscardVar' rm0 expDiscardVar e0

expDiscardVar' :: Fin ('Suc v)
               -> (forall v. Fin ('Suc v) -> e t ('Suc v) a -> Maybe (e t v a))
               -> Expr t ('Suc v) a e -> Maybe (Expr t v a e)
expDiscardVar' rm0 f e = case e of
  Variable (v, a)     -> Variable <$> ((,) <$> discardVar rm0 v <*> pure a)
  Fun fn ts notes     -> Fun fn <$> traverse (typDiscardVar rm0) ts <*> pure notes
  Op o ls             -> Op o <$> mapM go ls
  App e1 e2           -> App <$> go e1 <*> go e2
  Con tag e ty        -> Con <$> pure tag <*> go e <*> typDiscardVar rm0 ty
  Unit                -> pure Unit
  ILit i j            -> pure $ ILit i j
  SLit s              -> pure $ SLit s
  Let a e1 e2         -> Let a <$> go e1 <*> goSuc e2
  LetBang fs a e1 e2  -> LetBang <$> mapM (mfirst $ discardVar rm0) fs <*> pure a <*> go e1 <*> goSuc e2
  Tuple e1 e2         -> Tuple <$> go e1 <*> go e2
  Struct fes          -> Struct <$> mapM (msecond go) fes
  If ep et ef         -> If <$> go ep <*> go et <*> go ef
  Case es tag (l1,n1,e1) (l2,n2,e2)
                      -> Case <$> go es <*> pure tag
                      <*> ((l1,n1,) <$> goSuc e1)
                      <*> ((l2,n2,) <$> goSuc e2)
  Esac es             -> Esac <$> go es
  Split (n,n') es et  -> Split (n,n') <$> go es <*> goSuc2 et
  Member e1 f         -> Member <$> go e1 <*> pure f
  Take (n,n') es f et -> Take (n,n') <$> go es <*> pure f <*> goSuc2 et
  Put e1 f e2         -> Put <$> go e1 <*> pure f <*> go e2
  Promote t e1        -> Promote <$> typDiscardVar rm0 t <*> go e1
  Cast t e1           -> Cast <$> typDiscardVar rm0 t <*> go e1
#ifdef BUILTIN_ARRAYS
  ALit es             -> ALit <$> mapM go es
  ArrayIndex e1 e2    -> ArrayIndex <$> go e1 <*> go e2
  Pop (n,n') e1 e2    -> Pop (n,n') <$> go e1 <*> goSuc2 e2
  Singleton e1        -> Singleton <$> go e1
#endif
 where
  go     = f rm0
  goSuc  = f (FSuc rm0)
  goSuc2 = f (FSuc $ FSuc rm0)
  mfirst  g (a,b) = (,) <$> g    a <*> pure b
  msecond g (a,b) = (,) <$> pure a <*> g    b

typDiscardVar :: Fin ('Suc v) -> DType t ('Suc v) a -> Maybe (DType t v a)
typDiscardVar rm0 t = case t of
  TVar v            -> pure $ TVar v
  TVarBang v        -> pure $ TVarBang v
  TCon tn ts s      -> TCon tn <$> traverse go ts <*> pure s
  TFun t1 t2        -> TFun <$> go t1 <*> go t2
  TPrim pt          -> pure $ TPrim pt
  TString           -> pure TString
  TSum alts         -> TSum <$> mapM (secondM $ firstM go) alts
  TProduct t1 t2    -> TProduct <$> go t1 <*> go t2
  TRecord fs s      -> TRecord <$> mapM (secondM $ firstM go) fs <*> pure s
  TUnit             -> pure TUnit
#ifdef BUILTIN_ARRAYS
  TArray t l s mh   -> TArray <$> go t <*> pure l <*> pure s <*> mapM (uexpDiscardVar rm0) mh
#endif
 where
  go   = typDiscardVar rm0
  uexpDiscardVar :: Fin ('Suc v) -> UntypedExpr t ('Suc v) a -> Maybe (UntypedExpr t v a)
  uexpDiscardVar rm (E e) = E <$> expDiscardVar' rm uexpDiscardVar e


-- | Check if two variables are different: if so, remove first variable from second's context
--
-- > discard i j
-- > | i == j = Nothing
-- > | i <  j = Just (j - 1)
-- > | i >  j = Just j
--
discardVar :: forall v. Fin ('Suc v) -> Fin ('Suc v) -> Maybe (Fin v)
discardVar FZero    FZero    = Nothing
discardVar (FSuc r) FZero    = case r of
  -- Need to match on r again to prove that type 'v' is actually a Suc...
  FZero  -> Just FZero
  FSuc _ -> Just FZero
discardVar FZero    (FSuc v) = Just v
discardVar (FSuc r) (FSuc v) = case (r,v) of
  (FZero, FZero)  -> FSuc <$> discardVar r v
  (FSuc _,FZero)  -> FSuc <$> discardVar r v
  (FZero, FSuc _) -> FSuc <$> discardVar r v
  (FSuc _,FSuc _) -> FSuc <$> discardVar r v


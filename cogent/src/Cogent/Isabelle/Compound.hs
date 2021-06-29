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
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Cogent.Isabelle.Compound
    ( takeFlatCase
    , expDiscardVar
    , discardVar
    )
  where

import Cogent.Common.Syntax
import Cogent.Compiler (__todo)
import Cogent.Core
import Cogent.Util (firstM, secondM)
import Data.Fin
import Data.Nat

import Control.Applicative
import qualified Data.Map as M
import Data.Maybe
import Prelude as P

import Text.Parsec.Pos (SourcePos)

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
takeFlatCase :: PosTypedExpr t v VarName b
             -> Maybe ( PosTypedExpr t v VarName b
                      , M.Map TagName (VarName, PosTypedExpr t ('Suc v) VarName b))
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
  goAlts :: forall t u b. VarName
         -> PosTypedExpr t u VarName b
         -> (M.Map TagName (VarName, PosTypedExpr t u VarName b))
         -> Maybe (M.Map TagName (VarName, PosTypedExpr t u VarName b))
  -- Match a nested Case on the same scrutinee
  goAlts nscrut (TE _ (Case (TE _ (Variable (FZero, nscrut') loc)) tag (_, na1,ea1) (_, na2, ea2))) m
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
  goAlts nscrut (TE _ (Let nalt (TE _ (Esac (TE tscrut (Variable (FZero, nscrut') _)))) erest _)) m
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
expDiscardVar :: Fin ('Suc v) -> PosTypedExpr t ('Suc v) a b -> Maybe (PosTypedExpr t v a b)
expDiscardVar rm0 (TE t0 e0) = TE <$> typDiscardVar (finNat rm0) t0 <*> expDiscardVar' rm0 expDiscardVar e0

expDiscardVar' :: Fin ('Suc v)
               -> (forall v. Fin ('Suc v) -> e SourcePos t ('Suc v) a b -> Maybe (e SourcePos t v a b)) -- FIXME: use loc typevar instead of SourcePos
               -> PosExpr t ('Suc v) a b e -> Maybe (PosExpr t v a b e)
expDiscardVar' rm0 f e = case e of
  Variable (v, a) loc    -> Variable <$> ((,) <$> discardVar rm0 v <*> pure a) <*> pure loc
  Fun fn ts ls notes loc    -> Fun fn <$> traverse (typDiscardVar $ finNat rm0) ts <*> pure ls <*> pure notes <*> pure loc
  Op o ls loc               -> Op o <$> mapM go ls <*> pure loc
  App e1 e2 loc             -> App <$> go e1 <*> go e2 <*> pure loc
  Con tag e ty loc          -> Con <$> pure tag <*> go e <*> typDiscardVar (finNat rm0) ty <*> pure loc
  Unit loc                  -> pure $ Unit loc
  ILit i j loc              -> pure $ ILit i j loc
  SLit s loc                -> pure $ SLit s loc
  Let a e1 e2 loc           -> Let a <$> go e1 <*> goSuc e2 <*> pure loc
  LetBang fs a e1 e2     -> LetBang <$> mapM (mfirst $ discardVar rm0) fs <*> pure a <*> go e1 <*> goSuc e2
  Tuple e1 e2            -> Tuple <$> go e1 <*> go e2
  Struct fes             -> Struct <$> mapM (msecond go) fes
  If ep et ef            -> If <$> go ep <*> go et <*> go ef
  Case es tag (l1,n1,e1) (l2,n2,e2)
                         -> Case <$> go es <*> pure tag
                         <*> ((l1,n1,) <$> goSuc e1)
                         <*> ((l2,n2,) <$> goSuc e2)
  Esac es                -> Esac <$> go es
  Split (n,n') es et     -> Split (n,n') <$> go es <*> goSuc2 et
  Member e1 f            -> Member <$> go e1 <*> pure f
  Take (n,n') es f et    -> Take (n,n') <$> go es <*> pure f <*> goSuc2 et
  Put e1 f e2            -> Put <$> go e1 <*> pure f <*> go e2
  Promote t e1           -> Promote <$> typDiscardVar (finNat rm0) t <*> go e1
  Cast t e1              -> Cast <$> typDiscardVar (finNat rm0) t <*> go e1
#ifdef BUILTIN_ARRAYS
  ALit es                -> ALit <$> mapM go es
  ArrayIndex e1 e2       -> ArrayIndex <$> go e1 <*> go e2
  Pop (n,n') e1 e2       -> Pop (n,n') <$> go e1 <*> goSuc2 e2
  Singleton e1           -> Singleton <$> go e1
  ArrayMap2 _ _          -> __todo "expDiscardVar'"
  ArrayTake as arr idx e -> __todo "expDiscardVar'"
  ArrayPut arr idx v     -> __todo "expDiscardVar'"
#endif
 where
  go     = f rm0
  goSuc  = f (FSuc rm0)
  goSuc2 = f (FSuc $ FSuc rm0)
  mfirst  g (a,b) = (,) <$> g    a <*> pure b
  msecond g (a,b) = (,) <$> pure a <*> g    b

typDiscardVar :: Nat -> Type t b -> Maybe (Type t b)
typDiscardVar rm0 t = case t of
  TVar v            -> pure $ TVar v
  TVarBang v        -> pure $ TVarBang v
  TCon tn ts s      -> TCon tn <$> traverse go ts <*> pure s
  TSyn tn ts s r    -> TSyn tn <$> traverse go ts <*> pure s <*> pure r
  TFun t1 t2        -> TFun <$> go t1 <*> go t2
  TPrim pt          -> pure $ TPrim pt
  TString           -> pure TString
  TSum alts         -> TSum <$> mapM (secondM $ firstM go) alts
  TProduct t1 t2    -> TProduct <$> go t1 <*> go t2
  TRecord rp fs s   -> TRecord rp <$> mapM (secondM $ firstM go) fs <*> pure s
  TUnit             -> pure TUnit
#ifdef BUILTIN_ARRAYS
  TArray t l s mh   -> TArray <$> go t <*> pure l <*> pure s <*> mapM (lexpDiscardVar rm0) mh -- no lexpDiscardVar for l, is that correct? / gteege
#endif
 where
  go   = typDiscardVar rm0

lexpDiscardVar :: Nat -> LExpr t b -> Maybe (LExpr t b)
lexpDiscardVar rm0 = \case
  LVariable (v, a)     -> LVariable <$> ((,) <$> discardVar' rm0 v <*> pure a)
  LFun fn ts ls        -> pure $ LFun fn ts ls
  LOp o ls             -> LOp o <$> mapM go ls
  LApp e1 e2           -> LApp <$> go e1 <*> go e2
  LCon tag e ty        -> LCon <$> pure tag <*> go e <*> pure ty
  LUnit                -> pure LUnit
  LILit i j            -> pure $ LILit i j
  LSLit s              -> pure $ LSLit s
  LLet a e1 e2         -> LLet a <$> go e1 <*> goSuc e2
  LLetBang fs a e1 e2  -> LLetBang <$> mapM (mfirst $ discardVar' rm0) fs <*> pure a <*> go e1 <*> goSuc e2
  LTuple e1 e2         -> LTuple <$> go e1 <*> go e2
  LStruct fes          -> LStruct <$> mapM (msecond go) fes
  LIf ep et ef         -> LIf <$> go ep <*> go et <*> go ef
  LCase es tag (n1,e1) (n2,e2)
                       -> LCase <$> go es <*> pure tag
                       <*> ((n1,) <$> goSuc e1)
                       <*> ((n2,) <$> goSuc e2)
  LEsac es             -> LEsac <$> go es
  LSplit (n,n') es et  -> LSplit (n,n') <$> go es <*> goSuc2 et
  LMember e1 f         -> LMember <$> go e1 <*> pure f
  LTake (n,n') es f et -> LTake (n,n') <$> go es <*> pure f <*> goSuc2 et
  LPut e1 f e2         -> LPut <$> go e1 <*> pure f <*> go e2
  LPromote t e1        -> LPromote t <$> go e1
  LCast t e1           -> LCast t <$> go e1
 where
  go     = lexpDiscardVar rm0
  goSuc  = lexpDiscardVar (Suc rm0)
  goSuc2 = lexpDiscardVar (Suc $ Suc rm0)
  mfirst  g (a,b) = (,) <$> g    a <*> pure b
  msecond g (a,b) = (,) <$> pure a <*> g    b
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

discardVar' :: Nat -> Nat -> Maybe Nat
discardVar' Zero    Zero    = Nothing
discardVar' (Suc r) Zero    = Just Zero
discardVar' Zero    (Suc v) = Just v
discardVar' (Suc r) (Suc v) = Suc <$> discardVar' r v


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

{- LANGUAGE AllowAmbiguousTypes #-}
{- LANGUAGE DataKinds #-}
{- LANGUAGE DeriveDataTypeable -}
{- LANGUAGE DeriveFunctor #-}
{- LANGUAGE ExistentialQuantification #-}
{- LANGUAGE FlexibleContexts #-}
{- LANGUAGE FlexibleInstances #-}
{- LANGUAGE GADTs #-}
{- LANGUAGE GeneralizedNewtypeDeriving #-}
{- LANGUAGE InstanceSigs -}
{- LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
#if __GLASGOW_HASKELL__ < 709
{- LANGUAGE OverlappingInstances #-}
#endif
{- LANGUAGE PatternGuards #-}
{- LANGUAGE PolyKinds #-}
{- LANGUAGE Rank2Types #-}
{- LANGUAGE ScopedTypeVariables #-}
{- LANGUAGE StandaloneDeriving #-}
{- LANGUAGE TupleSections #-}
{- LANGUAGE TypeFamilies #-}
{- LANGUAGE TypeOperators #-}
{- LANGUAGE UndecidableInstances #-}
{- LANGUAGE ViewPatterns #-}
{- OPTIONS_GHC -fno-warn-orphans -fno-warn-missing-signatures #-}

module Cogent.TypeCheck.Solver.Z3 where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.PrettyPrint
import Cogent.Surface
import Cogent.TypeCheck.Base hiding (Sat, Unsat)
import Cogent.Util (bindM2)

import Control.Monad (forM)
import Data.IntMap as IM
import Text.PrettyPrint.ANSI.Leijen as P hiding ((<$>), (<>))
import Z3.Monad


model :: IM.IntMap TCType -> IM.IntMap TCType -> [SExpr] -> IO (Bool, Maybe (IM.IntMap SExpr))
model schms univs es = evalZ3With (Just QF_BV) stdOpts $ model' schms univs es

model' :: (MonadZ3 m) => IM.IntMap TCType -> IM.IntMap TCType -> [SExpr] -> m (Bool, Maybe (IM.IntMap SExpr))
model' schms univs es = do
  e <- mkAnd =<< mapM sexprToSmt es
  let (vs,ts) = unzip $ IM.toList univs
  symbs <- forM vs mkIntSymbol
  sorts <- forM ts tctypeToSmt
  e' <- mkForall [] symbs sorts e
  (res, mbm) <- getModel
  case res of 
    Unsat -> return (False, Nothing)
    Undef -> __impossible "model: SMT says undef"
    Sat -> case mbm of
             Nothing -> return (True, Nothing)
             Just m  -> readModel m schms >>= \m' -> return (True, Just m')

readModel :: (MonadZ3 m) => Model -> IM.IntMap TCType -> m (IM.IntMap SExpr)
readModel m schms =
  flip traverseWithKey schms $ \i t -> do
    e <- sexprToSmt (SU i t)
    mbe <- modelEval m e False
    case mbe of Nothing -> __impossible "readModel: something wrong!"
                Just e' -> smtToSExpr e' t

tctypeToSmt :: (MonadZ3 m) => TCType -> m Sort
tctypeToSmt (T (TCon "U8"   [] Unboxed)) = mkBvSort 8
tctypeToSmt (T (TCon "U16"  [] Unboxed)) = mkBvSort 16
tctypeToSmt (T (TCon "U32"  [] Unboxed)) = mkBvSort 32
tctypeToSmt (T (TCon "U64"  [] Unboxed)) = mkBvSort 64
tctypeToSmt (T (TCon "Bool" [] Unboxed)) = mkBoolSort
tctypeToSmt _ = __impossible "tctypeToSmt: invalid type"

sexprToSmt :: (MonadZ3 m) => SExpr -> m AST
sexprToSmt (SE _ (U _)) = __impossible "sexprToSmt: it's too early to solve this constraint"
sexprToSmt (SU _ (U _)) = __impossible "sexprToSmt: it's too early to solve this constraint"
sexprToSmt (SE (PrimOp op [e1,e2]) _) = bindM2 (bopToSmt op) (sexprToSmt e1) (sexprToSmt e2)
sexprToSmt (SE (PrimOp op [e]) _) = uopToSmt op =<< sexprToSmt e
sexprToSmt (SE (Var v) (T t)) = do
  sort <- case t of
            TCon "U8"   [] Unboxed -> mkBvSort 8
            TCon "U16"  [] Unboxed -> mkBvSort 16
            TCon "U32"  [] Unboxed -> mkBvSort 32
            TCon "U64"  [] Unboxed -> mkBvSort 64
            TCon "Bool" [] Unboxed -> mkBoolSort
            _ -> __todo $ "sexprToSmt: type " ++ show (pretty t) ++ " not yet supported"
  symb <- mkStringSymbol v
  mkConst symb sort
sexprToSmt (SE (IntLit i) (T t)) = 
  let w = case t of
            TCon "U8"   [] Unboxed -> 8
            TCon "U16"  [] Unboxed -> 16
            TCon "U32"  [] Unboxed -> 32
            TCon "U64"  [] Unboxed -> 64
            _ -> __impossible "sexprToSmt: wrong type for IntLit"
   in mkBvNum w i
sexprToSmt (SE (BoolLit b) _) = mkBool b
sexprToSmt (SE (Upcast e) _) = sexprToSmt e
sexprToSmt (SE (Annot e _) _) = sexprToSmt e
sexprToSmt (SU i (T t)) = do
  sort <- case t of
            TCon "U8"   [] Unboxed -> mkBvSort 8
            TCon "U16"  [] Unboxed -> mkBvSort 16
            TCon "U32"  [] Unboxed -> mkBvSort 32
            TCon "U64"  [] Unboxed -> mkBvSort 64
            TCon "Bool" [] Unboxed -> mkBoolSort
            _ -> __todo $ "sexprToSmt: type " ++ show (pretty t) ++ " not yet supported"
  symb <- mkIntSymbol i
  mkConst symb sort
sexprToSmt e = __todo "sexprToSmt: not yet support this expression"

bopToSmt :: (MonadZ3 m) => OpName -> (AST -> AST -> m AST)
bopToSmt = \case
  "+"   -> mkBvadd
  "-"   -> mkBvsub
  "*"   -> mkBvmul
  "/"   -> mkBvudiv
  "%"   -> mkBvurem
  "&&"  -> \e1 e2 -> mkAnd [e1,e2]
  "||"  -> \e1 e2 -> mkOr  [e1,e2]
  ".&." -> mkBvand
  ".|." -> mkBvor
  ".^." -> mkBvxor
  "<<"  -> mkBvshl
  ">>"  -> mkBvlshr
  "=="  -> mkEq
  "/="  -> ((mkNot =<<) .) . mkEq
  ">"   -> mkBvugt
  "<"   -> mkBvult
  ">="  -> mkBvuge
  "<="  -> mkBvule

uopToSmt :: (MonadZ3 m) => OpName -> (AST -> m AST)
uopToSmt = \case
  "not"        -> mkNot
  "complement" -> mkBvnot

smtToSExpr :: (MonadZ3 m) => AST -> TCType -> m SExpr
smtToSExpr e t@(T (TCon "U8"   [] Unboxed)) = SE <$> (IntLit <$> getBv e False) <*> pure t
smtToSExpr e t@(T (TCon "U16"  [] Unboxed)) = SE <$> (IntLit <$> getBv e False) <*> pure t
smtToSExpr e t@(T (TCon "U32"  [] Unboxed)) = SE <$> (IntLit <$> getBv e False) <*> pure t
smtToSExpr e t@(T (TCon "U64"  [] Unboxed)) = SE <$> (IntLit <$> getBv e False) <*> pure t
smtToSExpr e t@(T (TCon "Bool" [] Unboxed)) = SE <$> (BoolLit <$> getBool e) <*> pure t
smtToSExpr _ _ = __impossible "smtToSExpr: invalid Z3 expression"





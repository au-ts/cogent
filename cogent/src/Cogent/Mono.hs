--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
--{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Cogent.Mono where

import Cogent.Compiler (__impossible, __cogent_entry_funcs)
import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Core
import Cogent.Inference
import Cogent.Util (Warning)
import Cogent.Vec as Vec hiding (head)

import Control.Applicative
import Control.Arrow (first, second, (***))
import Control.Monad.Reader     hiding (mapM)
import Control.Monad.RWS.Strict hiding (Product, Sum, mapM)
import Data.Function.Flippers (flip3)
import Data.List as L (partition)
import Data.Map as M
import Data.Maybe (catMaybes, fromJust)
import Data.Set as S
import Prelude as P

-- import Debug.Trace


type Instance = [Type 'Zero]

-- The list of Definitions is pre-ordered, which means that we only need to visit each definition exactly once.
-- Traversal has to start from the roots of the call trees to collect instances.

type FunMono  = M.Map FunName  (M.Map Instance Int)  -- [] can never be an element in the map. mono-function should have M.empty
type TypeMono = M.Map TypeName (S.Set Instance)      -- as above

newtype Mono a = Mono { runMono :: RWS Instance
                                       ([Warning], [Definition TypedExpr VarName])
                                       (FunMono, TypeMono)
                                       a }
               deriving (Functor, Applicative, Monad,
                         MonadReader Instance,
                         MonadWriter ([Warning], [Definition TypedExpr VarName]),
                         MonadState  (FunMono, TypeMono))

-- Returns: (monomorphic abstract functions, poly-abs-funcs)
absFuns :: [Definition TypedExpr VarName] -> ([FunName], [FunName])
absFuns = (P.map getDefinitionId *** P.map getDefinitionId)
        . L.partition (\(AbsDecl _ _ ts _ _) -> case Vec.length ts of SZero -> True; _ -> False)
        . P.filter isAbsDecl
  where isAbsDecl (AbsDecl {}) = True; isAbsDecl _ = False

-- This is a function made for AlexH - this table maps abstract functions to the number of instantiations
-- With --entry-funcs flag, unused functions won't appear in the list
-- Without this flag, unused functions will be numbered 0
-- Mono-functions are always numbered -1
absFunMono :: FunMono -> [Definition TypedExpr VarName] -> M.Map FunName Int
absFunMono (M.toList -> l) (absFuns -> (ms,ps)) = M.fromList . catMaybes $ flip P.map l $ \(fn, M.size -> num) ->
                                                  if | fn `elem` ps -> Just (fn, num)
                                                     | fn `elem` ms -> Just (fn, -1)
                                                     | otherwise -> Nothing

printAFM :: FunMono -> [Definition TypedExpr VarName] -> String
printAFM = ((unlines . P.map (\(n,i) -> n ++ ", " ++ show i) . M.toList) .) . absFunMono

mono :: [Definition TypedExpr VarName] -> Maybe (FunMono, TypeMono) -> ((FunMono, TypeMono), ([Warning], [Definition TypedExpr VarName]))
mono ds initmap = (second . second $ reverse) . (flip3 execRWS initmap' []) . runMono $ monoDefinitions (reverse ds)
  where initmap' :: (FunMono, TypeMono)  -- a map consists of all function names, each of which has no instances
        initmap' = case initmap of
                     Nothing -> ( M.fromList $ P.zip (catMaybes $ P.map getFuncId ds) (P.repeat M.empty)  -- [] can never appear in the map
                                , M.empty)
                     Just m  -> m

monoDefinitions :: [Definition TypedExpr VarName] -> Mono ()
monoDefinitions = mapM_ monoDefinition

monoDefinition :: Definition TypedExpr VarName -> Mono ()
-- monoDefinition d@(TypeDef {}) = censor (second $ (d:)) (return ())  -- types are all structural, no need to monomorphise
monoDefinition d@(TypeDef _ Vec.Nil _) = censor (second $ (d:)) $ return ()  -- Only add non-parametric types to CG
  -- FIXME: It seems that this problem have been subsumed and fixed by #84 / zilinc (03/09/15)
  -- FIXME: No matter whether we use --entry-funcs, this problem persists.
  --        In this case, the missing type should be provided by the user, manually / zilinc
  -- XXX | NOTE: If entry-points are given, adding type definitions to CG will
  -- XXX |       cause problem if components of this type, together with the
  -- XXX |       type itself, is not used. The problem is, we will generate a
  -- XXX |       type synonym to that unused type, which requires the usused
  -- XXX |       components defined in the generated code. But because they
  -- XXX |       are unused, they are not defined. Thus this type will refer
  -- XXX |       to undeclared types. (see tests/wip_ent-defns.cogent, compiling
  -- XXX |       with tests/ent-defns.ed as --entry-funcs file) / zilinc
monoDefinition d@(TypeDef {}) = return ()  -- NOTE: Only monomorphic program can be brought to CG, however we don't have
                                           --       appropriate facilities to name monomorphised types here, so we don't
                                           --       export them / zilinc
monoDefinition d =
  let fn = getDefinitionId d
   in M.lookup fn . fst <$> get >>= \case
        Nothing -> censor (first $ (("Function `" ++ fn ++ "' not used within Cogent, discarded") :)) (return ())  -- shouldn't happen if __cogent_entry_funcs == Nothing
        Just is -> monoDefinitionInsts d $ M.keys is

-- given instances, instantiate a function
monoDefinitionInsts :: Definition TypedExpr VarName -> [Instance] -> Mono ()
monoDefinitionInsts d [] = case __cogent_entry_funcs of
  Just _  -> monoDefinitionInst d []  -- monomorphic function, because only functions in __cogent_entry_funcs get passed to this function
  Nothing -> if getTypeVarNum d == 0
              then monoDefinitionInst d []  -- monomorphic function
              else -- has type variables but no instances are given, so there's just no way to monomorphise it
                   censor (first $ (("Cannot monomorphise definition `" ++ getDefinitionId d ++ "'") :)) (return ())  -- shouldn't happen if __cogent_entry_funcs /= Nothing
monoDefinitionInsts d is = flip mapM_ is $ monoDefinitionInst d

monoName :: String -> Maybe Int -> String
monoName n Nothing  = n
monoName n (Just i) = n ++ "_" ++ show i

-- given one instance
monoDefinitionInst :: Definition TypedExpr VarName -> Instance -> Mono ()
monoDefinitionInst (FunDef attr fn tvs t rt e) i = do
  idx <- if P.null i then return Nothing else M.lookup i . fromJust . M.lookup fn . fst <$> get
  d' <- Mono $ local (const i) (runMono $ FunDef attr (monoName fn idx) Nil <$> monoType t <*> monoType rt <*> monoExpr e)
  censor (second $ (d':)) (return ())
monoDefinitionInst (AbsDecl attr fn tvs t rt) i = do
  idx <- if P.null i then return Nothing else M.lookup i . fromJust . M.lookup fn . fst <$> get
  d' <- Mono $ local (const i) (runMono $ AbsDecl attr (monoName fn idx) Nil <$> monoType t <*> monoType rt)
  censor (second $ (d':)) (return ())
monoDefinitionInst (TypeDef tn tvs t) i = __impossible "monoDefinitionInst"

getPrimInt :: TypedExpr t v VarName -> PrimInt
getPrimInt (TE t _) | TPrim p <- t = p
                    | otherwise = __impossible "getPrimInt"

monoExpr :: TypedExpr t v VarName -> Mono (TypedExpr 'Zero v VarName)
monoExpr (TE t e) = TE <$> monoType t <*> monoExpr' e
  where
    monoExpr' (Variable var       ) = pure $ Variable var
    monoExpr' (Fun      fn []  nt ) = modify (first $ M.insert fn M.empty) >> return (Fun fn [] nt)
    monoExpr' (Fun      fn tys nt ) = do
      tys' <- mapM monoType tys
      modify (first $ M.insertWith (\_ m -> insertWith (flip const) tys' (M.size m) m) fn (M.singleton tys' 0))  -- add one more instance to the env
      idx <- M.lookup tys' . fromJust . M.lookup fn . fst <$> get
      return $ Fun (monoName fn idx) [] nt  -- used to be tys'
    monoExpr' (Op      opr es     ) = Op opr <$> mapM monoExpr es
    monoExpr' (App     e1 e2      ) = App <$> monoExpr e1 <*> monoExpr e2
    monoExpr' (Con     tag e      ) = Con tag <$> monoExpr e
    monoExpr' (Unit               ) = pure Unit
    monoExpr' (ILit    n   pt     ) = pure $ ILit n pt
    monoExpr' (SLit    s          ) = pure $ SLit s
    monoExpr' (Let     a e1 e2    ) = Let a <$> monoExpr e1 <*> monoExpr e2
    monoExpr' (LetBang vs a e1 e2 ) = LetBang vs a <$> monoExpr e1 <*> monoExpr e2
    monoExpr' (Tuple   e1 e2      ) = Tuple <$> monoExpr e1 <*> monoExpr e2
    monoExpr' (Struct  fs         ) = let (ns,ts) = P.unzip fs in Struct <$> zipWithM (\n t -> (n,) <$> monoExpr t) ns ts
    monoExpr' (If      c e1 e2    ) = If <$> monoExpr c <*> monoExpr e1 <*> monoExpr e2
    monoExpr' (Case    c tag (l1,a1,e1) (l2,a2,e2)) = Case <$> monoExpr c <*> pure tag <*> ((l1,a1,) <$> monoExpr e1) <*> ((l2,a2,) <$> monoExpr e2)
    monoExpr' (Esac    e          ) = Esac <$> monoExpr e
    monoExpr' (Split   a tp e     ) = Split a <$> monoExpr tp <*> monoExpr e
    monoExpr' (Member  rec fld    ) = flip Member fld <$> monoExpr rec
    monoExpr' (Take    a rec fld e) = Take a <$> monoExpr rec <*> pure fld <*> monoExpr e
    monoExpr' (Put     rec fld e  ) = Put  <$> monoExpr rec <*> pure fld <*> monoExpr e
    monoExpr' (Promote ty e       ) = Promote <$> monoType ty <*> monoExpr e

monoType :: Type t -> Mono (Type 'Zero)
monoType (TVar v) = atList <$> ask <*> pure v
monoType (TVarBang v) = bang <$> (atList <$> ask <*> pure v)
monoType (TCon n [] s) = do
  modify . second $ M.insert n S.empty
  return $ TCon n [] s
monoType (TCon n ts s) = do
  ts' <- mapM monoType ts
  let f Nothing   = Just $ S.singleton ts'   -- If n is not in the set
      f (Just is) = Just $ S.insert ts' is   -- Otherwise
  modify . second $ M.alter f n
  return $ TCon n ts' s
monoType (TFun t1 t2) = TFun <$> monoType t1 <*> monoType t2
monoType (TPrim p) = pure $ TPrim p
monoType (TString) = pure $ TString
monoType (TSum alts) = do
  let (ns,(ts,bs)) = second P.unzip $ P.unzip alts
  ts' <- mapM monoType ts
  return $ TSum $ P.zip ns $ P.zip ts' bs
monoType (TProduct t1 t2) = TProduct <$> monoType t1 <*> monoType t2
monoType (TRecord fs s) = TRecord <$> mapM (\(f,(t,b)) -> (f,) <$> (,b) <$> monoType t) fs <*> pure s
monoType (TUnit) = pure TUnit

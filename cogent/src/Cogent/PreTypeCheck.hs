--
-- Copyright 2021, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Cogent.PreTypeCheck (
  PreTCError(..)
, preTc
) where

import Cogent.Compiler
import Cogent.Surface
import Cogent.Util
import Cogent.Common.Types

import Cogent.Dargent.DefaultGen
import Cogent.Dargent.Surface

import Control.Arrow
import Control.Monad
import Data.Maybe (fromJust)
import Text.Parsec.Pos (SourcePos)

data PreTCError = DefaultUninferrable
                deriving (Show, Eq)

preTc :: [(SourcePos, TopLevel LocType LocPatn LocExpr)]
      -> [(LocType, String)]
      -> Either (PreTCError, SourcePos) ([(SourcePos, TopLevel LocType LocPatn LocExpr)], [(LocType, String)])
preTc ds cts = (,) <$> mapM (uncurry preTcTl) ds <*> mapM (uncurry preTcCust) cts

preTcTl :: SourcePos -> TopLevel LocType LocPatn LocExpr
        -> Either (PreTCError, SourcePos) (SourcePos, TopLevel LocType LocPatn LocExpr)
preTcTl pos = \case
  TypeDec n vs t -> (pos,) . TypeDec n vs <$> rewriteDefault t
  AbsTypeDec n vs ts -> (pos,) . AbsTypeDec n vs <$> mapM rewriteDefault ts
  AbsDec n (PT ps ls t) -> (pos,) . AbsDec n . PT ps ls <$> rewriteDefault t
  RepDef decl@(DataLayoutDecl _ _ _ expr) ->
    if containDefault expr
       then Left  (DefaultUninferrable, pos)
       else Right (pos, RepDef decl)
  ConstDef n t e -> (pos,) . flip (ConstDef n) e <$> rewriteDefault t
  FunDef f (PT ps ls t) alts -> (pos,) . flip (FunDef f) alts . PT ps ls <$> rewriteDefault t
  tl -> Right (pos, tl)

preTcCust :: LocType -> String -> Either (PreTCError, SourcePos) (LocType, String)
preTcCust cust str = (,str) <$> rewriteDefault cust

rewriteDefault :: LocType -> Either (PreTCError, SourcePos) LocType
rewriteDefault t@(typeOfLT -> t') = LocType (posOfLT t) <$> f t'
  where
    f (TLayout l t) | containDefault l, isBoxedType t = flip TLayout t <$> f' l (LocType (posOfLT t) $ TUnbox t)
    f _ = traverse rewriteDefault t'
    f' DLDefault t | t' <- stripLocT t, null $ tvT t' = Right . fromJust $ genDefaultLayout t'
                   | otherwise, pos <- posOfLT t = Left (DefaultUninferrable, pos)
    f' (DLRecord fls) (typeOfLT -> TRecord _ fs Unboxed) = DLRecord <$>
      foldM (\fs l -> (:) <$> l <*> Right fs) [] (do
        (fn,(t,_)) <- fs
        (fn',p,l) <- fls
        guard $ fn == fn'
        if containDefault l
           then pure $ (fn,p,) <$> f' l t
           else pure $ Right (fn,p,l))
    f' l@DLRecord{} t@(typeOfLT -> TUnbox (typeOfLT -> TRecord rp fs Boxed{})) =
      f' l (LocType (posOfLT t) $ TRecord rp fs Unboxed)
#ifdef BUILTIN_ARRAYS
    f' (DLArray e p) (typeOfLT -> TArray te _ Unboxed _) = flip DLArray p <$> f' e te
    f' l@DLArray{} t@(typeOfLT -> TUnbox (typeOfLT -> TArray te len Boxed{} tkns)) =
      f' l (LocType (posOfLT t) $ TArray te len Unboxed tkns)
#endif
    f' (DLAfter l sz) t = flip DLAfter sz <$> f' l t
    f' (DLOffset l fn) t = flip DLOffset fn <$> f' l t
    f' _ _ = Left (DefaultUninferrable, posOfLT t)

isBoxedType :: LocType -> Bool
isBoxedType t@(typeOfLT -> TRecord _ _ Boxed{}) = True
#ifdef BUILTIN_ARRAYS
isBoxedType t@(typeOfLT -> TArray _ _ Boxed{} _) = True
#endif
isBoxedType (typeOfLT -> TBang t) = isBoxedType t
isBoxedType _ = False

isPrimType :: RawType -> Bool
isPrimType (unRT -> TCon n [] Unboxed) | n `elem` words "U8 U16 U32 U64 Bool" = True
isPrimType (unRT -> TBang t) = isPrimType t
isPrimType (unRT -> TUnbox t) = isPrimType t
isPrimType _ = False


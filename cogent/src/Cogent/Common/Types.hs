--
-- Copyright 2019, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}

module Cogent.Common.Types where

import Cogent.Common.Syntax
import Data.Bifunctor (first)
import Data.Data
#if __GLASGOW_HASKELL__ < 709
import Data.Monoid
#endif
import Text.PrettyPrint.ANSI.Leijen hiding (tupled,indent)

data ReadOnly = Ro -- 0-kinded
              | Wr -- 1-kinded
  deriving (Show, Eq, Data, Ord)

data PtrSigil = Boxed ReadOnly -- 0/1-kinded
              | Unboxed -- 2-kinded
  deriving (Show, Eq, Data, Ord)

type Sigil r = (PtrSigil, r)

bangPtrSigil :: PtrSigil -> PtrSigil
bangPtrSigil (Boxed _) = Boxed Ro
bangPtrSigil Unboxed = Unboxed

bangSigil :: Sigil r -> Sigil r
bangSigil = first bangPtrSigil

writable :: Sigil r -> Bool
writable = (== Boxed Wr) . fst

readonly :: Sigil r -> Bool
readonly = (== Boxed Ro) . fst

unboxed :: Sigil r -> Bool
unboxed = (== Unboxed) . fst


data PrimInt = U8 | U16 | U32 | U64 | Boolean deriving (Show, Data, Eq, Ord)

isSubtypePrim :: PrimInt -> PrimInt -> Bool
isSubtypePrim U8  U8  = True
isSubtypePrim U8  U16 = True
isSubtypePrim U8  U32 = True
isSubtypePrim U8  U64 = True
isSubtypePrim U16 U16 = True
isSubtypePrim U16 U32 = True
isSubtypePrim U16 U64 = True
isSubtypePrim U32 U32 = True
isSubtypePrim U32 U64 = True
isSubtypePrim U64 U64 = True
isSubtypePrim Boolean Boolean = True
isSubtypePrim _ _ = False

instance Pretty PrimInt where
  pretty = blue . bold . string . show

data Kind = K { canEscape :: Bool, canShare :: Bool, canDiscard :: Bool }
  deriving (Show, Data, Eq, Ord)

ptrSigilKind :: PtrSigil -> Kind
ptrSigilKind (Boxed Ro) = k0
ptrSigilKind (Boxed Wr) = k1
ptrSigilKind Unboxed = k2

sigilKind :: Sigil r -> Kind
sigilKind = ptrSigilKind . fst


k0, k1, k2 :: Kind
k0 = K False True  True
k1 = K True  False False
k2 = mempty
-- kAll = K False False False

#if __GLASGOW_HASKELL__ < 803
instance Monoid Kind where
  mempty = K True True True  -- 2-kind
  mappend (K a b c) (K a' b' c') = K (a && a') (b && b') (c && c')
    -- mappend   ka   0    1    2
    --    kb     +-----------------
    --    0      |    0    1x   0
    --    1      |    -    1    1
    --    2      |    -    -    2
    --    !      |    0    0    2
    -- 1x is a non-escapable linear kind
#else
instance Semigroup Kind where
  K a b c <> K a' b' c' = K (a && a') (b && b') (c && c')
instance Monoid Kind where
  mempty = K True True True
#endif

bangKind :: Kind -> Kind
bangKind (K e s d) = K (e && s && d) True True

primTypeCons :: [TypeName]
primTypeCons = words "U8 U16 U32 U64 Bool String"

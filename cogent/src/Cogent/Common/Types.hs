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
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}

module Cogent.Common.Types where

import Cogent.Common.Syntax
import Cogent.Compiler
import Data.Binary (Binary)
import Data.Data
import Data.Map as M
#if __GLASGOW_HASKELL__ < 709
import Data.Monoid
#endif
import GHC.Generics (Generic)
import Text.PrettyPrint.ANSI.Leijen hiding (tupled,indent)

type ReadOnly = Bool  -- True for r/o

data Sigil r = Boxed ReadOnly r  -- 0- or 1-kinded
             | Unboxed  -- 2-kinded
             deriving (Show, Data, Eq, Ord, Foldable, Functor, Generic, Traversable)

instance Binary r => Binary (Sigil r)

data RecursiveParameter = Rec VarName | NonRec deriving (Data, Show, Eq, Ord, Generic)

-- The context for a recursive type, i.e. a mapping from
-- recursive parameter names to the type it recursively references
type RecContext t = Maybe (M.Map RecParName t)

instance Binary RecursiveParameter

bangSigil :: Sigil r -> Sigil r
bangSigil (Boxed _ r)  = Boxed True r
bangSigil Unboxed      = Unboxed

unboxSigil :: Sigil r -> Sigil r
unboxSigil _ = Unboxed

writable :: Sigil r -> Bool
writable (Boxed False _) = True
writable _ = False

readonly :: Sigil r -> Bool
readonly (Boxed True _) = True
readonly _ = False

unboxed :: Sigil r -> Bool
unboxed Unboxed = True
unboxed _ = False

data PrimInt = U8 | U16 | U32 | U64 | Boolean deriving (Show, Data, Eq, Ord, Generic)

instance Binary PrimInt

machineWordType :: PrimInt
machineWordType = case __cogent_arch of
                    ARM32  -> U32
                    X86_32 -> U32
                    X86_64 -> U64

primIntSizeBits :: PrimInt -> Size
primIntSizeBits U8      = 8
primIntSizeBits U16     = 16
primIntSizeBits U32     = 32
primIntSizeBits U64     = 64
primIntSizeBits Boolean = 8


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

sigilKind :: Sigil r -> Kind
sigilKind (Boxed ro _) = if ro then k0 else k1
sigilKind Unboxed      = k2

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

natTypeCons :: [TypeName]
natTypeCons = words "U8 U16 U32 U64"

primTypeCons :: [TypeName]
primTypeCons = "Bool" : "String" : natTypeCons

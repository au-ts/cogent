-- @LICENSE(NICTA_CORE)

{-# LANGUAGE CPP #-}

module Cogent.Common.Types where

import Cogent.Common.Syntax
#if __GLASGOW_HASKELL__ < 709
import Data.Monoid
#endif
import Text.PrettyPrint.ANSI.Leijen hiding (tupled,indent)

data Sigil = ReadOnly  -- 0-kind
           | Writable  -- 1-kind
           | Unboxed   -- 2-kind
           deriving (Show, Eq, Ord)

bangSigil :: Sigil -> Sigil
bangSigil ReadOnly = ReadOnly
bangSigil Writable = ReadOnly
bangSigil Unboxed  = Unboxed

data PrimInt = U8 | U16 | U32 | U64 | Boolean deriving (Show, Eq, Ord)

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
          deriving (Show, Eq, Ord)

sigilKind :: Sigil -> Kind
sigilKind ReadOnly = k0
sigilKind Writable = k1
sigilKind Unboxed  = k2

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

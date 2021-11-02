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

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
module CogentTests.Dargent.TypeCheck where

import Control.Monad (guard)
import Control.Monad.Trans.Except (runExcept)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set, union, empty, intersection)
import qualified Data.Set as S
import Test.QuickCheck
import Test.QuickCheck.All
import Text.Parsec.Pos (SourcePos)

import Cogent.Common.Syntax (DataLayoutName, Size)
import Cogent.Dargent.Allocation
import Cogent.Dargent.Surface
import Cogent.Dargent.Core
import Cogent.Dargent.TypeCheck
import Cogent.Dargent.Util
import Cogent.Surface (noPos)
import CogentTests.Dargent.Core

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), empty)
import Cogent.PrettyPrint

import Debug.Trace

{- PROPERTIES -}

prop_allocationConj :: Allocation -> Allocation -> Bool
prop_allocationConj a b = case a /\ b of
  Right c ->
    (toSet a) `disjoint` (toSet b) &&
    (toSet a) `union`    (toSet b) == toSet c
  _ -> not (toSet a `disjoint` toSet b)

prop_overlaps :: BitRange -> BitRange -> Bool
prop_overlaps a b = overlaps a b == not (toSet a `disjoint` toSet b)

prop_typeCheckValidGivesNoErrors :: Property
prop_typeCheckValidGivesNoErrors =
  forAllShow (genDataLayout size) (\(l,_) -> show (pretty l)) $ \(Layout layout, alloc) -> do  -- FIXME: not considering CLayout for now / zilinc
    let layout' = sugarDataLayout layout
    case runExcept $ tcDataLayoutExpr M.empty [] layout' of
      Right (_,alloc') -> let allocExpected = toSet alloc
                              allocActual   = toSet alloc'
                              res = allocExpected == allocActual
                           in if not res then trace ("surface layout is:\n" ++ show (pretty layout') ++
                                                     "\nalloc  = " ++ show (pretty alloc) ++ 
                                                     "\nalloc' = " ++ show (pretty alloc') ++ "\n") res else res
      Left msg         -> trace (show $ pretty msg) False
  where size = 5

{-+ INVERSE FUNCTIONS
  |
  | Convert core DataLayout values back to surface DataLayoutExprs for round trip testing.
  +-}

bitSizeToDataLayoutSize :: Size -> DataLayoutSize
bitSizeToDataLayoutSize size
  | bytes == 0 = Bits bits
  | bits == 0 = Bytes bytes
  | otherwise = Add (Bytes bytes) (Bits bits)
  where
      bytes = size `div` 8
      bits = size `mod` 8

sugarBitRange :: BitRange -> DataLayoutExpr
sugarBitRange (BitRange size offset) =
  DL $ Offset (DLPrim (bitSizeToDataLayoutSize size)) (bitSizeToDataLayoutSize offset)

sugarDataLayout  :: DataLayout' BitRange -> DataLayoutExpr
sugarDataLayout UnitLayout = DL $ Prim (Bits 0)
sugarDataLayout (PrimLayout bitRange endianness) =
  case endianness of
    ME -> sugarBitRange bitRange
    _  -> DL $ Endian (sugarBitRange bitRange) endianness
sugarDataLayout (RecordLayout fields) =
  DL . Record $ fmap (\(name, layout) -> (name, noPos, (sugarDataLayout layout))) (M.toList fields)
sugarDataLayout (SumLayout tagBitRange alternatives) =
  DL $ Variant
    (sugarBitRange tagBitRange)
    (fmap (\(tagName, (tagValue, altLayout)) -> (tagName, noPos, tagValue, (sugarDataLayout altLayout))) (M.toList alternatives))

{- ARBITRARY INSTANCES -}
instance Arbitrary DataLayoutPath where
  arbitrary = InDecl <$> arbitrary <*> arbitrary

instance Arbitrary p => Arbitrary (Allocation' p) where
  arbitrary = Allocation <$> arbitrary


{- SET UTIL FUNCTIONS -}
disjoint :: Ord a => Set a -> Set a -> Bool
disjoint a b = a `intersection` b == empty

class SetLike a where
  toSet :: a -> Set Size

instance SetLike BitRange where
  toSet (BitRange size offset) = S.fromList [offset..offset + size - 1]

instance SetLike Allocation where
  toSet (Allocation a) = foldr union empty $ fmap (toSet . fst) a

return []
testAll = $quickCheckAll

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

module CogentTests.Dargent.Surface where

import Control.Monad (guard)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set, union, empty, intersection)
import qualified Data.Set as S
import Text.Parsec.Pos (SourcePos)
import Test.QuickCheck

import Cogent.Common.Syntax (FieldName, TagName, Size)
import Cogent.Dargent.Surface
import Cogent.Surface (noPos)
import CogentTests.Dargent.TypeCheck (bitSizeToDataLayoutSize)

instance Arbitrary DataLayoutSize where
  arbitrary = sized $
    \totalSize -> return $ bitSizeToDataLayoutSize $ fromIntegral totalSize

instance Arbitrary DataLayoutExpr where
  arbitrary = sized genDataLayoutExpr

genDataLayoutExpr :: Size -> Gen DataLayoutExpr
genDataLayoutExpr size = oneof
  [ genPrim size
  , genRecord size
  , genOffset size
  , genVariant size
  ]
  where
    genPrim :: Size -> Gen DataLayoutExpr
    genPrim size = DL . Prim <$> arbitrary

    genRecord :: Size -> Gen DataLayoutExpr
    genRecord size = DL . Record <$> genFields size

    genFields :: Size -> Gen [(FieldName, SourcePos, DataLayoutExpr)]
    genFields size = do
      fieldSize <- choose (0, size)
      if fieldSize == 0
        then return []
        else do
          otherFields <- genFields (size - fieldSize)
          fieldName <- arbitrary
          fieldDataLayoutExpr <- genDataLayoutExpr fieldSize
          return $ (fieldName, noPos, fieldDataLayoutExpr) : otherFields

    genVariant :: Size -> Gen DataLayoutExpr
    genVariant size = do
      tagSize <- choose (0, size)
      tagExpr <- genPrim tagSize
      alternatives <- genAlternatives (size - tagSize)
      return $ DL $ Variant tagExpr alternatives

    genAlternatives :: Size -> Gen [(TagName, SourcePos, Integer, DataLayoutExpr)]
    genAlternatives size = do
      altSize <- choose (0, size)
      if altSize == 0
        then return []
        else do
          otherAlts <- genAlternatives (size - altSize)
          altName <- arbitrary
          altValue <- arbitrary
          altDataLayoutExpr <- genDataLayoutExpr altSize
          return $ (altName, noPos, altValue, altDataLayoutExpr) : otherAlts

    genOffset :: Size -> Gen DataLayoutExpr
    genOffset size = DL <$> (Offset <$> genDataLayoutExpr size <*> arbitrary)


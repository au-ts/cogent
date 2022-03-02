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

genDataLayoutExpr :: Int -> Gen DataLayoutExpr
genDataLayoutExpr size =
  if size == 0 then
    return $ DL (Prim (Bits 0))
  else
  oneof
  [ genPrim size
  , genRecord size
  , genOffset size
  , genVariant size
  ]

genPrim :: Int -> Gen DataLayoutExpr
genPrim size = DL . Prim <$> arbitrary

genRecord :: Int -> Gen DataLayoutExpr
genRecord size = DL . Record <$> genFields 1 size
{-
    genFields :: Int -> Gen [(FieldName, SourcePos, DataLayoutExpr)]
    genFields size = do
      fieldSize <- choose (0, size)
      if fieldSize == 0
        then return []
        else do
          otherFields <- genFields (size - fieldSize)
          fieldName <- arbitrary
          fieldDataLayoutExpr <- genDataLayoutExpr fieldSize
          return $ (fieldName, noPos, fieldDataLayoutExpr) : otherFields
-}
genFields :: Int -> Int -> Gen [(FieldName, SourcePos, DataLayoutExpr)]
genFields nth size = do
  fieldSize <- choose (0, size)
  if fieldSize == 0
    then return []
    else do
      otherFields <- genFields (nth + 1)(size - fieldSize)
      fieldName <- return ("field" ++ show nth) -- arbitrary
      fieldDataLayoutExpr <- genDataLayoutExpr fieldSize
      sourcePos <- arbitrary
      return $ (fieldName, sourcePos, fieldDataLayoutExpr) : otherFields

genVariant :: Int -> Gen DataLayoutExpr
genVariant size = do
  tagSize <- choose (0, size)
  tagExpr <- genDataLayoutExpr tagSize
  alternatives <- genAlternatives 1 (size - tagSize)
  return $ DL $ Variant tagExpr alternatives

  {-
    genAlternatives :: Int -> Gen [(TagName, SourcePos, Size, DataLayoutExpr)]
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
-}
genAlternatives :: Int -> Int -> Gen [(TagName, SourcePos, Size, DataLayoutExpr)]
genAlternatives nth size = do
  altSize <- choose (0, size)
  if altSize == 0
    then return []
    else do
      otherAlts <- genAlternatives (nth + 1) (size - altSize)
      altName <- return ("con" ++ show nth) -- arbitrary
      altValue <- arbitrary
      altDataLayoutExpr <- genDataLayoutExpr altSize
      sourcePos <- arbitrary
      return $ (altName, sourcePos, altValue, altDataLayoutExpr) : otherAlts

genOffset :: Int -> Gen DataLayoutExpr
genOffset size = DL <$> (Offset <$> genDataLayoutExpr size <*> arbitrary)


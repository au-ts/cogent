module CogentTests.DataLayout.Surface where
  
import Data.Set (Set, union, empty, intersection)
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

import Control.Monad (guard)

import Test.QuickCheck

import Cogent.Common.Syntax (FieldName, TagName)
import Cogent.DataLayout.Syntax (SourcePos)
import Cogent.DataLayout.Surface
import CogentTests.DataLayout.TypeCheck (bitSizeToRepSize)


instance Arbitrary RepSize where
  arbitrary = sized $
    \totalSize -> return $ bitSizeToRepSize $ fromIntegral totalSize

instance Arbitrary RepExpr where
  arbitrary = sized genRepExpr

genRepExpr :: Int -> Gen RepExpr
genRepExpr size = oneof
  [ genPrim size
  , genRecord size
  , genOffset size
  , genVariant size
  ]
  where
    genPrim :: Int -> Gen RepExpr
    genPrim size = Prim <$> arbitrary
    
    genRecord :: Int -> Gen RepExpr
    genRecord size = Record <$> genFields size
      
    genFields :: Int -> Gen [(FieldName, SourcePos, RepExpr)]
    genFields size = do
      fieldSize <- choose (0, size)
      if fieldSize == 0
        then return []
        else do
          otherFields <- genFields (size - fieldSize)
          fieldName <- arbitrary
          fieldRepExpr <- genRepExpr fieldSize
          return $ (fieldName, (), fieldRepExpr) : otherFields
        
    
    genVariant :: Int -> Gen RepExpr
    genVariant size = do
      tagSize <- choose (0, size)
      tagExpr <- genPrim tagSize
      alternatives <- genAlternatives (size - tagSize)
      return $ Variant tagExpr alternatives
      
    
    genAlternatives :: Int -> Gen [(TagName, SourcePos, Integer, RepExpr)]
    genAlternatives size = do
      altSize <- choose (0, size)
      if altSize == 0
        then return []
        else do
          otherAlts <- genAlternatives (size - altSize)
          altName <- arbitrary
          altValue <- arbitrary
          altRepExpr <- genRepExpr altSize
          return $ (altName, (), altValue, altRepExpr) : otherAlts
    
    genOffset :: Int -> Gen RepExpr
    genOffset size = Offset <$> (genRepExpr size) <*> arbitrary
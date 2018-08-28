{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
module CogentTests.DataLayout.TypeCheck where

import Data.Set (Set, union, empty, intersection)
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

import Control.Monad (guard)

import Test.QuickCheck
import Test.QuickCheck.All
import Text.Parsec.Pos (SourcePos)

import Cogent.DataLayout.Surface
import Cogent.DataLayout.Core
import Cogent.DataLayout.TypeCheck
import CogentTests.DataLayout.Core
import Cogent.Common.Syntax (RepName, Size)

{- PROPERTIES -}
prop_allocationDisj :: Allocation -> Allocation -> Bool
prop_allocationDisj a b = case a \/ b of
  Left  _ -> False
  Right c -> toSet c == (toSet a) `union` (toSet b)

prop_allocationConj :: Allocation -> Allocation -> Bool
prop_allocationConj a b = case a /\ b of
  Left  overlapping -> not (toSet a `disjoint` toSet b)
  Right c           ->
    (toSet a) `disjoint` (toSet b) &&
    (toSet a) `union`    (toSet b) == toSet c 
    
prop_overlaps :: BitRange -> BitRange -> Bool
prop_overlaps a b = overlaps a b == not (toSet a `disjoint` toSet b)

prop_returnTrip = propReturnTrip 30
propReturnTrip :: Size -> RepName -> SourcePos -> Property
propReturnTrip size repName pos =
  forAll (genDataLayout size (InDecl repName pos)) $ \(layout, alloc) ->
  let
    repDecl = RepDecl pos repName (toRepExpr layout)
  in
    case dataLayoutSurfaceToCore M.empty repDecl of
      Left _                  -> False
      Right (layout', alloc') -> layout == layout' && (toSet alloc) == (toSet alloc')  

{-+ INVERSE FUNCTIONS
  |
  | Convert core DataLayout values back to surface RepExprs for round trip testing.
  +-}
  
bitSizeToRepSize :: Size -> RepSize
bitSizeToRepSize size =
  if bytes == 0
    then Bits bits
  else if bits == 0
    then Bytes bytes
    else Add (Bytes bytes) (Bits bits)
  where
    bytes = size `div` 8
    bits  = size `mod` 8
    
rangeToRepExpr :: BitRange -> RepExpr
rangeToRepExpr (BitRange size offset) =
  Offset (Prim (bitSizeToRepSize size)) (bitSizeToRepSize offset)
    
toRepExpr :: DataLayout BitRange -> RepExpr
toRepExpr UnitLayout = Prim (Bits 0)
toRepExpr (PrimLayout bitRange) = rangeToRepExpr bitRange
toRepExpr (RecordLayout fields) =
  Record $ fmap (\(name, (layout, pos)) -> (name, pos, (toRepExpr layout))) (M.toList fields)
toRepExpr (SumLayout tagBitRange alternatives) =
  Variant
    (rangeToRepExpr tagBitRange)
    (fmap (\(tagName, (tagValue, altLayout, altPos)) -> (tagName, altPos, tagValue, (toRepExpr altLayout))) (M.toList alternatives))
    
{- ARBITRARY INSTANCES -}
instance Arbitrary DataLayoutPath where
  arbitrary = InDecl <$> arbitrary <*> arbitrary
    

{- SET UTIL FUNCTIONS -}
disjoint :: Ord a => Set a -> Set a -> Bool
disjoint a b = a `intersection` b == empty

class SetLike a where
  toSet :: a -> Set Size

instance SetLike BitRange where
  toSet (BitRange size offset) = S.fromList [offset..offset + size - 1]

instance SetLike Allocation where
  toSet = foldr union empty . fmap (toSet . fst)
    
return []
testAll = $quickCheckAll

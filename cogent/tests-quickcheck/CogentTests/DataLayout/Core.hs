{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TemplateHaskell #-}
module CogentTests.DataLayout.Core where

import Data.Map (Map)
import qualified Data.Map as M

import Test.QuickCheck

import Cogent.DataLayout.Core
import Cogent.DataLayout.TypeCheck
import Cogent.Common.Syntax (FieldName, TagName, RepName)
import Cogent.DataLayout.Syntax (SourcePos)

{- PROPERTIES -}

prop_sizePreserved range =
  foldr (\x -> (+) (bitSizeABR x)) 0 (rangeToAlignedRanges range) == bitSizeBR range
  
prop_roundTrip range =
  case (alignedRangesToRanges . rangeToAlignedRanges) range of
    [range'] -> range == range'
    _        -> False
  
{- FUNCTIONS -}

-- A partial inverse to rangeToAlignedRanges
alignedRangesToRanges
  :: [AlignedBitRange]
  -> [BitRange]
alignedRangesToRanges = merge . fmap alignedRangeToRange 
  where
    alignedRangeToRange :: AlignedBitRange -> BitRange
    alignedRangeToRange AlignedBitRange { bitSizeABR, wordOffsetABR, bitOffsetABR } =
      BitRange
      { bitSizeBR = bitSizeABR
      , bitOffsetBR = wordOffsetABR * wordSizeBits + bitOffsetABR
      }
      
    merge :: [BitRange] -> [BitRange]
    merge [] = []
    merge (range1 : rest) = case merge rest of
      [] -> range1 : []
      range2 : rest'
        | bitOffsetBR range2 == bitOffsetBR range1 + bitSizeBR range1 ->
            BitRange
            { bitOffsetBR = bitOffsetBR range1
            , bitSizeBR   = bitSizeBR range1 + bitSizeBR range2
            }
            : rest'
        | otherwise -> range1 : range2 : rest'
    
{- ARBITRARY INSTANCES -}
instance Arbitrary BitRange where
  arbitrary = sized $ \totalSize -> do
    let totalSize' = fromIntegral totalSize
    offset    <- choose (0, (max (totalSize' - 1) 0))
    size      <- choose (1, (max (totalSize' - offset) 1))
    return $ BitRange size offset

{- GENERATORS -}
-- Generates a valid datalayout
genDataLayout
  :: Int -- For sizing
  -> DataLayoutPath -- Path to new layout
  -> Gen (DataLayout BitRange, Allocation)
genDataLayout n path = genDataLayout' (fromIntegral n) n path []

genDataLayout'
  :: Integer -- max allowed allocated bit index
  -> Int -- max allowed total bit size of the layout
  -> DataLayoutPath -- path in the DataLayout to this sublayout
  -> Allocation -- existing allocation
  -> Gen (DataLayout BitRange, Allocation)
genDataLayout' maxBitIndex maxSize path alloc = 
  if maxSize == 0
  then return (UnitLayout, alloc)
  else oneof
    [ genPrimLayout   maxBitIndex maxSize path alloc
    , genSumLayout    maxBitIndex maxSize path alloc
    , genRecordLayout maxBitIndex maxSize path alloc
    ]
        
genPrimLayout
  :: Integer -- max allowed allocated bit index
  -> Int -- max allowed bit size for the range
  -> DataLayoutPath -- Path to the prim layout
  -> Allocation -- Existing allocation
  -> Gen (DataLayout BitRange, Allocation)
genPrimLayout maxBitIndex maxSize path alloc = do
  (range, alloc') <- genBitRange maxBitIndex maxSize alloc path
  return (PrimLayout range, alloc')
    
genSumLayout
  :: Integer -- max allowed allocated bit index
  -> Int -- max allowed total bit size for the records fields
  -> DataLayoutPath -- Path to the record in the DataLayout
  -> Allocation -- Existing allocation
  -> Gen (DataLayout BitRange, Allocation)
genSumLayout maxBitIndex maxSize path alloc =
  do
    let maxTagSize = min 4 maxSize
    (tagBitRange, alloc') <- genBitRange maxBitIndex maxTagSize alloc path
    let maxNumAlternatives = 2^(bitSizeBR tagBitRange)
    (alts, alloc'') <- genAlts (maxSize - maxTagSize) 0 maxNumAlternatives alloc'
    return (SumLayout tagBitRange alts, alloc'')
  where
    genAlts
      :: Int -- max allowed total bit size for remaining fields
      -> Integer -- tag value for alternative
      -> Integer -- max number of alternatives
      -> Allocation -- existing allocation
      -> Gen (Map TagName (Integer, DataLayout BitRange, SourcePos), Allocation)
            
    genAlts 0 _ _ alloc          = return (M.empty, alloc)
    genAlts _ m n alloc | m == n = return (M.empty, alloc)
        
    genAlts maxSize tagValue maxTagValue alloc = do
      altSize <- choose (1, maxSize)
      (remainingAlts, remainingAlloc) <- genAlts (maxSize - altSize) (tagValue + 1) maxTagValue alloc
      let altName = show tagValue
      (altLayout, altAlloc) <- genDataLayout' maxBitIndex altSize (InAlt altName () path) alloc
      return $ (M.insert altName (tagValue, altLayout, ()) remainingAlts, altAlloc ++ remainingAlloc)

    
genRecordLayout
  :: Integer -- max allowed allocated bit index
  -> Int -- max allowed total bit size for the records fields
  -> DataLayoutPath -- Path to the record in the DataLayout
  -> Allocation -- Existing allocation
  -> Gen (DataLayout BitRange, Allocation)
genRecordLayout maxBitIndex maxSize path alloc =
  do
    (fields, alloc') <- genFields maxSize 0 alloc
    return (RecordLayout fields, alloc')
  where
    genFields
      :: Int -- max allowed total bit size for remaining fields
      -> Int -- for generating unique field names
      -> Allocation -- existing allocation
      -> Gen (Map FieldName (DataLayout BitRange, SourcePos), Allocation)
            
    genFields 0 _ alloc = return (M.empty, alloc)
    genFields maxSize name alloc = do
      fieldSize <- choose (1, maxSize)
      (remainingFields, alloc') <- genFields (maxSize - fieldSize) (name + 1) alloc
      let fieldName = show name
      (fieldLayout, alloc'') <- genDataLayout' maxBitIndex fieldSize (InField fieldName () path) alloc'
      return $ (M.insert fieldName (fieldLayout, ()) remainingFields, alloc'')


-- Generates an unallocated BitRange
-- of size at most the requested allocSize
-- and the corresponding new allocation
genBitRange
  :: Integer -- Max allowed bit index
  -> Int -- Max size for the new range
  -> Allocation -- Existing allocation which range must not overlap
  -> DataLayoutPath -- Path to range in the DataLayout
  -> Gen (BitRange, Allocation)
genBitRange maxBitIndex maxSize accumAlloc pathToRange = do
  let allRanges      = allNonAllocatedRanges maxBitIndex accumAlloc pathToRange
  let allSizedRanges = filter ((<= fromIntegral maxSize) . bitSizeBR . fst) allRanges
  elements allSizedRanges

-- Enumerates all bitranges from smallest last bit index to maxBitIndex
allNonEmptyRanges :: Integer -> [BitRange]
allNonEmptyRanges maxBitIndex = do
  lastBitIndex <- [1 .. maxBitIndex]
  size      <- [1 .. lastBitIndex]
  let offset = lastBitIndex - size
  return $ BitRange size offset
  
-- Enumerates all ranges which are not allocated in the given Allocation
allNonAllocatedRanges
  :: Integer -- Max allowed bit index
  -> Allocation -- Existing allocation
  -> DataLayoutPath -- Path to new range
  -> [(BitRange, Allocation)] -- All possible new (range, allocation) pairs
allNonAllocatedRanges maxBitIndex alloc path = do
  range <- allNonEmptyRanges maxBitIndex
  case [(range, path)] /\ alloc of
    Left _         -> []
    Right newAlloc -> return (range, newAlloc)


return []
testAll = $quickCheckAll

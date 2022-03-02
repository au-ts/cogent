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

{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TemplateHaskell #-}
module CogentTests.Dargent.Core where

import Control.Arrow (first)
import Data.Map (Map)
import Data.List as List
import qualified Data.Map as M
import Text.Parsec.Pos (SourcePos)
import Test.QuickCheck

import Cogent.Common.Syntax (FieldName, TagName, RepName, Size)
import Cogent.Dargent.Allocation
import Cogent.Dargent.Core
import Cogent.Dargent.Surface (Endianness(..))
import Cogent.Dargent.TypeCheck
import Cogent.Dargent.Util
import Cogent.Surface (noPos)

import Debug.Trace


possiblePrimBitSizes = [0, 1, 8, 16, 32, 64]

{- PROPERTIES -}

prop_sizePreserved range =
  foldr (\x -> (+ bitSizeABR x)) 0 (rangeToAlignedRanges wordSizeBits range) == bitSizeBR range

prop_roundTrip range =
  case (alignedRangesToRanges . rangeToAlignedRanges wordSizeBits) range of
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
  :: Size -- For sizing
  -> Gen (DataLayout BitRange, Allocation)
genDataLayout n = first Layout <$> genDataLayout' n n (Allocation [])

genDataLayout'
  :: Size -- max allowed allocated bit index
  -> Size -- max allowed total bit size of the layout
  -> Allocation -- existing allocation
  -> Gen (DataLayout' BitRange, Allocation)
genDataLayout' maxBitIndex maxSize alloc =
  if maxSize == 0 -- || maxBitIndex = 0
  then return (UnitLayout, alloc)
  else
    let primWeight = 
         if maxSize <= 16 then
           -- 15
           10
         else if maxSize <= 32 then
           -- 12
           5
          else
            4
    in
      frequency
      [ (primWeight, genPrimLayout   maxBitIndex maxSize alloc)
      , (1         , genSumLayout    maxBitIndex maxSize alloc)
      , (1         , genRecordLayout maxBitIndex maxSize alloc)
      ]

genPrimLayout
  :: Size -- max allowed allocated bit index
  -> Size -- max allowed bit size for the range
  -> Allocation -- Existing allocation
  -> Gen (DataLayout' BitRange, Allocation)
genPrimLayout maxBitIndex maxSize alloc = do
  (range, alloc') <- genBitRangeAllowed maxBitIndex 
      (\n -> n <= fromIntegral maxSize &&
         List.elem n possiblePrimBitSizes )       
      alloc
  return (PrimLayout range ME, alloc')

genSumLayout
  :: Size -- max allowed allocated bit index
  -> Size -- max allowed total bit size for the variant constructors
  -> Allocation -- Existing allocation
  -> Gen (DataLayout' BitRange, Allocation)
genSumLayout maxBitIndex maxSize alloc =
    let maxTagSize = min 4 maxSize in
    let dSize = maxSize - maxTagSize in
    if dSize == 0 then
      genPrimLayout maxBitIndex maxSize alloc
    else do
      (tagBitRange, alloc') <- genBitRange maxBitIndex maxTagSize alloc
      let alloc''            = fmap InTag alloc'
      let maxNumAlternatives = 2^(bitSizeBR tagBitRange)
      (alts, alloc''') <- genAlts dSize 0 maxNumAlternatives alloc''
      return (SumLayout tagBitRange alts, alloc''')
  {-
  do
    let maxTagSize = min 4 maxSize
    (tagBitRange, alloc') <- genBitRange maxBitIndex maxTagSize alloc
    let alloc''           = fmap InTag alloc'
    let noAlts = 2 ^ bitSizeBR tagBitRange
    -- FIXME: Add offset sugar for 0b offset alternatives.
    (alts, alloc''') <-
      first swizzle <$> genAlts (maxSize - maxTagSize) (noAlts - 1) ([],alloc'') alloc''
    return (SumLayout tagBitRange alts, alloc''')
    -}
  where
    swizzle :: [(TagName, Size, DataLayout' BitRange)] ->
      Map TagName (Size, DataLayout' BitRange)
    swizzle ts = M.fromList $ map (\(t,p,d) -> (t,(p,d))) ts

    genAlts _ m n alloc | m == n = return (M.empty, alloc)

    genAlts maxSize tagValue maxTagValue alloc = do
      sourcePos <- arbitrary
      altSize <- if 1 <= maxSize then choose (1, maxSize) else return 0
      (remainingAlts, remainingAlloc) <- genAlts (maxSize - altSize) (tagValue + 1) maxTagValue alloc
      let altName = "Con" ++ show tagValue
      (altLayout, altAlloc) <- genDataLayout' maxBitIndex altSize alloc
      let altAlloc' = fmap (InAlt altName sourcePos) altAlloc
      return (M.insert altName (tagValue, altLayout) remainingAlts, altAlloc' \/ remainingAlloc)
      {-
    genAlts
      :: Size     -- max allowed total bit size for remaining constrs.
      -> Size     -- tag value for alternative
      -> ([(TagName, Size, DataLayout' BitRange)], Allocation) -- accumlated state
      -> Allocation -- tag allocation
      -> Gen ([(TagName, Size, DataLayout' BitRange)], Allocation)

    genAlts _ tag (ts,alloc) _ | tag < 0 = return (ts, alloc)

    genAlts max tag (ts,alloc) tagAlloc = do
      sz <- if 1 <= max then choose (1, max) else return 0
      (altLayout, altAlloc) <- genDataLayout' maxBitIndex sz tagAlloc
      let tagName = show tag
          altAlloc' = fmap (InAlt tagName noPos) altAlloc
      genAlts (max - sz) (tag - 1)
        ((tagName,tag,altLayout):ts, altAlloc' \/ alloc) tagAlloc
        -}

genRecordLayout
  :: Size -- max allowed allocated bit index
  -> Size -- max allowed total bit size for the records fields
  -> Allocation -- Existing allocation
  -> Gen (DataLayout' BitRange, Allocation)
genRecordLayout maxBitIndex maxSize alloc =
  do
    (fields, alloc') <- genFields maxSize 0 alloc
    -- FIXME: Add offset sugar for 0b offset fields
    return (RecordLayout fields, alloc')
  where
    genFields
      :: Size -- max allowed total bit size for remaining fields
      -> Size -- for generating unique field names
      -> Allocation -- existing allocation
      -> Gen (Map FieldName (DataLayout' BitRange), Allocation)

    genFields 0 _ alloc = return (M.empty, alloc)
    genFields maxSize name alloc = do
      fieldSize <- choose (1, maxSize)
      (remainingFields, alloc') <- genFields (maxSize - fieldSize) (name + 1) alloc
      let fieldName = "field" ++ show name
      (fieldLayout, alloc'') <- genDataLayout' maxBitIndex fieldSize alloc'
      let alloc''' = fmap (InField fieldName noPos) alloc''
      return $ (M.insert fieldName fieldLayout remainingFields, alloc''')


-- Generates an unallocated BitRange
-- of size at most the requested allocSize
-- and the corresponding new allocation
genBitRange
  :: Size -- Max allowed bit index
  -> Size -- Max size for the new range
  -> Allocation -- Existing allocation which range must not overlap
  -- -> [Size] -- List of allowed sizes, by order of preference
  -> Gen (BitRange, Allocation)
genBitRange maxBitIndex maxSize =
  genBitRangeAllowed maxBitIndex (\ s -> s <= fromIntegral maxSize)

-- Generates an unallocated BitRange
-- of the biggest size that is allowed
-- and the corresponding new allocation
genBitRangeAllowed
  :: Size -- Max allowed bit index
  -> (Size -> Bool) -- allowed sizes    
  -> Allocation -- Existing allocation which range must not overlap
  -- -> [Size] -- List of allowed sizes, by order of preference
  -> Gen (BitRange, Allocation)
genBitRangeAllowed maxBitIndex allowedSizes accumAlloc =
  let allRanges      = allNonAllocatedRanges maxBitIndex accumAlloc in
  let allSizedRanges = filter (allowedSizes . bitSizeBR . fst) allRanges in
  let maxRange = maximumBy (\ (a, _) (b, _) -> compare (bitSizeBR a) (bitSizeBR b)) allSizedRanges in
  -- let smallerAllowedSizes = filter (((<=) fromIntegral maxSize) . bitSizeBR . fst ) in
  return maxRange
  -- oneof [return maxRange -- ,
  --        -- return maxRange,
  --        -- elements allSizedRanges
  --       ] 

-- Enumerates all bitranges from smallest last bit index to maxBitIndex
allNonEmptyRanges :: Size -> [BitRange]
allNonEmptyRanges maxBitIndex = do
  lastBitIndex  <- [1 .. maxBitIndex]
  size          <- [1 .. lastBitIndex]
  let offset    =  lastBitIndex - size
  return $ BitRange size offset

-- Enumerates all ranges which are not allocated in the given Allocation
allNonAllocatedRanges
  :: Size -- Max allowed bit index
  -> Allocation -- Existing allocation
  -> [(BitRange, Allocation)] -- All possible new (range, allocation) pairs
allNonAllocatedRanges maxBitIndex alloc = do
  range <- allNonEmptyRanges maxBitIndex
  case Allocation [(range, PathEnd)] /\ alloc of
    Right newAlloc -> return (range, newAlloc)
    _              -> []

return []
testAll = $quickCheckAll

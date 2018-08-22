{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Cogent.DataLayout.TypeCheck where

import Data.Map (Map)
import qualified Data.Map as M

import Control.Monad (guard)

import Cogent.Util (mapAccumLM)
import Cogent.Common.Syntax (FieldName, TagName, RepName)
import Text.Parsec.Pos (SourcePos)
import Cogent.DataLayout.Core
import Cogent.DataLayout.Surface

{-+ Data layouts go through two phases of type checking.
  | 1. When surface `RepDecl` syntax trees are converted to core `DataLayout` syntax trees
  | 2. After monomorphisation, for every type `Ptr T L`, we check the type `T` matches the layout `L`
  +-}

-- A path from a particular part of a RepDecl/DataLayout tree to the root decl.
--
-- Allows errors messages to pinpoint the exact location where the error occurred.
data DataLayoutPath
  = InField FieldName SourcePos DataLayoutPath
  | InTag   DataLayoutPath
  | InAlt   TagName SourcePos DataLayoutPath
  | InDecl  RepName SourcePos
  deriving (Eq, Show, Ord)
 
{- SURFACE (RepDecl) TO CORE (DataLayout) -}  

-- Transforms the surface RepDecl syntax tree to the core DataLayout abstract syntax tree
-- The RepDecl being checked may contain references to any already declared Rep's in the Map.
-- If so, we use the corresponding DataLayout and Allocation from the Map in place of that Rep reference.
dataLayoutSurfaceToCore
  :: Map RepName (DataLayout BitRange, Allocation, RepDecl)
  -> RepDecl
  -> Either DataLayoutSurfaceToCoreError (DataLayout BitRange, Allocation)
dataLayoutSurfaceToCore env (RepDecl repPos repName repExpr) = evalRepExpr (InDecl repName repPos) repExpr
  where
    evalRepExpr :: DataLayoutPath -> RepExpr -> Either DataLayoutSurfaceToCoreError (DataLayout BitRange, Allocation)
    
    evalRepExpr path (RepRef n) =
      case M.lookup n env of 
        Just (layout, allocation, _) -> Right (layout, allocation)
        Nothing                      -> Left $ UnknownRepr n path
            
    evalRepExpr path (Prim size) =
      if bitSize == 0
      then Right (UnitLayout, [])
      else Right (PrimLayout bitRange, [(bitRange, path)])
      where
        bitSize = evalSize size
        bitRange = BitRange bitSize 0
      
    evalRepExpr path (Offset repExpr offsetSize) = do
      (layout, allocation) <- evalRepExpr path repExpr
      return (offset (evalSize offsetSize) layout, offset (evalSize offsetSize) allocation)
        
    evalRepExpr path (Record fields) = do
      (alloc, fields') <- mapAccumLM evalField [] fields
      return (RecordLayout $ M.fromList fields', alloc)
      where
        evalField
          :: Allocation -- The accumulated allocation from previous alternatives
          -> (FieldName, SourcePos, RepExpr)
          -> Either DataLayoutSurfaceToCoreError (Allocation, (FieldName, (DataLayout BitRange, SourcePos)))
            
        evalField accumAlloc (fieldName, pos, repExpr) = do
          (fieldLayout, fieldAlloc) <- evalRepExpr (InField fieldName pos path) repExpr
          alloc                     <- accumAlloc /\ fieldAlloc
          return (alloc, (fieldName, (fieldLayout, pos)))
              
    evalRepExpr path (Variant tagExpr alternatives) = do
      (tagLayout, tagAlloc) <- evalRepExpr (InTag path) tagExpr
      case (tagLayout, tagAlloc) of 
        (PrimLayout tagBits, [_]) -> do
          ((altsAlloc, _), alternatives') <- mapAccumLM (evalAlternative tagBits) ([], M.empty) alternatives
          alloc                           <- tagAlloc /\ altsAlloc
          return (SumLayout tagBits $ M.fromList alternatives', alloc)
        _ -> Left $ TagNotSingleBlock (InTag path)
      where
        evalAlternative
          :: BitRange -- Of the variant's tag
          -> (Allocation, Map Integer TagName) -- The accumulated (allocation, set of used tag values) from already evaluated alternatives
          -> (TagName, SourcePos, Integer, RepExpr) -- The alternative to evaluate
          -> Either DataLayoutSurfaceToCoreError ((Allocation, Map Integer TagName), (TagName, (Integer, DataLayout BitRange, SourcePos)))
          
        evalAlternative range (accumAlloc, accumTagValues) (tagName, pos, tagValue, repExpr) = do
          (layout, alternativeAlloc)  <- evalRepExpr (InAlt tagName pos path) repExpr
          alloc                       <- accumAlloc \/ alternativeAlloc
          tagValues                   <- checkedTagValues
          return ((alloc, tagValues), (tagName, (tagValue, layout, pos)))
          where
            checkedTagValues :: Either DataLayoutSurfaceToCoreError (Map Integer TagName)
            checkedTagValues
              | tagValue < 0 || tagValue >= 2^(bitSizeBR range) =
                  Left $ OversizedTagValue path range tagName tagValue
              | Just conflictingTagName <- tagValue `M.lookup` accumTagValues =
                  Left $ SameTagValues path conflictingTagName tagName tagValue
              | otherwise =
                  Right $ M.insert tagValue tagName accumTagValues
          
    evalSize :: RepSize -> Integer
    evalSize (Bytes b) = b * 8
    evalSize (Bits b)  = b
    evalSize (Add a b) = evalSize a + evalSize b
    
-- Errors when transforming surface layout syntax trees (RepDecls)
-- to core DataLayout abstract syntax trees
data DataLayoutSurfaceToCoreError
  = OverlappingBlocks       (BitRange, DataLayoutPath) (BitRange, DataLayoutPath)
    -- Have declared two overlapping bit ranges which shouldn't overlap
    
  | UnknownRepr             RepName DataLayoutPath
    -- Have referenced a Rep which hasn't been declared
    -- The path is the path to the use of that Rep in the RepExpr being checked
    
  | TagNotSingleBlock       DataLayoutPath
  
  | SameTagValues           DataLayoutPath TagName TagName Integer
    -- Path to two tags in the same variant and their common value
    
  | OversizedTagValue       DataLayoutPath BitRange TagName Integer
    -- Used a tag value which is too large to fit in the variant's tag bit range
    -- Path to the variant, bits for its bit range, name of the alternative, it's tag value
    
  deriving (Eq, Show, Ord)


-- A set of bit indices into a data type.
--
-- Represents the set which is the union of the sets represented by the `BitRange`s in the list.
-- The DataLayoutPath associated with each BitRange is kept so that we can say exactly which ranges overlap in error messages.
type Allocation = [(BitRange, DataLayoutPath)]


-- Disjunction of allocations
--
-- Used when the two allocations will never be used simultaneously, and so they may overlap.
-- For example, if they are allocations for two alternatives of the same variant.
(\/) :: Allocation -> Allocation -> Either DataLayoutSurfaceToCoreError Allocation 
a1 \/ a2 = Right (a1 ++ a2)

-- Conjunction of allocations
--
-- Used when the two allocations could be used simultaneously, and so they must not overlap.
-- For example, if they are allocations for two fields of the same record.
-- An OverlappingBlocks DataLayoutSurfaceToCoreError is returned if the two allocations overlap.
(/\) :: Allocation -> Allocation -> Either DataLayoutSurfaceToCoreError Allocation
a1 /\ a2 =
  case allOverlappingBlocks a1 a2 of
    ((p1, p2) : _) -> Left $ OverlappingBlocks p1 p2
    []             -> Right (a1 ++ a2) 
  where
    allOverlappingBlocks :: Allocation -> Allocation -> [((BitRange, DataLayoutPath), (BitRange, DataLayoutPath))]
    allOverlappingBlocks a b = do
      pair1@(block1, path1) <- a
      pair2@(block2, path2) <- b
      guard $ overlaps block1 block2
      return $ (pair1, pair2)
     
overlaps :: BitRange -> BitRange -> Bool
overlaps (BitRange s1 o1) (BitRange s2 o2) =
  s1 > 0 &&
  s2 > 0 &&
  ((o1 >= o2 && o1 < (o2 + s2)) || 
   (o2 >= o1 && o2 < (o1 + s1)))

-- When transforming (Offset repExpr offsetSize),
-- we want to add offset bits to all blocks inside the repExpr,
-- as well as the allocation corresponding to that repExpr.
class Offsettable a where
  offset :: Integer -> a -> a
  
instance Offsettable BitRange where
  offset n range@(BitRange { bitOffsetBR }) = range { bitOffsetBR = bitOffsetBR + n}
  
instance Offsettable Block where
  offset n (DataBlock range) = DataBlock $ offset n range
  offset n block             = block
  
instance Offsettable a => Offsettable (DataLayout a) where
  offset n = fmap (offset n)
  
instance Offsettable Allocation where
  offset n = fmap $ \(range, path) -> (offset n range, path)



{- MATCHING DATALAYOUT AND TYPE -}

-- Errors when checking a DataLayout matches a Type
data DataLayoutTypeMatchError
  = FieldMissing          DataLayoutPath FieldName
  -- Path to the record with a missing field, and expected name of the field
  | FieldUnknown          DataLayoutPath
  -- Path to the unknown field in a record
  | AltMissing            DataLayoutPath TagName
  -- Path to the variant with the missing alternative, and expected name of the alternative
  | AltUnknown            DataLayoutPath
  -- Path to the unknown alternative in a variant
  | RecordLayoutExpected  DataLayoutPath
  -- Path to where we expect to find a record layout
  | SumLayoutExpected     DataLayoutPath
  -- Path to where we expect to find a sum layout
  | BitLayoutExpected     DataLayoutPath
  -- Path to where we expect to find a bit layout
  | TypeUnsupported       DataLayoutPath
  -- TODO: figure out how to identify parts of a type
  -- Initial implementation won't support embedding all types in a `Ptr T L`
  deriving (Eq, Show, Ord)



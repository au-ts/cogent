{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
module Cogent.DataLayout.TypeCheck where

import Data.Map (Map)
import qualified Data.Map as M

import Control.Monad (guard)

import Cogent.Util (mapAccumLM)
import Cogent.Common.Syntax (FieldName, TagName, DataLayoutName, Size)
import Cogent.Common.Types (Sigil)
import Cogent.DataLayout.Core
import Cogent.DataLayout.Surface
import Cogent.Compiler (__fixme)

import Text.Parsec.Pos (SourcePos)



{- IMPORTANT FUNCTIONS -}
typeCheckDataLayoutExpr
  :: NamedDataLayouts
  -> DataLayoutExpr
  -> ([DataLayoutTypeCheckError], Allocation)
typeCheckDataLayoutExpr _ _ = __fixme ([], [])

-- Normalises the layout remove references to named layouts
normaliseDataLayoutExpr
  :: NamedDataLayouts
  -> DataLayoutExpr
  -> DataLayoutExpr
normaliseDataLayoutExpr _ expr = __fixme expr

{- IMPORTANT TYPES -}
type NamedDataLayouts = Map DataLayoutName (DataLayoutExpr, Allocation)
type DataLayoutTypeCheckError = DataLayoutTypeCheckErrorP DataLayoutPath

-- The type parameter p is the type of the path to the error (DataLayoutPath)
-- We parameterise by p so we can use the functor instance to map changes to the path
data DataLayoutTypeCheckErrorP p
  = OverlappingBlocks       (BitRange, p) (BitRange, p)
    -- Have declared two overlapping bit ranges which shouldn't overlap
    
  | UnknownDataLayout       DataLayoutName p
    -- Have referenced a data layout which hasn't been declared
    -- The path is the path to the use of that Rep in the RepExpr being checked
    
  | TagNotSingleBlock       p
  
  | SameTagValues           p TagName TagName Size
    -- Path to two tags in the same variant and their common value
    
  | OversizedTagValue       p BitRange TagName Size
    -- Used a tag value which is too large to fit in the variant's tag bit range
    -- Path to the variant, bits for its bit range, name of the alternative, it's tag value
    
  deriving (Eq, Show, Ord)

-- Allows errors messages to pinpoint the exact location where the error occurred in a DataLayoutExpr/Decl
data DataLayoutPath
  = InField FieldName SourcePos DataLayoutPath
  | InTag   DataLayoutPath
  | InAlt   TagName SourcePos DataLayoutPath
  | InDecl  DataLayoutName DataLayoutPath
  | PathEnd
  deriving (Eq, Show, Ord)




{- OTHER FUNCTIONS -}
typeCheckDataLayoutDecl
  :: NamedDataLayouts
  -> DataLayoutDecl
  -> ([DataLayoutTypeCheckError], Allocation)

typeCheckDataLayoutDecl _ _ = __fixme ([], [])

normaliseDataLayoutDecl
  :: NamedDataLayouts
  -> DataLayoutDecl
  -> DataLayoutDecl

normaliseDataLayoutDecl _ decl = __fixme decl

-- Normalises the layout in the sigil to remove references to named layouts
normaliseSigil
  :: NamedDataLayouts
  -> Sigil (Maybe DataLayoutExpr)
  -> Sigil (Maybe DataLayoutExpr)

normaliseSigil _ sigil = __fixme sigil


{- ALLOCATIONS -}

-- A set of bit indices into a data type.
--
-- Represents the set which is the union of the sets represented by the `BitRange`s in the list.
type Allocation = [(BitRange, DataLayoutPath)]

-- Disjunction of allocations
--
-- Used when the two allocations will never be used simultaneously, and so they may overlap.
-- For example, if they are allocations for two alternatives of the same variant.
(\/) :: Allocation -> Allocation -> Either DataLayoutTypeCheckError Allocation 
a1 \/ a2 = Right (a1 ++ a2)

-- Conjunction of allocations
--
-- Used when the two allocations could be used simultaneously, and so they must not overlap.
-- For example, if they are allocations for two fields of the same record.
-- An OverlappingBlocks DataLayoutTypeCheckError is returned if the two allocations overlap.
(/\) :: Allocation -> Allocation -> Either DataLayoutTypeCheckError Allocation
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

mapOntoPaths
  :: (DataLayoutPath -> DataLayoutPath)
  -> Allocation
  -> Allocation
mapOntoPaths = fmap . fmap

-- When transforming (Offset repExpr offsetSize),
-- we want to add offset bits to all blocks inside the repExpr,
-- as well as the allocation corresponding to that repExpr.
class Offsettable a where
  offset :: Size -> a -> a
  
instance Offsettable BitRange where
  offset n range@(BitRange { bitOffsetBR }) = range { bitOffsetBR = bitOffsetBR + n}
  
instance Offsettable a => Offsettable (DataLayout a) where
  offset n = fmap (offset n)
  
instance Offsettable Allocation where
  offset n = fmap $ \(range, path) -> (offset n range, path)






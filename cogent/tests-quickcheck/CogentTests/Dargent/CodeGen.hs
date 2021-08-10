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

module CogentTests.Dargent.CodeGen where

import Cogent.C.Render
import Cogent.C.Syntax
import Cogent.Common.Syntax
import Cogent.Dargent.Allocation
import Cogent.Dargent.CodeGen
import Cogent.Dargent.Core
import Cogent.Dargent.Surface (Endianness(..))

import Control.Monad
import Text.PrettyPrint.Mainland.Class as M (pprint)

alignedBitRangeExamples :: [AlignedBitRange]
alignedBitRangeExamples =
  [ AlignedBitRange
    { bitSizeABR    = 1
    , bitOffsetABR  = 0
    , wordOffsetABR = 0
    }
  , AlignedBitRange
    { bitSizeABR    = 1
    , bitOffsetABR  = 0
    , wordOffsetABR = 3
    }
  , AlignedBitRange
    { bitSizeABR    = 1
    , bitOffsetABR  = 4
    , wordOffsetABR = 3
    }
  , AlignedBitRange
    { bitSizeABR    = 8
    , bitOffsetABR  = 0
    , wordOffsetABR = 0
    }
  , AlignedBitRange
    { bitSizeABR    = 4
    , bitOffsetABR  = 4
    , wordOffsetABR = 0
    }
  , AlignedBitRange
    { bitSizeABR    = 4
    , bitOffsetABR  = 2
    , wordOffsetABR = 0
    }
  ]

rangesToComposedRangeInput :: String -> [AlignedBitRange] -> [(AlignedBitRange, FunName)]
rangesToComposedRangeInput functionPrefix ranges =
  zip ranges (fmap (\x -> functionPrefix ++ "Range" ++ show x) [1 ..])


compileSanityCheck :: IO ()
compileSanityCheck = do
  putStrLn "Printing examples of generated C code for visual inspection."
  forM_ alignedBitRangeExamples $ \alignedBitRange -> do
    putStrLn "Cogent aligned range:"
    putStrLn $ show alignedBitRange
    putStrLn "Pretty C getter:"
    pprint $ cExtDecl $ mkGsDeclABR True (CStruct "boxType") alignedBitRange "getFoo" Get
    putStrLn "Pretty C setter:"
    pprint $ cExtDecl $ mkGsDeclABR True (CStruct "boxType") alignedBitRange "setFoo" Set
    putStrLn ""
  putStrLn "List of cogent aligned ranges:"
  putStrLn $ show alignedBitRangeExamples
  putStrLn "Pretty C getter:"
  pprint $ cExtDecl $ mkGsDeclBlock (rangesToComposedRangeInput "get" alignedBitRangeExamples) ME (CStruct "boxType") (CIdent "embeddedType") "getFoo" Get
  putStrLn "Pretty C setter:"
  pprint $ cExtDecl $ mkGsDeclBlock (rangesToComposedRangeInput "set" alignedBitRangeExamples) ME (CStruct "boxType") (CIdent "embeddedType") "setFoo" Set
  putStrLn ""
  recordGetterSanityCheck


recordFieldExamples =
  [ [ ("field1", "getSetField1")
    , ("field2", "getSetField2")
    ]

  , [ ("field1", "getSetField1") ]

  , []
  ]

recordGetterSanityCheck :: IO ()
recordGetterSanityCheck = do
  putStrLn "Printing examples of getters for embedded records:"
  forM_ recordFieldExamples $ \recordFields -> do
    putStrLn "Field names, getter/setter names:"
    putStrLn $ show recordFields
    putStrLn "Pretty C getter:"
    pprint $ cExtDecl $ mkGsDeclRecord recordFields (CStruct "boxType") (CIdent "embeddedType") "getFoo" Get
    putStrLn "Pretty C setter:"
    pprint $ cExtDecl $ mkGsDeclRecord recordFields (CStruct "boxType") (CIdent "embeddedType") "setFoo" Set
  putStrLn ""





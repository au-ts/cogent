module CogentTests.DataLayout.CodeGen where
import Cogent.DataLayout.CodeGen
import Cogent.DataLayout.Core
import Cogent.C.Render
import Cogent.C.Compile
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


compileSanityCheck :: IO ()
compileSanityCheck = do
  putStrLn "Printing examples of generated getters and setters for visual inspection."
  forM_ alignedBitRangeExamples $ \alignedBitRange -> do
    putStrLn "Cogent aligned range:"
    putStrLn $ show alignedBitRange
    putStrLn "Pretty C getter:"
    pprint $ cExtDecl $ genAlignedRangeGetter alignedBitRange "getFoo"
    putStrLn "Pretty C setter:"
    pprint $ cExtDecl $ genAlignedRangeSetter alignedBitRange "setFoo"
    putStrLn ""




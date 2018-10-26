module CogentTests.DataLayout.CodeGen where
import Cogent.DataLayout.CodeGen
import Cogent.DataLayout.Core
import Cogent.C.Render
import Cogent.C.Compile
import Cogent.C.Syntax
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

rangesToComposedRangeInput :: String -> [AlignedBitRange] -> [(AlignedBitRange, CExpr)]
rangesToComposedRangeInput functionPrefix ranges =
  zip ranges (fmap (\x -> CVar (functionPrefix ++ "Range" ++ show x) Nothing) [1 ..])


compileSanityCheck :: IO ()
compileSanityCheck = do
  putStrLn "Printing examples of generated C code for visual inspection."
  forM_ alignedBitRangeExamples $ \alignedBitRange -> do
    putStrLn "Cogent aligned range:"
    putStrLn $ show alignedBitRange
    putStrLn "Pretty C getter:"
    pprint $ cExtDecl $ alignedRangeGetter (CStruct "boxType") alignedBitRange "getFoo"
    putStrLn "Pretty C setter:"
    pprint $ cExtDecl $ alignedRangeSetter (CStruct "boxType") alignedBitRange "setFoo"
    putStrLn ""
  putStrLn "List of cogent aligned ranges:"
  putStrLn $ show alignedBitRangeExamples
  putStrLn "Pretty C getter:"
  pprint $ cExtDecl $ composedAlignedRangeGetter (rangesToComposedRangeInput "get" alignedBitRangeExamples) (CStruct "boxType") (CIdent "embeddedType") "getFoo"
  putStrLn "Pretty C setter:"
  pprint $ cExtDecl $ composedAlignedRangeSetter (rangesToComposedRangeInput "set" alignedBitRangeExamples) (CStruct "boxType") (CIdent "embeddedType") "setFoo"
  putStrLn ""
  recordGetterSanityCheck






recordFieldExamples =
  [ [ ("field1", CVar "getSetField1" Nothing)
    , ("field2", CVar "getSetField2" Nothing)]
  
  , [("field1", CVar "getSetField1" Nothing)]
  
  , []
  ]


recordGetterSanityCheck :: IO ()
recordGetterSanityCheck = do
  putStrLn "Printing examples of getters for embedded records:"
  forM_ recordFieldExamples $ \recordFields -> do
    putStrLn "Field names, getter/setter names:"
    putStrLn $ show recordFields
    putStrLn "Pretty C getter:"
    pprint $ cExtDecl $ recordGetter recordFields (CStruct "boxType") (CIdent "embeddedType") "getFoo"
    putStrLn "Pretty C setter:"
    pprint $ cExtDecl $ recordSetter recordFields (CStruct "boxType") (CIdent "embeddedType") "getFoo"
  putStrLn ""
    




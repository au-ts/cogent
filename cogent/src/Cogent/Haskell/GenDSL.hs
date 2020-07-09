-- -----------------------------------------------------------------------
-- Cogent PBT: Simple DSL
-- -----------------------------------------------------------------------
module Cogent.Haskell.GenDSL where

data ICType = Pointer
            | CList 
            | Tree
            -- | Bag
            | Int
            | Word32 
            | String
            deriving (Show)

data FuncInfo = FuncInfo { name :: String
                         , ispure :: Bool
                         , nondet :: Bool
                         , ictype :: ICType
                         } deriving (Show)

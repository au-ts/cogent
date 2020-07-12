{-# LANGUAGE DuplicateRecordFields #-}

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

data IAType a = InputA (Int, Int)
              | IOther a
              deriving Show

data OAType a = OutputA (Int, Int)
              | OOther a
              deriving Show


data FuncInfo = FuncInfo { name :: String
                         , ispure :: Bool
                         , nondet :: Bool
                         , ictype :: ICType
                         } deriving (Show)

data FunInfo = FunInfo { ispure :: Bool
                       , nondet :: Bool
                       } deriving (Show)

data FunTypes = FunTypes { ia :: String
                         , oa :: String
                         } deriving (Show)

data FunRels = FunRels { ai     :: String
                       , ro     :: String
                       } deriving (Show)

data PBTInfo = PBTInfo { fname :: String
                       , finfo :: FunInfo
                       , ftys  :: FunTypes
                       , frels :: FunRels
                       } deriving (Show)

data PBTInfoList = PBTInfoList [PBTInfo]

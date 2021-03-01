{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TemplateHaskell #-}

-- -----------------------------------------------------------------------
-- Cogent PBT: Simple DSL
-- -----------------------------------------------------------------------
module Cogent.Haskell.GenDSL where
import Language.Haskell.Exts
import Language.Haskell.Exts.SrcLoc
import Data.Map
import Lens.Micro
import Lens.Micro.TH

data PBTInfo = PBTInfo { fname :: String
                       , finfo :: FunDefs -- Info
                       , fabsf :: FunDefs --AbsF
                       , frrel :: FunDefs --RRel
                       -- , fwelf :: FunWelF
                       } deriving (Show)

data FunDefs = FunInfo { ispure :: Bool
                       , nondet :: Bool } 
             | FunAbsF { absf  :: (String, [String])
                       , ityps :: [(String, Type ())] } 
             | FunRRel { rrel  :: (String, [String])
                       , otyps :: [(String, Type ())] } 
             deriving (Show)

-- map fieldNames to either Exp
-- key = FieldName
-- val = with be either a int or another map
--       this int represents position in the current structure
-- help with build lens view / set

-- for generators, as each group has differing syntax for views
data GroupTag = HsTuple
                | HsRecord 
                | HsVariant
                | HsList
                | HsPrim
                deriving (Show)

data HsEmbedLayout = HsEmbedLayout 
    { _hsTyp :: Type ()
    , _grTag :: GroupTag
    , _fieldMap :: Map String (Either Int HsEmbedLayout)
    } deriving (Show)

makeLenses ''HsEmbedLayout

-- TODO: update/include in FunDefs
data FunWelF = FunWelF { welf :: (String, [String])
                       , typs :: [(String, [String])]
                       } deriving (Show)

{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TemplateHaskell #-}

module Cogent.Haskell.PBT.Types where
import qualified Language.Haskell.Exts as HS
import Language.Haskell.Exts.SrcLoc
import Data.Map
import Lens.Micro
import Lens.Micro.TH

-- | Cogent HS embedding Layout type
-- -----------------------------------------------------------------------
-- | used in analysing the types ic/ia/oc/oa when building abstraction
-- | function and refinement relation

data GroupTag = HsTuple | HsRecord | HsVariant | HsList | HsPrim | Unknown deriving (Show)

data HsEmbedLayout = HsEmbedLayout 
    { _hsTyp :: HS.Type ()
    , _grTag :: GroupTag
    , _fieldMap :: Map String (Either Int HsEmbedLayout)
    } deriving (Show)

makeLenses ''HsEmbedLayout

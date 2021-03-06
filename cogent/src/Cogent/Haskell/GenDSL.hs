{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TemplateHaskell #-}

module Cogent.Haskell.GenDSL where
import qualified Language.Haskell.Exts as HS
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
                       , ityps :: [(String, HS.Type ())] } 
             | FunRRel { rrel  :: (String, [String])
                       , otyps :: [(String, HS.Type ())] } 
             deriving (Show)

-- TODO: update/include in FunDefs
data FunWelF = FunWelF { welf :: (String, [String])
                       , typs :: [(String, [String])]
                       } deriving (Show)

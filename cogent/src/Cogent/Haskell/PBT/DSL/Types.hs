{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TemplateHaskell #-}

module Cogent.Haskell.PBT.DSL.Types where
import qualified Language.Haskell.Exts as HS
import Language.Haskell.Exts.SrcLoc
import Data.Map
import Lens.Micro
import Lens.Micro.TH

-- | PBT Description DSL type
-- -----------------------------------------------------------------------
-- | contains info parsed in from PBT Description DSL

data PbtDescStmt = PbtDescStmt { _name :: String
                               , _decls :: [PbtDescDecl]
                               } deriving (Show)

data PbtDescDecl = PbtDescDecl { _kword :: PbtKeyword
                               , _exprs :: [PbtDescExpr]
                               } deriving (Show)

data PbtDescExpr = PbtDescExpr { _var :: Maybe PbtKeyvars 
                               , _exp :: HS.Exp ()
                               } deriving Show

data PbtKeyword = Absf | Rrel | Welf | Pure | Nond deriving Show
data PbtKeyvars = Ic | Ia | Oc | Oa deriving Show

makeLenses ''PbtDescStmt

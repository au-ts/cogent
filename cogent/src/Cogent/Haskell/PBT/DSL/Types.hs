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

data PbtDescStmt = PbtDescStmt { _funcname :: String
                               , _decls :: [PbtDescDecl]
                               } deriving (Show)

data PbtDescDecl = PbtDescDecl { _kword :: PbtKeyword
                               , _kexprs :: [PbtDescExpr]
                               } deriving (Show)

data PbtDescExpr = PbtDescExpr { _kvar :: Maybe PbtKeyvars 
                               , _kexp :: Either (HS.Type ()) (HS.Exp ())
                               } deriving Show

data PbtKeyword = Absf | Rrel | Welf | Pure | Nond deriving (Show, Eq)
data PbtKeyvars = Ic | Ia | Oc | Oa deriving (Show, Eq)

makeLenses ''PbtDescStmt
makeLenses ''PbtDescDecl
makeLenses ''PbtDescExpr

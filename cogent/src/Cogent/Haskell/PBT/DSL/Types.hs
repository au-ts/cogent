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

data PbtDescExpr = PbtDescExpr { _kident :: Maybe PbtKeyidents 
                               , _rhsExp :: Maybe (HS.Exp ())
                               , _kexp :: Maybe (Either (HS.Type ()) (HS.Exp ()))
                               } deriving Show

data PbtKeyword = Absf | Rrel | Welf | Pure | Nond | Spec 
                deriving (Show, Eq, Ord)
data PbtKeyidents = Ic | Ia | Oc | Oa | Pred 
                  deriving (Show, Eq, Ord)

makeLenses ''PbtDescStmt
makeLenses ''PbtDescDecl
makeLenses ''PbtDescExpr

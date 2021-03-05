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
                | Unknown
                deriving (Show)

data HsEmbedLayout = HsEmbedLayout 
    { _hsTyp :: HS.Type ()
    , _grTag :: GroupTag
    , _fieldMap :: Map String (Either Int HsEmbedLayout)
    } deriving (Show)

makeLenses ''HsEmbedLayout



-- PBT Description AST
-- -----------------------------------------------------------------------
-- contains info parsed in from PBT Description DSL

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







-- TODO: update/include in FunDefs
data FunWelF = FunWelF { welf :: (String, [String])
                       , typs :: [(String, [String])]
                       } deriving (Show)

{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TemplateHaskell #-}

module Cogent.Haskell.PBT.Types where

import Cogent.Haskell.PBT.DSL.Types
import Cogent.Compiler (__impossible)

import Language.Haskell.Exts.SrcLoc
import qualified Language.Haskell.Exts as HS
import qualified Data.Map as M
import Data.List (find)
import Data.Maybe (fromMaybe)

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
    , _fieldMap :: M.Map String (Either Int HsEmbedLayout)
    } deriving (Show)

makeLenses ''HsEmbedLayout



-- | Helper functions for accessing structure
-- -----------------------------------------------------------------------
findExprsInDecl :: PbtKeyword -> [PbtDescDecl] -> [PbtDescExpr]
findExprsInDecl x ds = let res = fromMaybe (__impossible "No expression found!") $ find (\d -> case d ^. kword of x -> True; _ -> False) ds
                         in res ^. kexprs

-- find ic/ia/oc/oa type and expression
findKvarsInDecl :: PbtKeyword -> PbtKeyidents -> [PbtDescDecl] -> (PbtKeyidents, Maybe (HS.Type ()), Maybe (HS.Exp ()))
findKvarsInDecl x y ds
    = let decl = case find (\d -> (d ^. kword) == x) ds of
                   Just x -> x
                   Nothing -> __impossible $ "The decl: "++show x++ " was not specified"
          exprs = filter (\e -> case e ^. kident of
                             Just y' -> y' == y; _ -> False
                  ) $ decl ^. kexprs
          in ( y
               -- find ty
             , (exprs ^.. each . kexp . _Just . _Left) ^? ix 0
               -- find mapping exp associated with this keyvar
             , (exprs ^.. each . kexp . _Just . _Right) ^? ix 0 )

checkBoolE :: [PbtDescExpr] -> Bool
checkBoolE a = case (a ^.. each . kexp . _Just . _Left) ^? ix 0 of
                     Just x -> boolResult x
                     _ -> False

boolResult :: HS.Type () -> Bool
boolResult (HS.TyCon _ (HS.UnQual _ (HS.Ident _ n))) = read n
boolResult _ = False

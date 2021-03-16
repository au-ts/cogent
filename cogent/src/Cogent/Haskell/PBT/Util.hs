{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TemplateHaskell #-}

module Cogent.Haskell.PBT.Util where

import Cogent.Haskell.PBT.DSL.Types
import Cogent.Compiler (__impossible)

import Language.Haskell.Exts.SrcLoc
import qualified Language.Haskell.Exts as HS
import qualified Data.Map as M
import Data.List (find)
import Data.Maybe (fromMaybe)
import Debug.Trace

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
    , _prevGrTag :: GroupTag
    , _fieldMap :: M.Map String (Either Int HsEmbedLayout)
    } deriving (Show)

makeLenses ''HsEmbedLayout



-- | Helper functions for accessing structure
-- -----------------------------------------------------------------------
findExprsInDecl :: PbtKeyword -> [PbtDescDecl] -> [PbtDescExpr]
findExprsInDecl kw ds = fromMaybe (__impossible "No expression found!") $ 
                          (find (\d -> d ^. kword == kw) ds) <&> (^. kexprs)

-- find ic/ia/oc/oa type and expression
findKIdentTyExp :: PbtKeyword -> PbtKeyidents -> [PbtDescDecl] -> (Maybe (HS.Type ()), Maybe (HS.Exp ()))
findKIdentTyExp kw kid ds
    = let declExprs = fromMaybe [] $ (find (\d -> d ^. kword == kw) ds) <&> (^. kexprs)
          exprs = filter (\e -> case e ^. kident of
                             Just kid' -> kid' == kid; _ -> False
                  ) $ declExprs
          in ( (exprs ^.. each . kexp . _Just . _Left) ^? ix 0    -- find ty
             , (exprs ^.. each . kexp . _Just . _Right) ^? ix 0 ) -- find mapping exp associated with this keyvar


-- find ic/ia/oc/oa map expression, maybe lhs transform on kid and maybe rhs transform on kid.
findKIdentExp :: PbtKeyword -> PbtKeyidents -> [PbtDescDecl] -> (Maybe (HS.Exp ()), Maybe (HS.Exp ()))
findKIdentExp kw kid ds
    = let declExprs = fromMaybe [] $ (find (\d -> (d ^. kword) == kw) ds) <&> (^. kexprs)
          exprs = filter (\e -> case e ^. kident of
                             Just kid' -> kid' == kid; _ -> False
                  ) $ declExprs
          in ( (exprs ^.. each . rhsExp . _Just) ^? ix 0
             , (exprs ^.. each . kexp . _Just . _Right) ^? ix 0 )

checkBoolE :: [PbtDescExpr] -> Bool
checkBoolE a = case (a ^.. each . kexp . _Just . _Left) ^? ix 0 of
                     Just x -> boolResult x
                     _ -> False

boolResult :: HS.Type () -> Bool
boolResult (HS.TyCon _ (HS.UnQual _ (HS.Ident _ n))) = read n
boolResult _ = False

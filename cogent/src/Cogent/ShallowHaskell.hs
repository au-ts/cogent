--
-- Copyright 2017, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}


module Cogent.ShallowHaskell where

import Cogent.Common.Syntax
import Cogent.Shallow
import Cogent.Sugarfree as S
import Cogent.Util (Stage(..), Warning)

import Control.Applicative
import Data.Either (lefts, rights)
import Data.List as L
import Language.Haskell.TH.Syntax
import Prelude as P

data HaskellModule = HM Module ModuleInfo [Dec]
                   deriving (Show)

shhm :: Module
shhm = undefined

sshm :: Module
sshm = undefined

shallowDefinitionsH = undefined

shallowTypeFromTableH = undefined

shallowFileH :: String -> Stage -> [Definition TypedExpr VarName]
             -> SG (HaskellModule, HaskellModule)
shallowFileH name stg defs = do
  let (typedecls,defs') = L.partition isAbsTyp defs
  (htdecls,_) <- shallowDefinitionsH typedecls
  (htypes,_,_) <- shallowTypeFromTableH
  (hdefs,_) <- shallowDefinitionsH defs'
  return ( HM shhm (ModuleInfo []) $ lefts hdefs
         , HM sshm (ModuleInfo []) $ rights htdecls ++ htypes ++ rights hdefs)


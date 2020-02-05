--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE DeriveGeneric #-}
module Cogent.Common.Repr where

import Cogent.Common.Syntax
-- import qualified Cogent.Surface as S

import Data.Binary (Binary)
import qualified Data.Map as M
import GHC.Generics (Generic)

data Representation = Bits { allocSize :: Int, allocOffset :: Int } -- in bits 
                    | Variant { tagSize :: Int, tagOffset :: Int, alternatives :: M.Map TagName (Integer, Representation) }
                    | Record { fields :: M.Map FieldName Representation }
                    deriving (Show, Eq, Ord, Generic)

instance Binary Representation

-- Once we have repr in the surface lang, this can be removed.
dummyRepr = Bits 0 0


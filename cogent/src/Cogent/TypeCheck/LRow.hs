--
-- Copyright 2019, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ViewPatterns #-}

-- this small module helps with matching layouts,
-- and may be extended later

module Cogent.TypeCheck.LRow where

import Cogent.Common.Syntax
import Cogent.Compiler
import Cogent.Dargent.Util
import Cogent.Surface
import Cogent.Util

import qualified Data.List as L
import qualified Data.Map as M

import Prelude hiding (null)

data LRow e s = LRow { entries :: M.Map FieldName (FieldName, e, s) }
                deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

empty :: LRow e s
empty = LRow $ M.empty

fromList :: [(FieldName, e, s)] -> LRow e s
fromList s = LRow . M.fromList $ zip (fst3 <$> s) s

common :: LRow e s -> LRow e s -> [((FieldName, e, s), (FieldName, e, s))]
common r1@(entries -> es1) r2@(entries -> es2) = M.elems $ M.intersectionWith (,) es1 es2

withoutCommon :: LRow e s -> LRow e s -> (LRow e s, LRow e s)
withoutCommon r1@(entries -> es1) r2@(entries -> es2) =
  (LRow $ M.withoutKeys es1 $ M.keysSet es2, LRow $ M.withoutKeys es2 $ M.keysSet es1)

identicalFields :: (Eq s) => LRow e s -> LRow e s -> Bool
identicalFields r1 r2
  | (r1', r2') <- withoutCommon r1 r2
  , null r1' && null r2'
  = all (\((n1,_,s1), (n2,_,s2)) -> n1 == n2 && s1 == s2) $ common r1 r2

identical :: (DataLayoutComparable e, Eq s) => LRow e s -> LRow e s -> Bool
identical r1 r2
  | (r1', r2') <- withoutCommon r1 r2
  , null r1' && null r2'
  = all (\((n1,e1,s1), (n2,e2,s2)) -> n1 == n2 && testEqual e1 e2 && s1 == s2) $ common r1 r2
identical r1 r2 = False

null :: LRow e s -> Bool
null r@(entries -> es) = L.null $ M.elems es


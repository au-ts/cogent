--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Cogent.TypeCheck.GoalSet where

import           Control.Lens hiding ((:<))
import qualified Data.Map as M
import           Cogent.TypeCheck.Base
import           Cogent.PrettyPrint
import qualified Text.PrettyPrint.ANSI.Leijen as P
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))
import qualified Data.Foldable as F

-- A more efficient implementation would be a term net

data Goal = Goal { _goalContext :: [ErrorContext]
                 , _goal :: Constraint
                 }  -- high-level context at the end of _goalContext

instance Show Goal where
  show (Goal c g) = show small
    where big = (small P.<$> (P.vcat $ map (flip prettyCtx True) c))
          small = pretty g

instance Pretty Goal where
  pretty (Goal c g) = text "Goal" <+> parens (pretty g)

makeLenses ''Goal

newtype GoalSet = GS (M.Map Constraint Goal) deriving (Show)

instance Pretty GoalSet where
  pretty (GS m) = text "GoalSet" <+> parens (pretty m)

singleton :: Goal -> GoalSet
singleton = insert mempty

insert :: GoalSet -> Goal -> GoalSet
insert (GS x) g = GS (M.insert (g ^. goal) g x)

toList :: GoalSet -> [Goal]
toList (GS x) = F.toList x

#if __GLASGOW_HASKELL__ < 803
instance Monoid GoalSet where
  mempty = GS mempty
  mappend (GS a) (GS b) = GS (mappend a b)
#else
instance Semigroup GoalSet where
  GS a <> GS b = GS (a <> b)
instance Monoid GoalSet where
  mempty = GS mempty
#endif


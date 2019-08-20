{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Cogent.Dargent.Common where
  
import Data.Data

-- The Dargent wrapper type
data DargentLayout l
  = Layout l -- this type has this layout
  | CLayout  -- defer the layout of this type to C
  deriving (Data, Eq, Ord, Show, Functor, Foldable, Traversable)

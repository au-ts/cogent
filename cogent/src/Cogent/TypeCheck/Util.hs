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

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{- LANGUAGE TypeFamilies #-}

module Cogent.TypeCheck.Util where

import Cogent.Compiler
-- import Cogent.TypeCheck.Base
-- import Cogent.PrettyPrint

-- import Control.Lens
-- import Control.Monad.Except
-- import Control.Monad.IO.Class
import Control.Monad.State
-- import Control.Monad.Trans.Maybe
-- import Control.Monad.Writer
-- import Data.Function ((&))
-- import System.IO
import Text.PrettyPrint.ANSI.Leijen as L hiding (indent)

indent = nest 2

traceTc :: MonadIO m => String -> Doc -> m ()
traceTc s d = traceTcBracket s d (return ()) (const empty)

traceTc' :: MonadIO m => String -> String -> m ()
traceTc' s = traceTc s . text

traceTcBracket :: MonadIO m => String -> Doc -> m a -> (a -> Doc) -> m a
traceTcBracket s d1 m f
  | Just ws <- __cogent_ddump_tc_filter, s `notElem` ws = m
  | otherwise = do
      liftIO . dumpMsg $ indent (text ("[dump-tc/" ++ s ++ "]") <+> d1)
      a <- m
      liftIO . dumpMsg $ indent (f a) L.<$> line
      return a


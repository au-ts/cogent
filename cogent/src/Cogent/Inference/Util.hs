--
-- Copyright 2021, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--


module Cogent.Inference.Util where

import Cogent.Compiler

import Control.Monad.IO.Class
import Text.PrettyPrint.ANSI.Leijen as L hiding (indent)


-- ////////////////////////////////////////////////////////////////////////////
--                                 Debugging
-- ////////////////////////////////////////////////////////////////////////////

indent = nest 2

traceTc :: MonadIO m => String -> Doc -> m ()
traceTc s d = traceTcBracket s d (return ()) (const empty)

traceTc' :: MonadIO m => String -> String -> m ()
traceTc' s = traceTc s . text

traceTcBracket :: MonadIO m => String -> Doc -> m a -> (a -> Doc) -> m a
traceTcBracket s d1 m f
  | Just ws <- __cogent_ddump_tc_filter, s `notElem` ws = m
  | otherwise = do
      liftIO . dumpCoreTcMsg $ indent (text ("[dump-core/" ++ s ++ "]") <+> d1)
      a <- m
      liftIO . dumpCoreTcMsg $ indent (f a) L.<$> line
      return a




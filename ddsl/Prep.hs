--
-- Copyright 2017, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--
module Prep (prep) where

import Data.IORef
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Syntax

import Util

-- Only set flags, but will never clear flags
prep :: String -> IO ()
prep s = do
  let p = getTopPragmas s
  case p of
    ParseOk prgms -> setFlags prgms
    _ -> return ()

setFlags :: [ModulePragma] -> IO ()
setFlags = mapM_ setFlag

setFlag :: ModulePragma -> IO ()
setFlag (LanguagePragma _ names) = do
  if Ident "AllowU24" `elem` names
    then writeIORef allow_u24_ref True
    else return ()
  if Ident "AllowEmptyStruct" `elem` names
    then writeIORef allow_empty_struct_ref True
    else return ()
setFlag _ = return ()



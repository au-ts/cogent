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



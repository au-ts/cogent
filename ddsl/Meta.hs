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
{-# LANGUAGE TemplateHaskell #-}

module Meta where

import Control.Applicative ((<$>), (<*>))
import Data.IORef
import Language.Haskell.TH
import System.IO.Unsafe

mkNameI :: String -> Name
mkNameI n = mkName $ n ++ "_internal"

mkNameR :: String -> Name
mkNameR n = mkName $ n ++ "_ref"

mkFlag :: String -> Q [Dec]
mkFlag n = (++) <$> mkInternal n <*> mkRef n
 
mkInternal :: String -> Q [Dec]
mkInternal n = do
  s <- sigD (mkNameI n) [t|Bool|]
  v <- valD (varP $ mkNameI n) 
            (normalB (appE [|unsafePerformIO|] 
                       (appE [|readIORef|] (varE $ mkNameR n)))) 
            []
  return [s, v]

mkRef :: String -> Q [Dec]
mkRef n = do
  s <- sigD (mkNameR n) [t|IORef Bool|]
  p <- pragInlD (mkNameR n) NoInline FunLike AllPhases
  v <- valD (varP $ mkNameR n)
            (normalB (appE [|unsafePerformIO|]
                           [|newIORef False|]))
            []
  return [s, p, v]

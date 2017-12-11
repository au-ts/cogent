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

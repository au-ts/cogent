--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ < 709
import Control.Applicative ((<$>))
#endif
-- import Data.Time
import qualified Distribution.ModuleName as ModuleName
import Distribution.PackageDescription
import Distribution.Simple
import Distribution.Simple.BuildPaths (autogenModulesDir)
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Setup
import Distribution.Simple.Utils (createDirectoryIfMissingVerbose, rewriteFile)
import Distribution.Text (display)
import System.FilePath ((</>), (<.>))
import System.Process
import Control.Exception

main = defaultMainWithHooks hook

hook = simpleUserHooks { buildHook = buildCOGENTHook }

buildCOGENTHook :: PackageDescription -> LocalBuildInfo -> UserHooks -> BuildFlags -> IO ()
buildCOGENTHook pkg lbi hooks flags = do
  newPkg <- (do
      githash <- init <$> readProcess "git" ["rev-parse", "--short=10", "HEAD"] []  -- get rid of the newline
      -- utc <- getCurrentTime
      -- zone <- getCurrentTimeZone
      let -- zoned = utcToZonedTime zone utc
          -- buildtime = formatTime defaultTimeLocale "%a, %-d %b %Y %H:%M:%S %Z" zoned
          -- modulename = autogenBuildInfoModuleName pkg
          pId = package pkg
          ver = pkgVersion pId
          newVer = ver { versionTags = [githash] }
          newPId = pId { pkgVersion = newVer }
          newPkg = pkg { package = newPId }
      return newPkg)
      `catch` (\x -> do let _ = (x :: IOError) -- type annotation
                        putStrLn "Warning: failed to retrieve git hash. Continuing anyway..."
                        return pkg)
      -- verbosity = fromFlag (buildVerbosity flags)
  -- createDirectoryIfMissingVerbose verbosity True (autogenModulesDir lbi)
  -- rewriteFile (autogenModulesDir lbi </> ModuleName.toFilePath modulename <.> "hs") (generate modulename githash buildtime)
  buildHook simpleUserHooks newPkg lbi hooks flags
  -- buildHook simpleUserHooks pkg lbi hooks flags

-- |The name of the auto-generated module associated with a package
-- Adapted from Cabal - Distribution.Simple.BuildPaths function `autogenModuleName' / zilinc
autogenBuildInfoModuleName :: PackageDescription -> ModuleName.ModuleName
autogenBuildInfoModuleName pkg =
  ModuleName.fromString $ "BuildInfo_" ++ map fixchar (display (packageName pkg))
  where fixchar '-' = '_'
        fixchar c   = c

-- ------------------------------------------------------------
-- * Building BuildInfo_<pkg>.hs
-- Adapted from Cabal - Distribution.Simple.Build.PathsModule function of the same name / zilinc
--
-- Copyright   :  Isaac Jones 2003-2005,
--                Ross Paterson 2006,
--                Duncan Coutts 2007-2008, 2012
-- License     :  BSD3 (see bilby/cogent/Cabal_LICENSE)
-----------------------------------------------------------------------------

generate :: ModuleName.ModuleName -> String -> String -> String
generate modulename githash buildtime = unlines $
  [ "module " ++ display modulename ++ " ("
  , "    githash, buildtime"
  , "  ) where"
  , ""
  , "import Prelude"
  , ""
  , "githash :: String"
  , "githash = \"" ++ githash ++ "\""
  , ""
  , "buildtime :: String"
  , "buildtime = \"" ++ buildtime ++ "\""
  ]


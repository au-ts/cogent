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
import Control.Arrow (first)
import Control.Exception (SomeException, catch)

import Distribution.PackageDescription
import Distribution.Simple
#if MIN_VERSION_Cabal (2,0,0)
import Distribution.Simple.BuildPaths (autogenModulesDir, autogenPackageModulesDir)
#else
import Distribution.Simple.BuildPaths (autogenModulesDir)
#endif
import Distribution.Simple.LocalBuildInfo as L
import qualified Distribution.Simple.Setup as S
import Distribution.Simple.Utils
import Distribution.PackageDescription
import Distribution.Verbosity (Verbosity)

import System.Directory(removeFile)
import System.Exit
import System.FilePath ((</>), (<.>), takeExtension)
import qualified System.FilePath.Posix as Px
import System.Process (readProcess)

-- Flags
isRelease :: S.ConfigFlags -> Bool
isRelease flags =
#if MIN_VERSION_Cabal (2,2,0)
  case lookup (mkFlagName "release") (unFlagAssignment $ S.configConfigurationsFlags flags) of
#elif MIN_VERSION_Cabal (2,0,0)
  case lookup (mkFlagName "release") (S.configConfigurationsFlags flags) of
#else
  case lookup (FlagName "release") (S.configConfigurationsFlags flags) of
#endif
    Just x  -> x
    Nothing -> False

-- Git Hash
gitHash :: IO String
gitHash = do h <- Control.Exception.catch (readProcess "git" ["rev-parse", "--short=10", "HEAD"] "")
               (\e -> let e' = (e :: SomeException) in return "devel")
             return $ takeWhile (/= '\n') h

-- Version Module
generateVersionModule verbosity dir release flags = do
  hash <- gitHash
  let versionModulePath = dir </> "Version_cogent" <.> "hs"
  putStrLn $ "Generating " ++ versionModulePath ++
    if release then " for release" else " for dev " ++ hash ++ "\n" ++
      "(Configured with flags: " ++ flagsInfo ++ ")"
  createDirectoryIfMissingVerbose verbosity True dir
  
#if MIN_VERSION_Cabal (2,0,0)
  rewriteFileEx verbosity versionModulePath (versionModuleContents hash)
#else
  rewriteFile versionModulePath (versionModuleContents hash)
#endif

  where 
    flagsInfo = unwords (flip map flags (\(f,a) -> (if a then "+" else "-") ++ f))
    versionModuleContents h = "module Version_cogent where\n\n" ++
          "gitHash :: String\n" ++
            (if release
               then "gitHash = \"\"\n"
               else "gitHash = \"" ++ h ++ "\"\n") ++
            "configFlags :: String" ++ "\n" ++
            "configFlags = \"Built with flags: " ++ flagsInfo ++ "\""


-- Configure
cogentConfigure :: Args -> S.ConfigFlags -> PackageDescription -> LocalBuildInfo -> IO ()
cogentConfigure _ flags _ lbi = do
#if MIN_VERSION_Cabal (2,0,0)
  generateVersionModule verbosity (autogenPackageModulesDir lbi) (isRelease (configFlags lbi)) flagAssignment
#else
  generateVersionModule verbosity (autogenModulesDir lbi) (isRelease (configFlags lbi)) flagAssignment
#endif
  where
    verbosity = S.fromFlag $ S.configVerbosity flags
    version = pkgVersion . package $ localPkgDescr lbi
#if MIN_VERSION_Cabal (2,2,0)
    flagAssignment = map (first unFlagName) $ unFlagAssignment $ S.configConfigurationsFlags flags
#else 
    flagAssignment = map (first unFlagName) $ S.configConfigurationsFlags flags
#endif

-- Copy
copyGumHdrs :: Verbosity -> PackageDescription -> LocalBuildInfo -> CopyDest -> IO ()
copyGumHdrs verbosity pkg lbi copy = do
  let hdrsdest = datadir (L.absoluteInstallDirs pkg lbi copy) </> "include"
  putStrLn $ "Installing Gum headers in `" ++ hdrsdest ++ "'..."
  createDirectoryIfMissingVerbose verbosity True hdrsdest
  installDirectoryContents verbosity "lib" hdrsdest
    where
      -- This function is copied from Cabal-1.24.2.0 and modified
      installDirectoryContents :: Verbosity -> FilePath -> FilePath -> IO ()
      installDirectoryContents verbosity srcDir destDir = do
        info verbosity ("copy directory '" ++ srcDir ++ "' to '" ++ destDir ++ "'...")
        srcFiles <- getDirectoryContentsRecursive srcDir
        let srcFiles' = filter ((`elem` [".ac", ".ah", ".h", ".cogent", ".c"]) . takeExtension) srcFiles
        installOrdinaryFiles verbosity destDir [ (srcDir, f) | f <- srcFiles' ]

installManPage :: Verbosity -> PackageDescription -> LocalBuildInfo -> CopyDest -> IO ()
installManPage verbosity pkg lbi copy = do
  let mandest = mandir (L.absoluteInstallDirs pkg lbi copy) ++ "/man1"
  putStrLn $ "Installing man page to `" ++ mandest ++ "'..."
  r <- rawSystemExitCode verbosity "perl" ["scripts/man-gen.pl", mandest, buildDir lbi </> "cogent/cogent"]
  case r of
    ExitSuccess -> return ()
    ExitFailure n -> putStrLn $ "Installing man page failed: exit code " ++ show n


-- Test
-- cabal has two unrelated "dataDir" variables.
-- We need to use the one in the install directory where cogent is installed.
fixPkg pkg target = pkg { dataDir = target }

-- "Args" argument of testHooks have been added in cabal 1.22.0
#if __GLASGOW_HASKELL__ < 710
originalTestHook _ = testHook simpleUserHooks
#else
originalTestHook = testHook simpleUserHooks
#endif

cogentTestHook args pkg lbi hooks flags = do
  let target = datadir $ L.absoluteInstallDirs pkg lbi NoCopyDest
  originalTestHook args (fixPkg pkg target) lbi hooks flags

-- -----
-- Main
-- -----
main = defaultMainWithHooks $ autoconfUserHooks
  { postConf = cogentConfigure
  -- TODO:
  -- , postBuild = \_ flags pkg lbi -> do
  --     copyGumHdrs 
  --     buildManPage 
  , postCopy = \_ flags pkg lbi -> do
      copyGumHdrs (S.fromFlag $ S.copyVerbosity flags) pkg lbi (S.fromFlag $ S.copyDest flags)
      installManPage (S.fromFlag $ S.copyVerbosity flags) pkg lbi (S.fromFlag $ S.copyDest flags)
  -- No idea why `postInst' is needed, as it doesn't seem to execute.
  -- Looking at other packages, they mostly do the same.
  -- Googled for quite a while and found some questions but no answers. / zilinc
  , postInst = \_ flags pkg lbi -> do
      installManPage (S.fromFlag $ S.installVerbosity flags) pkg lbi NoCopyDest
#if __GLASGOW_HASKELL__ < 710
  , testHook = cogentTestHook ()
#else
  , testHook = cogentTestHook
#endif
  }

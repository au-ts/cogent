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

import Control.Exception (SomeException, catch)

import Distribution.Simple
#if MIN_VERSION_Cabal (2,0,0)
import Distribution.Simple.BuildPaths (autogenModulesDir, autogenPackageModulesDir)
#else
import Distribution.Simple.BuildPaths (autogenModulesDir)
#endif
import Distribution.Simple.LocalBuildInfo as L
import qualified Distribution.Simple.Setup as S
import Distribution.Simple.Utils (createDirectoryIfMissingVerbose, rewriteFile, installOrdinaryFiles, installDirectoryContents)

import Distribution.PackageDescription

import System.Directory(removeFile)
import System.FilePath ((</>))
import qualified System.FilePath.Posix as Px
import System.Process (readProcess)

-- Flags
isRelease :: S.ConfigFlags -> Bool
isRelease flags =
#if MIN_VERSION_Cabal (2,0,0)
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
generateVersionModule verbosity dir release = do
  hash <- gitHash
  let versionModulePath = dir </> "Version_cogent" Px.<.> "hs"
  putStrLn $ "Generating " ++ versionModulePath ++
    if release then " for release" else " for dev " ++ hash
  createDirectoryIfMissingVerbose verbosity True dir
  rewriteFile versionModulePath (versionModuleContents hash)

  where versionModuleContents h = "module Version_cogent where\n\n" ++
          "gitHash :: String\n" ++
          if release
             then "gitHash = \"\"\n"
          else "gitHash = \"" ++ h ++ "\"\n"

-- Configure
cogentConfigure _ flags _ local = do
#if MIN_VERSION_Cabal (2,0,0)
  generateVersionModule verbosity (autogenPackageModulesDir local) (isRelease (configFlags local))
#else
  generateVersionModule verbosity (autogenModulesDir local) (isRelease (configFlags local))
#endif
  where
    verbosity = S.fromFlag $ S.configVerbosity flags
    version = pkgVersion .package $ localPkgDescr local

-- Install
cogentInstall verbosity copy pkg local = do
  installGumHdrs
  installManPage
  where
    installGumHdrs = do
      let hdrsdest = (datadir $ L.absoluteInstallDirs pkg local copy) ++ "/include"
      putStrLn $ "Installing Gum headers in " ++ hdrsdest
      createDirectoryIfMissingVerbose verbosity True hdrsdest
      installDirectoryContents verbosity "lib" hdrsdest

    installManPage = do
      let mandest = mandir (L.absoluteInstallDirs pkg local copy) ++ "/man1"
      putStrLn $ "Copying man page to " ++ mandest
      installOrdinaryFiles verbosity mandest [("man", "cogent.1")]

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

cogentTestHook args pkg local hooks flags = do
  let target = datadir $ L.absoluteInstallDirs pkg local NoCopyDest
  originalTestHook args (fixPkg pkg target) local hooks flags

-- -----
-- Main
-- -----
main = defaultMainWithHooks $ simpleUserHooks
  { postConf = cogentConfigure
  , postCopy = \_ flags pkg local ->
    cogentInstall (S.fromFlag $ S.copyVerbosity flags) (S.fromFlag $ S.copyDest flags) pkg local
  , postInst = \_ flags pkg local ->
    cogentInstall (S.fromFlag $ S.installVerbosity flags)
    NoCopyDest pkg local
#if __GLASGOW_HASKELL__ < 710
  , testHook = cogentTestHook ()
#else
  , testHook = cogentTestHook
#endif
  }

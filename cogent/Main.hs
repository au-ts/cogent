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

{- LANGUAGE BangPatterns -}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiWayIf                 #-}
{-# LANGUAGE NamedFieldPuns             #-}
{- LANGUAGE QuasiQuotes -}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{- LANGUAGE TemplateHaskell -}
{-# LANGUAGE TupleSections              #-}
{-# OPTIONS_GHC -Wwarn #-}

module Main where

import           Cogent.C                         as CG (cgen, printCTable, printATM)
import           Cogent.Common.Syntax             as SY (CoreFunName (..))
import           Cogent.Compiler
import           Cogent.Core                      as CC (getDefinitionId, isConFun, untypeD)
import           Cogent.Desugar                   as DS (desugar)
#ifdef WITH_DOCGENT
import           Cogent.DocGent                   as DG (docGent)
#endif
import           Cogent.Flags
import           Cogent.GetOpt
import           Cogent.Glue                      as GL (GlState, GlueMode (..), defaultExts, defaultTypnames,
                                                         glue, mkGlState, parseFile, readEntryFuncs)
#ifdef WITH_HASKELL
import           Cogent.Haskell.Shallow           as HS
#endif
import           Cogent.Inference                 as IN (retype, tc, tcConsts, tc_, tcExpand, tcConstExpand, filterTypeDefs)
import           Cogent.Interpreter               as Repl (replWithState)
import           Cogent.Isabelle                  as Isa
#ifdef WITH_LLVM
import           Cogent.LLVM.Compile              as LLVM
#endif
import           Cogent.Mono                      as MN (mono, printAFM)
import           Cogent.Normal                    as NF (normal, verifyNormal)
import           Cogent.Parser                    as PA (parseCustTyGen, parseWithIncludes)
import           Cogent.Preprocess                as PR
import           Cogent.PrettyPrint               as PP (prettyPrint, prettyRE, prettyTWE)
import           Cogent.Reorganizer               as RO (reorganize)
import           Cogent.Simplify                  as SM
import           Cogent.SuParser                  as SU (parse)
import           Cogent.Surface                   as SR (stripAllLoc)
import           Cogent.TypeCheck                 as TC (tc)
import           Cogent.TypeCheck.Base            as TC
import           Cogent.Util                      as UT

-- import BuildInfo_cogent (githash, buildtime)
import           Control.Monad                    (forM, forM_, unless, when, (<=<))
import           Control.Monad.Trans.Except       (runExceptT)
-- import Control.Monad.Cont
-- import Control.Monad.Except (runExceptT)
-- import Control.Monad.Trans.Either (eitherT, runEitherT)
import           Data.Binary                      (decodeFileOrFail, encodeFile)
import           Data.Char                        (isSpace)
import           Data.Either                      (fromLeft, isLeft)
import           Data.Foldable                    (fold, foldrM)
import           Data.IORef                       (writeIORef)
import           Data.List                        as L (find, intersect, isPrefixOf, nub, partition)
import           Data.Map                         (empty, fromList)
import           Data.Maybe                       (fromJust, isJust)
import           Data.Monoid                      (getLast)
import           Data.Time
import qualified Data.Traversable                 as T (forM)
-- import Isabelle.InnerAST (subSymStr)
-- import Language.Haskell.TH.Ppr ()
import           Lens.Micro                       ((^.))
import           Prelude                          hiding (mapM_)
import           System.AtomicWrite.Writer.String (atomicWithFile)
-- import System.Console.GetOpt
import           System.Directory
import           System.Environment
import           System.Exit                      hiding (exitFailure, exitSuccess)
import           System.FilePath                  hiding ((</>))
import           System.IO
import           System.Process                   (readProcessWithExitCode)
import           Text.PrettyPrint.ANSI.Leijen     as LJ (Doc, displayIO, hPutDoc, plain)
#if MIN_VERSION_mainland_pretty(0,6,0)
import           Text.PrettyPrint.Mainland        as M (hPutDoc, line, string, (</>))
import           Text.PrettyPrint.Mainland.Class  as M (ppr)
#else
import           Text.PrettyPrint.Mainland        as M (hPutDoc, line, ppr, string, (</>))
#endif
import           Text.Show.Pretty                 (ppShow)
-- import Debug.Trace


type Flags = [IO ()]

parseArgs :: [String] -> IO ()
parseArgs args = case getOpt' Permute options args of
    (cmds,xs,us,[]) -> case addCommands cmds of
                         Left  err       -> exitErr (err ++ "\n")
                         Right (_,cmds') -> withCommands (cmds',xs,us,args)  -- XXX | noCommandError (cmds',xs,us,args)
    (_,_,us,errs)   -> exitErr (concat errs)
  where
    withCommands :: ([Command], [String], [String], [String]) -> IO ()
#ifndef WITH_HASKELL
    withCommands (cs,_,_,_) | not . null $ [HsFFIGen, HsShallowTuples, HsShallow] `intersect` cs
      = exitErr $ unlines [ "Haskell-related features are disabled in this build."
                          , "Try building the Cogent compiler with the flag `haskell-backend' on."]
#endif
#ifndef WITH_DOCGENT
    withCommands (cs,_,_,_) | Documentation `elem` cs
      = exitErr $ unlines [ "Cogent documentation generation is disabled in this build."
                          , "Try building the Cogent compiler with the flag `docgent' on."]
#endif
    withCommands (cs,xs,us,args) = case getOpt Permute flags (filter (`elem` us ++ xs) args) of  -- Note: this is to keep the order of arguments / zilinc
      (flags,xs',[]) -> noFlagError (cs,flags,xs',args)
      (_,_,errs)     -> exitErr (concat errs)

    noFlagError :: ([Command], Flags, [String], [String]) -> IO ()
    noFlagError ([LibgumDir],_,_,_) = getLibgumDir >>= putStrLn >> exitSuccess_
    noFlagError ([Help v],_,_,_) = putStr (usage v) >> exitSuccess_
    noFlagError ([Version],_,_,_) = putStrLn versionInfo >> exitSuccess_
    noFlagError ([Interpret],fs,_,_) = replWithState
    noFlagError (_,_,[],_) = exitErr ("no Cogent file specified\n")
    noFlagError (cs,fs,x:[],args) = oneFile (cs,fs,x,args)
    noFlagError (_,_,xs,_) = exitErr ("only one Cogent file can be given\n")

    oneFile :: ([Command], Flags, FilePath, [String]) -> IO ()
    oneFile (cmds,flags,source,args) = do
      sequence_ flags
      runCompiler cmds source args

    putProgress :: String -> IO ()
    putProgress s = when (not __cogent_quiet) $ hPutStr stderr s

    putProgressLn :: String -> IO ()
    putProgressLn s = when (not __cogent_quiet) $ hPutStrLn stderr s

    runCompiler :: [Command] -> FilePath -> [String] -> IO ()
    runCompiler cmds source args =
      if | Compile STGParse `elem` cmds -> do
             preDump
             utc <- getCurrentTime
             zone <- getCurrentTimeZone
             let zoned = utcToZonedTime zone utc
                 buildinfo =
                   "-----------------------------------------------------------------------------\n" ++
                   "This file is generated by " ++ versionInfo ++ "\n" ++
                   "with command ./cogent " ++ unwords args ++ "\n" ++
                   "at " ++ formatTime defaultTimeLocale "%a, %-d %b %Y %H:%M:%S %Z" zoned ++ "\n" ++
                   "-----------------------------------------------------------------------------\n"
                 log = if __cogent_fgen_header
                         then buildinfo
                         else "This file is generated by Cogent\n"
             parse cmds source buildinfo log
         | Just (AstC) <- find isAstC cmds -> c_parse cmds source
         | Just (StackUsage p) <- find isStackUsage cmds -> stack_usage cmds p source
         | otherwise -> exitSuccess

    c_parse cmds source = do
      putProgressLn "Parsing C file..."
      let hl, hr :: forall a b. Show a => a -> IO b
          hl err = hPutStrLn stderr (show err) >> exitFailure
          hr defs = lessPretty stdout defs >> exitSuccess
      exceptT hl hr $ GL.parseFile GL.defaultExts defaultTypnames source

    stack_usage cmds p source = do
      putProgressLn "Parsing .su file..."
      let outf = case p of Nothing  -> Just $ source ++ ".psu"
                           Just "-" -> Nothing
                           Just o   -> Just o
      SU.parse source >>= \case
        Left err  -> hPutStrLn stderr err >> exitFailure
        Right sus -> writeFileMsg outf >> output outf (flip hPutStrLn (show sus)) >> exitSuccess

    parse cmds source buildinfo log = do
      let stg = STGParse
      putProgressLn "Parsing..."
      parseWithIncludes source __cogent_include >>= \case
        Left err -> hPutStrLn stderr err >> exitFailure
        Right (parsed,pragmas) -> do
          prune <- T.forM __cogent_prune_call_graph simpleLineParser
          putProgressLn "Resolving dependencies..."
          case reorganize prune parsed of
            Left err -> printError prettyRE [err] >> exitFailure
            Right reorged -> do when (Ast stg `elem` cmds) $ genAst stg (map (stripAllLoc . thd3) reorged)
                                when (Pretty stg `elem` cmds) $ genPretty stg (map (stripAllLoc . thd3) reorged)
#ifdef WITH_DOCGENT
                                when (Documentation `elem` cmds) $ DG.docGent reorged
#endif
                                let noDocs (a,_,c) = (a,c)
                                when (Compile (succ stg) `elem` cmds) $ do
                                  ctygen <- mapM parseCustTyGen __cogent_cust_ty_gen
                                  case sequence ctygen of
                                    Left err -> hPutStrLn stderr err >> exitFailure
                                    Right ctygen' -> typecheck cmds (map noDocs reorged) (fold ctygen') source pragmas buildinfo log
                                exitSuccessWithBuildInfo cmds buildinfo

    typecheck cmds reorged ctygen source pragmas buildinfo log = do
      let stg = STGTypeCheck
      putProgressLn "Typechecking..."
      ((mtc',tclog),tcst) <- TC.tc reorged ctygen pragmas
      let (errs,warns) = partition (isLeft . snd) $ tclog^.errLog
      when (not $ null errs) $ do
        printError (prettyTWE __cogent_ftc_ctx_len) errs
        when (and $ map (isWarnAsError . fromLeft undefined . snd) errs) $ hPutStrLn stderr "Failing due to --Werror."
        exitFailure
      case mtc' of
        Nothing -> __impossible "main: typecheck"
        Just (tced,ctygen',pragmas') -> do
          __assert (null errs) "no errors, only warnings"
          unless (null $ warns) $ printError (prettyTWE __cogent_ftc_ctx_len) $ warns
          when (Ast stg `elem` cmds) $ genAst stg tced
          when (Pretty stg `elem` cmds) $ genPretty stg tced
          when (Compile (succ stg) `elem` cmds) $ desugar cmds tced ctygen' tcst source pragmas' buildinfo log
          exitSuccessWithBuildInfo cmds buildinfo

    desugar cmds tced ctygen tcst source pragmas buildinfo log = do
      let stg = STGDesugar
      putProgressLn "Desugaring and typing..."
      let ((desugared,ctygen',pragmas'),typedefs) = DS.desugar tced ctygen pragmas
      when __cogent_ddump_pretty_ds_no_tc $ pretty stdout desugared
      case IN.tc desugared of
        Left err -> hPutStrLn stderr ("Internal TC failed: " ++ err) >> exitFailure
        Right (desugared',fts) -> do
          when (Ast stg `elem` cmds) $ genAst stg desugared'
          when (Pretty stg `elem` cmds) $ genPretty stg desugared'
          when (Deep stg `elem` cmds) $ genDeep cmds source stg desugared' typedefs fts log
          case IN.tcConsts ((\(a,b,c) -> c) $ fromJust $ getLast typedefs) fts $ filterTypeDefs desugared' of
            Left err -> hPutStrLn stderr ("Internal TC failed: " ++ err) >> exitFailure
            Right (constdefs,_) -> do
              _ <- genShallow cmds source stg desugared' typedefs fts constdefs log
                     ( Shallow       stg   `elem` cmds
                     , SCorres       stg   `elem` cmds
                     , ShallowConsts stg   `elem` cmds
                     , ShallowTuples       `elem` cmds
                     , ShallowConstsTuples `elem` cmds
                     , ShallowTuplesProof  `elem` cmds
                     , HsShallow           `elem` cmds
                     , HsShallowTuples     `elem` cmds)
              when (TableShallow `elem` cmds) $
                putProgressLn ("Generating shallow table...") >> putStrLn (printTable $ st desugared')
              when (Compile (succ stg) `elem` cmds) $
                normal cmds desugared' ctygen' pragmas' source tced tcst typedefs fts constdefs buildinfo log
              exitSuccessWithBuildInfo cmds buildinfo

    normal cmds desugared ctygen pragmas source tced tcst typedefs fts buildinfo log = do
      let stg = STGNormal
      putProgress "Normalising..."
      let desugared' = IN.tcExpand desugared
      nfed' <- case __cogent_fnormalisation of
        NoNF -> putProgressLn "Skipped." >> return desugared'
        nf -> do putProgressLn (show nf)
                 let nfed = NF.normal $ map untypeD desugared'
                 if not $ verifyNormal nfed
                   then hPutStrLn stderr "Normalisation failed!" >> exitFailure
                   else do when __cogent_ddump_pretty_normal_no_tc $ pretty stdout nfed
                           putProgressLn "Re-typing NF..."
                           case IN.tc_ nfed of
                             Left err -> hPutStrLn stderr ("Re-typing NF failed: " ++ err) >> exitFailure
                             Right nfed' -> return nfed'
      let thy = mkProofName source Nothing
      when (Ast stg `elem` cmds) $ genAst stg nfed'
      when (Pretty stg `elem` cmds) $ genPretty stg nfed'
      when (Deep stg `elem` cmds) $ genDeep cmds source stg nfed' typedefs fts log
      when (TypeProof STGNormal `elem` cmds) $ do
        let suf = __cogent_suffix_of_type_proof ++ __cogent_suffix_of_stage STGNormal
            tpfile = mkThyFileName source suf
            tpthy  = thy ++ suf
        writeFileMsg tpfile
        output tpfile $ flip LJ.hPutDoc $
          deepTypeProof id __cogent_ftp_with_decls __cogent_ftp_with_bodies tpthy nfed' fts log
      shallowTypeNames <-
        genShallow cmds source stg nfed' typedefs fts log (Shallow stg `elem` cmds,
                                                           SCorres stg `elem` cmds,
                                                           ShallowConsts stg `elem` cmds,
                                                           False, False, False, False, False)
      when (NormalProof `elem` cmds) $ do
        let npfile = mkThyFileName source __cogent_suffix_of_normal_proof
        writeFileMsg npfile
        output npfile $ flip LJ.hPutDoc $ normalProof thy shallowTypeNames nfed' log
      when (Compile (succ stg) `elem` cmds) $ simpl cmds nfed' ctygen pragmas source tced tcst typedefs fts buildinfo log
      exitSuccessWithBuildInfo cmds buildinfo

    simpl cmds nfed ctygen pragmas source tced tcst typedefs fts buildinfo log = do
      let stg = STGSimplify
      putProgressLn "Simplifying..."
      simpled' <- case __cogent_fsimplifier of
        False -> putProgressLn "Skipped" >> return nfed
        True  -> do putProgressLn ""
                    let simpled = map untypeD $ SM.simplify nfed
                    putProgressLn "Re-typing simplified AST..."
                    case IN.tc_ simpled of
                      Left err -> hPutStrLn stderr ("Re-typing simplified AST failed: " ++ err) >> exitFailure
                      Right simpled' -> return simpled'
      when (Ast stg `elem` cmds) $ genAst stg simpled'
      when (Pretty stg `elem` cmds) $ genPretty stg simpled'
      when (Compile (succ stg) `elem` cmds) $ mono cmds simpled' ctygen pragmas source tced tcst typedefs fts buildinfo log
      exitSuccessWithBuildInfo cmds buildinfo

    mono cmds simpled ctygen pragmas source tced tcst typedefs fts buildinfo log = do
      let stg = STGMono
      putProgressLn "Monomorphising..."
      efuns <- T.forM __cogent_entry_funcs $
                 return . (,empty) <=< (readEntryFuncs tced tcst typedefs fts) <=< simpleLineParser
      entryFuncs <- case efuns of
                      Nothing -> return Nothing
                      Just (Nothing, _) -> exitFailure
                      Just (Just f, i) -> return $ Just (f, i)

      let (insts,(warnings,monoed,ctygen',pragmas')) = MN.mono simpled ctygen pragmas entryFuncs
      when (TableAbsFuncMono `elem` cmds) $ do
        let afmfile = mkFileName source Nothing __cogent_ext_of_afm
        putProgressLn "Generating table for monomorphised abstract functions..."
        writeFileMsg afmfile
        output afmfile $ flip hPutStrLn (printAFM (fst insts) simpled)
      putProgressLn "Re-typing monomorphic AST..."
      case retype monoed of
        Left err -> hPutStrLn stderr ("Re-typing monomorphic AST failed: " ++ err) >> exitFailure
        Right monoed' -> do
          printWarnings warnings
          when (Ast stg `elem` cmds) $ lessPretty stdout monoed'
          when (Pretty stg `elem` cmds) $ pretty stdout monoed'
          when (Deep stg `elem` cmds) $ genDeep cmds source stg monoed' typedefs fts log
          _ <- genShallow cmds source stg monoed' typedefs fts log (Shallow stg `elem` cmds,
                                                                    SCorres stg `elem` cmds,
                                                                    ShallowConsts stg `elem` cmds,
                                                                    False, False, False, False, False)
          -- LLVM Entrance
#ifdef WITH_LLVM
          when (LLVMGen `elem` cmds) $ llvmg cmds monoed' ctygen' insts source tced tcst typedefs fts buildinfo log
#endif
          when (Compile (succ stg) `elem` cmds) $ cg cmds monoed' ctygen' pragmas' insts source tced tcst typedefs fts buildinfo log
          c_refinement source monoed' insts log (ACInstall `elem` cmds, CorresSetup `elem` cmds, CorresProof `elem` cmds)
          when (MonoProof `elem` cmds) $ do
            let mpfile = mkThyFileName source __cogent_suffix_of_mono_proof
            writeFileMsg mpfile
            output mpfile $ flip LJ.hPutDoc $ monoProof source (fst insts) log
          when (TypeProof STGMono `elem` cmds) $ do
            let tpfile = mkThyFileName source __cogent_suffix_of_type_proof
                tpthy  = mkProofName source (Just __cogent_suffix_of_type_proof)
            writeFileMsg tpfile
            output tpfile $ flip LJ.hPutDoc $ deepTypeProof id __cogent_ftp_with_decls __cogent_ftp_with_bodies tpthy monoed' fts log
          when (AllRefine `elem` cmds) $ do
            let arfile = mkThyFileName source __cogent_suffix_of_all_refine
            writeFileMsg arfile
            output arfile $ flip LJ.hPutDoc $ allRefine source log
          when (Root `elem` cmds) $ do
            let rtfile = if __cogent_fdump_to_stdout then Nothing else Just $ __cogent_dist_dir `combine` __cogent_root_name
            writeFileMsg rtfile
            output rtfile $ flip hPutStrLn (unlines $ root source log)
          when (GraphGen `elem` cmds) $ putProgressLn ("Generating graph...") >> graphGen monoed' log
          exitSuccessWithBuildInfo cmds buildinfo

#ifdef WITH_LLVM
    llvmg cmds monoed ctygen insts source tced tcst typedefs fts buildinfo log = do
      putProgressLn "Now using the LLVM backend"
      LLVM.to_llvm monoed source
#endif

    cg cmds monoed ctygen pragmas insts source tced tcst typedefs fts buildinfo log = do
      let hName = mkOutputName source Nothing <.> __cogent_ext_of_h
          hscName = mkOutputName' toHsModName source (Just __cogent_suffix_of_ffi_types)
          hsName  = mkOutputName' toHsModName source (Just __cogent_suffix_of_ffi)
          cNames  = map (\n -> takeBaseName n ++ __cogent_suffix_of_pp ++ __cogent_suffix_of_inferred <.> __cogent_ext_of_c) __cogent_infer_c_func_files
      (mcache, decodingFailed) <- case __cogent_name_cache of
        Nothing -> return (Nothing, False)
        Just cacheFile -> do
          cacheExists <- doesFileExist cacheFile
          if not cacheExists
            then putProgressLn ("No name cache file found: " ++ cacheFile) >> return (Nothing, False)
            else do putProgressLn ("Using existing name cache file: " ++ cacheFile)
                    decodeResult <- decodeFileOrFail cacheFile
                    case decodeResult of
                      Left (_, err) -> hPutStrLn stderr ("Decoding name cache file failed: " ++ err ++ ".\nNot using name cache.") >> return (Nothing, True)
                      Right cache -> return (Just cache, False)
      let (h,c,atm,ct,ct',hsc,hs,genst) = cgen hName cNames hscName hsName monoed mcache ctygen pragmas log
      when (TableAbsTypeMono `elem` cmds) $ do
        let atmfile = mkFileName source Nothing __cogent_ext_of_atm
        putProgressLn "Generating table for monomorphised asbtract types..."
        writeFileMsg atmfile
        output atmfile $ flip hPutStrLn (printATM atm)
      when (TableCType `elem` cmds) $ do
        let ctyfile = mkFileName source Nothing __cogent_ext_of_c_type_table
        putProgressLn "Generating table for C-Cogent type correspondence..."
        writeFileMsg ctyfile
        output ctyfile $ \h -> fontSwitch h >>= \s -> printCTable h s ct log
      when (NewTableCType `elem` cmds) $ do
        let ctyfile' = mkFileName source Nothing (__cogent_ext_of_c_type_table ++ ".new")
        putProgressLn "Generating (new) table for C-Cogent type correspondence..."
        writeFileMsg ctyfile'
        output ctyfile' $ \h -> fontSwitch h >>= \s -> printCTable h s ct' log
#ifdef WITH_HASKELL
      when (HsFFIGen `elem` cmds) $ do
        putProgressLn "Generating Hsc file..."
        let hscf = mkHscFileName source __cogent_suffix_of_ffi_types
        writeFileMsg hscf
        output hscf $ flip LJ.hPutDoc hsc
        putProgressLn "Generating Hs file..."
        let hsf = mkHsFileName source __cogent_suffix_of_ffi
        writeFileMsg hsf
        output hsf $ flip hPutStrLn hs
#endif
      when (CodeGen `elem` cmds) $ do
        putProgressLn "Generating C code..."
        let hf = mkFileName source Nothing __cogent_ext_of_h
            cf = mkFileName source Nothing __cogent_ext_of_c
        writeFileMsg hf
        output hf $ flip M.hPutDoc (ppr h </> M.line)       -- .h file gen
        writeFileMsg cf
        output cf $ flip M.hPutDoc (ppr c </> M.line)       -- .c file gen
        unless (null $ __cogent_infer_c_func_files ++ __cogent_infer_c_type_files) $
          glue cmds tced tcst typedefs fts insts genst buildinfo log
        forM_ __cogent_name_cache $ \cacheFile -> do
          unless decodingFailed $ do
            putProgressLn ("Writing name cache file: " ++ cacheFile)
            encodeFile cacheFile genst

    c_refinement source monoed insts log (False,False,False) = return ()
    c_refinement source monoed insts log (ac,cs,cp) = do
      let confns = map getDefinitionId $ filter isConFun monoed
          acfile = mkThyFileName source __cogent_suffix_of_ac_install
          csfile = mkThyFileName source __cogent_suffix_of_corres_setup
          cpfile = mkThyFileName source __cogent_suffix_of_corres_proof
          thy = mkProofName source Nothing
          inputc = maybe (mkOutputName source Nothing <.> __cogent_ext_of_c) id __cogent_proof_input_c
      when ac $ do
        putProgressLn "Generating a theory file to install AutoCorres..."
        let acInstallThy = acInstallDefault thy inputc log
        writeFileMsg acfile
        output acfile $ flip hPutStrLn (unlines acInstallThy)
      when cs $ do
        putProgressLn "Generating lemmas for C-refinement..."
        let corresSetupThy = corresSetup thy inputc log
        writeFileMsg csfile
        output csfile $ flip LJ.hPutDoc corresSetupThy
      when cp $ do
        putProgressLn "Generating C-refinement proofs..."
        ent <- T.forM __cogent_entry_funcs simpleLineParser  -- a simple parser
        let corresProofThy = corresProof thy inputc (map SY.CoreFunName confns) (map SY.CoreFunName <$> ent) log
        writeFileMsg cpfile
        output cpfile $ flip LJ.hPutDoc corresProofThy

    glue cmds tced tcst typedefs fts insts genst buildinfo log = do
      putProgressLn "Generating glue code..."
      let glreader = GL.mkGlState tced tcst typedefs fts [] insts genst
      runExceptT (GL.glue glreader defaultTypnames GL.TypeMode __cogent_infer_c_type_files) >>= \case
        Left err -> hPutStrLn stderr ("Glue code (types) generation failed: \n" ++ err) >> exitFailure
        Right infed -> do forM_ infed $ \(filename, defs) -> do
                            writeFileMsg $ Just filename
                            output (Just filename) $ flip M.hPutDoc (M.ppr defs </> M.line)
      resAcFiles <- processAcFiles __cogent_infer_c_func_files glreader log
      if not __cogent_interactive
        then earlyExit resAcFiles
        else processMoreAcFiles glreader resAcFiles log

      where
        processMoreAcFiles :: GL.GlState -> Bool -> String -> IO ()
        processMoreAcFiles glreader resAcFiles log = do
          hPutStrLn stderr $ "Cogenti: More ." ++ __cogent_ext_of_ac ++ " files (separated by space, empty to quit): "
          morefiles <- words <$> hGetLine stdin
          if null morefiles
            then earlyExit resAcFiles
            else do resMoreAcFiles <- processAcFiles morefiles glreader log
                    processMoreAcFiles glreader resMoreAcFiles log

        processAcFiles :: [FilePath] -> GL.GlState -> String -> IO Bool
        processAcFiles acfiles glreader log = do
          funcfiles <- forM acfiles $ \funcfile -> do
            let outfile = __cogent_dist_dir `combine` takeFileName (replaceBaseName funcfile (takeBaseName funcfile ++ __cogent_suffix_of_pp))
            putProgressLn $ "Preprocessing C files..."
            -- vvv This is needed because e.g. $(CPP) is defined to be `cc -E'.
            -- The functions in the `process' module normally want the command and the arguments separated.
            let cppcmd:cpparg = words __cogent_cpp
                cppargs = cpparg ++ map (replace "$CPPIN" funcfile . replace "$CPPOUT" outfile) __cogent_cpp_args
            (cppcode, cppout, cpperr) <- readProcessWithExitCode cppcmd cppargs []
            when (not $ null cpperr) $ hPutStrLn stderr cpperr
            when (cppcode /= ExitSuccess) $ exitFailure
            writeFileMsg (Just outfile)
            return outfile
          runExceptT (GL.glue glreader defaultTypnames GL.FuncMode funcfiles) >>= \case
            Left err -> hPutStrLn stderr ("Glue code (functions) generation failed: \n" ++ err) >> return False
            Right infed -> do forM_ infed $ \(filename, defs) -> do
                                writeFileMsg (Just filename)
                                output (Just filename) $ flip M.hPutDoc (M.string ("/*\n" ++ log ++ "\n*/\n") </> M.ppr defs </> M.line)
                              return True
        earlyExit :: Bool -> IO ()
        earlyExit x = if x then return () else exitFailure

    genAst stg defns = lessPretty stdout defns >> exitSuccess

    genPretty stg defns = pretty stdout defns >> exitSuccess

    genDeep cmds source stg defns typedefs fts log = do
      let dpfile = mkThyFileName source (__cogent_suffix_of_deep ++ __cogent_suffix_of_stage stg)
          thy = mkProofName source (Just $ __cogent_suffix_of_deep ++ __cogent_suffix_of_stage stg)
          de = deep thy stg defns fts log
      putProgressLn ("Generating deep embedding (" ++ stgMsg stg ++ ")...")
      writeFileMsg dpfile
      output dpfile $ flip LJ.hPutDoc de

    genShallow cmds source stg defns typedefs fts log (False,False,False,False,False,False,False,False) = return empty
    genShallow cmds source stg defns typedefs fts log (sh,sc,ks,sh_tup,ks_tup,tup_proof,shhs,shhs_tup) = do
          -- Isabelle files
      let shfile = mkThyFileName source (__cogent_suffix_of_shallow ++ __cogent_suffix_of_stage stg)
          ssfile = mkThyFileName source (__cogent_suffix_of_shallow_shared)
          scfile = mkThyFileName source (__cogent_suffix_of_scorres ++ __cogent_suffix_of_stage stg)
          ksfile = mkThyFileName source (__cogent_suffix_of_shallow_consts ++ __cogent_suffix_of_stage stg)
          sh_tupfile = mkThyFileName source (__cogent_suffix_of_shallow ++ __cogent_suffix_of_stage STGDesugar ++ __cogent_suffix_of_recover_tuples)
          ss_tupfile = mkThyFileName source (__cogent_suffix_of_shallow_shared ++ __cogent_suffix_of_recover_tuples)
          ks_tupfile = mkThyFileName source (__cogent_suffix_of_shallow_consts ++ __cogent_suffix_of_stage STGDesugar ++ __cogent_suffix_of_recover_tuples)
          tup_prooffile = mkThyFileName source __cogent_suffix_of_shallow_tuples_proof

          thy = mkProofName source Nothing
          -- Run the generators
          (shal    ,shrd    ,scorr,shallowTypeNames) = Isa.shallow False thy stg        defns log
          (shal_tup,shrd_tup,_    ,_               ) = Isa.shallow True  thy STGDesugar defns log
          constsTypeCheck = IN.tcConsts ((\(a,b,c) -> c) $ fromJust $ getLast typedefs) fts $ filterTypeDefs defns
#ifdef WITH_HASKELL
          -- Haskell shallow embedding
          hsShalName    = mkOutputName' toHsModName source (Just $ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage stg)
          hsShalTupName = mkOutputName' toHsModName source (Just $ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage STGDesugar ++ __cogent_suffix_of_recover_tuples)
          hsShalFile         = nameToFileName hsShalName    __cogent_ext_of_hs
          hsShalTupFile      = nameToFileName hsShalTupName __cogent_ext_of_hs
          hsShal    = \consts -> HS.shallow False hsShalName    stg defns consts log
          hsShalTup = \consts -> HS.shallow True  hsShalTupName stg defns consts log
#endif
          tup_proof_thy = shallowTuplesProof thy
                            (mkProofName source (Just $ __cogent_suffix_of_shallow_shared))
                            (mkProofName source (Just $ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage stg))
                            (mkProofName source (Just $ __cogent_suffix_of_shallow_shared ++ __cogent_suffix_of_recover_tuples))
                            (mkProofName source (Just $ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage STGDesugar ++ __cogent_suffix_of_recover_tuples))
                            shallowTypeNames defns log
      when sh $ do
        putProgressLn ("Generating shallow embedding (" ++ stgMsg stg ++ ")...")
        writeFileMsg ssfile
        output ssfile $ flip LJ.hPutDoc shrd
        writeFileMsg shfile
        output shfile $ flip LJ.hPutDoc shal
#ifdef WITH_HASKELL
      when shhs $ do
        putProgressLn ("Generating Haskell shallow embedding (" ++ stgMsg stg ++ ")...")
        case constsTypeCheck of
          Left err -> hPutStrLn stderr ("Internal TC failed: " ++ err) >> exitFailure
          Right (cs,_) -> do writeFileMsg hsShalFile
                             output hsShalFile $ flip hPutStrLn (hsShal cs)
#endif
      when ks $ do
        putProgressLn ("Generating shallow constants (" ++ stgMsg stg ++ ")...")
        case constsTypeCheck of
          Left err -> hPutStrLn stderr ("Internal TC failed: " ++ err) >> exitFailure
          Right (cs,_) -> do writeFileMsg ksfile
                             output ksfile $ flip LJ.hPutDoc $ shallowConsts False thy stg cs defns log
      when sc $ do
        putProgressLn ("Generating scorres (" ++ stgMsg stg ++ ")...")
        writeFileMsg scfile
        output scfile $ flip LJ.hPutDoc scorr
      when sh_tup $ do
        putProgressLn ("Generating shallow embedding (with HOL tuples)...")
        writeFileMsg ss_tupfile
        output ss_tupfile $ flip LJ.hPutDoc shrd_tup
        writeFileMsg sh_tupfile
        output sh_tupfile $ flip LJ.hPutDoc shal_tup
#ifdef WITH_HASKELL
      when shhs_tup $ do
        putProgressLn ("Generating Haskell shallow embedding (with Haskell tuples)...")
        case constsTypeCheck of
          Left err -> hPutStrLn stderr ("Internal TC failed: " ++ err) >> exitFailure
          Right (cs,_) -> do writeFileMsg hsShalTupFile
                             output hsShalTupFile $ flip hPutStrLn (hsShalTup cs)
#endif
      when ks_tup $ do
        putProgressLn ("Generating shallow constants (with HOL tuples)...")
        case constsTypeCheck of
          Left err -> hPutStrLn stderr ("Internal TC failed: " ++ err) >> exitFailure
          Right (cs,_) -> do writeFileMsg ks_tupfile
                             output ks_tupfile $ flip LJ.hPutDoc $ shallowConsts True thy stg cs defns log

      when tup_proof $ do
        putProgressLn ("Generating shallow tuple proof...")
        writeFileMsg tup_prooffile
        output tup_prooffile $ flip LJ.hPutDoc tup_proof_thy
      return shallowTypeNames

    genBuildInfo cmds buildinfo =
      when (BuildInfo `elem` cmds && not __cogent_fdump_to_stdout) $ do
        let bifile = Just $ __cogent_dist_dir `combine` __cogent_build_info_name
        writeFileMsg bifile
        output bifile $ flip hPutStrLn buildinfo


    -- ------------------------------------------------------------------------
    -- Helper functions

    printError f e = fontSwitch stderr >>= \s ->
                     displayIO stderr (prettyPrint s $ map f e) >>
                     hPutStrLn stderr ""
    usage :: Verbosity -> String
    usage 0 = "Usage: cogent COMMAND.. [FLAG..] FILENAME\n"
    usage v = usage 0 ++
              usageInfoImportant "COMMANDS:" v options ++ "\n" ++
              usageInfoImportant "FLAGS:" v flags

    versionInfo = UT.getCogentVersion
    -- Depending on the target of output, switch on or off fonts
    fontSwitch :: Handle -> IO (Doc -> Doc)
    fontSwitch h = hIsTerminalDevice h >>= \isTerminal ->
                     return $ if isTerminal && __cogent_fpretty_errmsgs then id else plain
    -- Commnad line parsing error
    exitErr x = hPutStrLn stderr ("cogent: " ++ x ++ "(run `cogent -h' for help)") >> exitWith (ExitFailure 133)  -- magic number, doesn't mean anything
    -- Compilation success
    exitSuccess_ = exitWith ExitSuccess
    exitSuccess = putProgressLn "Compilation finished!" >> postDump >> exitWith ExitSuccess
    exitSuccessWithBuildInfo cmds buildinfo = genBuildInfo cmds buildinfo >> exitSuccess
    -- Compilation failure
    exitFailure = hPutStrLn stderr "Compilation failed!" >> postDump >> exitWith (ExitFailure 134)
    -- pretty-print
    pretty h a = fontSwitch h >>= \s -> displayIO h (prettyPrint s a) >> hPutStrLn h ""
    -- pretty AST
    lessPretty h a = hPutStrLn h (ppShow a)
    -- Warnings
    printWarnings :: [Warning] -> IO ()
    printWarnings ws | __cogent_wmono = hPutStr stderr $ unlines $ map ("Warning: " ++) ws
                     | otherwise = return ()

    writeFileMsg :: Maybe FilePath -> IO ()
    writeFileMsg mbfile = when (isJust mbfile) $ putProgressLn ("  > Writing to file: " ++ fromJust mbfile)

    output :: Maybe FilePath -> (Handle -> IO ()) -> IO ()
    output Nothing     f = f stdout
    output (Just path) f = do
      createDirectoryIfMissing True (takeDirectory path)
      atomicWithFile path f

main :: IO ()
main = getArgs >>= parseArgs

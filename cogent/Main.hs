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
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{- LANGUAGE QuasiQuotes -}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- LANGUAGE TemplateHaskell -}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wwarn #-}

module Main where

import Cogent.C.Compile                as CG (printCTable, printATM)
import Cogent.CodeGen                  as CG (cgen)
import Cogent.Common.Syntax            as SY (CoreFunName(..))
import Cogent.Compiler
import Cogent.Core                     as CC (isConFun, getDefinitionId, untypeD)  -- FIXME: zilinc
import Cogent.Desugar                  as DS (desugar)
#ifdef WITH_DOCGENT
import Cogent.DocGent                  as DG (docGent)
#endif
import Cogent.GetOpt
import Cogent.Glue                     as GL (defaultExts, defaultTypnames,
                                              GlState, glue, GlueMode(..), mkGlState,
                                              parseFile, readEntryFuncs)
#ifdef WITH_HASKELL
import Cogent.Haskell.Shallow          as HS
#endif
import Cogent.Inference                as IN (tc, tc_, tcConsts, retype)
import Cogent.Isabelle.ACInstall       as AC (acInstallDefault)
import Cogent.Isabelle.AllRefine       as AR (allRefine)
import Cogent.Isabelle.CorresProof     as CP (corresProof)
import Cogent.Isabelle.CorresSetup     as CS (corresSetup)
import Cogent.Isabelle.Deep            as DP (deep)
import Cogent.Isabelle.MonoProof       as MP  -- FIXME: zilinc
import Cogent.Isabelle.NormalProof     as NP (normalProof)
import Cogent.Isabelle.Root            as RT (root)
import Cogent.Isabelle.Shallow         as IS (shallowConsts, shallow, shallowTuplesProof)
import Cogent.Isabelle.ShallowTable    as ST (st, printTable)  -- for debugging only
import Cogent.Isabelle.TypeProofs      as TP (deepTypeProof)
import Cogent.Isabelle.GraphGen        as GG
import Cogent.Mono                     as MN (mono, printAFM)
import Cogent.Normal                   as NF (normal, verifyNormal)
import Cogent.Parser                   as PA (parseWithIncludes, parseCustTyGen)
import Cogent.Preprocess               as PR
import Cogent.PrettyPrint              as PP (prettyPrint, prettyRE, prettyTWE)
import Cogent.Reorganizer              as RO (reorganize)
import Cogent.Simplify                 as SM
import Cogent.SuParser                 as SU (parse)
import Cogent.Surface                  as SR (stripAllLoc)
import Cogent.TypeCheck                as TC (tc)
import Cogent.TypeCheck.Base           as TC
import Cogent.Util                     as UT

-- import BuildInfo_cogent (githash, buildtime)
#if __GLASGOW_HASKELL__ < 709
import Control.Applicative (liftA, (<$>))
#else
import Control.Applicative (liftA)
#endif
import Control.Monad (forM, forM_, unless, when, (<=<))
import Control.Monad.Trans.Except (runExceptT)
-- import Control.Monad.Cont
-- import Control.Monad.Except (runExceptT)
-- import Control.Monad.Trans.Either (eitherT, runEitherT)
import Data.Char (isSpace)
import Data.Either (isLeft, fromLeft)
import Data.Foldable (fold, foldrM)
import Data.List as L (find, intersect, isPrefixOf, nub, partition)
import Data.Map (empty, fromList)
import Data.Maybe (fromJust, isJust)
import Data.Monoid (getLast)
import Data.Time
import qualified Data.Traversable as T (forM)
-- import Isabelle.InnerAST (subSymStr)
-- import Language.Haskell.TH.Ppr ()
import Prelude hiding (mapM_)
import System.AtomicWrite.Writer.String (atomicWithFile)
-- import System.Console.GetOpt
import System.Directory
import System.Environment
import System.Exit hiding (exitSuccess, exitFailure)
import System.FilePath hiding ((</>))
import System.IO
import System.Process (readProcessWithExitCode)
import Text.PrettyPrint.ANSI.Leijen as LJ (displayIO, Doc, hPutDoc, plain)
#if MIN_VERSION_mainland_pretty(0,6,0)
import Text.PrettyPrint.Mainland as M (hPutDoc, line, string, (</>))
import Text.PrettyPrint.Mainland.Class as M (ppr)
#else
import Text.PrettyPrint.Mainland as M (ppr, hPutDoc, line, string, (</>))
#endif
import Text.Show.Pretty (ppShow)
import Lens.Micro((^.))
-- import Debug.Trace

-- Major modes of operation.
data Mode = ModeAstC
          | ModeStackUsage
          | ModeCompiler
          | ModeAbout
          deriving (Eq, Show)

type Verbosity = Int

-- Commands.
-- Multiple commands may be given, but they must all have the same Mode (wrt. getMode).
-- `!' means collective command
data Command = AstC
             | StackUsage (Maybe FilePath)
             | Compile Stage
             | CodeGen
             | ACInstall
             | CorresSetup
             | CorresProof
             | Documentation
             | CRefinement  -- !
             | Ast       Stage
             | Pretty    Stage
             | HsShallow
             | HsShallowTuples
             | HsFFIGen
             | Deep      Stage
             | Shallow   Stage
             | ShallowTuples -- STGDesugar
             | SCorres   Stage
             | Embedding Stage  -- ! (excl. HsShallow*)
             | ShallowConsts Stage
             | ShallowConstsTuples -- STGDesugar
             | TableCType
             | TableAbsFuncMono
             | TableAbsTypeMono
             | TableShallow
             | ShallowTuplesProof
             | NormalProof
             | MonoProof
             | GraphGen
             | TypeProof Stage
             | AllRefine
             | Root
             | BuildInfo
             | All  -- ! (excl. Hs stuff)
             | QuickCheck  -- !
             | StdGumDir
             | Help Verbosity
             | Version
             -- More
             deriving (Eq, Show)


isAstC :: Command -> Bool
isAstC AstC = True
isAstC _ = False

isStackUsage :: Command -> Bool
isStackUsage (StackUsage _) = True
isStackUsage _ = False

isDeep :: Stage -> Command -> Bool
isDeep s (Deep s') = s == s'
isDeep _ _ = False

isShallow :: Stage -> Command -> Bool
isShallow s (Shallow s') = s == s'
isShallow STGDesugar ShallowTuples = True
isShallow _ _ = False

isSCorres :: Stage -> Command -> Bool
isSCorres s (SCorres s') = s == s'
isSCorres _ _ = False

isShallowConsts :: Stage -> Command -> Bool
isShallowConsts s (ShallowConsts s') = s == s'
isShallowConsts STGDesugar ShallowConstsTuples = True
isShallowConsts _ _ = False

isHelp :: Command -> Bool
isHelp (Help _) = True
isHelp _ = False

addCommands :: [Command] -> Either String (Mode, [Command])
addCommands [] = Left "no command is given"
addCommands [c] = Right (getMode c, setActions c)
addCommands (c:cs) = foldrM addCommand (getMode c, setActions c) cs

addCommand :: Command -> (Mode, [Command]) -> Either String (Mode, [Command])
addCommand c = \(m',cs) -> if getMode c == m'
                            then case checkConflicts c cs of
                                   Nothing  -> Right $ (m', nub $ setActions c ++ cs)
                                   Just err -> Left err
                            else Left $ "command conflicts with others: " ++ show c

getMode :: Command -> Mode
getMode AstC = ModeAstC
getMode (StackUsage _) = ModeStackUsage
getMode StdGumDir = ModeAbout
getMode (Help _) = ModeAbout
getMode Version = ModeAbout
getMode _ = ModeCompiler

ccStandalone :: Command -> [Command] -> Maybe Command
ccStandalone c cs | null cs = Nothing
                  | otherwise = Just c

checkConflicts :: Command -> [Command] -> Maybe String
checkConflicts c cs | isHelp c || c == Version || c == StdGumDir = fmap (("command conflicts with others: " ++) . show) $ ccStandalone c cs
checkConflicts c cs = Nothing

setActions :: Command -> [Command]
-- C
setActions c@AstC = [c]
-- Stack Usage
setActions c@(StackUsage x) = [c]
-- Cogent
setActions c@(Compile STGParse) = [c]
setActions c@(CodeGen      ) = setActions (Compile STGCodeGen) ++ [c]
setActions c@(TableCType   ) = setActions (Compile STGCodeGen) ++ [c]
setActions c@(Compile   stg) = setActions (Compile $ pred stg) ++ [c]
setActions c@(Ast       stg) = setActions (Compile stg) ++ [c]
setActions c@(Documentation) = setActions (Compile STGParse) ++ [c]
setActions c@(Pretty    stg) = setActions (Compile stg) ++ [c]
setActions c@(HsShallow      ) = setActions (Compile STGDesugar) ++ [c]
setActions c@(HsShallowTuples) = setActions (Compile STGDesugar) ++ [c]
setActions c@(HsFFIGen       ) = setActions (Compile STGCodeGen) ++ [c]
setActions c@(Deep      stg) = setActions (Compile stg) ++ [c]
setActions c@(Shallow   stg) = setActions (Compile stg) ++ [c]
setActions c@(ShallowTuples) = setActions (Compile STGDesugar) ++ [c]
setActions c@(SCorres   stg) = setActions (Compile stg) ++ [c]
setActions c@(Embedding stg) = setActions (Compile stg) ++ [Deep stg, Shallow stg, SCorres stg]
setActions c@(ShallowConsts stg) = setActions (Compile stg) ++ [c]
setActions c@ShallowConstsTuples = setActions (Compile STGDesugar) ++ [c]
setActions c@(TableShallow ) = setActions (Compile STGDesugar) ++ [c]
setActions c@(TypeProof stg) = setActions (Compile stg)        ++ [c]
setActions c@ShallowTuplesProof = setActions (ShallowTuples) ++
                                  setActions (ShallowConstsTuples) ++
                                  setActions (Shallow STGDesugar) ++
                                  setActions (ShallowConsts STGDesugar) ++
                                  [c]
setActions c@(NormalProof  ) = setActions (Compile STGNormal)  ++
                               setActions (Shallow STGDesugar) ++
                               setActions (Shallow STGNormal)  ++ [c]
setActions c@(MonoProof    ) = setActions (Compile STGMono)    ++ [c]
setActions c@(ACInstall    ) = setActions (Compile STGMono)    ++ [c]
setActions c@(CorresSetup  ) = setActions (Compile STGMono)    ++ [c]
setActions c@(CorresProof  ) = setActions (Compile STGMono)    ++ [c]
setActions c@(CRefinement  ) = setActions (Compile STGMono)    ++ [ACInstall, CorresSetup, CorresProof]
setActions c@(AllRefine    ) = setActions (Compile STGMono)    ++ [c]
setActions c@(Root         ) = setActions (Compile STGMono)    ++ [c]  -- FIXME: can be earlier / zilinc
setActions c@(BuildInfo    ) = setActions (Compile STGMono)    ++ [c]
setActions c@(GraphGen     ) = setActions (Compile STGMono)    ++ [c]
setActions c@(QuickCheck   ) = nub $ setActions (HsFFIGen) ++
                                     setActions (CodeGen) ++
                                     setActions (HsShallow) ++
                                     setActions (HsShallowTuples) ++
                                     setActions (ShallowTuplesProof)
setActions c@(All          ) = nub $ setActions (TableCType) ++
                                     setActions (CodeGen) ++
                                     setActions (ShallowTuplesProof) ++
                                     setActions (Embedding STGNormal) ++
                                     setActions (TypeProof STGMono) ++
                                     setActions (NormalProof) ++
                                     setActions (MonoProof) ++
                                     setActions (AllRefine) ++
                                     setActions (CRefinement) ++
                                     setActions (Root) ++
                                     setActions (BuildInfo)
setActions c = [c]  -- -h, -v

type Flags = [IO ()]

stgMsg :: Stage -> String
stgMsg STGParse     = "surface"
stgMsg STGTypeCheck = "type-checked surface"
stgMsg STGDesugar   = "desugared core"
stgMsg STGNormal    = "normalised core"
stgMsg STGSimplify  = "simplified core"
stgMsg STGMono      = "monomorphised core"
stgMsg STGCodeGen   = "code generation"

stgCmd :: Stage -> String
stgCmd STGDesugar = "desugar"
stgCmd STGNormal  = "normal"
stgCmd STGMono    = "mono"
stgCmd _          = __impossible "stgCmd"

astMsg s       = "display " ++ stgMsg s ++ " language AST"
prettyMsg s    = "pretty-print " ++ stgMsg s ++ " language"
#ifdef WITH_HASKELL
hsShallowMsg s tup = "generate Haskell shallow embedding (" ++ stgMsg s ++
                     (if tup then ", with Haskell Tuples" else "") ++ ")"
#else
hsShallowMsg s tup = "generate Haskell shallow embedding (" ++ stgMsg s ++
                     (if tup then ", with Haskell Tuples" else "") ++ ") [disabled in this build]"
#endif
deepMsg s      = "generate Isabelle deep embedding (" ++ stgMsg s ++ ")"
shallowMsg s tup = "generate Isabelle shallow embedding (" ++ stgMsg s ++
                   (if tup then ", with HOL tuples" else "") ++ ")"
scorresMsg s   = "generate scorres (" ++ stgMsg s ++ ")"
embeddingMsg s = let s' = stgCmd s
                  in "implies --deep-" ++ s' ++ " --shallow-" ++ s' ++ " --scorres-" ++ s' ++ " --shallow-funcs-" ++ s'
shallowFuncsMsg  s = "generate a list of function names for shallow embedding (" ++ stgMsg s ++ ")"
shallowConstsMsg s tup = "generate constant definitions for shallow embedding (" ++ stgMsg s ++
                         (if tup then ", with HOL tuples" else "") ++ ")"

options :: [OptDescr Command]
options = [
  -- C
    Option []         ["ast-c"]           3 (NoArg AstC)                   "parse C file with Cogent antiquotation and print AST"
  -- stack usage
  , Option ['u']      ["stack-usage"]     3 (OptArg StackUsage "FILE")     "parse stack usage .su file generated by gcc"
  -- compilation
  , Option []         ["parse"]           0 (NoArg $ Compile STGParse)     "parse Cogent source code"
  , Option ['t']      ["typecheck"]       0 (NoArg $ Compile STGTypeCheck) "typecheck surface program"
  , Option []         ["desugar"]         0 (NoArg $ Compile STGDesugar)   "desugar surface program and re-type it"
  , Option []         ["normal"]          0 (NoArg $ Compile STGNormal)    "normalise core language and re-type it"
  , Option []         ["simplify"]        1 (NoArg $ Compile STGSimplify)  "simplify core language and re-type it"
  , Option []         ["mono"]            0 (NoArg $ Compile STGMono)      "monomorphise core language and re-type it"
  , Option ['g']      ["code-gen"]        0 (NoArg CodeGen)                "generate C code"
  -- AST
  , Option []         ["ast-parse"]       2 (NoArg $ Ast STGParse)          (astMsg STGParse)
  , Option []         ["ast-tc"]          2 (NoArg $ Ast STGTypeCheck)      (astMsg STGTypeCheck)
  , Option []         ["ast-desugar"]     2 (NoArg $ Ast STGDesugar)        (astMsg STGDesugar)
  , Option []         ["ast-normal"]      2 (NoArg $ Ast STGNormal)         (astMsg STGNormal)
  , Option []         ["ast-simpl"]       2 (NoArg $ Ast STGSimplify)       (astMsg STGSimplify)
  , Option []         ["ast-mono"]        2 (NoArg $ Ast STGMono)           (astMsg STGMono)
  -- documentation
#ifdef WITH_DOCGENT
  , Option []         ["docgent"]         2 (NoArg $ Documentation)         "generate HTML documentation"
#else
  , Option []         ["docgent"]         2 (NoArg $ Documentation)         "generate HTML documentation [disabled in this build]"
#endif
  -- pretty
  , Option ['p']      ["pretty-parse"]    2 (NoArg $ Pretty STGParse)       (prettyMsg STGParse)
  , Option []         ["pretty-tc"]       2 (NoArg $ Pretty STGTypeCheck)   (prettyMsg STGTypeCheck)
  , Option ['c']      ["pretty-desugar"]  2 (NoArg $ Pretty STGDesugar)     (prettyMsg STGDesugar)
  , Option []         ["pretty-normal"]   2 (NoArg $ Pretty STGNormal)      (prettyMsg STGNormal)
  , Option []         ["pretty-simpl"]    2 (NoArg $ Pretty STGSimplify)    (prettyMsg STGSimplify)
  , Option []         ["pretty-mono"]     2 (NoArg $ Pretty STGMono)        (prettyMsg STGMono)
  -- Haskell shallow
#ifdef WITH_HASKELL
  , Option []         ["hs-shallow-desugar"]         2 (NoArg HsShallow      )  (hsShallowMsg STGDesugar False)
  , Option []         ["hs-shallow-desugar-tuples"]  2 (NoArg HsShallowTuples)  (hsShallowMsg STGDesugar True )
  -- FFI
  , Option []         ["hs-ffi"]          2 (NoArg HsFFIGen)                  "generate Haskell FFI code to access generated C code (incl. a .hsc module for types and a .hs module for functions)"
#else
  , Option []         ["hs-shallow-desugar"]         2 (NoArg HsShallow      )  (hsShallowMsg STGDesugar False)
  , Option []         ["hs-shallow-desugar-tuples"]  2 (NoArg HsShallowTuples)  (hsShallowMsg STGDesugar True )
  -- FFI
  , Option []         ["hs-ffi"]          2 (NoArg HsFFIGen)                  "generate Haskell FFI code to access generated C code (incl. a .hsc module for types and a .hs module for functions) [disabled in this build]"
#endif
  -- deep

  , Option ['D']      ["deep-desugar"]    1 (NoArg (Deep STGDesugar))       (deepMsg STGDesugar)
  , Option ['N']      ["deep-normal"]     1 (NoArg (Deep STGNormal ))       (deepMsg STGNormal)
  , Option ['M']      ["deep-mono"]       1 (NoArg (Deep STGMono   ))       (deepMsg STGMono)
  -- shallow
  , Option ['d']      ["shallow-desugar"] 1 (NoArg (Shallow STGDesugar))    (shallowMsg STGDesugar False)
  , Option ['n']      ["shallow-normal"]  1 (NoArg (Shallow STGNormal ))    (shallowMsg STGNormal  False)
  , Option ['m']      ["shallow-mono"]    1 (NoArg (Shallow STGMono   ))    (shallowMsg STGMono    False)
  , Option []         ["shallow-desugar-tuples"] 1 (NoArg ShallowTuples)    (shallowMsg STGDesugar True)
  -- s-corres
  , Option []         ["scorres-desugar"] 1 (NoArg (SCorres STGDesugar))    (scorresMsg STGDesugar)
  , Option []         ["scorres-normal"]  1 (NoArg (SCorres STGNormal ))    (scorresMsg STGNormal)
  , Option []         ["scorres-mono"]    1 (NoArg (SCorres STGMono   ))    (scorresMsg STGMono)
  -- embedding
  , Option []         ["embedding-desugar"] 1 (NoArg (Embedding STGDesugar)) (embeddingMsg STGDesugar)
  , Option []         ["embedding-normal"]  1 (NoArg (Embedding STGNormal )) (embeddingMsg STGNormal)
  , Option []         ["embedding-mono"]    1 (NoArg (Embedding STGMono   )) (embeddingMsg STGMono)
  -- shallow consts
  , Option []         ["shallow-consts-desugar"] 1 (NoArg (ShallowConsts STGDesugar)) (shallowConstsMsg STGDesugar False)
  , Option []         ["shallow-consts-normal"]  1 (NoArg (ShallowConsts STGNormal )) (shallowConstsMsg STGNormal  False)
  , Option []         ["shallow-consts-mono"]    1 (NoArg (ShallowConsts STGMono   )) (shallowConstsMsg STGMono    False)
  , Option []         ["shallow-consts-desugar-tuples"] 1 (NoArg ShallowConstsTuples) (shallowConstsMsg STGDesugar True)
  -- tuples proof
  , Option []         ["shallow-tuples-proof"]   1 (NoArg ShallowTuplesProof) "generate proof for shallow tuples embedding"
  -- normalisation proof
  , Option []         ["normal-proof"]      1 (NoArg NormalProof)         "generate Isabelle proof of normalisation"
  -- mono proof
  , Option []         ["mono-proof"]        1 (NoArg MonoProof)           "generate monomorphisation proof"
  -- c refinement
  , Option []         ["ac-install"]        1 (NoArg ACInstall)           "generate an Isabelle theory to install AutoCorres"
  , Option []         ["corres-setup"]      1 (NoArg CorresSetup)         "generate Isabelle lemmas for c-refinement"
  , Option []         ["corres-proof"]      1 (NoArg CorresProof)         "generate Isabelle proof of c-refinement"
  , Option ['r']      ["c-refinement"]      1 (NoArg CRefinement)         "implies --ac-install --corres-setup --corres-proof"
  -- type proof
  , Option []         ["type-proof-normal"] 1 (NoArg (TypeProof STGNormal)) "generate Isabelle proof of type correctness of normalised AST"
  , Option ['P']      ["type-proof"]        1 (NoArg (TypeProof STGMono  )) "generate Isabelle proof of type correctness of normal-mono AST"
  -- misc.
  , Option []         ["root"]              1 (NoArg Root)                ("generate Isabelle " ++ __cogent_root_name ++ " file")
  , Option []         ["table-c-types"]     1 (NoArg TableCType)          "generate a table of Cogent and C type correspondence"
  , Option []         ["table-shallow"]     2 (NoArg TableShallow)        "generate a table of type synonyms for shallow embedding"
  , Option []         ["table-abs-func-mono"] 1 (NoArg TableAbsFuncMono)  "generate a table of monomorphised abstract functions"
  , Option []         ["table-abs-type-mono"] 1 (NoArg TableAbsTypeMono)  "generate a table of monomorphised abstract types"
  , Option ['G']      ["graph-gen"]       1 (NoArg GraphGen)              "generate graph for graph-refine"
  , Option []         ["build-info"]      2 (NoArg BuildInfo)             ("generate " ++ __cogent_build_info_name ++ " file")
  -- top level
  , Option []         ["all-refine"]      1 (NoArg AllRefine)          "generate shallow-to-C refinement proof"
  , Option ['A']      ["all"]             0 (NoArg All)                "generate everything"
  , Option ['Q']      ["quickcheck"]      0 (NoArg QuickCheck)         "generate QuickCheck related artifacts"
  -- info.
  , Option []         ["stdgum-dir"]      0 (NoArg StdGumDir)          "directory where standard gum headers are installed (can be set by COGENT_STD_GUM_DIR environment variable)"
  , Option ['h','?']  ["help"]            0 (OptArg (Help . maybe 1 read) "VERBOSITY")  "display help message (VERBOSITY=0..4, default to 1)"
  , Option ['v','V']  ["version"]         0 (NoArg Version)            "show version number"
  ]

flags :: [OptDescr (IO ())]
flags =
  [
  -- names
    Option ['o']      ["output-name"]     1 (ReqArg set_flag_outputName "NAME")            "specify base name for output files (default is derived from source Cogent file)"
  , Option ['y']      ["proof-name"]      1 (ReqArg set_flag_proofName "NAME")             "specify Isabelle theory file name (default is derived from source Cogent file)"
  -- dir specification
  , Option []         ["abs-type-dir"]    1 (ReqArg set_flag_absTypeDir "PATH")            "abstract type definitions will be in $DIR/abstract/, which must exist (default=./)"
  , Option []         ["dist-dir"]        1 (ReqArg set_flag_distDir "PATH")               "specify path to all output files (default=./)"
  , Option []         ["fake-header-dir"] 1 (ReqArg set_flag_fakeHeaderDir "PATH")         "specify path to fake c header files"
  , Option []         ["root-dir"]        1 (ReqArg set_flag_rootDir "PATH")               "specify path to top-level directory (for imports in theory files only, default=./)"
  -- config and other output files
  , Option []         ["cust-ty-gen"]    1 (ReqArg set_flag_custTyGen "FILE")              "config file to customise type generation"
  , Option []         ["entry-funcs"]    1 (ReqArg set_flag_entryFuncs "FILE")             "give a list of Cogent functions that are only called from outside"
  , Option []         ["ext-types"]      1 (ReqArg set_flag_extTypes "FILE")               "give external type names to C parser"
  , Option []         ["infer-c-funcs"]  1 (ReqArg (set_flag_inferCFunc . words) "FILE..") "infer Cogent abstract function definitions"
  , Option []         ["infer-c-types"]  1 (ReqArg (set_flag_inferCType . words) "FILE..") "infer Cogent abstract type definitions"
  , Option []         ["proof-input-c"]  1 (ReqArg set_flag_proofInputC "FILE")            "specify input C file to generate proofs (default to the same base name as input Cogent file)"
  -- external programs
  , Option []         ["cogent-pp-args"] 2 (ReqArg (set_flag_cogentPpArgs) "ARG..")        "arguments given to Cogent preprocessor (same as cpphs), --noline should be enabled"
  , Option []         ["cpp"]            2 (ReqArg (set_flag_cpp) "PROG")                  "set which C-preprocessor to use (default to cpp)"
  , Option []         ["cpp-args"]       2 (ReqArg (set_flag_cppArgs . words) "ARG..")     "arguments given to C-preprocessor (default to $CPPIN -E -P -o $CPPOUT)"
  -- debugging options
  , Option []         ["ddump-smt"]        3 (NoArg set_flag_ddumpSmt)                     "dump verbose SMT-solving information"
  , Option []         ["ddump-tc"]         3 (NoArg set_flag_ddumpTc)                      "dump (massive) surface typechecking internals"
  , Option []         ["ddump-tc-ctx"]     3 (NoArg set_flag_ddumpTcCtx)                   "dump surface typechecking with context"
  , Option []         ["ddump-tc-filter"]  3 (ReqArg set_flag_ddumpTcFilter "KEYWORDS")    "a space-separated list of keywords to indicate which groups of info to display (gen, sol, post, tc)"
  , Option []         ["ddump-to-file"]    3 (ReqArg set_flag_ddumpToFile "FILE")          "dump debugging output to specific file instead of terminal"
  -- behaviour
  , Option []         ["fcheck-undefined"]    2 (NoArg set_flag_fcheckUndefined)           "(default) check for undefined behaviours in C"
  , Option ['B']      ["fdisambiguate-pp"]    3 (NoArg set_flag_fdisambiguatePp)           "when pretty-printing, also display internal representation as comments"
  , Option []         ["fffi-c-functions"]    1 (NoArg set_flag_fffiCFunctions)            "generate FFI functions in the C code (should be used when -Q)"
  , Option []         ["fflatten-nestings"]   2 (NoArg set_flag_fflattenNestings)          "flatten out nested structs in C code (does nothing)"
  , Option []         ["ffncall-as-macro"]    3 (NoArg set_flag_ffncallAsMacro)            "generate macros instead of real function calls"
  , Option []         ["ffull-src-path"]      2 (NoArg set_flag_ffullSrcPath)              "display full path for source file locations"
  , Option []         ["ffunc-purity-attr"]   2 (NoArg set_flag_ffuncPurityAttr)           "(default) generate GCC attributes to classify purity of Cogent functions"
  , Option []         ["fgen-header"]          2 (NoArg set_flag_fgenHeader)               "generate build info header in all output files, reverse of --fno-gen-header"
  , Option []         ["fintermediate-vars"]   2 (NoArg set_flag_fintermediateVars)        "(default) generate intermediate variables for Cogent expressions"
  , Option []         ["flax-take-put"]        3 (NoArg set_flag_flaxTakePut)              "allow take/put type operators on abstract datatypes"
  , Option []         ["flet-in-if"]           2 (NoArg set_flag_fletInIf)                 "(default) put binding of a let inside an if-clause"
  , Option []         ["fletbang-in-if"]       2 (NoArg set_flag_fletbangInIf)             "(default) put binding of a let! inside an if-clause"
  , Option []         ["fml-typing-tree"]      2 (NoArg set_flag_fmlTypingTree)            "(default) generate ML typing tree in type proofs"
  , Option []         ["fnormalisation"]       2 (OptArg set_flag_fnormalisation "NF")     "(default) normalise the core language (NF=anf[default], knf, lnf)"
  , Option []         ["fno-check-undefined"]    1 (NoArg set_flag_fnoCheckUndefined)      "reverse of --fcheck-undefined"
  , Option []         ["fno-flatten-nestings"]   2 (NoArg set_flag_fnoFlattenNestings)     "(default) reverse of --fflatten-nestings"
  , Option []         ["fno-fncall-as-macro"]    2 (NoArg set_flag_fnoFncallAsMacro)       "(default) reverse of --ffncall-as-macro"
  , Option []         ["fno-func-purity-attr"]   2 (NoArg set_flag_fnoFuncPurityAttr)      "reverse of --ffunc-purity-attr"
  , Option []         ["fno-gen-header"]         2 (NoArg set_flag_fnoGenHeader)           "(default) don't generate build info header in any output files"
  , Option []         ["fno-intermediate-vars"]  1 (NoArg set_flag_fnoIntermediateVars)    "reverse of --fintermediate-vars"
  , Option []         ["fno-lax-take-put"]       3 (NoArg set_flag_fnoLaxTakePut)          "(default) reverse of --flax-take-put"
  , Option []         ["fno-let-in-if"]          1 (NoArg set_flag_fnoLetInIf)             "reverse of --flet-in-if"
  , Option []         ["fno-letbang-in-if"]      1 (NoArg set_flag_fnoLetbangInIf)         "reverse of --fletbang-in-if"
  , Option []         ["fno-ml-typing-tree"]     2 (NoArg set_flag_fnoMlTypingTree)        "reverse of --fml-typing-tree"
  , Option []         ["fno-normalisation"]      1 (NoArg set_flag_fnoNormalisation)       "reverse of --fnormalisation"
  , Option []         ["fno-pragmas"]            1 (NoArg set_flag_fnoPragmas)             "reverse of --fpragmas"
  , Option []         ["fno-pretty-errmsgs"]     3 (NoArg set_flag_fnoPrettyErrmsgs)       "reverse of --fpretty-errmsgs"
  , Option []         ["fno-reverse-tc-errors"]  2 (NoArg set_flag_fnoReverseTcErrors)     "(default) reverse of --freverse-tc-errors"
  , Option []         ["fno-share-linear-vars"]  2 (NoArg set_flag_fnoShareLinearVars)     "(default) reverse of --fshare-linear-vars"
  , Option []         ["fno-show-types-in-pretty"] 2 (NoArg set_flag_fnoShowTypesInPretty) "(default) reverse of --fshow-types-in-pretty"
  , Option []         ["fno-simplifier"]      2 (NoArg set_flag_fnoSimplifier)             "(default) reverse of --fsimplifier"
  , Option []         ["fno-static-inline"]   1 (NoArg set_flag_fnoStaticInline)           "reverse of --fstatic-inline"
  , Option []         ["fno-tc-ctx-constraints"] 3 (NoArg set_flag_ftcCtxConstraints)      "(default) reverse of --ftc-ctx-constraints"
  , Option []         ["fno-tp-with-bodies"]  1   (NoArg set_flag_fnoTpWithBodies)         "reverse of --ftp-with-bodies"
  , Option []         ["fno-tp-with-decls"]   1   (NoArg set_flag_fnoTpWithDecls)          "reverse of --ftp-with-decls"
  , Option []         ["fno-tuples-as-sugar"] 1 (NoArg set_flag_fnoTuplesAsSugar)          "reverse of --ftuples-as-sugar"
  , Option []         ["fno-union-for-variants"] 2 (NoArg set_flag_fnoUnionForVariants)    "(default) reverse of --funion-for-variants"
  , Option []         ["fno-untyped-func-enum"]  2 (NoArg set_flag_fnoUntypedFuncEnum)     "reverse of --funtyped-func-enum"
  , Option []         ["fno-use-compound-literals"] 1 (NoArg set_flag_fnoUseCompoundLiterals)   "reverse of --fuse-compound-literals, it instead creates new variables"
  , Option []         ["fno-wrap-put-in-let"] 2 (NoArg set_flag_fnoWrapPutInLet)           "(default) reverse of --fwrap-put-in-let"
  , Option []         ["fpragmas"]            2 (NoArg set_flag_fpragmas)                  "(default) preprocess pragmas"
  , Option []         ["fpretty-errmsgs"]     3 (NoArg set_flag_fprettyErrmsgs)            "(default) pretty-print error messages (requires ANSI support)"
  , Option []         ["freverse-tc-errors"]  1 (NoArg set_flag_freverseTcErrors)          "Print type errors in reverse order"
  , Option []         ["fshare-linear-vars"]  2 (NoArg set_flag_fshareLinearVars)          "reuse C variables for linear objects"
  , Option ['T']      ["fshow-types-in-pretty"] 2 (NoArg set_flag_fshowTypesInPretty)      "show inferred types of each AST node when doing pretty-printing"
  , Option []         ["fsimplifier"]         1 (NoArg set_flag_fsimplifier)               "enable simplifier on core language"
  , Option []         ["fsimplifier-level"]   1 (ReqArg (set_flag_fsimplifierIterations . read) "NUMBER")  "number of iterations simplifier does (default=4)"
  , Option []         ["fstatic-inline"]      2 (NoArg set_flag_fstaticInline)             "(default) generate static-inlined functions in C"
  , Option []         ["ftuples-as-sugar"]    2 (NoArg set_flag_ftuplesAsSugar)            "(default) treat tuples as syntactic sugar to unboxed records, which gives better performance"
  , Option ['C']      ["ftc-ctx-constraints"] 3 (NoArg set_flag_ftcCtxConstraints)         "display constraints in type errors"
  , Option ['l']      ["ftc-ctx-len"]         1 (ReqArg (set_flag_ftcCtxLen . read) "NUMBER")   "set the depth for printing error context in typechecker (default=3)"
  , Option []         ["ftp-with-bodies"]     2 (NoArg set_flag_ftpWithBodies)             "(default) generate type proof with bodies"
  , Option []         ["ftp-with-decls"]      2 (NoArg set_flag_ftpWithDecls)              "(default) generate type proof with declarations"
  , Option []         ["funion-for-variants"] 2 (NoArg set_flag_funionForVariants)         "use union types for variants in C code (cannot be verified)"
  , Option []         ["funtyped-func-enum"]  2 (NoArg set_flag_funtypedFuncEnum)          "(default) use untyped function enum type"
  , Option []         ["fuse-compound-literals"] 2 (NoArg set_flag_fuseCompoundLiterals)   "(default) use compound literals when possible in C code"
  , Option []         ["fwrap-put-in-let"]       1 (NoArg set_flag_fwrapPutInLet)          "Put always appears in a Let-binding when normalised"
  , Option ['O']      ["optimisation"]   0 (OptArg set_flag_O "LEVEL")                     "set optimisation level (0, 1, 2, d, n, s or u; default -Od)"
  -- warning control
  , Option []         ["Wall"]           1 (NoArg set_flag_Wall)                           "issue all warnings"
  , Option ['E']      ["Werror"]         1 (NoArg set_flag_Werror)                         "make any warning into a fatal error"
  , Option []         ["Wdodgy-take-put"]             2 (NoArg set_flag_WdodgyTakePut) "(default) enable warnings on ill-formed take or put in types"
  , Option []         ["Wdynamic-variant-promotion"]  2 (NoArg set_flag_WdynamicVariantPromotion) "enable warnings on dynamic variant type promotion"
  , Option []         ["Wimplicit-int-lit-promotion"] 2 (NoArg set_flag_WimplicitIntLitPromotion) "(default) enable warning on implicit integer literal promotion"
  , Option []         ["Wmono"]                       3 (NoArg set_flag_Wmono) "enable warnings during monomorphisation"
  , Option []         ["Wunused-local-binds"]         2 (NoArg set_flag_WunusedLocalBinds) "warn about unused local binders"
  , Option []         ["Wno-dodgy-take-put"]             2 (NoArg set_flag_WnoDodgyTakePut) "reverse of --Wdodgy-take-put"
  , Option []         ["Wno-dynamic-variant-promotion"]  2 (NoArg set_flag_WnoDynamicVariantPromotion) "(default) reverse of --Wdynamic-variant-promotion"
  , Option []         ["Wno-mono"]                       3 (NoArg set_flag_WnoMono) "(default) reverse of --Wmono"
  , Option []         ["Wno-implicit-int-lit-promotion"] 2 (NoArg set_flag_WnoImplicitIntLitPromotion) "reverse of --Wimplicit-int-lit-promotion"
  , Option []         ["Wno-unused-local-binds"]         2 (NoArg set_flag_WnoUnusedLocalBinds) "(default) reverse of --Wunused-local-binds"
  , Option ['w']      ["Wno-warn"]      1 (NoArg set_flag_w)                               "turn off all warnings"
  , Option []         ["Wwarn"]         1 (NoArg set_flag_Wwarn)                           "(default) warnings are treated only as warnings, not as errors"
  -- misc
  , Option ['q']      ["quiet"]            1 (NoArg set_flag_quiet)                        "do not display compilation progress"
  , Option ['x']      ["fdump-to-stdout"]  1 (NoArg set_flag_fdumpToStdout)                "dump all output to stdout"
  , Option ['i']      ["interactive"]      3 (NoArg set_flag_interactive)                  "interactive compiler mode"
  ]

parseArgs :: [String] -> IO ()
parseArgs args = case getOpt' Permute options args of
    (cmds,xs,us,[]) -> case addCommands cmds of
                         Left  err -> exitErr (err ++ "\n")
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
    noFlagError ([StdGumDir],_,_,_) = getStdGumDir >>= putStrLn >> exitSuccess_
    noFlagError ([Help v],_,_,_) = putStr (usage v) >> exitSuccess_
    noFlagError ([Version],_,_,_) = putStrLn versionInfo >> exitSuccess_
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
                 buildinfo = "This file is generated by " ++ versionInfo ++ "\n" ++
                             "with command ./cogent " ++ unwords args ++ "\n" ++
                             "at " ++ formatTime defaultTimeLocale "%a, %-d %b %Y %H:%M:%S %Z" zoned
                 log = if __cogent_fgen_header
                         then buildinfo
                         else "This build info header is now disabled by --fno-gen-header.\n" ++
                              "--------------------------------------------------------------------------------\n" ++
                              "We strongly discourage users from generating individual files for Isabelle\n" ++
                              "proofs, as it will end up with an inconsistent collection of output files (i.e.\n" ++
                              "Isabelle input files)."
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
      parseWithIncludes source [] >>= \case
        Left err -> hPutStrLn stderr err >> exitFailure
        Right (parsed,pragmas) -> do
          putProgressLn "Resolving dependencies..." >> case reorganize parsed of
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
      ((mtc',tclog),tcst) <- TC.tc reorged ctygen
      let (errs,warns) = partition (isLeft . snd) $ tclog^.errLog
      when (not $ null errs) $ do
        printError (prettyTWE __cogent_ftc_ctx_len) errs
        when (and $ map (isWarnAsError . fromLeft undefined . snd) errs) $ hPutStrLn stderr "Failing due to --Werror."
        exitFailure
      case mtc' of
        Nothing -> __impossible "main: typecheck"
        Just (tced,ctygen') -> do
          __assert (null errs) "no errors, only warnings"
          unless (null $ warns) $ printError (prettyTWE __cogent_ftc_ctx_len) $ warns
          when (Ast stg `elem` cmds) $ genAst stg tced
          when (Pretty stg `elem` cmds) $ genPretty stg tced
          when (Compile (succ stg) `elem` cmds) $ desugar cmds tced ctygen' tcst source (map pragmaOfLP pragmas) buildinfo log
          exitSuccessWithBuildInfo cmds buildinfo

    desugar cmds tced ctygen tcst source pragmas buildinfo log = do
      let stg = STGDesugar
      putProgressLn "Desugaring and typing..."
      let ((desugared,ctygen'),typedefs) = DS.desugar tced ctygen pragmas
      case IN.tc desugared of
        Left err -> hPutStrLn stderr ("Internal TC failed: " ++ err) >> exitFailure
        Right (desugared',fts) -> do
          when (Ast stg `elem` cmds) $ genAst stg desugared'
          when (Pretty stg `elem` cmds) $ genPretty stg desugared'
          when (Deep stg `elem` cmds) $ genDeep cmds source stg desugared' typedefs fts log
          _ <- genShallow cmds source stg desugared' typedefs fts log (Shallow stg `elem` cmds,
                                                                       SCorres stg `elem` cmds,
                                                                       ShallowConsts stg `elem` cmds,
                                                                       ShallowTuples `elem` cmds,
                                                                       ShallowConstsTuples `elem` cmds,
                                                                       ShallowTuplesProof `elem` cmds,
                                                                       HsShallow `elem` cmds,
                                                                       HsShallowTuples `elem` cmds)
          when (TableShallow `elem` cmds) $ putProgressLn ("Generating shallow table...") >> putStrLn (printTable $ st desugared')
          when (Compile (succ stg) `elem` cmds) $ normal cmds desugared' ctygen' source tced tcst typedefs fts buildinfo log
          exitSuccessWithBuildInfo cmds buildinfo

    normal cmds desugared ctygen source tced tcst typedefs fts buildinfo log = do
      let stg = STGNormal
      putProgress "Normalising..."
      nfed' <- case __cogent_fnormalisation of
        NoNF -> putProgressLn "Skipped" >> return desugared
        nf -> do putProgressLn (show nf)
                 let nfed = NF.normal $ map untypeD desugared
                 if not $ verifyNormal nfed
                   then hPutStrLn stderr "Normalisation failed!" >> exitFailure
                   else do putProgressLn "Re-typing NF..."
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
          deepTypeProof id __cogent_ftp_with_decls __cogent_ftp_with_bodies tpthy nfed' log
      shallowTypeNames <-
        genShallow cmds source stg nfed' typedefs fts log (Shallow stg `elem` cmds,
                                                           SCorres stg `elem` cmds,
                                                           ShallowConsts stg `elem` cmds,
                                                           False, False, False, False, False)
      when (NormalProof `elem` cmds) $ do
        let npfile = mkThyFileName source __cogent_suffix_of_normal_proof
        writeFileMsg npfile
        output npfile $ flip LJ.hPutDoc $ normalProof thy shallowTypeNames nfed' log
      when (Compile (succ stg) `elem` cmds) $ simpl cmds nfed' ctygen source tced tcst typedefs fts buildinfo log
      exitSuccessWithBuildInfo cmds buildinfo

    simpl cmds nfed ctygen source tced tcst typedefs fts buildinfo log = do
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
      when (Compile (succ stg) `elem` cmds) $ mono cmds simpled' ctygen source tced tcst typedefs fts buildinfo log
      exitSuccessWithBuildInfo cmds buildinfo

    mono cmds simpled ctygen source tced tcst typedefs fts buildinfo log = do
      let stg = STGMono
      putProgressLn "Monomorphising..."
      -- entryFuncs <- T.forM __cogent_entry_funcs $
      --                liftA ((,empty) . fromList . flip zip (repeat empty) . parseEntryFuncs) . readFile
      entryFuncs <- T.forM __cogent_entry_funcs $
                      return . (,empty) <=< (readEntryFuncs tced tcst typedefs fts) <=< return . parseEntryFuncs <=< readFile
      let (insts,(warnings,monoed,ctygen')) = MN.mono simpled ctygen entryFuncs
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
          when (Compile (succ stg) `elem` cmds) $ cg cmds monoed' ctygen' insts source tced tcst typedefs fts buildinfo log
          c_refinement source monoed' insts log (ACInstall `elem` cmds, CorresSetup `elem` cmds, CorresProof `elem` cmds)
          when (MonoProof `elem` cmds) $ do
            let mpfile = mkThyFileName source __cogent_suffix_of_mono_proof
            writeFileMsg mpfile
            output mpfile $ flip LJ.hPutDoc $ monoProof source (fst insts) log
          when (TypeProof STGMono `elem` cmds) $ do
            let tpfile = mkThyFileName source __cogent_suffix_of_type_proof
                tpthy  = mkProofName source (Just __cogent_suffix_of_type_proof)
            writeFileMsg tpfile
            output tpfile $ flip LJ.hPutDoc $ deepTypeProof id __cogent_ftp_with_decls __cogent_ftp_with_bodies tpthy monoed' log
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

    cg cmds monoed ctygen insts source tced tcst typedefs fts buildinfo log = do
      let hName = mkOutputName source Nothing <.> __cogent_ext_of_h
          hscName = mkOutputName' toHsModName source (Just __cogent_suffix_of_ffi_types)
          hsName  = mkOutputName' toHsModName source (Just __cogent_suffix_of_ffi)
          cNames  = map (\n -> takeBaseName n ++ __cogent_suffix_of_pp ++ __cogent_suffix_of_inferred <.> __cogent_ext_of_c) __cogent_infer_c_func_files
          (h,c,atm,ct,hsc,hs,genst) = cgen hName cNames hscName hsName monoed ctygen log
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
        ent <- T.forM __cogent_entry_funcs $ (liftA parseEntryFuncs) . readFile  -- a simple parser
        let corresProofThy = corresProof thy inputc (map SY.CoreFunName confns) (map SY.CoreFunName <$> ent) log
        writeFileMsg cpfile
        output cpfile $ flip LJ.hPutDoc corresProofThy

    glue cmds tced tcst typedefs fts insts genst buildinfo log = do
      putProgressLn "Generating glue code..."
      let glreader = GL.mkGlState tced tcst typedefs fts insts genst
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
            let cppargs = map (replace "$CPPIN" funcfile . replace "$CPPOUT" outfile) __cogent_cpp_args
            (cppcode, cppout, cpperr) <- readProcessWithExitCode __cogent_cpp cppargs []
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

    -- genAst :: Stage -> [Definition TypedExpr VarName] -> IO ()
    genAst stg defns = lessPretty stdout defns >> exitSuccess

    -- genPretty :: Stage -> [Definition TypedExpr VarName] -> IO ()
    genPretty stg defns = pretty stdout defns >> exitSuccess

    genDeep cmds source stg defns typedefs fts log = do
      let dpfile = mkThyFileName source (__cogent_suffix_of_deep ++ __cogent_suffix_of_stage stg)
          thy = mkProofName source (Just $ __cogent_suffix_of_deep ++ __cogent_suffix_of_stage stg)
          de = deep thy stg defns log
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
          (shal    ,shrd    ,scorr,shallowTypeNames) = IS.shallow False thy stg        defns log
          (shal_tup,shrd_tup,_    ,_               ) = IS.shallow True  thy STGDesugar defns log
          constsTypeCheck = IN.tcConsts ((\(a,b,c) -> c) $ fromJust $ getLast typedefs) fts
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

    -- --entry-funcs expects one function name per line; lines starting with -- are comments
    parseEntryFuncs = filter (not . isPrefixOf "--") . filter (not . null) . map (dropWhile isSpace) . lines

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

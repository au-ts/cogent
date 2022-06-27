module Cogent.Flags where

import Cogent.Compiler
import Cogent.GetOpt
import Cogent.Util

import Data.Foldable (foldrM)
import Data.List (nub)


-- Major modes of operation.
data Mode = ModeAstC
          | ModeStackUsage
          | ModeCompiler
          | ModeInterpreter
          | ModeLLVM
          | ModeAbout
          deriving (Eq, Show)

type Verbosity = Int

-- Commands.
-- Multiple commands may be given, but they must all have the same Mode (wrt. getMode).
-- `!' means collective command
data Command = AstC
             | StackUsage (Maybe FilePath)
             | Compile Stage
             | Interpret
             | CodeGen
             | LLVMGen
             | ACInstall
             | CorresSetup
             | CorresProof
             | Documentation
             | Ast       Stage
             | Pretty    Stage
             | HsShallow
             | HsShallowTuples
             | HsFFIGen
             | Deep      Stage
             | Shallow   Stage
             | ShallowTuples -- STGDesugar
             | SCorres   Stage
             | ShallowConsts Stage
             | ShallowConstsTuples -- STGDesugar
             | TableCType
             | NewTableCType
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
             | CRefinement  -- !
             | FunctionalCorrectness  -- !
             | QuickCheck  -- !
             | LibgumDir
             | Help Verbosity
             | Version
             -- More
             deriving (Eq, Show)


isAstC :: Command -> Bool
isAstC AstC = True
isAstC _    = False

isStackUsage :: Command -> Bool
isStackUsage (StackUsage _) = True
isStackUsage _              = False
 
isLLVMGen :: Command -> Bool
isLLVMGen LLVMGen = True
isLLVMGen _       = False

isDeep :: Stage -> Command -> Bool
isDeep s (Deep s') = s == s'
isDeep _ _         = False

isShallow :: Stage -> Command -> Bool
isShallow s (Shallow s')           = s == s'
isShallow STGDesugar ShallowTuples = True
isShallow _ _                      = False

isSCorres :: Stage -> Command -> Bool
isSCorres s (SCorres s') = s == s'
isSCorres _ _            = False

isShallowConsts :: Stage -> Command -> Bool
isShallowConsts s (ShallowConsts s')           = s == s'
isShallowConsts STGDesugar ShallowConstsTuples = True
isShallowConsts _ _                            = False

isHelp :: Command -> Bool
isHelp (Help _) = True
isHelp _        = False

addCommands :: [Command] -> Either String (Mode, [Command])
addCommands []     = Left "no command is given"
addCommands [c]    = Right (getMode c, setActions c)
addCommands (c:cs) = foldrM addCommand (getMode c, setActions c) cs

addCommand :: Command -> (Mode, [Command]) -> Either String (Mode, [Command])
addCommand c = \(m',cs) -> if getMode c == m'
                            then case checkConflicts c cs of
                                   Nothing  -> Right $ (m', nub $ setActions c ++ cs)
                                   Just err -> Left err
                            else Left $ "command conflicts with others: " ++ show c

getMode :: Command -> Mode
getMode AstC           = ModeAstC
getMode (StackUsage _) = ModeStackUsage
getMode LibgumDir      = ModeAbout
getMode (Help _)       = ModeAbout
getMode Version        = ModeAbout
getMode LLVMGen        = ModeLLVM
getMode _              = ModeCompiler

ccStandalone :: Command -> [Command] -> Maybe Command
ccStandalone c cs | null cs = Nothing
                  | otherwise = Just c

checkConflicts :: Command -> [Command] -> Maybe String
checkConflicts c cs | isHelp c || c == Version || c == LibgumDir || c == Interpret
  = fmap (("command conflicts with others: " ++) . show) $ ccStandalone c cs
checkConflicts c cs = Nothing

setActions :: Command -> [Command]
-- C
setActions c@AstC = [c]
-- Stack Usage
setActions c@(StackUsage x) = [c]
-- LLVM
setActions c@LLVMGen = setActions (Compile STGMono) ++ [c]
-- Cogent
setActions c@(Compile STGParse) = [c]
setActions c@(CodeGen      ) = setActions (Compile STGCodeGen) ++ [c]
setActions c@(TableCType   ) = setActions (Compile STGCodeGen) ++ [c]
setActions c@(NewTableCType) = setActions (Compile STGCodeGen) ++ [c]
setActions c@(Compile   stg) = setActions (Compile $ pred stg) ++ [c]
setActions c@(Interpret    ) = [c]
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
setActions c@(AllRefine    ) = setActions (Compile STGMono)    ++ [c]
setActions c@(Root         ) = setActions (Compile STGMono)    ++ [c]  -- FIXME: can be earlier / zilinc
setActions c@(BuildInfo    ) = [c]
setActions c@(GraphGen     ) = setActions (Compile STGMono)    ++ [c]
-- NOTE: The --c-refinement flag generates almost all the things C refinement proof needs, but the
-- proof is actually done in AllRefine, which also relies on the functional correctness proof. It
-- means that, unfortunately, we can't simply split up the thing into two halves cleanly. We have to generate
-- everything even when only part of it is needed. / zilinc
setActions c@(CRefinement  ) = nub $ setActions (CodeGen) ++
                                     setActions (Deep STGNormal) ++
                                     setActions (Shallow STGNormal) ++
                                     setActions (SCorres STGNormal) ++
                                     setActions (TypeProof STGMono) ++
                                     setActions (MonoProof) ++  -- although technically only needed for C-refinement,
                                                                -- it's only invoked in AllRefine.
                                     setActions (TableCType) ++
                                     setActions (NewTableCType) ++
                                     setActions (Root) ++
                                     [ACInstall, CorresSetup, CorresProof, BuildInfo]
setActions c@(FunctionalCorrectness) = nub $ setActions (ShallowTuplesProof) ++
                                             setActions (NormalProof) ++
                                             setActions (Root) ++
                                             [BuildInfo]
setActions c@(QuickCheck   ) = nub $ setActions (HsFFIGen) ++
                                     setActions (CodeGen) ++
                                     setActions (HsShallow) ++
                                     setActions (HsShallowTuples) ++
                                     setActions (ShallowTuplesProof) ++
                                     [BuildInfo]
setActions c@(All          ) = nub $ setActions (CodeGen) ++
                                     setActions (CRefinement) ++
                                     setActions (FunctionalCorrectness) ++
                                     setActions (AllRefine)
setActions c = [c]  -- -h, -v


options :: [OptDescr Command]
options = [
  -- C
    Option []         ["ast-c"]           3 (NoArg AstC)                   "parse C file with Cogent antiquotation and print AST"
  -- stack usage
  , Option []         ["stack-usage"]     3 (OptArg StackUsage "FILE")     "parse stack usage .su file generated by gcc"
  -- compilation
  , Option []         ["parse"]           0 (NoArg $ Compile STGParse)     "parse Cogent source code"
  , Option ['t']      ["typecheck"]       0 (NoArg $ Compile STGTypeCheck) "typecheck surface program"
  , Option ['d']      ["desugar"]         0 (NoArg $ Compile STGDesugar)   "desugar surface program and re-type it"
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
  -- interpreter
  , Option ['i']      ["repl"]            1 (NoArg $ Interpret)             "run Cogent REPL"
  -- llvm
#ifdef WITH_LLVM
  , Option []         ["llvm"]            0 (NoArg LLVMGen)                 "use the experimental LLVM backend"
#else
  , Option []         ["llvm"]            0 (NoArg LLVMGen)                 "use the experimental LLVM backend [disabled in this build]"
#endif
  -- documentation
#ifdef WITH_DOCGENT
  , Option []         ["docgent"]         2 (NoArg $ Documentation)         "generate HTML documentation"
#else
  , Option []         ["docgent"]         2 (NoArg $ Documentation)         "generate HTML documentation [disabled in this build]"
#endif
  -- pretty
  , Option []         ["pretty-parse"]    2 (NoArg $ Pretty STGParse)       (prettyMsg STGParse)
  , Option ['T']      ["pretty-tc"]       2 (NoArg $ Pretty STGTypeCheck)   (prettyMsg STGTypeCheck)
  , Option ['D']      ["pretty-desugar"]  2 (NoArg $ Pretty STGDesugar)     (prettyMsg STGDesugar)
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

  , Option []         ["deep-desugar"]    1 (NoArg (Deep STGDesugar))       (deepMsg STGDesugar)
  , Option []         ["deep-normal"]     1 (NoArg (Deep STGNormal ))       (deepMsg STGNormal)
  , Option []         ["deep-mono"]       1 (NoArg (Deep STGMono   ))       (deepMsg STGMono)
  -- shallow
  , Option []         ["shallow-desugar"] 1 (NoArg (Shallow STGDesugar))    (shallowMsg STGDesugar False)
  , Option []         ["shallow-normal"]  1 (NoArg (Shallow STGNormal ))    (shallowMsg STGNormal  False)
  , Option []         ["shallow-mono"]    1 (NoArg (Shallow STGMono   ))    (shallowMsg STGMono    False)
  , Option []         ["shallow-desugar-tuples"] 1 (NoArg ShallowTuples)    (shallowMsg STGDesugar True)
  -- s-corres
  , Option []         ["scorres-desugar"] 1 (NoArg (SCorres STGDesugar))    (scorresMsg STGDesugar)
  , Option []         ["scorres-normal"]  1 (NoArg (SCorres STGNormal ))    (scorresMsg STGNormal)
  , Option []         ["scorres-mono"]    1 (NoArg (SCorres STGMono   ))    (scorresMsg STGMono)
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
  -- type proof
  , Option []         ["type-proof-normal"] 1 (NoArg (TypeProof STGNormal)) "generate Isabelle proof of type correctness of normalised AST"
  , Option []         ["type-proof"]        1 (NoArg (TypeProof STGMono  )) "generate Isabelle proof of type correctness of normal-mono AST"
  -- top-level theory
  , Option []         ["all-refine"]      1 (NoArg AllRefine)          "[COLLECTIVE] generate shallow-to-C refinement proof"
  -- misc.
  , Option []         ["root"]              1 (NoArg Root)                ("generate Isabelle " ++ __cogent_root_name ++ " file")
  , Option []         ["table-c-types"]     1 (NoArg TableCType)          "generate a table of Cogent and C type correspondence"
  , Option []         ["new-table-c-types"] 1 (NoArg NewTableCType)       "generate a table of Cogent and C type correspondence, and getter/setter functions for Dargent"
  , Option []         ["table-shallow"]     1 (NoArg TableShallow)        "generate a table of type synonyms for shallow embedding"
  , Option []         ["table-abs-func-mono"] 3 (NoArg TableAbsFuncMono)  "generate a table of monomorphised abstract functions"
  , Option []         ["table-abs-type-mono"] 3 (NoArg TableAbsTypeMono)  "generate a table of monomorphised abstract types"
  , Option ['G']      ["graph-gen"]       3 (NoArg GraphGen)              "generate graph for graph-refine"
  , Option []         ["build-info"]      0 (NoArg BuildInfo)             ("log how cogent is being invoked by generating " ++ __cogent_build_info_name ++ " file; implied by any collective commands")
  -- top level
  , Option ['C']      ["c-refinement"]    0 (NoArg CRefinement)        "[COLLECTIVE] generate all files needed for the C refinement proof"
  , Option ['F']      ["functional-correctness"] 0 (NoArg FunctionalCorrectness) "[COLLECTIVE] generate all files needed for the functional correctness proof"
  , Option ['A']      ["all"]             0 (NoArg All)                "[COLLECTIVE] generate everything"
  , Option ['Q']      ["quickcheck"]      1 (NoArg QuickCheck)         "[COLLECTIVE] generate QuickCheck related artifacts"
  -- info.
  , Option []         ["libgum-dir"]      0 (NoArg LibgumDir)          "display directory where libgum is installed (can be set by COGENT_LIBGUM_DIR environment variable)"
  , Option ['h','?']  ["help"]            0 (OptArg (Help . maybe 1 read) "VERBOSITY")  "display help message (VERBOSITY=0..4, default to 1)"
  , Option ['v','V']  ["version"]         0 (NoArg Version)            "show version number"
  ]

flags :: [OptDescr (IO ())]
flags =
  [
  -- names
    Option ['o']      ["output-name"]     1 (ReqArg set_flag_outputName "NAME")            "specify base name for output files (default is derived from source Cogent file)"
  , Option []         ["proof-name"]      1 (ReqArg set_flag_proofName "NAME")             "specify Isabelle theory file name (default is derived from source Cogent file)"
  -- dir specification
  , Option []         ["abs-type-dir"]    1 (ReqArg set_flag_absTypeDir "PATH")            "abstract type definitions will be in $DIR/abstract/, which must exist (default=./)"
  , Option []         ["dist-dir"]        1 (ReqArg set_flag_distDir "PATH")               "specify path to all output files (default=./)"
  , Option []         ["fake-header-dir"] 1 (ReqArg set_flag_fakeHeaderDir "PATH")         "specify path to fake c header files"
  , Option ['I']      ["include"]         1 (ReqArg add_flag_include "PATH")               "specify directories to search for included cogent files"
  , Option []         ["root-dir"]        1 (ReqArg set_flag_rootDir "PATH")               "specify path to top-level directory (for imports in theory files only, default=./)"
  -- config and other output files
  , Option []         ["arch"]           2 (ReqArg set_flag_arch "ARCH")                   "set the target architecture; ARCH could be one of arm32 (default), x86_64, x86"
  , Option []         ["cust-ty-gen"]    1 (ReqArg set_flag_custTyGen "FILE")              "config file to customise type generation"
  , Option []         ["entry-funcs"]    1 (ReqArg set_flag_entryFuncs "FILE")             "give a list of Cogent functions that are only called from outside"
  , Option []         ["ext-types"]      1 (ReqArg set_flag_extTypes "FILE")               "give external type names to C parser"
  , Option []         ["infer-c-funcs"]  1 (ReqArg (set_flag_inferCFunc . words) "FILE..") "infer Cogent abstract function definitions"
  , Option []         ["infer-c-types"]  1 (ReqArg (set_flag_inferCType . words) "FILE..") "infer Cogent abstract type definitions"
  , Option []         ["isabelle-var-avoidance"] 1 (ReqArg (set_flag_isabelleVarAvoidance) "FILE")  "variable names that should be avoided when generation Isabelle embeddings"
  , Option []         ["name-cache"]     1 (ReqArg set_flag_nameCache "FILE")              "specify the name cache file to use"
  , Option []         ["proof-input-c"]  1 (ReqArg set_flag_proofInputC "FILE")            "specify input C file to generate proofs (default to the same base name as input Cogent file)"
  , Option []         ["type-proof-timing"] 3 (NoArg set_flag_proofTiming)                  "Log type proof timings in the generated isabelle embedding to ~/TypeProofTacticTiming.json"
  , Option []         ["prune-call-graph"] 2 (ReqArg set_flag_pruneCallGraph "FILE")       "specify Cogent entry-point definitions"
  -- external programs
  , Option []         ["cogent-pp-args"] 2 (ReqArg (set_flag_cogentPpArgs) "ARG..")        "arguments given to Cogent preprocessor (same as cpphs)"
  , Option []         ["cpp"]            2 (ReqArg (set_flag_cpp) "PROG")                  "set which C-preprocessor to use (default to cpp)"
  , Option []         ["cpp-args"]       2 (ReqArg (set_flag_cppArgs . words) "ARG..")     "arguments given to C-preprocessor (default to -x c $CPPIN -P -o $CPPOUT)"
  -- debugging options
  , Option []         ["ddump-smt"]        3 (NoArg set_flag_ddumpSmt)                     "dump verbose SMT-solving information"
  , Option []         ["ddump-tc"]         3 (NoArg set_flag_ddumpTc)                      "dump (massive) surface typechecking internals"
  , Option []         ["ddump-tc-ctx"]     3 (NoArg set_flag_ddumpTcCtx)                   "dump surface typechecking with context"
  , Option []         ["ddump-tc-filter"]  3 (ReqArg set_flag_ddumpTcFilter "KEYWORDS")    "a space-separated list of keywords to indicate which groups of info to display (gen, sol, post, tc)"
  , Option []         ["ddump-to-file"]    3 (ReqArg set_flag_ddumpToFile "FILE")          "dump debugging output to specific file instead of terminal"
  , Option []         ["ddump-pretty-ds-no-tc"]  3 (NoArg set_flag_ddumpPrettyDsNoTc)                "dump the pretty printed desugared expression before typechecking"
  , Option []         ["ddump-pretty-normal-no-tc"]  3 (NoArg set_flag_ddumpPrettyNormalNoTc)        "dump the pretty printed normalised expression before typechecking"
  -- behaviour
  , Option []         ["fcheck-undefined"]    2 (NoArg set_flag_fcheckUndefined)           "(default) check for undefined behaviours in C"
  , Option []         ["fdargent-word-size"]  3 (ReqArg set_flag_fdargentWordSize "SIZE")  "set the word size (8, 16, 32, 64) for storing data when Dargent is used"
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
  , Option []         ["fno-simplify-shallow-tuples"] 2 (NoArg set_flag_fnoSimplifyShallowTuples)  "reverse of --fsimplify-shallow-tuples"
  , Option []         ["fno-static-inline"]   1 (NoArg set_flag_fnoStaticInline)           "reverse of --fstatic-inline"
  , Option []         ["fno-tc-ctx-constraints"] 3 (NoArg set_flag_ftcCtxConstraints)      "(default) reverse of --ftc-ctx-constraints"
  , Option []         ["fno-tp-with-bodies"]  1   (NoArg set_flag_fnoTpWithBodies)         "reverse of --ftp-with-bodies"
  , Option []         ["fno-tp-with-decls"]   1   (NoArg set_flag_fnoTpWithDecls)          "reverse of --ftp-with-decls"
  , Option []         ["fno-tuples-as-sugar"] 1 (NoArg set_flag_fnoTuplesAsSugar)          "reverse of --ftuples-as-sugar"
  , Option []         ["fno-union-for-variants"] 2 (NoArg set_flag_fnoUnionForVariants)    "(default) reverse of --funion-for-variants"
  , Option []         ["fno-untyped-func-enum"]  2 (NoArg set_flag_fnoUntypedFuncEnum)     "reverse of --funtyped-func-enum"
  , Option []         ["fno-unused-dargent-accessors"] 2 (NoArg set_flag_fnoUnusedDargentAccessors)  "(default) only generate Dargent getter/setter functions when the relevant field is accessed (e.g. via take, put, member) in the program"
  , Option []         ["fno-use-compound-literals"] 1 (NoArg set_flag_fnoUseCompoundLiterals)   "reverse of --fuse-compound-literals, it instead creates new variables"
  , Option []         ["fno-wrap-put-in-let"] 2 (NoArg set_flag_fnoWrapPutInLet)           "(default) reverse of --fwrap-put-in-let"
  , Option []         ["fpragmas"]            2 (NoArg set_flag_fpragmas)                  "(default) preprocess pragmas"
  , Option []         ["fpretty-errmsgs"]     3 (NoArg set_flag_fprettyErrmsgs)            "(default) pretty-print error messages (requires ANSI support)"
  , Option []         ["freverse-tc-errors"]  1 (NoArg set_flag_freverseTcErrors)          "Print type errors in reverse order"
  , Option []         ["fshare-linear-vars"]  2 (NoArg set_flag_fshareLinearVars)          "reuse C variables for linear objects"
  , Option []         ["fshow-types-in-pretty"] 2 (NoArg set_flag_fshowTypesInPretty)      "show inferred types of each AST node when doing pretty-printing"
  , Option []         ["fsimplifier"]         1 (NoArg set_flag_fsimplifier)               "enable simplifier on core language"
  , Option []         ["fsimplifier-level"]   1 (ReqArg (set_flag_fsimplifierIterations . read) "NUMBER")  "number of iterations simplifier does (default=4)"
  , Option []         ["fsimplify-shallow-tuples"] 1 (NoArg set_flag_fsimplifyShallowTuples)    "(default) simplify shallow embedding for readability"
  , Option []         ["fstatic-inline"]      2 (NoArg set_flag_fstaticInline)             "(default) generate static-inlined functions in C"
  , Option []         ["ftuples-as-sugar"]    2 (NoArg set_flag_ftuplesAsSugar)            "(default) treat tuples as syntactic sugar to unboxed records, which gives better performance"
  , Option []         ["ftc-ctx-constraints"] 3 (NoArg set_flag_ftcCtxConstraints)         "display constraints in type errors"
  , Option []         ["ftc-ctx-len"]         3 (ReqArg (set_flag_ftcCtxLen . read) "NUMBER")   "set the depth for printing error context in typechecker (default=3)"
  , Option []         ["ftp-with-bodies"]     2 (NoArg set_flag_ftpWithBodies)             "(default) generate type proof with bodies"
  , Option []         ["ftp-with-decls"]      2 (NoArg set_flag_ftpWithDecls)              "(default) generate type proof with declarations"
  , Option []         ["funion-for-variants"] 2 (NoArg set_flag_funionForVariants)         "use union types for variants in C code (cannot be verified)"
  , Option []         ["funtyped-func-enum"]  2 (NoArg set_flag_funtypedFuncEnum)          "(default) use untyped function enum type"
  , Option []         ["funused-dargent-accessors"] 2 (NoArg set_flag_funusedDargentAccessors)  "reverse of --fno-unused-dargent-accessors"
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
  , Option []         ["interactive"]      3 (NoArg set_flag_interactive)                  "interactive compiler mode"
  , Option []         ["type-proof-sorry-before"]  1 (ReqArg set_flag_type_proof_sorry_before "FUN_NAME")            "bad hack: sorry all type proofs for functions that precede given function name"
  ]


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



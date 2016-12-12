--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cogent.Compiler where

import Cogent.Util

import Control.Monad
import Data.Char
import Data.Function ((&))
import Data.IORef
import System.Directory (doesFileExist, getCurrentDirectory, removeFile)
import System.FilePath
import System.IO
import System.IO.Unsafe
import Text.PrettyPrint.ANSI.Leijen (Doc, displayIO, plain, renderPretty)

__impossible :: String -> a
__impossible msg = __impossible' msg []

__impossible' :: String -> [String] -> a
__impossible' mh mb = error $ mh ++ ": the 'impossible' happened!\n" 
                           ++ unlines (map ("  " ++) mb) 
                           ++ "Please file a bug report at https://github.com/NICTA/cogent/issues"

-- This bug has been closed and will be in new GHC / zilinc (16/02/2016)
#if __GLASGOW_HASKELL__ < 711
__ghc_t4139 :: String -> a
__ghc_t4139 msg = error $ msg ++ ": GHC doesn't get exhaustivity right (see trac #4139)"
#else

#endif

__exhaustivity :: String -> a
__exhaustivity msg = error $ msg ++ ": `otherwise' is not used for clarity, so GHC doesn't know the guards are exhaustive"

__todo :: String -> a
{-# WARNING __todo "TODO" #-}
__todo msg = error $ "TODO: " ++ msg

__fixme :: a -> a
{-# WARNING __fixme "FIXME" #-}
__fixme = id

__assert :: Monad m => Bool -> String -> m ()
__assert ass msg = unless ass $ error ("ASSERTION FAILED: " ++ msg)


-- Deal with files

cogentRelDir s d = relDir s d __cogent_current_dir

mkOutputName :: FilePath -> Maybe String -> String
mkOutputName src mbsuf = maybe (takeBaseName src) id __cogent_output_name ++ maybe [] id mbsuf

mkFileName :: FilePath -> Maybe String -> String -> Maybe FilePath
mkFileName src mbsuf ext =
  if __cogent_fdump_to_stdout then Nothing else Just $ __cogent_dist_dir `combine` mkOutputName src mbsuf <.> ext

mkProofName :: FilePath -> Maybe String -> String
mkProofName src mbsuf = maybe (toIsaName $ takeBaseName src) id __cogent_proof_name ++ maybe [] id mbsuf

mkThyFileName :: FilePath -> String -> Maybe FilePath
mkThyFileName src suffix =
  if __cogent_fdump_to_stdout then Nothing else Just $ __cogent_dist_dir `combine` (mkProofName src $ Just suffix) <.> __cogent_ext_of_thy

-- Cogent Flags

data Cogent_WarningSwitch = Flag_w | Flag_Wwarn | Flag_Werror

set_flag_absTypeDir = writeIORef __cogent_abs_type_dir_ref
set_flag_cpp = writeIORef __cogent_cpp_ref
set_flag_cppArgs = writeIORef __cogent_cpp_args_ref
set_flag_quiet = writeIORef __cogent_quiet_ref True
set_flag_debug = writeIORef __cogent_debug_ref True
set_flag_ddumpTc = writeIORef __cogent_ddump_tc_ref True
set_flag_ddumpTcCtx = writeIORef __cogent_ddump_tc_ctx_ref True
set_flag_ddumpTcFilter = writeIORef __cogent_ddump_tc_filter_ref . Just . words
set_flag_ddumpToFile = writeIORef __cogent_ddump_to_file_ref . Just
set_flag_distDir = writeIORef __cogent_dist_dir_ref
set_flag_entryFuncs = writeIORef __cogent_entry_funcs_ref . Just
set_flag_extTypes = writeIORef __cogent_ext_types_ref . Just
set_flag_fakeHeaderDir dir = writeIORef __cogent_fake_header_dir_ref $ Just (cogentRelDir dir __cogent_dist_dir)
set_flag_fcheckUndefined = writeIORef __cogent_fcheck_undefined_ref True
set_flag_fdisambiguatePp = writeIORef __cogent_fdisambiguate_pp_ref True
set_flag_fdumpToStdout = writeIORef __cogent_fdump_to_stdout_ref True
set_flag_fflattenNestings = writeIORef __cogent_fflatten_nestings_ref (__fixme False)  -- FIXME after fixing the impl'n
set_flag_ffncallAsMacro = writeIORef __cogent_ffncall_as_macro_ref True
set_flag_ffullSrcPath = writeIORef __cogent_ffull_src_path_ref True
set_flag_ffuncPurityAttr = writeIORef __cogent_ffunc_purity_attr_ref True
set_flag_fgenHeader = writeIORef __cogent_fgen_header_ref True
set_flag_fintermediateVars = writeIORef __cogent_fintermediate_vars_ref True
set_flag_fletInIf = writeIORef __cogent_flet_in_if_ref True
set_flag_fletbangInIf = writeIORef __cogent_fletbang_in_if_ref True
set_flag_fmlTypingTree = writeIORef __cogent_fml_typing_tree_ref True
set_flag_fnoCheckUndefined = writeIORef __cogent_fcheck_undefined_ref False
set_flag_fnoFlattenNestings = writeIORef __cogent_fflatten_nestings_ref False
set_flag_fnoFncallAsMacro = writeIORef __cogent_ffncall_as_macro_ref False
set_flag_fnoFuncPurityAttr = writeIORef __cogent_ffunc_purity_attr_ref False
set_flag_fnoGenHeader = writeIORef __cogent_fgen_header_ref False
set_flag_fnoIntermediateVars = writeIORef __cogent_fintermediate_vars_ref False
set_flag_fnoLetInIf = writeIORef __cogent_flet_in_if_ref False
set_flag_fnoLetbangInIf = writeIORef __cogent_fletbang_in_if_ref False
set_flag_fnoMlTypingTree = writeIORef __cogent_fml_typing_tree_ref False
set_flag_fnoNormalisation = writeIORef __cogent_fnormalisation_ref NoNF
set_flag_fnoPragmas = writeIORef __cogent_fpragmas_ref False
set_flag_fnoPrettyErrmsgs = writeIORef __cogent_fpretty_errmsgs_ref False
set_flag_fnoReverseTcErrors = writeIORef __cogent_freverse_tc_errors_ref False
set_flag_fnormalisation Nothing = writeIORef __cogent_fnormalisation_ref ANF
set_flag_fnormalisation (Just s) | s' <- map toLower s =
  writeIORef __cogent_fnormalisation_ref $ case s' of "anf" -> ANF; "knf" -> KNF; "lnf" -> LNF; nf -> error ("unrecognised normal form: " ++ show nf)
set_flag_fnoShareLinearVars = writeIORef __cogent_fshare_linear_vars_ref False
set_flag_fnoShareVariants = writeIORef __cogent_fshare_variants_ref False
set_flag_fnoShowTypesInPretty = writeIORef __cogent_fshow_types_in_pretty_ref False
set_flag_fnoSimplifier = writeIORef __cogent_fsimplifier_ref False
set_flag_fnoStaticInline = writeIORef __cogent_fstatic_inline_ref False
set_flag_fnoTcCtxConstraints = writeIORef __cogent_ftc_ctx_constraints_ref False
set_flag_fnoTpWithBodies = writeIORef __cogent_ftp_with_bodies_ref False
set_flag_fnoTpWithDecls = writeIORef __cogent_ftp_with_decls_ref False
set_flag_fnoTuplesAsSugar = writeIORef __cogent_ftuples_as_sugar_ref False
set_flag_fnoUnionForVariants = writeIORef __cogent_funion_for_variants_ref False
set_flag_fnoUntypedFuncEnum = writeIORef __cogent_funtyped_func_enum_ref False
set_flag_fnoUseCompoundLiterals = writeIORef __cogent_fuse_compound_literals_ref False
set_flag_fnoWrapPutInLet = writeIORef __cogent_fwrap_put_in_let_ref False
set_flag_fpragmas = writeIORef __cogent_fpragmas_ref True
set_flag_fprettyErrmsgs = writeIORef __cogent_fpretty_errmsgs_ref True
set_flag_freverseTcErrors = writeIORef __cogent_freverse_tc_errors_ref True
set_flag_fshareLinearVars = writeIORef __cogent_fshare_linear_vars_ref True
set_flag_fshareVariants = writeIORef __cogent_fshare_variants_ref False  -- FIXME after fixing the impl'n
set_flag_fshowTypesInPretty = writeIORef __cogent_fshow_types_in_pretty_ref True
set_flag_fsimplifier = writeIORef __cogent_fsimplifier_ref True
set_flag_fsimplifierIterations = writeIORef __cogent_fsimplifier_iterations_ref
set_flag_fstaticInline = writeIORef __cogent_fstatic_inline_ref True
set_flag_ftcCtxConstraints = writeIORef __cogent_ftc_ctx_constraints_ref True
set_flag_ftcCtxLen = writeIORef __cogent_ftc_ctx_len_ref
set_flag_ftpWithBodies = writeIORef __cogent_ftp_with_bodies_ref True
set_flag_ftpWithDecls = writeIORef __cogent_ftp_with_decls_ref True
set_flag_ftuplesAsSugar = writeIORef __cogent_ftuples_as_sugar_ref True
set_flag_funionForVariants = writeIORef __cogent_funion_for_variants_ref True
set_flag_funtypedFuncEnum = writeIORef __cogent_funtyped_func_enum_ref True
set_flag_fuseCompoundLiterals = writeIORef __cogent_fuse_compound_literals_ref True
set_flag_fwrapPutInLet = writeIORef __cogent_fwrap_put_in_let_ref True
set_flag_inferCFunc = writeIORef __cogent_infer_c_func_files_ref
set_flag_inferCType = writeIORef __cogent_infer_c_type_files_ref
set_flag_interactive = writeIORef __cogent_interactive_ref True
set_flag_O Nothing = return ()
set_flag_O (Just n :: Maybe String)
  | n == "0" = do set_flag_fnormalisation Nothing
                  set_flag_fnoFlattenNestings
                  set_flag_fnoShareLinearVars
                  set_flag_fnoShareVariants
                  set_flag_fnoStaticInline
                  set_flag_fnoTuplesAsSugar
                  set_flag_fnoUnionForVariants
  | n == "1" = do set_flag_fnoIntermediateVars
                  set_flag_ffncallAsMacro
                  set_flag_fshareLinearVars
  | n == "d" = return ()
  | n == "n" = do set_flag_O $ Just "1"
                  set_flag_fnoNormalisation
  | n == "s" = do set_flag_O $ Just "1"
                  set_flag_fsimplifier
  | n == "u" = do set_flag_O $ Just "1"
                  set_flag_funionForVariants
  | n == "v" = do set_flag_O $ Just "1"
                  set_flag_fshareVariants
  | n == "2" = do set_flag_O $ Just "s"
                  set_flag_fflattenNestings
                  set_flag_fshareVariants
  | otherwise = error $ "unrecognised optimisation level: " ++ show n
set_flag_outputName = writeIORef __cogent_output_name_ref . Just . takeBaseName
set_flag_proofInputC = writeIORef __cogent_proof_input_c_ref . Just
set_flag_proofName = writeIORef __cogent_proof_name_ref . Just . takeBaseName
set_flag_rootDir dir = writeIORef __cogent_root_dir_ref (cogentRelDir dir __cogent_dist_dir)
set_flag_w      = writeIORef __cogent_warning_switch_ref Flag_w
set_flag_Wall = do set_flag_WdynamicVariantPromotion
                   set_flag_WimplicitIntLitPromotion
                   set_flag_WunusedLocalBinds
set_flag_Werror = writeIORef __cogent_warning_switch_ref Flag_Werror
set_flag_WdynamicVariantPromotion = writeIORef __cogent_wdynamic_variant_promotion_ref True
set_flag_WimplicitIntLitPromotion = writeIORef __cogent_wimplicit_int_lit_promotion_ref True
set_flag_WnoDynamicVariantPromotion = writeIORef __cogent_wdynamic_variant_promotion_ref False
set_flag_WnoImplicitIntLitPromotion = writeIORef __cogent_wimplicit_int_lit_promotion_ref False
set_flag_WnoUnusedLocalBinds = writeIORef __cogent_wunused_local_binds_ref False
set_flag_WunusedLocalBinds = writeIORef __cogent_wunused_local_binds_ref True
set_flag_Wwarn  = writeIORef __cogent_warning_switch_ref Flag_Wwarn

__cogent_abs_type_dir :: FilePath
__cogent_abs_type_dir = unsafePerformIO $ readIORef __cogent_abs_type_dir_ref

__cogent_abs_type_dir_ref :: IORef FilePath
{-# NOINLINE __cogent_abs_type_dir_ref #-}
__cogent_abs_type_dir_ref = unsafePerformIO $ newIORef "."

__cogent_cpp :: FilePath
__cogent_cpp = unsafePerformIO $ readIORef __cogent_cpp_ref

__cogent_cpp_ref :: IORef FilePath
{-# NOINLINE __cogent_cpp_ref #-}
__cogent_cpp_ref = unsafePerformIO $ newIORef "cpp"

__cogent_cpp_args :: [String]
__cogent_cpp_args = unsafePerformIO $ readIORef __cogent_cpp_args_ref

__cogent_cpp_args_ref :: IORef [String]
{-# NOINLINE __cogent_cpp_args_ref #-}
__cogent_cpp_args_ref = unsafePerformIO $ newIORef ["$CPPIN", "-o", "$CPPOUT", "-E", "-P"]

__cogent_quiet :: Bool
__cogent_quiet = unsafePerformIO $ readIORef __cogent_quiet_ref

__cogent_quiet_ref :: IORef Bool
{-# NOINLINE __cogent_quiet_ref #-}
__cogent_quiet_ref = unsafePerformIO $ newIORef False

__cogent_debug :: Bool
__cogent_debug = unsafePerformIO $ readIORef __cogent_debug_ref

__cogent_debug_ref :: IORef Bool
{-# NOINLINE __cogent_debug_ref #-}
__cogent_debug_ref = unsafePerformIO $ newIORef False

__cogent_ddump_tc :: Bool
__cogent_ddump_tc = unsafePerformIO $ readIORef __cogent_ddump_tc_ref

__cogent_ddump_tc_ref :: IORef Bool
{-# NOINLINE __cogent_ddump_tc_ref #-}
__cogent_ddump_tc_ref = unsafePerformIO $ newIORef False

__cogent_ddump_tc_ctx :: Bool
__cogent_ddump_tc_ctx = unsafePerformIO $ readIORef __cogent_ddump_tc_ctx_ref

__cogent_ddump_tc_ctx_ref :: IORef Bool
{-# NOINLINE __cogent_ddump_tc_ctx_ref #-}
__cogent_ddump_tc_ctx_ref = unsafePerformIO $ newIORef False

__cogent_ddump_tc_filter :: Maybe [String]
__cogent_ddump_tc_filter = unsafePerformIO $ readIORef __cogent_ddump_tc_filter_ref

__cogent_ddump_tc_filter_ref :: IORef (Maybe [String])
{-# NOINLINE __cogent_ddump_tc_filter_ref #-}
__cogent_ddump_tc_filter_ref = unsafePerformIO $ newIORef Nothing

__cogent_ddump_to_file :: Maybe FilePath
__cogent_ddump_to_file = unsafePerformIO $ readIORef __cogent_ddump_to_file_ref

__cogent_ddump_to_file_ref :: IORef (Maybe FilePath)
{-# NOINLINE __cogent_ddump_to_file_ref #-}
__cogent_ddump_to_file_ref = unsafePerformIO $ newIORef Nothing

__cogent_dist_dir :: FilePath
__cogent_dist_dir = unsafePerformIO $ readIORef __cogent_dist_dir_ref

__cogent_dist_dir_ref :: IORef FilePath
{-# NOINLINE __cogent_dist_dir_ref #-}
__cogent_dist_dir_ref = unsafePerformIO $ newIORef "."

__cogent_entry_funcs :: Maybe FilePath
__cogent_entry_funcs = unsafePerformIO $ readIORef __cogent_entry_funcs_ref

__cogent_entry_funcs_ref :: IORef (Maybe FilePath)
{-# NOINLINE __cogent_entry_funcs_ref #-}
__cogent_entry_funcs_ref = unsafePerformIO $ newIORef Nothing

__cogent_ext_types :: Maybe FilePath
__cogent_ext_types = unsafePerformIO $ readIORef __cogent_ext_types_ref

__cogent_ext_types_ref :: IORef (Maybe FilePath)
{-# NOINLINE __cogent_ext_types_ref #-}
__cogent_ext_types_ref = unsafePerformIO $ newIORef Nothing

-- naming conventions for other output files

__cogent_ext_of_afm :: String
__cogent_ext_of_afm = unsafePerformIO $ readIORef __cogent_ext_of_afm_ref

__cogent_ext_of_afm_ref :: IORef String
{-# NOINLINE __cogent_ext_of_afm_ref #-}
__cogent_ext_of_afm_ref = unsafePerformIO $ newIORef "afm"

__cogent_ext_of_atm :: String
__cogent_ext_of_atm = unsafePerformIO $ readIORef __cogent_ext_of_atm_ref

__cogent_ext_of_atm_ref :: IORef String
{-# NOINLINE __cogent_ext_of_atm_ref #-}
__cogent_ext_of_atm_ref = unsafePerformIO $ newIORef "atm"

__cogent_ext_of_c_type_table :: String
__cogent_ext_of_c_type_table = unsafePerformIO $ readIORef __cogent_ext_of_c_type_table_ref

__cogent_ext_of_c_type_table_ref :: IORef String
{-# NOINLINE __cogent_ext_of_c_type_table_ref #-}
__cogent_ext_of_c_type_table_ref = unsafePerformIO $ newIORef "table"

__cogent_ext_of_c :: String
__cogent_ext_of_c = "c"

__cogent_ext_of_h :: String
__cogent_ext_of_h = "h"

__cogent_ext_of_thy :: String
__cogent_ext_of_thy = "thy"

__cogent_ext_of_ac :: String
__cogent_ext_of_ac = "ac"

__cogent_ext_of_ah :: String
__cogent_ext_of_ah = "ah"

-- ----------

__cogent_fake_header_dir :: Maybe FilePath
__cogent_fake_header_dir = unsafePerformIO $ readIORef __cogent_fake_header_dir_ref

__cogent_fake_header_dir_ref :: IORef (Maybe FilePath)
{-# NOINLINE __cogent_fake_header_dir_ref #-}
__cogent_fake_header_dir_ref = unsafePerformIO $ newIORef Nothing

__cogent_fcheck_undefined :: Bool
__cogent_fcheck_undefined = unsafePerformIO $ readIORef __cogent_fcheck_undefined_ref

__cogent_fcheck_undefined_ref :: IORef Bool
{-# NOINLINE __cogent_fcheck_undefined_ref #-}
__cogent_fcheck_undefined_ref = unsafePerformIO $ newIORef True

-- __cogent_fcondition_knf :: Bool
-- __cogent_fcondition_knf = True

-- TODO

-- Mostly used for disambiguating types that are normalised and not;
-- they look the same in PP but internally distinct / zilinc
__cogent_fdisambiguate_pp :: Bool
__cogent_fdisambiguate_pp = unsafePerformIO $ readIORef __cogent_fdisambiguate_pp_ref

__cogent_fdisambiguate_pp_ref :: IORef Bool
{-# NOINLINE __cogent_fdisambiguate_pp_ref #-}
__cogent_fdisambiguate_pp_ref = unsafePerformIO $ newIORef False

__cogent_fdump_to_stdout :: Bool
__cogent_fdump_to_stdout = unsafePerformIO $ readIORef __cogent_fdump_to_stdout_ref

__cogent_fdump_to_stdout_ref :: IORef Bool
{-# NOINLINE __cogent_fdump_to_stdout_ref #-}
__cogent_fdump_to_stdout_ref = unsafePerformIO $ newIORef False

__cogent_fflatten_nestings :: Bool
__cogent_fflatten_nestings = unsafePerformIO $ readIORef __cogent_fflatten_nestings_ref

__cogent_fflatten_nestings_ref :: IORef Bool
{-# NOINLINE __cogent_fflatten_nestings_ref #-}
__cogent_fflatten_nestings_ref = unsafePerformIO $ newIORef False

__cogent_ffncall_as_macro :: Bool
__cogent_ffncall_as_macro = unsafePerformIO $ readIORef __cogent_ffncall_as_macro_ref

__cogent_ffncall_as_macro_ref :: IORef Bool
{-# NOINLINE __cogent_ffncall_as_macro_ref #-}
__cogent_ffncall_as_macro_ref = unsafePerformIO $ newIORef False

__cogent_ffull_src_path :: Bool
__cogent_ffull_src_path = unsafePerformIO $ readIORef __cogent_ffull_src_path_ref

__cogent_ffull_src_path_ref :: IORef Bool
{-# NOINLINE __cogent_ffull_src_path_ref #-}
__cogent_ffull_src_path_ref = unsafePerformIO $ newIORef False

__cogent_ffunc_purity_attr :: Bool
__cogent_ffunc_purity_attr = unsafePerformIO $ readIORef __cogent_ffunc_purity_attr_ref

__cogent_ffunc_purity_attr_ref :: IORef Bool
{-# NOINLINE __cogent_ffunc_purity_attr_ref #-}
__cogent_ffunc_purity_attr_ref = unsafePerformIO $ newIORef False

__cogent_fgen_header :: Bool
__cogent_fgen_header = unsafePerformIO $ readIORef __cogent_fgen_header_ref

__cogent_fgen_header_ref :: IORef Bool
{-# NOINLINE __cogent_fgen_header_ref #-}
__cogent_fgen_header_ref = unsafePerformIO $ newIORef False

__cogent_fintermediate_vars :: Bool
__cogent_fintermediate_vars = unsafePerformIO $ readIORef __cogent_fintermediate_vars_ref

__cogent_fintermediate_vars_ref :: IORef Bool
{-# NOINLINE __cogent_fintermediate_vars_ref #-}
__cogent_fintermediate_vars_ref = unsafePerformIO $ newIORef True

__cogent_flet_in_if :: Bool
__cogent_flet_in_if = unsafePerformIO $ readIORef __cogent_flet_in_if_ref

__cogent_flet_in_if_ref :: IORef Bool
{-# NOINLINE __cogent_flet_in_if_ref #-}
__cogent_flet_in_if_ref = unsafePerformIO $ newIORef True

__cogent_fletbang_in_if :: Bool
__cogent_fletbang_in_if = unsafePerformIO $ readIORef __cogent_fletbang_in_if_ref

__cogent_fletbang_in_if_ref :: IORef Bool
{-# NOINLINE __cogent_fletbang_in_if_ref #-}
__cogent_fletbang_in_if_ref = unsafePerformIO $ newIORef True

__cogent_fml_typing_tree :: Bool
__cogent_fml_typing_tree = unsafePerformIO $ readIORef __cogent_fml_typing_tree_ref

__cogent_fml_typing_tree_ref :: IORef Bool
{-# NOINLINE __cogent_fml_typing_tree_ref #-}
__cogent_fml_typing_tree_ref = unsafePerformIO $ newIORef True


data NF = NoNF | ANF | KNF | LNF deriving (Eq, Show)

__cogent_fnormalisation :: NF
__cogent_fnormalisation = unsafePerformIO $ readIORef __cogent_fnormalisation_ref

__cogent_fnormalisation_ref :: IORef NF
{-# NOINLINE __cogent_fnormalisation_ref #-}
__cogent_fnormalisation_ref = unsafePerformIO $ newIORef ANF

__cogent_fpragmas :: Bool
__cogent_fpragmas = unsafePerformIO $ readIORef __cogent_fpragmas_ref

__cogent_fpragmas_ref :: IORef Bool
{-# NOINLINE __cogent_fpragmas_ref #-}
__cogent_fpragmas_ref = unsafePerformIO $ newIORef True

__cogent_fpretty_errmsgs :: Bool
__cogent_fpretty_errmsgs = unsafePerformIO $ readIORef __cogent_fpretty_errmsgs_ref

__cogent_fpretty_errmsgs_ref :: IORef Bool
{-# NOINLINE __cogent_fpretty_errmsgs_ref #-}
__cogent_fpretty_errmsgs_ref = unsafePerformIO $ newIORef True

__cogent_freverse_tc_errors :: Bool
__cogent_freverse_tc_errors = unsafePerformIO $ readIORef __cogent_freverse_tc_errors_ref

__cogent_freverse_tc_errors_ref :: IORef Bool
{-# NOINLINE __cogent_freverse_tc_errors_ref #-}
__cogent_freverse_tc_errors_ref = unsafePerformIO $ newIORef False

__cogent_fshare_linear_vars :: Bool
__cogent_fshare_linear_vars = unsafePerformIO $ readIORef __cogent_fshare_linear_vars_ref

__cogent_fshare_linear_vars_ref :: IORef Bool
{-# NOINLINE __cogent_fshare_linear_vars_ref #-}
__cogent_fshare_linear_vars_ref = unsafePerformIO $ newIORef False

__cogent_fshare_variants :: Bool
__cogent_fshare_variants = unsafePerformIO $ readIORef __cogent_fshare_variants_ref

__cogent_fshare_variants_ref :: IORef Bool
{-# NOINLINE __cogent_fshare_variants_ref #-}
__cogent_fshare_variants_ref = unsafePerformIO $ newIORef False

__cogent_fshow_types_in_pretty :: Bool
__cogent_fshow_types_in_pretty = unsafePerformIO $ readIORef __cogent_fshow_types_in_pretty_ref

__cogent_fshow_types_in_pretty_ref :: IORef Bool
{-# NOINLINE __cogent_fshow_types_in_pretty_ref #-}
__cogent_fshow_types_in_pretty_ref = unsafePerformIO $ newIORef False

__cogent_fsimplifier :: Bool
__cogent_fsimplifier = unsafePerformIO $ readIORef __cogent_fsimplifier_ref

__cogent_fsimplifier_ref :: IORef Bool
{-# NOINLINE __cogent_fsimplifier_ref #-}
__cogent_fsimplifier_ref = unsafePerformIO $ newIORef False

__cogent_fsimplifier_iterations :: Int
__cogent_fsimplifier_iterations = unsafePerformIO $ readIORef __cogent_fsimplifier_iterations_ref

__cogent_fsimplifier_iterations_ref :: IORef Int
{-# NOINLINE __cogent_fsimplifier_iterations_ref #-}
__cogent_fsimplifier_iterations_ref = unsafePerformIO $ newIORef 4

__cogent_fstatic_inline :: Bool
__cogent_fstatic_inline = unsafePerformIO $ readIORef __cogent_fstatic_inline_ref

__cogent_fstatic_inline_ref :: IORef Bool
{-# NOINLINE __cogent_fstatic_inline_ref #-}
__cogent_fstatic_inline_ref = unsafePerformIO $ newIORef True

__cogent_ftc_ctx_constraints :: Bool
__cogent_ftc_ctx_constraints = unsafePerformIO $ readIORef __cogent_ftc_ctx_constraints_ref

__cogent_ftc_ctx_constraints_ref  :: IORef Bool
{-# NOINLINE __cogent_ftc_ctx_constraints_ref #-}
__cogent_ftc_ctx_constraints_ref = unsafePerformIO $ newIORef False

__cogent_ftc_ctx_len :: Int
__cogent_ftc_ctx_len = unsafePerformIO $ readIORef __cogent_ftc_ctx_len_ref

__cogent_ftc_ctx_len_ref :: IORef Int
{-# NOINLINE __cogent_ftc_ctx_len_ref #-}
__cogent_ftc_ctx_len_ref = unsafePerformIO $ newIORef 3

__cogent_ftp_with_bodies :: Bool
__cogent_ftp_with_bodies = unsafePerformIO $ readIORef __cogent_ftp_with_bodies_ref

__cogent_ftp_with_bodies_ref :: IORef Bool
{-# NOINLINE __cogent_ftp_with_bodies_ref #-}
__cogent_ftp_with_bodies_ref = unsafePerformIO $ newIORef True

__cogent_ftp_with_decls :: Bool
__cogent_ftp_with_decls = unsafePerformIO $ readIORef __cogent_ftp_with_decls_ref

__cogent_ftp_with_decls_ref :: IORef Bool
{-# NOINLINE __cogent_ftp_with_decls_ref #-}
__cogent_ftp_with_decls_ref = unsafePerformIO $ newIORef True

__cogent_ftuples_as_sugar :: Bool
__cogent_ftuples_as_sugar = unsafePerformIO $ readIORef __cogent_ftuples_as_sugar_ref

__cogent_ftuples_as_sugar_ref :: IORef Bool
{-# NOINLINE __cogent_ftuples_as_sugar_ref #-}
__cogent_ftuples_as_sugar_ref = unsafePerformIO $ newIORef True

-- TODO
__cogent_funboxed_arg_by_ref :: Bool
__cogent_funboxed_arg_by_ref = False

-- TODO
__cogent_funboxed_arg_ref_size_threshold :: Int
__cogent_funboxed_arg_ref_size_threshold = 32

-- TODO
-- It's difficult in the case that the unboxed is not constructed right
-- before being used as a function argument. Do we additionally unpack it
-- and pass them to the function? or giving as a whole? If the later,
-- we will likely have two versions of the same function, which complicates
-- the dispatch function generation. / zilinc
__cogent_funboxed_multi_param :: Bool
__cogent_funboxed_multi_param = False

-- TODO
-- Idea: Once we have an unboxed object, we keep a mapping from a C var to
--   a list of C vars, one for each field of it. When we use the unboxed,
--   we directly pick the relevant fields from the mapping. Not sure if this
--   is going to help though. / zilinc
__cogent_funboxed_loose :: Bool
__cogent_funboxed_loose = False

__cogent_funion_for_variants :: Bool
__cogent_funion_for_variants = unsafePerformIO $ readIORef __cogent_funion_for_variants_ref

__cogent_funion_for_variants_ref :: IORef Bool
{-# NOINLINE __cogent_funion_for_variants_ref #-}
__cogent_funion_for_variants_ref = unsafePerformIO $ newIORef False

__cogent_funtyped_func_enum :: Bool
__cogent_funtyped_func_enum = unsafePerformIO $ readIORef __cogent_funtyped_func_enum_ref

__cogent_funtyped_func_enum_ref :: IORef Bool
{-# NOINLINE __cogent_funtyped_func_enum_ref #-}
__cogent_funtyped_func_enum_ref = unsafePerformIO $ newIORef True

__cogent_fuse_compound_literals :: Bool
__cogent_fuse_compound_literals = unsafePerformIO $ readIORef __cogent_fuse_compound_literals_ref

__cogent_fuse_compound_literals_ref :: IORef Bool
{-# NOINLINE __cogent_fuse_compound_literals_ref #-}
__cogent_fuse_compound_literals_ref = unsafePerformIO $ newIORef True

__cogent_fwrap_put_in_let :: Bool
__cogent_fwrap_put_in_let = unsafePerformIO $ readIORef __cogent_fwrap_put_in_let_ref

__cogent_fwrap_put_in_let_ref :: IORef Bool
{-# NOINLINE __cogent_fwrap_put_in_let_ref #-}
__cogent_fwrap_put_in_let_ref = unsafePerformIO $ newIORef False

__cogent_infer_c_func_files :: [FilePath]
__cogent_infer_c_func_files = unsafePerformIO $ readIORef __cogent_infer_c_func_files_ref

__cogent_infer_c_func_files_ref :: IORef [FilePath]
{-# NOINLINE __cogent_infer_c_func_files_ref #-}
__cogent_infer_c_func_files_ref = unsafePerformIO $ newIORef []

__cogent_infer_c_type_files :: [FilePath]
__cogent_infer_c_type_files = unsafePerformIO $ readIORef __cogent_infer_c_type_files_ref

__cogent_infer_c_type_files_ref :: IORef [FilePath]
{-# NOINLINE __cogent_infer_c_type_files_ref #-}
__cogent_infer_c_type_files_ref = unsafePerformIO $ newIORef []

__cogent_interactive :: Bool
__cogent_interactive = unsafePerformIO $ readIORef __cogent_interactive_ref

__cogent_interactive_ref :: IORef Bool
{-# NOINLINE __cogent_interactive_ref #-}
__cogent_interactive_ref = unsafePerformIO $ newIORef False

__cogent_output_name :: Maybe String
__cogent_output_name = unsafePerformIO $ readIORef __cogent_output_name_ref

__cogent_output_name_ref :: IORef (Maybe String)
{-# NOINLINE __cogent_output_name_ref #-}
__cogent_output_name_ref = unsafePerformIO $ newIORef Nothing

__cogent_proof_input_c :: Maybe FilePath
__cogent_proof_input_c = unsafePerformIO $ readIORef __cogent_proof_input_c_ref

__cogent_proof_input_c_ref :: IORef (Maybe FilePath)
{-# NOINLINE __cogent_proof_input_c_ref #-}
__cogent_proof_input_c_ref = unsafePerformIO $ newIORef Nothing
  -- same as output C file name
  -- NOTE: if antiquotation is used, you need specify this / zilinc

__cogent_proof_name :: Maybe String
__cogent_proof_name = unsafePerformIO $ readIORef __cogent_proof_name_ref

__cogent_proof_name_ref :: IORef (Maybe String)
{-# NOINLINE __cogent_proof_name_ref #-}
__cogent_proof_name_ref = unsafePerformIO $ newIORef Nothing

__cogent_root_name :: String
__cogent_root_name = "ROOT"  -- TODO

__cogent_build_info_name :: String
__cogent_build_info_name = "BUILD_INFO"

__cogent_root_dir :: FilePath
__cogent_root_dir = unsafePerformIO $ readIORef __cogent_root_dir_ref

__cogent_root_dir_ref :: IORef FilePath
{-# NOINLINE __cogent_root_dir_ref #-}
__cogent_root_dir_ref = unsafePerformIO $ newIORef (cogentRelDir "." __cogent_dist_dir)

-- Naming conventions of theory files

-- TODO: zilinc

__cogent_suffix_of_all_refine :: String
__cogent_suffix_of_all_refine = "_AllRefine"

__cogent_suffix_of_ac_install :: String
__cogent_suffix_of_ac_install = "_ACInstall"

__cogent_suffix_of_corres_setup :: String
__cogent_suffix_of_corres_setup = "_CorresSetup"

__cogent_suffix_of_corres_proof :: String
__cogent_suffix_of_corres_proof = "_CorresProof"

__cogent_suffix_of_mono_proof :: String
__cogent_suffix_of_mono_proof = "_MonoProof"

__cogent_suffix_of_normal_proof :: String
__cogent_suffix_of_normal_proof = "_NormalProof"

__cogent_suffix_of_type_proof :: String
__cogent_suffix_of_type_proof = "_TypeProof"

__cogent_suffix_of_shallow :: String
__cogent_suffix_of_shallow = "_Shallow"

__cogent_suffix_of_recover_tuples :: String
__cogent_suffix_of_recover_tuples = "_Tuples"

__cogent_suffix_of_shallow_tuples_proof :: String
__cogent_suffix_of_shallow_tuples_proof = "_ShallowTuplesProof"

__cogent_suffix_of_shallow_shared :: String
__cogent_suffix_of_shallow_shared = "_ShallowShared"

__cogent_suffix_of_shallow_consts :: String
__cogent_suffix_of_shallow_consts = "_ShallowConsts"

__cogent_suffix_of_deep :: String
__cogent_suffix_of_deep = "_Deep"

__cogent_suffix_of_scorres :: String
__cogent_suffix_of_scorres = "_SCorres"

__cogent_suffix_of_stage :: Stage -> String
__cogent_suffix_of_stage s | s == STGDesugar = "_Desugar"
                         | s == STGNormal  = "_Normal"
                         | s == STGMono    = "_Mono"
                         | otherwise       = __impossible "__cogent_suffix_of_stage"

-- ----------
-- Naming conventions of antiquotation files

__cogent_suffix_of_pp :: String
__cogent_suffix_of_pp = unsafePerformIO $ readIORef __cogent_suffix_of_pp_ref

__cogent_suffix_of_pp_ref :: IORef String
{-# NOINLINE __cogent_suffix_of_pp_ref #-}
__cogent_suffix_of_pp_ref = unsafePerformIO $ newIORef "_pp"

__cogent_suffix_of_inferred :: String
__cogent_suffix_of_inferred = unsafePerformIO $ readIORef __cogent_suffix_of_inferred_ref

__cogent_suffix_of_inferred_ref :: IORef String
{-# NOINLINE __cogent_suffix_of_inferred_ref #-}
__cogent_suffix_of_inferred_ref = unsafePerformIO $ newIORef "_inferred"

-- ----------

__cogent_warning_switch :: Cogent_WarningSwitch
__cogent_warning_switch = unsafePerformIO $ readIORef __cogent_warning_switch_ref

__cogent_warning_switch_ref :: IORef Cogent_WarningSwitch
{-# NOINLINE __cogent_warning_switch_ref #-}
__cogent_warning_switch_ref = unsafePerformIO $ newIORef Flag_Wwarn

__cogent_wdynamic_variant_promotion :: Bool
__cogent_wdynamic_variant_promotion = unsafePerformIO $ readIORef __cogent_wdynamic_variant_promotion_ref

__cogent_wdynamic_variant_promotion_ref :: IORef Bool
{-# NOINLINE __cogent_wdynamic_variant_promotion_ref #-}
__cogent_wdynamic_variant_promotion_ref = unsafePerformIO $ newIORef False

__cogent_wimplicit_int_lit_promotion :: Bool
__cogent_wimplicit_int_lit_promotion = unsafePerformIO $ readIORef __cogent_wimplicit_int_lit_promotion_ref

__cogent_wimplicit_int_lit_promotion_ref :: IORef Bool
{-# NOINLINE __cogent_wimplicit_int_lit_promotion_ref #-}
__cogent_wimplicit_int_lit_promotion_ref = unsafePerformIO $ newIORef True

__cogent_wunused_local_binds :: Bool
__cogent_wunused_local_binds = unsafePerformIO $ readIORef __cogent_wunused_local_binds_ref

__cogent_wunused_local_binds_ref :: IORef Bool
{-# NOINLINE __cogent_wunused_local_binds_ref #-}
__cogent_wunused_local_binds_ref = unsafePerformIO $ newIORef False

-- Internal flags

__cogent_current_dir :: FilePath
__cogent_current_dir = unsafePerformIO $ readIORef __cogent_current_dir_ref

__cogent_current_dir_ref :: IORef FilePath
{-# NOINLINE __cogent_current_dir_ref #-}
__cogent_current_dir_ref = unsafePerformIO $ getCurrentDirectory >>= newIORef

-- If not using normalisation (or applying simplifier to normalised code),
-- need to use more verbose codegen
__cogent_simpl_cg :: Bool
__cogent_simpl_cg = (__cogent_fsimplifier && __cogent_fsimplifier_iterations > 0) ||
                  __cogent_fnormalisation == NoNF

__cogent_dump_handle :: IORef Handle
{-# NOINLINE __cogent_dump_handle #-}
__cogent_dump_handle = unsafePerformIO $ newIORef stderr


--Dump

preDump :: IO ()
preDump = (case __cogent_ddump_to_file of
             Nothing -> return stderr
             Just fp -> doesFileExist fp >>= \case True -> removeFile fp; False -> return ()
                        >> openFile fp AppendMode) >>=
          writeIORef __cogent_dump_handle

postDump :: IO ()
postDump = readIORef __cogent_dump_handle >>= \h ->
           whenMM (liftM2 (&&)
                    (hIsOpen h)
                    (not <$> hIsTerminalDevice h)) $
             (hClose =<< readIORef __cogent_dump_handle)

dumpMsg :: Doc -> IO ()
dumpMsg d
  | __cogent_ddump_tc = do
      h <- readIORef __cogent_dump_handle
      b <- hIsTerminalDevice h
      displayIO h (d & (renderPretty 1.0 120 . if b then id else plain))
      hFlush h
  | otherwise = return ()


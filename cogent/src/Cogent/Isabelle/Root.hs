--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

module Cogent.Isabelle.Root where

import Cogent.Compiler
import Cogent.Util (Stage(..))

import System.FilePath ((-<.>), (<.>))

root :: String -> String -> [String]
root source log =
  let thy = mkProofName source Nothing
      inputc = maybe (mkOutputName source Nothing <.> __cogent_ext_of_c) id __cogent_proof_input_c
      -- if user supplies C source, don't assume default header exists
      inputh = case __cogent_proof_input_c of Just _ -> Nothing
                                              _      -> Just $ inputc -<.> __cogent_ext_of_h
      shal_shrd = thy ++ __cogent_suffix_of_shallow_shared
      shal_shrd_tup = thy ++ __cogent_suffix_of_shallow_shared ++ __cogent_suffix_of_recover_tuples
      shal_desg = thy ++ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage STGDesugar
      shal_desg_tup = thy ++ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage STGDesugar ++ __cogent_suffix_of_recover_tuples
      shal_norm = thy ++ __cogent_suffix_of_shallow ++ __cogent_suffix_of_stage STGNormal
      shal_tuples = thy ++ __cogent_suffix_of_shallow_tuples_proof
      normal_proof = thy ++ __cogent_suffix_of_normal_proof
      deep_norm = thy ++ __cogent_suffix_of_deep    ++ __cogent_suffix_of_stage STGNormal
      scor_norm = thy ++ __cogent_suffix_of_scorres ++ __cogent_suffix_of_stage STGNormal
      ac_install = thy ++ __cogent_suffix_of_ac_install
      type_proof = thy ++ __cogent_suffix_of_type_proof
      corres_setup = thy ++ __cogent_suffix_of_corres_setup
      corres_proof = thy ++ __cogent_suffix_of_corres_proof
      all_refine = thy ++ __cogent_suffix_of_all_refine
  in ["(*"] ++ lines log ++ ["*)"] ++
     [ ""
     , "session " ++ shal_tuples ++ " = Deep_C_Static +"
     , "  theories"
     , "    \"" ++ shal_shrd ++ "\""
     , "    \"" ++ shal_shrd_tup ++ "\""
     , "    \"" ++ shal_desg ++ "\""
     , "    \"" ++ shal_desg_tup ++ "\""
     , "  theories [condition = \"SKIP_TUPLE_PROOF\", skip_proofs, quick_and_dirty]"
     , "    \"" ++ shal_tuples ++ "\""
     , "  theories [quick_and_dirty]"
     , "    \"" ++ shal_tuples ++ "\""
     , ""
     , "session " ++ normal_proof ++ " = " ++ shal_tuples ++ " +"
     , "  theories"
     , "    \"" ++ shal_norm ++ "\""
     , "  theories [condition = \"SKIP_NORMAL_PROOF\", skip_proofs]"
     , "    \"" ++ normal_proof ++ "\""
     , "  theories"
     , "    \"" ++ normal_proof ++ "\""
     , ""
     , "session " ++ scor_norm ++ " = " ++ normal_proof ++ " +"
     , "  theories \"" ++ deep_norm ++ "\""
     , "  theories [condition = \"SKIP_SCORRES_PROOF\", skip_proofs, quick_and_dirty] \"" ++ scor_norm ++ "\""
     , "  theories [quick_and_dirty] \"" ++ scor_norm ++ "\""
     , ""
     , "session " ++ ac_install ++ " = " ++ scor_norm ++ " +"
     , "  theories \"" ++ ac_install ++ "\""
     , "  files \"" ++ inputc ++ "\"" ++ maybe "" (\f -> " \"" ++ f ++ "\"") inputh
     , ""
     , "session " ++ type_proof ++ " = " ++ ac_install ++ " +"
     , "  theories [condition = \"SKIP_TYPE_PROOF\", skip_proofs] \"" ++ type_proof ++ "\""
     , "  theories \"" ++ type_proof ++ "\""
     , ""
     , "session " ++ corres_setup ++ " = " ++ type_proof ++ " +"
     , "  theories [quick_and_dirty] \"" ++ corres_setup ++ "\""
     , ""
     , "session " ++ corres_proof ++ " = " ++ corres_setup ++ " +"
     , "  theories [condition = \"SKIP_CORRES_PROOF\", skip_proofs, quick_and_dirty] \"" ++ corres_proof ++ "\""
     , "  theories [quick_and_dirty] \"" ++ corres_proof ++ "\""
     , ""
     , "session " ++ all_refine ++ " = " ++ corres_proof ++ " +"
     , "  theories [condition = \"SKIP_ALL_REFINE\", skip_proofs] \"" ++ all_refine ++ "\""
     , "  theories \"" ++ all_refine ++ "\""
     , ""
     ]

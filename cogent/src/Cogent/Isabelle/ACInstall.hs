--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--


module Cogent.Isabelle.ACInstall where

import Cogent.Compiler

class ML t where
  hs2ml :: t -> String

instance ML Bool where
  hs2ml True  = "true"
  hs2ml False = "false"

-- ////////////////////////////////////////////////////////////////////////////

acInstallDefault :: String -> FilePath -> String -> [String]
acInstallDefault proj cfile log = acInstall proj "AutoCorres.AutoCorres" False True cfile log

-- Given theory name, generate text
acInstall :: String -> FilePath -> Bool -> Bool -> FilePath -> String -> [String]
acInstall proj ac cg anonymous cfile log =
  ["(*"] ++ lines log ++ ["*)"] ++
  [ "theory " ++ proj ++ __cogent_suffix_of_ac_install
  , "imports"
  , "  \"" ++ ac ++ "\""  -- AutoCorres
  , ""
  , "begin"
  , ""
  , "declare [[record_codegen = " ++ hs2ml cg ++ "]]"  -- slower if true
  , "declare [[use_anonymous_local_variables=" ++ hs2ml anonymous ++ "]]"  -- faster if true
  ] ++ (case __cogent_fake_header_dir of
          Nothing -> []
          Just fd -> ["new_C_include_dir \"" ++ fd ++ "\""]) ++  -- fake
  [ "install_C_file \"" ++ cfile ++ "\""  -- generated
  , "autocorres [keep_going, ts_rules = nondet, no_opt, skip_word_abs] \"" ++ cfile ++ "\""  -- generated
  , ""
  , "end"
  ]



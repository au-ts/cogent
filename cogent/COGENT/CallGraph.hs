--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

module COGENT.CallGraph where

import Data.ByteString hiding (concatMap)
import Text.Disassembler.X86Disassembler
import Text.Parsec
import Prelude hiding (readFile)

daX86 :: FilePath -> IO (Either ParseError [Instruction])
daX86 file = do c <- readFile file
                let conf = defaultConfig {confIn64BitMode = True}
                disassembleListWithConfig conf (unpack c)

printIntel :: [Instruction] -> String
printIntel = concatMap showIntel

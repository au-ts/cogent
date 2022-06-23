--
-- Copyright 2019, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

module Cogent.Dargent.Util where

import Cogent.Compiler
import Cogent.Common.Syntax
import Cogent.Common.Types

import Text.Parsec.Pos (SourcePos)

byteSizeBits :: Size
byteSizeBits = 8

pointerSizeBits, wordSizeBits :: Size
pointerSizeBits = primIntSizeBits machineWordType
-- vvv The size is already senitised by the Cogent.Compiler module when it's set
wordSizeBits    = case __cogent_fdargent_word_size of
                    Nothing -> primIntSizeBits machineWordType
                    Just s  -> s


-- When transforming (Offset repExpr offsetSize),
-- we want to add offset bits to all blocks inside the repExpr,
-- as well as the allocation corresponding to that repExpr.
class Offsettable a where
  offset :: Size -> a -> a

-- | Allows errors messages to pinpoint the exact location where the error occurred in a DataLayoutExpr/Decl
data DataLayoutPath
  = InField FieldName SourcePos DataLayoutPath
  | InTag   DataLayoutPath
  | InAlt   TagName SourcePos DataLayoutPath
#ifdef BUILTIN_ARRAYS
  | InElmt  SourcePos DataLayoutPath
#endif
  | InDecl  DataLayoutName DataLayoutPath
  | PathEnd
  deriving (Eq, Show, Ord)


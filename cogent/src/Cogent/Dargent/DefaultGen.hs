--
-- Copyright 2021, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE TupleSections #-}

module Cogent.Dargent.DefaultGen (genDefaultLayout) where

import           Cogent.Common.Syntax
import           Cogent.Common.Types
import           Cogent.Compiler
import           Cogent.Dargent.TypeCheck
import           Cogent.Surface
import qualified Cogent.TypeCheck.ARow as ARow
import           Cogent.TypeCheck.Base
import qualified Cogent.TypeCheck.Row as Row
import           Cogent.Util

{- * default layout generation -}

-- WIP
genDefaultLayout :: TCType -> Maybe TCDataLayout
genDefaultLayout (T (TCon tn [] Unboxed))
  | tn == "U8"   = pure $ TLPrim (Bytes 1)
  | tn == "U16"  = pure $ TLPrim (Bytes 2)
  | tn == "U32"  = pure $ TLPrim (Bytes 4)
  | tn == "U64"  = pure $ TLPrim (Bytes 8)
  | tn == "Bool" = pure $ TLPrim (Bytes 1)
genDefaultLayout (T (TUnbox (R rp r (Left Boxed{})))) = genDefaultLayout (R rp r (Left Unboxed))
genDefaultLayout (R _ r s)
  | Left Unboxed <- s, Row.isComplete r =
    let (fs,_) = foldl (\(ls,mfn) e ->
          let fn = Row.fname e
              ft = Row.payload e
           in ((:) <$> (case mfn of Just pf -> (fn,noPos,) . (`TLAfter` pf) <$> genDefaultLayout ft
                                    Nothing -> (fn,noPos,) <$> genDefaultLayout ft) <*> ls, Just fn))
          (Just [], Nothing) (Row.entries r)
     in TLRecord <$> fs
  | Left Boxed{} <- s = pure TLPtr
genDefaultLayout (V r)
  | Row.isComplete r =
    let (fs,_,tv) = foldl (\(ls,mfn,tv) e ->
          let fn = Row.fname e
              ft = Row.payload e
           in ((:) <$> (case mfn of Just pf -> (fn,noPos,tv,) . (`TLAfter` pf) <$> genDefaultLayout ft
                                    Nothing -> (fn,noPos,tv,) <$> genDefaultLayout ft) <*> ls, Just fn, tv+1))
          (Just [], Nothing, 0) (Row.entries r)
        sz = Bits . ceiling . logBase 2.0 . fromIntegral $ tv
     in TLVariant (TLPrim sz) . fmap (fourth4 (`TLOffset` sz)) <$> fs
#ifdef BUILTIN_ARRAYS
genDefaultLayout (T (TUnbox (A t l (Left Boxed{}) tks))) = genDefaultLayout (A t l (Left Unboxed) tks)
genDefaultLayout (A t _ s _)
  | Left Unboxed <- s = flip TLArray noPos <$> genDefaultLayout t
  | Left Boxed{} <- s = pure TLPtr
#endif
genDefaultLayout _ = Nothing


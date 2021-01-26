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
{-# LANGUAGE ViewPatterns #-}

module Cogent.Dargent.DefaultGen (genDefaultLayout) where

import           Cogent.Common.Syntax
import           Cogent.Common.Types
import           Cogent.Compiler
import           Cogent.Dargent.TypeCheck
import           Cogent.Surface
import           Cogent.TypeCheck.Base
import           Cogent.Util

import qualified Data.Map.Strict as M

{- * default layout generation -}

genDefaultLayout :: RawType -> Maybe DataLayoutExpr
genDefaultLayout (unRT -> t) = f t
  where
    f (TCon tn [] Unboxed)
      | tn == "U8"   = pure $ DLPrim (Bytes 1)
      | tn == "U16"  = pure $ DLPrim (Bytes 2)
      | tn == "U32"  = pure $ DLPrim (Bytes 4)
      | tn == "U64"  = pure $ DLPrim (Bytes 8)
      | tn == "Bool" = pure $ DLPrim (Bytes 1)
    f (TUnbox (unRT -> TRecord rp fs Boxed{})) = f $ TRecord rp fs Unboxed
    f (TRecord _ fs s)
      | Unboxed <- s =
        let (fs',_) = foldl (\(ls,mfn) (fn,(ft,_)) ->
              ((:) <$> (case mfn of Just pf -> (fn,noPos,) . (`DLAfter` pf) <$> genDefaultLayout ft
                                    Nothing -> (fn,noPos,) <$> genDefaultLayout ft) <*> ls, Just fn))
              (Just [], Nothing) fs
         in DLRecord <$> fs'
      | Boxed{} <- s = pure DLPtr
    f (TVariant fs) =
      let (fs',_,tv) = M.foldlWithKey (\(ls,mfn,tv) fn ([ft],_) ->
            ((:) <$> (case mfn of Just pf -> (fn,noPos,tv,) . (`DLAfter` pf) <$> genDefaultLayout ft
                                  Nothing -> (fn,noPos,tv,) <$> genDefaultLayout ft) <*> ls, Just fn, tv+1))
            (Just [], Nothing, 0) fs
          sz = Bits . ceiling . logBase 2.0 . fromIntegral $ tv
       in DLVariant (DLPrim sz) . fmap (fourth4 (`DLOffset` sz)) <$> fs'
#ifdef BUILTIN_ARRAYS
    f (TUnbox (unRT -> TArray t l Boxed{} tks)) = f $ TArray t l Unboxed tks
    f (TArray t _ s _)
      | Unboxed <- s = flip DLArray noPos <$> genDefaultLayout t
      | Boxed{} <- s = pure DLPtr
#endif
    f _ = Nothing


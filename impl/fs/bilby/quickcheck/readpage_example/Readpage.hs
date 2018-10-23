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

{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module Readpage where

import Control.Arrow
import Data.Array
import Data.Bits
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.Word
-- import Data.Void
import Test.QuickCheck hiding (Success, Error)

import CogentMonad
import Corres
import qualified Readpage_Shallow_Desugar_Tuples as C
import Fsop as Ax
import Util


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Haskell spec.


data VfsInode = VfsInode { ino :: U32 } deriving (Eq, Ord, Show)

vfs_inode_get_ino :: VfsInode -> U32
vfs_inode_get_ino (VfsInode ino) = ino

type OSPageOffset = U64

hs_fsop_readpage :: OstoreState -> VfsInode -> OSPageOffset -> CogentMonad (Either ErrCode (WordArray U8))
hs_fsop_readpage ostore vnode block =
  let size = vfs_inode_get_size vnode :: U64  -- the number of bytes we need to read
      limit = size `shiftR` fromIntegral bilbyFsBlockShift  -- the number of blocks we need to read
   in if | block > limit -> return $ Left eNoEnt
         -- ^ if we are reading beyond the last block we need to read, return an zeroed buffer
         | block == limit && (size `mod` fromIntegral bilbyFsBlockSize == 0) ->
             return $ Right empty_array
         -- ^ if we are reading the "last" one which extra bytes in this block is 0, then return old buffer
         | otherwise -> return $ Right $ read_block ostore vnode block
         -- ^ if we are reading a block which contains data, then we read the block

read_block :: OstoreState -> VfsInode -> OSPageOffset -> WordArray U8
read_block ostore inode block =
  let obj   = fromJust $ M.lookup (fromIntegral $ vfs_inode_get_ino inode) ostore
      idata = odata (extract_data_from_obj obj)
      arrElems = elems idata ++ take (fromIntegral bilbyFsBlockSize - length idata) (repeat 0 :: [U8])
   in listArray (0, fromIntegral bilbyFsBlockSize - 1) arrElems

extract_data_from_obj :: Obj -> ObjData
extract_data_from_obj obj =
  let union = ounion obj
   in case union of
        TObjData d -> d
        _ -> error "extract_data_from_obj: must be of type ObjData"

vfs_inode_get_size :: VfsInode -> VfsSize
vfs_inode_get_size = undefined

-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @fsop_readpage@


prop_corres_fsop_readpage :: Property
prop_corres_fsop_readpage = 
  forAll gen_fsop_readpage_arg $ \ic -> 
    let (ostore_st,vnode,block) = abs_fsop_readpage_arg ic
        oa = hs_fsop_readpage ostore_st vnode block
        oc = C.fsop_readpage ic
     in corres rel_fsop_readpage_ret oa oc

gen_fsop_readpage_arg :: Gen C.Fsop_readpage_ArgT
gen_fsop_readpage_arg = C.R7 <$> pure ()
                             <*> gen_FsState
                             <*> gen_VfsInode
                             <*> gen_OSPageOffset
                             <*> gen_Buffer

gen_FsState :: Gen C.FsState
gen_FsState = undefined

gen_VfsInode :: Gen C.VfsInode
gen_VfsInode = undefined

gen_OSPageOffset :: Gen C.OSPageOffset
gen_OSPageOffset = undefined

gen_Buffer :: Gen C.Buffer
gen_Buffer = undefined

abs_fsop_readpage_arg :: C.Fsop_readpage_ArgT -> (OstoreState, VfsInode, OSPageOffset)
abs_fsop_readpage_arg (C.R7 _ fs_st_c vnode_c block_c _) =
  let ostore_st_a = C.ostore_st fs_st_c
      C.R20 _ (C.R21 ino) = vnode_c
      vnode_a = VfsInode ino
      block_a = block_c
   in (ostore_st_a, vnode_a, block_a)

rel_fsop_readpage_ret :: Either ErrCode (WordArray U8) -> C.Fsop_readpage_RetT -> Bool
rel_fsop_readpage_ret (Left e_a) (_, C.V34_Error e_c) = e_a == e_c
rel_fsop_readpage_ret (Right arr_a) (C.R6 _ _ _ (C.R8 data_c bound_c), C.V34_Success ()) =
  let (l_a, u_a) = bounds arr_a
      (l_c, u_c) = bounds data_c
   in u_a - 1 == min (u_c - 1) bound_c - 1 &&
      l_a == 0 && l_c == 0 &&
      elems arr_a == elems data_c
rel_fsop_readpage_ret _ _ = False



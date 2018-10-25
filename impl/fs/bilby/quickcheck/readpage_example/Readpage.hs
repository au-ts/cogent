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


data VfsInode = VfsInode { ino :: U32, isize :: VfsSize } deriving (Eq, Ord, Show)

vfs_inode_get_ino :: VfsInode -> VfsIno
vfs_inode_get_ino = ino

vfs_inode_get_size :: VfsInode -> VfsSize
vfs_inode_get_size  = isize

type OSPageOffset = U64

hs_fsop_readpage :: OstoreState
                 -> VfsInode
                 -> OSPageOffset
                 -> CogentMonad (Either ErrCode (Maybe (WordArray U8)))
hs_fsop_readpage ostore vnode block =
  let size = vfs_inode_get_size vnode :: U64  -- the number of bytes we need to read
      limit = size `shiftR` fromIntegral bilbyFsBlockShift  -- the number of blocks we need to read
   in if | block > limit -> return $ Left eNoEnt
         -- ^ if we are reading beyond the last block we need to read, return an zeroed buffer
         | block == limit && (size `mod` fromIntegral bilbyFsBlockSize == 0) ->
             return $ Right Nothing
         -- ^ if we are reading the "last" one which extra bytes in this block is 0, then return old buffer
         | otherwise -> return (Right $ Just $ read_block ostore vnode block) <|>
                        (Left <$> [eIO, eNoMem, eInval, eBadF, eNoEnt])
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


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @fsop_readpage@


prop_corres_fsop_readpage :: Property
prop_corres_fsop_readpage = 
  forAll gen_fsop_readpage_arg $ \ic -> 
    let (ostore_st,vnode,block) = abs_fsop_readpage_arg ic
        oa = hs_fsop_readpage ostore_st vnode block
        oc = C.fsop_readpage ic
     in corres rel_fsop_readpage_ret oa (ic,oc)

gen_fsop_readpage_arg :: Gen C.Fsop_readpage_ArgT
gen_fsop_readpage_arg = do
  ino <- arbitrary
  C.R7 <$> pure ()
       <*> gen_FsState ino
       <*> gen_VfsInode ino
       <*> gen_OSPageOffset
       <*> gen_Buffer

gen_FsState :: C.VfsIno -> Gen C.FsState
gen_FsState ino = C.R22 <$> gen_FsopState <*> gen_MountState <*> gen_OstoreState ino

gen_FsopState :: Gen C.FsopState
gen_FsopState = arbitrary

gen_MountState :: Gen C.MountState
gen_MountState = arbitrary

gen_OstoreState :: C.VfsIno -> Gen C.OstoreState
gen_OstoreState ino = do
  let gen_entry = (,) <$> arbitrary <*> gen_Obj
      hit_entry = (,) <$> pure (fromIntegral ino) <*> gen_Obj
  l <- (:) <$> hit_entry <*> listOf gen_entry
  return $ M.fromList l
  
gen_Obj :: Gen Ax.Obj
gen_Obj = Ax.Obj <$> arbitrary
                 <*> arbitrary
                 <*> arbitrary
                 <*> arbitrary
                 <*> arbitrary
                 <*> arbitrary
                 <*> arbitrary
                 <*> gen_ObjUnion_Data

gen_ObjUnion_Data :: Gen Ax.ObjUnion
gen_ObjUnion_Data = TObjData <$> gen_ObjData

gen_ObjData :: Gen Ax.ObjData
gen_ObjData = Ax.ObjData <$> arbitrary <*> gen_WordArray_Word8

gen_VfsInode :: C.VfsIno -> Gen C.VfsInode
gen_VfsInode ino = C.R20 <$> gen_VfsInodeAbstract ino <*> (C.R21 <$> arbitrary)

gen_VfsInodeAbstract :: C.VfsIno -> Gen C.VfsInodeAbstract
gen_VfsInodeAbstract ino = C.VfsInodeAbstract ino <$> arbitrary  -- FIXME: what's the range of the size?

gen_OSPageOffset :: Gen C.OSPageOffset
gen_OSPageOffset = arbitrary  -- FIXME: what does this mean in the FS?

gen_Buffer :: Gen C.Buffer
gen_Buffer = do
  arr <- gen_WordArray_Word8
  let (0, u) = bounds arr
  b <- choose (0, u)
  return $ C.R8 arr b

gen_WordArray_Word8 :: Gen (WordArray Word8)
gen_WordArray_Word8 = do 
  l <- choose (1, 200)
  elems <- vector l
  return $ listArray (0, fromIntegral $ length elems - 1) elems

abs_fsop_readpage_arg :: C.Fsop_readpage_ArgT -> (OstoreState, VfsInode, OSPageOffset)
abs_fsop_readpage_arg (C.R7 _ fs_st_c vnode_c block_c _) =
  let ostore_st_a = C.ostore_st fs_st_c
      C.R20 (C.VfsInodeAbstract ino isize) _ = vnode_c
      vnode_a = VfsInode ino isize
      block_a = block_c
   in (ostore_st_a, vnode_a, block_a)

rel_fsop_readpage_ret :: Either ErrCode (Maybe (WordArray U8))
                      -> (C.Fsop_readpage_ArgT, C.Fsop_readpage_RetT)
                      -> Bool
rel_fsop_readpage_ret (Left e_a) (_, (_, C.V34_Error e_c)) = e_a == e_c
rel_fsop_readpage_ret (Right Nothing) (C.R7 _ _ _ _ addr, (C.R6 _ _ _ addr', C.V34_Success ())) =
  addr == addr'
rel_fsop_readpage_ret (Right (Just arr_a)) (_, (C.R6 _ _ _ (C.R8 data_c bound_c), C.V34_Success ())) =
  let (l_a, u_a) = bounds arr_a
      (l_c, u_c) = bounds data_c
   in u_a - 1 == min (u_c - 1) bound_c - 1 &&
      l_a == 0 && l_c == 0 &&
      elems arr_a == elems data_c
rel_fsop_readpage_ret _ _ = False



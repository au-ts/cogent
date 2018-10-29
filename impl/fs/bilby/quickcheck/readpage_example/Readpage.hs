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
import Data.List
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

import Debug.Trace

-- /////////////////////////////////////////////////////////////////////////////
--
-- * Haskell spec.


data VfsInode = VfsInode { ino :: U32, isize :: VfsSize } deriving (Eq, Ord, Show)

vfs_inode_get_ino :: VfsInode -> VfsIno
vfs_inode_get_ino = ino

vfs_inode_get_size :: VfsInode -> VfsSize
vfs_inode_get_size  = isize

type OSPageOffset = U64

hs_fsop_readpage :: AfsState
                 -> VfsInode
                 -> OSPageOffset
                 -> WordArray U8
                 -> CogentMonad (Either ErrCode (WordArray U8))
hs_fsop_readpage afs vnode block buf =
  let size = vfs_inode_get_size vnode :: U64  -- the number of bytes we need to read
      limit = size `shiftR` fromIntegral bilbyFsBlockShift  -- the number of blocks we need to read
   in if | block > limit -> return $ Left eNoEnt
         -- ^ if we are reading beyond the last block we need to read, return an zeroed buffer
         | block == limit && (size `mod` fromIntegral bilbyFsBlockSize == 0) ->
             return $ Right buf
         -- ^ if we are reading the "last" one which extra bytes in this block is 0, then return old buffer
         | otherwise -> return (Right $ read_block afs vnode block) <|>
                        (Left <$> [eIO, eNoMem, eInval, eBadF, eNoEnt])
         -- ^ if we are reading a block which contains data, then we read the block

read_block :: AfsState -> VfsInode -> OSPageOffset -> WordArray U8
read_block afs inode block =
  let pages = fromJust $ M.lookup (vfs_inode_get_ino inode) afs 
   in pages !! fromIntegral block


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @fsop_readpage@


prop_corres_fsop_readpage :: Property
prop_corres_fsop_readpage = 
  forAll gen_fsop_readpage_arg $ \ic -> 
    let (afs,vnode,block,buf) = abs_fsop_readpage_arg ic
        oa = hs_fsop_readpage afs vnode block buf
        oc = C.fsop_readpage ic
     in corres rel_fsop_readpage_ret oa oc

gen_fsop_readpage_arg :: Gen C.Fsop_readpage_ArgT
gen_fsop_readpage_arg = do
  ino <- arbitrary
  m <- getSmall <$> arbitrary
  isize <- frequency [ (1, pure (m * fromIntegral bilbyFsBlockSize))
                     , (1, arbitrary) ]  -- FIXME: what's the range of this size?
  C.R7 <$> pure ()
       <*> gen_FsState ino
       <*> gen_VfsInode ino isize
       <*> gen_OSPageOffset isize
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
  M.fromList <$> shuffle l
  
gen_Obj :: Gen C.Obj
gen_Obj = C.R28 <$> arbitrary  -- magic
                <*> arbitrary  -- crc
                <*> arbitrary  -- sqnum
                <*> arbitrary  -- offs
                <*> arbitrary  -- len
                <*> arbitrary  -- trans
                <*> arbitrary  -- otype
                <*> gen_ObjUnion_Data  -- ounion

gen_ObjUnion_Data :: Gen C.ObjUnion
gen_ObjUnion_Data = C.V29_TObjData <$> gen_ObjData

gen_ObjData :: Gen C.ObjData
gen_ObjData = C.R30 <$> arbitrary <*> (gen_WordArray_Word8 =<< choose (1, bilbyFsBlockSize))

gen_VfsInode :: C.VfsIno -> C.VfsSize -> Gen C.VfsInode
gen_VfsInode ino isize = C.R20 <$> gen_VfsInodeAbstract ino isize <*> (C.R21 <$> arbitrary)

gen_VfsInodeAbstract :: C.VfsIno -> C.VfsSize -> Gen C.VfsInodeAbstract
gen_VfsInodeAbstract = (return .) . C.VfsInodeAbstract

gen_OSPageOffset :: C.VfsSize -> Gen C.OSPageOffset
gen_OSPageOffset isize = do
  let limit = isize `shiftR` fromIntegral bilbyFsBlockShift
  pos <- getPositive <$> arbitrary
  frequency [ (1, pure $ limit + pos)
            , (1, pure $ limit)
            , (3, choose (1, limit - 1))
            ]

gen_Buffer :: Gen C.Buffer
gen_Buffer = do
  arr <- gen_WordArray_Word8 bilbyFsBlockSize
  return $ C.R8 arr bilbyFsBlockSize

gen_WordArray_Word8 :: Word32 -> Gen (WordArray Word8)
gen_WordArray_Word8 sz = do 
  elems <- vector (fromIntegral sz)
  return $ listArray (0, fromIntegral $ length elems - 1) elems

abs_fsop_readpage_arg :: C.Fsop_readpage_ArgT -> (AfsState, VfsInode, OSPageOffset, WordArray U8)
abs_fsop_readpage_arg (C.R7 _ fs_st_c vnode_c block_c buf_c) =
  let ostore_c = C.ostore_st fs_st_c
      C.R20 (C.VfsInodeAbstract ino isize) _ = vnode_c
      vnode_a = VfsInode ino isize
      block_a = block_c
      buf_a = abs_Buffer buf_c
      afs_a = abs_OstoreState ostore_c
   in (afs_a, vnode_a, block_a, buf_a)

abs_OstoreState :: C.OstoreState -> AfsState
abs_OstoreState ostore = undefined

abs_Buffer :: C.Buffer -> WordArray U8
abs_Buffer (C.R8 buf bd) =
  let (0, u) = bounds buf
      u' = min u bd
      arrElems = genericTake u' $ elems buf
   in listArray (0, u'-1) arrElems

rel_fsop_readpage_ret :: Either ErrCode (WordArray U8)
                      -> C.Fsop_readpage_RetT
                      -> Bool
rel_fsop_readpage_ret (Left e_a) (_, C.V34_Error e_c) = e_a == e_c
rel_fsop_readpage_ret (Right arr_a) (C.R6 _ _ _ (C.R8 data_c bound_c), C.V34_Success ()) =
  let (l_a, u_a) = bounds arr_a
      (l_c, u_c) = bounds data_c
   in trace ("arr_a = " ++ show (take 10 $ elems arr_a) ++ "\narr_c = " ++ show (elems data_c)) $ 
        u_a == min u_c bound_c &&
      l_a == 0 && l_c == 0 &&
      elems arr_a == elems data_c
rel_fsop_readpage_ret _ _ = False



-- /////////////////////////////////////////////////////////////////////////////
-- 
-- top level

main = quickCheckWith (stdArgs { chatty = False }) prop_corres_fsop_readpage



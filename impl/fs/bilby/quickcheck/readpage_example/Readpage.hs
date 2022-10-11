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
{-# LANGUAGE ImplicitParams #-}
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
import Data.Tuple.Select (sel1, sel2, sel3)
import Data.Word
-- import Data.Void
import Numeric (showHex)
import Test.QuickCheck hiding (Success)
import qualified Test.QuickCheck as Qc (Result(..))

import CogentMonad
import Corres
import qualified Readpage_Shallow_Desugar_Tuples as C
import Fsop as Ax
import Util

-- import Debug.Trace

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
    forAll gen_oracle $ \o -> 
      let ?o = o in
      let ia = abs_fsop_readpage_arg ic
          oa = uncurry4 hs_fsop_readpage ia
          oc = C.fsop_readpage ic
       in corres rel_fsop_readpage_ret oa oc

gen_oracle :: Gen O
gen_oracle = frequency [ (9, pure 0) 
                       , (1, elements [eIO, eNoMem, eInval, eBadF])
                       ]

gen_fsop_readpage_arg :: Gen C.Fsop_readpage_ArgT
gen_fsop_readpage_arg = do
  ino <- arbitrary
  m <- getSmall <$> arbitrary
  isize <- frequency [ (1, pure (m * fromIntegral bilbyFsBlockSize))
                     , (1, fromIntegral <$> (arbitrary :: Gen VfsSize)) ]
  -- \ ^ NOTE: when this size is too large, it will be extremely slow
  C.R7 <$> pure ()
       <*> gen_FsState ino isize
       <*> gen_VfsInode ino isize
       <*> gen_OSPageOffset isize
       <*> gen_Buffer

gen_FsState :: C.VfsIno -> C.VfsSize -> Gen C.FsState
gen_FsState ino isize = C.R22 <$> gen_FsopState <*> gen_MountState <*> gen_OstoreState ino isize

gen_FsopState :: Gen C.FsopState
gen_FsopState = arbitrary

gen_MountState :: Gen C.MountState
gen_MountState = arbitrary

gen_OstoreState :: C.VfsIno -> C.VfsSize -> Gen C.OstoreState
gen_OstoreState ino isize = do
  let numOfBlk = ceiling (fromInteger (fromIntegral isize) / fromInteger (fromIntegral bilbyFsBlockSize))
  blk <- choose (0, numOfBlk - 1)
  oids <- sublistOf (map (obj_id_data_mk ino . fromIntegral) $ blk `delete` [0 .. numOfBlk - 1])
  hit_entry <- (,) <$> pure (obj_id_data_mk ino blk) <*> gen_Obj
  entries <- zip oids <$> listOf gen_Obj
  return $ M.fromList (hit_entry : entries)
  
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

-- In fact, the buffers in ObjData can be smaller than the max size, then the abs
-- function @abs_OstoreState@ will do more work to pad the smaller ones.
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
  return $ listArray (0, fromIntegral sz - 1) elems

abs_fsop_readpage_arg :: C.Fsop_readpage_ArgT -> (AfsState, VfsInode, OSPageOffset, WordArray U8)
abs_fsop_readpage_arg (C.R7 _ fs_st_c vnode_c block_c buf_c) =
  let ostore_c = C.ostore_st fs_st_c
      C.R20 (C.VfsInodeAbstract ino isize) _ = vnode_c
      vnode_a = VfsInode ino isize
      block_a = block_c
      buf_a = abs_Buffer buf_c
      afs_a = abs_OstoreState ostore_c isize
   in (afs_a, vnode_a, block_a, buf_a)

abs_OstoreState :: C.OstoreState -> C.VfsSize -> AfsState
abs_OstoreState ostore isize =
  let ostore' = M.toList ostore
      tuples = for ostore' $ \(oid, obj) -> 
                 let C.R28 _ _ _ _ _ _ _ ounion = obj
                     C.V29_TObjData (C.R30 _ odata) = ounion
                     ino = inum_from_obj_id oid
                     blk = oid Data.Bits..&. 0x1fffffff  -- lower 29 bits
                  in (ino, blk, odata)
      ino = sel1 $ head tuples
      numOfBlk = ceiling (fromInteger (fromIntegral isize) / fromInteger (fromIntegral bilbyFsBlockSize))
      all0 = listArray (0, bilbyFsBlockSize - 1) (replicate (fromIntegral bilbyFsBlockSize) 0)
      base = map (\idx -> (idx, all0)) [0 .. numOfBlk - 1]
      pages = (M.fromList $ map (\(_,b,c) -> (b,c)) tuples) `M.union` M.fromList base 
      pages' = M.map (\page -> if fromIntegral (length page) < bilbyFsBlockSize then pad page else page) pages
   in M.fromList [(ino, M.elems pages')]
  where
    pad :: WordArray U8 -> WordArray U8
    pad arr = let elems' = elems arr ++ repeat 0
               in listArray (0, bilbyFsBlockSize - 1) elems'


abs_Buffer :: C.Buffer -> WordArray U8
abs_Buffer (C.R8 buf bd) =
  let len = min (fromIntegral $ length buf) bd
      arrElems = genericTake len $ elems buf
   in listArray (0, len - 1) arrElems

rel_fsop_readpage_ret :: Either ErrCode (WordArray U8)
                      -> C.Fsop_readpage_RetT
                      -> Bool
rel_fsop_readpage_ret (Left e_a) (_, C.V34_Error e_c) = e_a == e_c
rel_fsop_readpage_ret (Right arr_a) (C.R6 _ _ _ (C.R8 data_c bound_c), C.V34_Success ()) =
  let len_a = length arr_a
      len_c = length data_c
   in len_a == min len_c (fromIntegral bound_c) &&
      elems arr_a == elems data_c
rel_fsop_readpage_ret _ _ = False


-- /////////////////////////////////////////////////////////////////////////////
-- 
-- misc.

for = flip map

-- /////////////////////////////////////////////////////////////////////////////
-- 
-- top level

main = quickCheckWith (stdArgs { maxSuccess = 500, maxSize = 40 }) prop_corres_fsop_readpage



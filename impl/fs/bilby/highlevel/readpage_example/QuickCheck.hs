{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}

module QuickCheck where

import Fsop
import Control.Arrow
import Data.Array
import Data.Bits
import qualified Data.Map as M
import Data.Word
import Data.Void
import Test.QuickCheck hiding (Success, Error)


ostore_read_A :: OstoreState -> ObjId -> Gen (R Obj ErrCode)
ostore_read_A ostore oid = do
  case M.lookup oid ostore of
    Nothing -> return $ Error eNoEnt
    Just o  -> elements $ Success o : map Error [eIO, eNoMem, eInval, eBadF]

-- prop_read_blockG :: Property
-- prop_read_blockG =
--   forAll (arbitrary :: OstoreState) $ \ostore -> 
--     forAll (aribitrary :: VfsInode) $ \vnode ->
--       forAll (arbitrary :: OSPageOffset) $ \block ->
--         forAll (arbitrary :: ObjId) $ \oid ->

read_block_A :: OstoreState -> VfsInode -> OSPageOffset -> Gen (R (WordArray U8) ErrCode)
read_block_A ostore vnode block = do
  let oid = obj_id_data_mk (vfs_inode_get_ino vnode) (downcast block)
  ostore_read_A ostore oid >>= \case
    Error e -> return $ if e == eNoEnt 
                 then Success $ wordarray_create_nz bilbyFsBlockSize
                 else Error e
    Success obj -> return $ 
      let bdata = odata . extract_data_from_union $ ounion obj
          size = wordarray_length bdata
       in if size > bilbyFsBlockSize
             then Error eInval
             else Success . listArray (0, bilbyFsBlockSize - 1) $
                    elems bdata ++ (replicate (fromIntegral $ bilbyFsBlockSize - size) (0 :: U8))

fsop_readpage_A :: OstoreState -> VfsInode -> OSPageOffset -> Gen (R (WordArray U8) ErrCode)
fsop_readpage_A ostore vnode block =
  let size = vfs_inode_get_size vnode :: U64  -- the number of bytes we need to read
      limit = size `shiftR` fromIntegral bilbyFsBlockShift  -- the number of blocks we need to read
   in if | block > limit -> return $ Error eNoEnt
         -- ^ if we are reading beyond the last block we need to read, return an zeroed buffer
         | block == limit && (size `mod` fromIntegral bilbyFsBlockSize == 0) -> 
             return . Success $ wordarray_create 0
         -- ^ if we are reading the "last" one which extra bytes in this block is 0, then return old buffer
         | otherwise -> read_block_A ostore vnode block
         -- ^ if we are reading a block which contains data, then we read the block

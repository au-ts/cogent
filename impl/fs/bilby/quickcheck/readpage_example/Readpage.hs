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
import Data.Word
-- import Data.Void
import Test.QuickCheck hiding (Success, Error)

import CogentMonad
import Corres
import qualified Bilbyfs_Shallow_Desugar_Tuples as Conc
import Fsop
import Util


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Haskell spec.

hs_read_block :: OstoreState -> VfsInode -> OSPageOffset -> CogentMonad (R (WordArray U8) ErrCode)
hs_read_block ostore vnode block = do
  let oid = obj_id_data_mk (vfs_inode_get_ino vnode) (downcast block)
  hs_ostore_read ostore oid >>= \case
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

hs_fsop_readpage :: OstoreState -> VfsInode -> OSPageOffset -> CogentMonad (R (WordArray U8) ErrCode)
hs_fsop_readpage ostore vnode block =
  let size = vfs_inode_get_size vnode :: U64  -- the number of bytes we need to read
      limit = size `shiftR` fromIntegral bilbyFsBlockShift  -- the number of blocks we need to read
   in if | block > limit -> return $ Error eNoEnt
         -- ^ if we are reading beyond the last block we need to read, return an zeroed buffer
         | block == limit && (size `mod` fromIntegral bilbyFsBlockSize == 0) -> 
             return . Success $ wordarray_create 0
         -- ^ if we are reading the "last" one which extra bytes in this block is 0, then return old buffer
         | otherwise -> hs_read_block ostore vnode block
         -- ^ if we are reading a block which contains data, then we read the block

hs_ostore_read :: OstoreState -> ObjId -> CogentMonad (R Obj ErrCode)
hs_ostore_read ostore oid = do
  case M.lookup oid ostore of
    Nothing -> return $ Error eNoEnt
    Just o  -> return (Success o) <|> map Error [eIO, eNoMem, eInval, eBadF]



-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @fsop_readpage@


prop_corres_fsop_readpage :: Property
prop_corres_fsop_readpage = 
  forAll gen_fsop_readpage_arg $ \ic -> 
    let (ostore_st,vnode,block) = abs_fsop_readpage_arg ic
        oa = hs_fsop_readpage ostore_st vnode block
        oc = Conc.fsop_readpage ic
     in corres rel_fsop_readpage_ret oa oc

gen_fsop_readpage_arg :: Gen Conc.Fsop_readpage_ArgT
gen_fsop_readpage_arg = undefined

abs_fsop_readpage_arg :: Conc.Fsop_readpage_ArgT -> (OstoreState, VfsInode, OSPageOffset)
abs_fsop_readpage_arg = undefined

rel_fsop_readpage_ret :: R (WordArray U8) ErrCode -> Conc.Fsop_readpage_RetT -> Bool
rel_fsop_readpage_ret = undefined



{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TupleSections #-}

module Fsop where

import Control.Arrow
import Data.Array
import Data.Bits
import qualified Data.Map as M
import Data.Word
import Data.Void

type U8  = Word8
type U16 = Word16
type U32 = Word32
type U64 = Word64

-- FIXME: this is implemented as a C cast in bilby
downcast = fromIntegral

data R a e = Success a | Error e

type ErrCode = U32

type OstoreState = M.Map ObjId Obj

-- We make it abstract
data VfsInode = VfsInode { ino :: U32 }

-- abstract function
vfs_inode_get_ino :: VfsInode -> U32
vfs_inode_get_ino (VfsInode ino) = ino

type OSPageOffset = U64

bilbyFsBlockShift = 12  :: U32
bilbyFsBlockSize = 4096 :: U32

ePerm        = 1    :: ErrCode
eNoEnt       = 2    :: ErrCode
eSrch        = 3    :: ErrCode
eIntr        = 4    :: ErrCode
eIO          = 5    :: ErrCode
eNXIO        = 6    :: ErrCode
eTooBig      = 7    :: ErrCode
eNoExec      = 8    :: ErrCode
eBadF        = 9    :: ErrCode
eChild       = 10   :: ErrCode
eAgain       = 11   :: ErrCode
eAcces       = 13   :: ErrCode
eNoMem       = 12   :: ErrCode
eFault       = 14   :: ErrCode
eNotBlk      = 15   :: ErrCode
eBusy        = 16   :: ErrCode
eExist       = 17   :: ErrCode
eXDev        = 18   :: ErrCode
eNoDev       = 19   :: ErrCode
eNotDir      = 20   :: ErrCode
eIsDir       = 21   :: ErrCode
eInval       = 22   :: ErrCode
eNFile       = 23   :: ErrCode
eMFile       = 24   :: ErrCode
eNoTty       = 25   :: ErrCode
eTxtBsy      = 26   :: ErrCode
eFBig        = 27   :: ErrCode
eNoSpc       = 28   :: ErrCode
eSPipe       = 29   :: ErrCode
eRoFs        = 30   :: ErrCode
eMLink       = 31   :: ErrCode
ePipe        = 32   :: ErrCode
eDom         = 33   :: ErrCode
eRange       = 34   :: ErrCode
eNameTooLong = 36   :: ErrCode
eNotEmpty    = 39   :: ErrCode
eNoData      = 42   :: ErrCode
eCrap        = 66   :: ErrCode
eOverflow    = 75   :: ErrCode
eRecover     = 88   :: ErrCode

{-
 
|<-------------------- data ----------------------->|
+--------------+--------------+--------------+---------------
|xxxxxxxxxxxxxx|xxxxxxxxxxxxxx|xxxxxxxxxxxxxx|xxxxxxx........  -- (A)
+--------------+--------------+--------------+---------------
|xxxxxxxxxxxxxx|xxxxxxxxxxxxxx|xxxxxxxxxxxxxx|...............  -- (B)
+--------------+--------------+--------------+---------------
|<- block 0 -->|      1              2               3

In case (A), limit = 3.
When block = 0,1,2 just read.
     block = 3, because the size of the data is not perfectly aligned at the end, we still read.
     block >= 4, return empty.
In case (B), limit = 3.
when block = 3, that's the special case. We return the old buffer unmodified.

-}


fsop_readpage :: OstoreState -> VfsInode -> OSPageOffset -> R (WordArray U8) ErrCode
fsop_readpage ostore vnode block =
  let size = vfs_inode_get_size vnode :: U64  -- the number of bytes we need to read
      limit = size `shiftR` fromIntegral bilbyFsBlockShift  -- the number of blocks we need to read
   in if | block > limit -> Error eNoEnt
         -- ^ if we are reading beyond the last block we need to read, return an zeroed buffer
         | block == limit && (size `mod` fromIntegral bilbyFsBlockSize == 0) -> 
             Success $ wordarray_create 0
         -- ^ if we are reading the "last" one which extra bytes in this block is 0, then return old buffer
         | otherwise -> read_block ostore vnode block
         -- ^ if we are reading a block which contains data, then we read the block


read_block :: OstoreState -> VfsInode -> OSPageOffset -> R (WordArray U8) ErrCode
read_block ostore vnode block =
  let oid = obj_id_data_mk (vfs_inode_get_ino vnode) (downcast block)
   in case ostore_read ostore oid of
        Error e -> if e == eNoEnt 
                      then Success $ wordarray_create_nz bilbyFsBlockSize
                      else Error e
        Success obj ->
          let bdata = odata . extract_data_from_union $ ounion obj
              size = wordarray_length bdata
           in if size > bilbyFsBlockSize
                 then Error eInval
                 else Success . listArray (0, bilbyFsBlockSize - 1) $
                        elems bdata ++ (replicate (fromIntegral $ bilbyFsBlockSize - size) (0 :: U8))


extract_data_from_union :: ObjUnion -> ObjData
extract_data_from_union u = case u of TObjData v -> v

data Obj = Obj { magic  :: U32
               , crc    :: U32
               , sqnum  :: U64
               , offs   :: U32  -- in-mem only field
               , len    :: U32
               , trans  :: ObjTrans
               , otype  :: ObjType
               , ounion :: ObjUnion
               }

type ObjTrans = U8
type ObjType  = U8
data ObjUnion = TObjDentarr ObjDentarr
              | TObjInode ObjInode
              | TObjData ObjData
              | TObjDel ObjDel
              | TObjSuper ObjSuper
              | TObjSummary ObjSummary
              | TObjPad ()

-- Their definitions shouldn't matter for this example
data ObjDentarr
data ObjInode
data ObjDel
data ObjSuper
data ObjSummary

data ObjData = ObjData { oid :: ObjId, odata :: WordArray U8 }

type ObjId = U64

type VfsIno = U32

obj_id_inode_mk :: VfsIno -> ObjId
obj_id_inode_mk ino = (fromIntegral ino `shiftL` 32) .|. bilbyFsOidMaskInode

obj_id_data_mk :: VfsIno -> U32 -> ObjId
obj_id_data_mk ino blk = obj_id_inode_mk ino .|. bilbyFsOidMaskData .|. fromIntegral blk

bilbyFsOidMaskData :: U64
bilbyFsOidMaskData = fromIntegral bilbyFsObjTypeData `shiftL` fromIntegral bilbyFsXinfoShift

bilbyFsOidMaskInode :: U64
bilbyFsOidMaskInode = fromIntegral bilbyFsObjTypeInode `shiftL` fromIntegral bilbyFsXinfoShift

bilbyFsXinfoShift :: U64
bilbyFsXinfoShift = 29

bilbyFsObjTypeInode :: U8
bilbyFsObjTypeInode = 0

bilbyFsObjTypeData :: U8
bilbyFsObjTypeData = 1


-- TODO: out-of-scope
ostore_read :: OstoreState -> ObjId -> R Obj ErrCode
ostore_read ostore oid = undefined


type VfsSize = U64

-- TODO: abstract function
vfs_inode_get_size :: VfsInode -> VfsSize
vfs_inode_get_size = undefined

-- abstract datatype
-- NOTE: we assume that the lower bound is always 1
type WordArray a = Array U32 a

type WordArrayIndex = U32

-- TODO: abstract function
wordarray_create :: (Num a) => U32 -> WordArray a
wordarray_create = wordarray_create_nz

-- TODO: abstract function
wordarray_create_nz :: (Num a) => U32 -> WordArray a
wordarray_create_nz l = listArray (0, l-1) (replicate (fromIntegral l) 0)

-- abstract function
wordarray_length :: (Num a) => WordArray a -> U32
wordarray_length = snd . bounds 


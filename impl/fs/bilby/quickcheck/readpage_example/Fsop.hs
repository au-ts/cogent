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

type OstoreState = M.Map ObjId Obj

-- We make it abstract
data VfsInode = VfsInode { ino :: U32 } deriving (Eq, Ord, Show)

-- abstract function
vfs_inode_get_ino :: VfsInode -> U32
vfs_inode_get_ino (VfsInode ino) = ino

type OSPageOffset = U64


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


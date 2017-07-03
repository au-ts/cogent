
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module FFI where

import Foreign
import Foreign.Ptr
import Foreign.C.String
import Foreign.C.Types

#include "wrapper_pp_inferred.c"

#{enum Tag, Tag, \
    TAG_ENUM_Break, \
    TAG_ENUM_Error, \
    TAG_ENUM_Iterate, \
    TAG_ENUM_None, \
    TAG_ENUM_Some, \
    TAG_ENUM_Success, \
    TAG_ENUM_TObjData, \
    TAG_ENUM_TObjDel, \
    TAG_ENUM_TObjDentar, \
    TAG_ENUM_TObjInode, \
    TAG_ENUM_TObjPad, \
    TAG_ENUM_TObjSummary, \
    TAG_ENUM_TObjSuper \
}

newtype CSysState = CSysState { dummy :: CChar } deriving Storable

newtype Tag = Tag Int deriving (Enum)

newtype Ctag_t = Ctag_t CInt deriving Storable
newtype Cunit_t = Cunit_t { dummy :: CInt } deriving Storable
newtyoe Cbool_t = Cbool_t { boolean :: CUChar } deriving Storable

type Cu8  = CUChar
type Cu16 = CUShort 
type Cu32 = CUInt
type Cu64 = CULLong

data Ct432 = Ct432 { p1 :: Ptr CSysState, p2 :: Ptr Ct72, p3 :: Ptr Ct68 }
data Ct435 = Ct435 { p1 :: Ptr CSysState, p2 :: Ct434 }

data Ct434 = Ct434 {
    tag     :: Ctag_t
  , error   :: Ct433
  , success :: Ptr Ct68
}

data Ct433 = Ct433 { p1 :: Cu32, p2 :: Ptr Ct68 }

data Ct72 = Ct72 {
    eb_recovery      :: Cu32
  , eb_recovery_offs :: Cu32
  , super            :: Ptr Ct39
  , obh_sup          :: Ptr Ct66
  , super_offs       :: Cu32
  , vol              :: Ptr CUbiVolInfo
  , dev              :: Ptr CUbiDevInfo
  , no_summary       :: Cbool_t
  }

data Ct68 = Ct68 {
    nb_free_eb  :: Cu32
  , used_eb     :: Ptr CWordArray_u8
  , dirty_space :: Ptr CWordArray_u32
  , gim         :: Ptr CRbt_u64_ut18
  }

data Ct66 = Ct66 {
    magic  :: Cu32
  , crc    :: Cu32
  , sqnum  :: Cu64
  , offs   :: Cu32
  , trans  :: Cu8
  , otype  :: Cu8
  , ounion :: Ct65
  }

data Ct65 = Ct65 {
    tag         :: Ctag_t
  , tObjData    :: Ct62
  , tObjDel     :: Ct63
  , tObjDentarr :: Ptr Ct64
  , tObjInode   :: Ptr Ct45
  , tObjPad     :: Cunit_t
  , tObjSummary :: Ptr Ct42
  , tObjSuper   :: Ptr Ct39
  }

data Ct64 = Ct64 {
    id        :: Cu64
  , nb_dentry :: Cu32
  , entries   :: Ptr CArray_t48
  }

data Ct63 = Ct63 { id :: Cu64 }

data Ct62 = Ct62 { id :: Cu64, odata :: Ptr CWordArray_u8 }

data Ct48 = Ct48 { 
    ino   :: Cu32
  , dtype :: Cu8
  , nlen  :: Cu16
  , name  :: Ptr CWordArray_u8
  }

data Ct45 = Ct45 {
    id        :: Cu64
  , size      :: Cu64
  , atime_sec :: Cu64
  , ctime_sec :: Cu64
  , mtime_sec :: Cu64
  , nlink     :: Cu32
  , uid       :: Cu32
  , gid       :: Cu32
  , mode      :: Cu32
  , flags     :: Cu32
  }

data Ct42 = Ct42 {
    nb_sum_entry :: Cu32
  , entries      :: Ptr CWordArray_ut10
  , sum_offs     :: Cu32
  }

data Ct39 = Ct39 {
    nb_eb           :: Cu32
  , eb_size         :: Cu32
  , io_size         :: Cu32
  , nb_reserved_gc  :: Cu32
  , nb_reserved_del :: Cu32
  , cur_eb          :: Cu32
  , cur_offs        :: Cu32
  , last_inum       :: Cu32
  , next_sqnum      :: Cu64
  }

data Ct10 = Ct10 {
    id    :: Cu64
  , sqnum :: Cu64
  , len   :: Cu32
  , del_flags_and_offs :: Cu32
  , count :: Cu16
  }

type CUbiVolInfo = Cubi_volume_info

data Cubi_volume_info = Cubi_volume_info {
    ubi_num         :: CInt
  , vol_id          :: CInt
  , size            :: CInt
  , used_bytes      :: CLLong
  , used_ebs        :: CInt
  , vol_type        :: CInt
  , corrupted       :: CInt
  , upd_marker      :: CInt
  , alignment       :: CInt
  , usable_leb_size :: CInt
  , name_len        :: CInt
  , name            :: Ptr CChar
  , cdev            :: Cdev_t
  }

{-
struct ubi_volume_info {
	int ubi_num;
	int vol_id;
	int size;
	long long used_bytes;
	int used_ebs;
	int vol_type;
	int corrupted;
	int upd_marker;
	int alignment;
	int usable_leb_size;
	int name_len;
	const char *name;
	dev_t cdev;
};
-}

type Cdev_t = C__kernel_dev_t
type C__kernel_dev_t = C__u32
type C__u32 = Word32

type CUbiDevInfo = Cubi_device_info

data Cubi_device_info = Cubi_device_info {
    ubi_num        :: CInt
  , leb_size       :: CInt
  , leb_start      :: CInt
  , min_io_size    :: CInt
  , max_write_size :: CInt
  , ro_mode        :: CInt
  , cdev           :: Cdev_t
  }

{-
struct ubi_device_info {
	int ubi_num;
	int leb_size;
	int leb_start;
	int min_io_size;
	int max_write_size;
	int ro_mode;
	dev_t cdev;
};
-}

data CArray_t48 = CArray_t48 {
    len    :: CInt
  , values :: Ptr (Ptr Ct48)
  }

data CWordArray_u8 = CWordArray_u8 {
    len    :: CInt
  , values :: Ptr Cu8
  }

data CWordArray_ut10 = CWordArray_ut10 {
    len    :: CInt
  , values :: Ptr Ct10
  }

data CWordArray_u32 = CWordArray_u32 {
    len    :: CInt
  , values :: Ptr Cu32
  }

data CRbt_u64_ut18 = CRbt_u64_ut18 { rbt :: Crbt_root }

data Crbt_root = Crbt_root { root :: Crbt_node }

data Crbt_node = Crbt_node {
    rbt_parent_color :: CULong
  , rbt_left         :: Ptr Crbt_node
  , rbt_right        :: Ptr Crbt_node
  }


instance Storable Ct27 where
  sizeOf    _ = (#size t27)
  alignment _ = (#alignment t27)
  peek ptr = Ct27 <$> (#peek t27, p1) ptr <*> (#peek t27, p2) ptr <*> (#peek t27, p3) ptr
  poke ptr (Ct27 p1 p2 p3) = do
    (#poke t27, p1) ptr p1
    (#poke t27, p2) ptr p2
    (#poke t27, p3) ptr p3

instance Storable Ct4 where
  sizeOf    _ = (#size t4)
  alignment _ = (#alignment t4)
  peek ptr = Ct4 <$> (#peek t4, len) ptr <*> (#peek t4, key) ptr
  poke ptr (Ct4 len key) = (#poke t4, len) ptr len >> (#poke t4, key) ptr key

instance Storable Ct28 where
  sizeOf    _ = (#size t28)
  alignment _ = (#alignment t28)
  peek ptr = Ct28 <$> (#peek t28, tag) ptr <*> (#peek t28, None) ptr <*> (#peek t28, Some) ptr
  poke ptr (Ct28 tag none some) = do
    (#poke t28, tag ) ptr tag
    (#poke t28, None) ptr none
    (#poke t28, Some) ptr some

instance Storable Ct29 where
  sizeOf    _ = (#size t29)
  alignment _ = (#alignment t29)
  peek ptr = Ct29 <$> (#peek t29, p1) ptr <*> (#peek t29, p2) ptr
  poke ptr (Ct29 p1 p2) = do
    (#poke t29, p1) ptr p1
    (#poke t29, p2) ptr p2

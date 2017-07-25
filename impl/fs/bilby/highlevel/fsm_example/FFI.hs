{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -F -pgmFderive -optF-F #-}

module FFI where

import Data.Functor.Const (Const(..))
import Foreign
import Foreign.Ptr
import Foreign.C.String
import Foreign.C.Types
import System.IO.Unsafe
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen

import Util

-- /////////////////////////////////////////////////////////////////////////////

tag_ENUM_Error       = Tag 0
tag_ENUM_Success     = Tag 1
tag_ENUM_TObjData    = Tag 2
tag_ENUM_TObjDel     = Tag 3
tag_ENUM_TObjDentarr = Tag 4
tag_ENUM_TObjInode   = Tag 5
tag_ENUM_TObjPad     = Tag 5
tag_ENUM_TObjSummary = Tag 6
tag_ENUM_TObjSuper   = Tag 7

newtype CSysState = CSysState { dummy :: CChar } deriving Storable

instance Arbitrary CSysState where
  arbitrary = return dummyCSysState

dummyCSysState :: CSysState
dummyCSysState = CSysState $ CChar 0

pDummyCSysState :: IO (Ptr CSysState)
pDummyCSysState = new dummyCSysState

newtype Tag = Tag Int deriving (Enum)

instance Bounded Tag where
  maxBound = tag_ENUM_TObjSuper
  minBound = tag_ENUM_Error

newtype Ctag_t = Ctag_t CInt deriving (Show, Storable)
newtype Cunit_t = Cunit_t { dummy :: CInt } deriving (Show, Storable)
newtype Cbool_t = Cbool_t { boolean :: CUChar } deriving (Show, Storable)

instance Arbitrary Ctag_t where
  arbitrary = Ctag_t <$> elements [minBound .. maxBound]

instance Arbitrary Cunit_t where
  arbitrary = return const_unit

instance Arbitrary Cbool_t where
  arbitrary = elements [const_true, const_false]

const_unit = Cunit_t $ CInt 0
const_true  = Cbool_t $ CUChar 1
const_false = Cbool_t $ CUChar 0

type Cu8  = CUChar
type Cu16 = CUShort 
type Cu32 = CUInt
type Cu64 = CULLong

data Ct24 = Ct24 { p1 :: Ptr CSysState, p2 :: Ct23 } deriving Show

instance Storable Ct24 where
  sizeOf    _ = 40
  alignment _ = 8
  peek ptr = Ct24 <$> (\p -> peekByteOff p 0) ptr <*> (\p -> peekByteOff p 8) ptr
  poke ptr (Ct24 f1 f2) = (\p -> pokeByteOff p 0) ptr f1 >> (\p -> pokeByteOff p 8) ptr f2

data Ct23 = Ct23 {
    tag     :: Ctag_t
  , error   :: Ct22
  , success :: Ptr Ct20
} deriving Show

instance Storable Ct23 where
  sizeOf    _ = 32
  alignment _ = 8
  peek ptr = Ct23 <$> (\p -> peekByteOff p 0 ) ptr
                  <*> (\p -> peekByteOff p 8 ) ptr
                  <*> (\p -> peekByteOff p 24) ptr
  poke ptr (Ct23 f1 f2 f3) = do
    (\p -> pokeByteOff p 0 ) ptr f1
    (\p -> pokeByteOff p 8 ) ptr f2
    (\p -> pokeByteOff p 24) ptr f3

data Ct22 = Ct22 { p1 :: Cu32, p2 :: Ptr Ct20 } deriving Show

instance Storable Ct22 where
  sizeOf    _ = 16
  alignment _ = 8
  peek ptr = Ct22 <$> (\p -> peekByteOff p 0) ptr <*> (\p -> peekByteOff p 8) ptr
  poke ptr (Ct22 p1 p2) = (\p -> pokeByteOff p 0) ptr p1 >> (\p -> pokeByteOff p 8) ptr p2

data Ct21 = Ct21 { p1 :: Ptr CSysState, p2 :: Ptr Ct19, p3 :: Ptr Ct20 } deriving Show

instance Storable Ct21 where
  sizeOf    _ = 24
  alignment _ = 8
  peek ptr = Ct21 <$> (\p -> peekByteOff p 0 ) ptr
                  <*> (\p -> peekByteOff p 8 ) ptr
                  <*> (\p -> peekByteOff p 16) ptr
  poke ptr (Ct21 p1 p2 p3) = do
    (\p -> pokeByteOff p 0 ) ptr p1
    (\p -> pokeByteOff p 8 ) ptr p2
    (\p -> pokeByteOff p 16) ptr p3

data Ct19 = Ct19 {
    eb_recovery      :: Cu32
  , eb_recovery_offs :: Cu32
  , super            :: Ptr Ct9
  , obj_sup          :: Ptr Ct18
  , super_offs       :: Cu32
  , vol              :: Ptr CUbiVolInfo
  , dev              :: Ptr CUbiDevInfo
  , no_summary       :: Cbool_t
  } deriving Show

instance Storable Ct19 where
  sizeOf    _ = 56
  alignment _ = 8
  peek ptr = Ct19 <$> (\p -> peekByteOff p 0 ) ptr
                  <*> (\p -> peekByteOff p 4 ) ptr
                  <*> (\p -> peekByteOff p 8 ) ptr
                  <*> (\p -> peekByteOff p 16) ptr
                  <*> (\p -> peekByteOff p 24) ptr
                  <*> (\p -> peekByteOff p 32) ptr
                  <*> (\p -> peekByteOff p 40) ptr
                  <*> (\p -> peekByteOff p 48) ptr
  poke ptr (Ct19 f1 f2 f3 f4 f5 f6 f7 f8) = do
    (\p -> pokeByteOff p 0 ) ptr f1
    (\p -> pokeByteOff p 4 ) ptr f2
    (\p -> pokeByteOff p 8 ) ptr f3
    (\p -> pokeByteOff p 16) ptr f4
    (\p -> pokeByteOff p 24) ptr f5
    (\p -> pokeByteOff p 32) ptr f6
    (\p -> pokeByteOff p 40) ptr f7
    (\p -> pokeByteOff p 48) ptr f8

data Ct20 = Ct20 {
    nb_free_eb  :: Cu32
  , used_eb     :: Ptr (CWordArray Cu8 )
  , dirty_space :: Ptr (CWordArray Cu32)
  , gim         :: Ptr (CRbt Cu64 Ct3)
  } deriving Show

instance Storable Ct20 where
  sizeOf    _ = 32
  alignment _ = 8
  peek ptr = Ct20 <$> (\p -> peekByteOff p 0 ) ptr
                  <*> (\p -> peekByteOff p 8 ) ptr
                  <*> (\p -> peekByteOff p 16) ptr
                  <*> (\p -> peekByteOff p 24) ptr
  poke ptr (Ct20 f1 f2 f3 f4) = do
    (\p -> pokeByteOff p 0 ) ptr f1
    (\p -> pokeByteOff p 8 ) ptr f2
    (\p -> pokeByteOff p 16) ptr f3
    (\p -> pokeByteOff p 24) ptr f4

data Ct18 = Ct18 {
    magic  :: Cu32
  , crc    :: Cu32
  , sqnum  :: Cu64
  , offs   :: Cu32
  , trans  :: Cu8
  , otype  :: Cu8
  , ounion :: Ct17
  }

instance Storable Ct18 where
  sizeOf    _ = 96
  alignment _ = 8
  peek ptr = Ct18 <$> (\p -> peekByteOff p 0 ) ptr
                  <*> (\p -> peekByteOff p 4 ) ptr
                  <*> (\p -> peekByteOff p 8 ) ptr
                  <*> (\p -> peekByteOff p 16) ptr
                  <*> (\p -> peekByteOff p 20) ptr
                  <*> (\p -> peekByteOff p 22) ptr
                  <*> (\p -> peekByteOff p 24) ptr
  poke ptr (Ct18 f1 f2 f3 f4 f5 f6 f7) = do
    (\p -> pokeByteOff p 0 ) ptr f1
    (\p -> pokeByteOff p 4 ) ptr f2
    (\p -> pokeByteOff p 8 ) ptr f3
    (\p -> pokeByteOff p 16) ptr f4
    (\p -> pokeByteOff p 20) ptr f5
    (\p -> pokeByteOff p 22) ptr f6
    (\p -> pokeByteOff p 24) ptr f7

data Ct17 = Ct17 {
    tag         :: Ctag_t
  , tObjData    :: Ct10
  , tObjDel     :: Ct11
  , tObjDentarr :: Ptr Ct13
  , tObjInode   :: Ptr Ct14
  , tObjPad     :: Cunit_t
  , tObjSummary :: Ptr Ct16
  , tObjSuper   :: Ptr Ct9
  }

instance Storable Ct17 where
  sizeOf    _ = 72
  alignment _ = 8
  peek ptr = Ct17 <$> (\p -> peekByteOff p 0 ) ptr
                  <*> (\p -> peekByteOff p 8 ) ptr
                  <*> (\p -> peekByteOff p 24) ptr
                  <*> (\p -> peekByteOff p 32) ptr
                  <*> (\p -> peekByteOff p 40) ptr
                  <*> (\p -> peekByteOff p 48) ptr
                  <*> (\p -> peekByteOff p 56) ptr
                  <*> (\p -> peekByteOff p 64) ptr
  poke ptr (Ct17 f1 f2 f3 f4 f5 f6 f7 f8) = do
    (\p -> pokeByteOff p 0 ) ptr f1
    (\p -> pokeByteOff p 8 ) ptr f2
    (\p -> pokeByteOff p 24) ptr f3
    (\p -> pokeByteOff p 32) ptr f4
    (\p -> pokeByteOff p 40) ptr f5
    (\p -> pokeByteOff p 48) ptr f6
    (\p -> pokeByteOff p 56) ptr f7
    (\p -> pokeByteOff p 64) ptr f8

data Ct13 = Ct13 {
    id        :: Cu64
  , nb_dentry :: Cu32
  , entries   :: Ptr (CArray Ct12)
  }

instance Storable Ct13 where
  sizeOf    _ = 24
  alignment _ = 8
  peek ptr = Ct13 <$> (\p -> peekByteOff p 0 ) ptr
                  <*> (\p -> peekByteOff p 8 ) ptr
                  <*> (\p -> peekByteOff p 16) ptr
  poke ptr (Ct13 f1 f2 f3) = do
    (\p -> pokeByteOff p 0 ) ptr f1
    (\p -> pokeByteOff p 8 ) ptr f2
    (\p -> pokeByteOff p 16) ptr f3


newtype Ct11 = Ct11 { id :: Cu64 } deriving (Storable)

data Ct10 = Ct10 { id :: Cu64, odata :: Ptr (CWordArray Cu8) }

instance Storable Ct10 where
  sizeOf    _ = 16
  alignment _ = 8
  peek ptr = Ct10 <$> (\p -> peekByteOff p 0) ptr <*> (\p -> peekByteOff p 8) ptr
  poke ptr (Ct10 id odata) = (\p -> pokeByteOff p 0) ptr id >> (\p -> pokeByteOff p 8) ptr odata

data Ct12 = Ct12 { 
    ino   :: Cu32
  , dtype :: Cu8
  , nlen  :: Cu16
  , name  :: Ptr (CWordArray Cu8)
  }

instance Storable Ct12 where
  sizeOf    _ = 16
  alignment _ = 8
  peek ptr = Ct12 <$> (\p -> peekByteOff p 0 ) ptr
                  <*> (\p -> peekByteOff p 4 ) ptr
                  <*> (\p -> peekByteOff p 6 ) ptr
                  <*> (\p -> peekByteOff p 8 ) ptr
  poke ptr (Ct12 f1 f2 f3 f4) = do
    (\p -> pokeByteOff p 0) ptr f1
    (\p -> pokeByteOff p 4) ptr f2
    (\p -> pokeByteOff p 6) ptr f3
    (\p -> pokeByteOff p 8) ptr f4

data Ct14 = Ct14 {
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

instance Storable Ct14 where
  sizeOf    _ = 64
  alignment _ = 8
  peek ptr = Ct14 <$> (\p -> peekByteOff p 0 ) ptr
                  <*> (\p -> peekByteOff p 8 ) ptr
                  <*> (\p -> peekByteOff p 16) ptr
                  <*> (\p -> peekByteOff p 24) ptr
                  <*> (\p -> peekByteOff p 32) ptr
                  <*> (\p -> peekByteOff p 40) ptr
                  <*> (\p -> peekByteOff p 44) ptr
                  <*> (\p -> peekByteOff p 48) ptr
                  <*> (\p -> peekByteOff p 52) ptr
                  <*> (\p -> peekByteOff p 56) ptr
  poke ptr (Ct14 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10) = do
    (\p -> pokeByteOff p 0 ) ptr f1
    (\p -> pokeByteOff p 8 ) ptr f2
    (\p -> pokeByteOff p 16) ptr f3
    (\p -> pokeByteOff p 24) ptr f4
    (\p -> pokeByteOff p 32) ptr f5
    (\p -> pokeByteOff p 40) ptr f6
    (\p -> pokeByteOff p 44) ptr f7
    (\p -> pokeByteOff p 48) ptr f8
    (\p -> pokeByteOff p 52) ptr f9
    (\p -> pokeByteOff p 56) ptr f10

data Ct16 = Ct16 {
    nb_sum_entry :: Cu32
  , entries      :: Ptr (CWordArray Ct15)
  , sum_offs     :: Cu32
  }

instance Storable Ct16 where
  sizeOf    _ = 24
  alignment _ = 8
  peek ptr = Ct16 <$> (\p -> peekByteOff p 0 ) ptr
                  <*> (\p -> peekByteOff p 8 ) ptr
                  <*> (\p -> peekByteOff p 16) ptr
  poke ptr (Ct16 f1 f2 f3) = do
    (\p -> pokeByteOff p 0 ) ptr f1
    (\p -> pokeByteOff p 8 ) ptr f2
    (\p -> pokeByteOff p 16) ptr f3


data Ct9 = Ct9 {
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

instance Storable Ct9 where
  sizeOf    _ = 40
  alignment _ = 8
  peek ptr = Ct9 <$> (\p -> peekByteOff p 0 ) ptr
                  <*> (\p -> peekByteOff p 4 ) ptr
                  <*> (\p -> peekByteOff p 8 ) ptr
                  <*> (\p -> peekByteOff p 12) ptr
                  <*> (\p -> peekByteOff p 16) ptr
                  <*> (\p -> peekByteOff p 20) ptr
                  <*> (\p -> peekByteOff p 24) ptr
                  <*> (\p -> peekByteOff p 28) ptr
                  <*> (\p -> peekByteOff p 32) ptr
  poke ptr (Ct9 f1 f2 f3 f4 f5 f6 f7 f8 f9) = do
    (\p -> pokeByteOff p 0 ) ptr f1
    (\p -> pokeByteOff p 4 ) ptr f2
    (\p -> pokeByteOff p 8 ) ptr f3
    (\p -> pokeByteOff p 12) ptr f4
    (\p -> pokeByteOff p 16) ptr f5
    (\p -> pokeByteOff p 20) ptr f6
    (\p -> pokeByteOff p 24) ptr f7
    (\p -> pokeByteOff p 28) ptr f8
    (\p -> pokeByteOff p 32) ptr f9

data Ct3 = Ct3 {
    count :: Cu16
  , sqnum :: Cu64
  }

instance Storable Ct3 where
  sizeOf    _ = 16
  alignment _ = 8
  peek ptr = Ct3 <$> (\p -> peekByteOff p 0) ptr <*> (\p -> peekByteOff p 8) ptr
  poke ptr (Ct3 count sqnum) = (\p -> pokeByteOff p 0) ptr count >> (\p -> pokeByteOff p 8) ptr sqnum

data Ct15 = Ct15 {
    id    :: Cu64
  , sqnum :: Cu64
  , len   :: Cu32
  , del_flags_and_offs :: Cu32
  , count :: Cu16
  }

instance Storable Ct15 where
  sizeOf    _ = 32
  alignment _ = 8
  peek ptr = Ct15 <$> (\p -> peekByteOff p 0 ) ptr
                  <*> (\p -> peekByteOff p 8 ) ptr
                  <*> (\p -> peekByteOff p 16) ptr
                  <*> (\p -> peekByteOff p 20) ptr
                  <*> (\p -> peekByteOff p 24) ptr
  poke ptr (Ct15 f1 f2 f3 f4 f5) = do
    (\p -> pokeByteOff p 0 ) ptr f1
    (\p -> pokeByteOff p 8 ) ptr f2
    (\p -> pokeByteOff p 16) ptr f3 
    (\p -> pokeByteOff p 20) ptr f4
    (\p -> pokeByteOff p 24) ptr f5

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
  } deriving (Show)

{-!
deriving instance Arbitrary Cubi_volume_info
!-}

instance Storable Cubi_volume_info where
  sizeOf    _ = 72
  alignment _ = 8
  peek ptr = Cubi_volume_info <$> (\p -> peekByteOff p 0 ) ptr
                              <*> (\p -> peekByteOff p 4 ) ptr
                              <*> (\p -> peekByteOff p 8 ) ptr
                              <*> (\p -> peekByteOff p 16) ptr
                              <*> (\p -> peekByteOff p 24) ptr
                              <*> (\p -> peekByteOff p 28) ptr
                              <*> (\p -> peekByteOff p 32) ptr
                              <*> (\p -> peekByteOff p 36) ptr
                              <*> (\p -> peekByteOff p 40) ptr
                              <*> (\p -> peekByteOff p 44) ptr
                              <*> (\p -> peekByteOff p 48) ptr
                              <*> (\p -> peekByteOff p 56) ptr
                              <*> (\p -> peekByteOff p 64) ptr
  poke ptr (Cubi_volume_info f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13) = do
    (\p -> pokeByteOff p 0 ) ptr f1
    (\p -> pokeByteOff p 4 ) ptr f2
    (\p -> pokeByteOff p 8 ) ptr f3
    (\p -> pokeByteOff p 16) ptr f4
    (\p -> pokeByteOff p 24) ptr f5
    (\p -> pokeByteOff p 28) ptr f6
    (\p -> pokeByteOff p 32) ptr f7
    (\p -> pokeByteOff p 36) ptr f8
    (\p -> pokeByteOff p 40) ptr f9
    (\p -> pokeByteOff p 44) ptr f10
    (\p -> pokeByteOff p 48) ptr f11
    (\p -> pokeByteOff p 56) ptr f12
    (\p -> pokeByteOff p 64) ptr f13

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
  } deriving (Show)

instance Storable Cubi_device_info where
  sizeOf    _ = 28
  alignment _ = 4
  peek ptr = Cubi_device_info <$> (\p -> peekByteOff p 0 ) ptr
                              <*> (\p -> peekByteOff p 4 ) ptr
                              <*> (\p -> peekByteOff p 8 ) ptr
                              <*> (\p -> peekByteOff p 12) ptr
                              <*> (\p -> peekByteOff p 16) ptr
                              <*> (\p -> peekByteOff p 20) ptr
                              <*> (\p -> peekByteOff p 24) ptr
  poke ptr (Cubi_device_info f1 f2 f3 f4 f5 f6 f7) = do
    (\p -> pokeByteOff p 0 ) ptr f1
    (\p -> pokeByteOff p 4 ) ptr f2
    (\p -> pokeByteOff p 8 ) ptr f3
    (\p -> pokeByteOff p 12) ptr f4
    (\p -> pokeByteOff p 16) ptr f5
    (\p -> pokeByteOff p 20) ptr f6
    (\p -> pokeByteOff p 24) ptr f7

{-!
deriving instance Arbitrary Cubi_device_info
!-}

data CArray t = CArray {
    len    :: CInt
  , values :: Ptr (Ptr t)
  }

instance Storable t => Storable (CArray t) where
  sizeOf    _ = 16
  alignment _ = 8
  peek ptr = CArray <$> (\p -> peekByteOff p 0) ptr
                    <*> (\p -> peekByteOff p 8) ptr
  poke ptr (CArray len values) = do
    (\p -> pokeByteOff p 0) ptr len
    (\p -> pokeByteOff p 8) ptr values

data CWordArray t = CWordArray {
    len    :: CInt
  , values :: Ptr t
  }

instance (Storable t) => Storable (CWordArray t) where
  sizeOf    _ = 16
  alignment _ = 8
  peek ptr = CWordArray <$> (\p -> peekByteOff p 0) ptr
                        <*> (\p -> peekByteOff p 8) ptr
  poke ptr (CWordArray len values) = do
    (\p -> pokeByteOff p 0) ptr len
    (\p -> pokeByteOff p 8) ptr values

newtype CRbt k v = CRbt { rbt :: Crbt_root k v } deriving (Eq, Ord, Show, Storable, Functor, Traversable, Foldable)

instance Functor (Flip CRbt v) where
  fmap f (Flip (CRbt r)) = Flip (CRbt $ ffmap f r)

instance Traversable (Flip CRbt v) where
  traverse f (Flip (CRbt r)) = Flip <$> (CRbt <$> ttraverse f r)

instance Foldable (Flip CRbt v) where
  foldMap f a = getConst $ traverse (Const . f) a

newtype Crbt_root k v = Crbt_root { root :: Ptr (Crbt_node k v) } deriving (Eq, Ord, Show, Storable)

instance Functor (Crbt_root k) where
  fmap _ (Crbt_root r) = Crbt_root $ castPtr r
instance Functor (Flip Crbt_root v) where
  fmap _ (Flip (Crbt_root r)) = Flip (Crbt_root $ castPtr r)

instance Traversable (Crbt_root k) where
  traverse _ (Crbt_root r) = pure $ Crbt_root $ castPtr r
instance Traversable (Flip Crbt_root v) where
  traverse _ (Flip (Crbt_root r)) = pure $ Flip $ Crbt_root $ castPtr r

instance Foldable (Crbt_root k) where
  foldMap f a = getConst $ traverse (Const . f) a
instance Foldable (Flip Crbt_root v) where
  foldMap f a = getConst $ traverse (Const . f) a


data Crbt_node k v = Crbt_node {
    rbt_parent_color :: CULong
  , rbt_left         :: Ptr (Crbt_node k v)
  , rbt_right        :: Ptr (Crbt_node k v)
  } deriving (Eq, Ord, Show)

instance (Arbitrary k, Arbitrary v) => Arbitrary (CRbt k v) where
  arbitrary = CRbt <$> arbitrary

instance (Arbitrary k, Arbitrary v) => Arbitrary (Crbt_root k v) where
  arbitrary = pure $ Crbt_root nullPtr

instance (Arbitrary k, Arbitrary v) => Arbitrary (Crbt_node k v) where
  arbitrary = undefined  -- TODO

instance Storable (Crbt_node k v) where
  sizeOf    _ = 24
  alignment _ = 8
  peek ptr = Crbt_node <$> (\p -> peekByteOff p 0 ) ptr
                       <*> (\p -> peekByteOff p 8 ) ptr
                       <*> (\p -> peekByteOff p 16) ptr
  poke ptr (Crbt_node rbt_parent_color rbt_left rbt_right) = do
    (\p -> pokeByteOff p 0 ) ptr rbt_parent_color
    (\p -> pokeByteOff p 8 ) ptr rbt_left
    (\p -> pokeByteOff p 16) ptr rbt_right

instance (Arbitrary t, Storable t) => Arbitrary (Ptr t) where
  arbitrary = arbitrary >>= \x -> return (unsafePerformIO (new x))  -- FIXME

data Cffi_fsm_init_ds = Cffi_fsm_init_ds { ret :: Ptr Ct24, ds :: Ptr Bool }

instance Storable Cffi_fsm_init_ds where
  sizeOf    _ = 16
  alignment _ = 8
  peek ptr = Cffi_fsm_init_ds <$> (\p -> peekByteOff p 0) ptr
                              <*> (\p -> peekByteOff p 8) ptr
  poke ptr (Cffi_fsm_init_ds ret ds) = do
    (\p -> pokeByteOff p 0) ptr ret
    (\p -> pokeByteOff p 8) ptr ds

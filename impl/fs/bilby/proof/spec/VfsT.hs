module VfsT (
  module VfsT
, module TypBucket
)where

import TypBucket

data VfsInode = VfsInode {
  v_ino   :: Ino
, v_nlink :: U32
, v_size  :: SizeT
, v_mtime :: TimeT
, v_ctime :: TimeT
, v_uid   :: U32
, v_gid   :: U32
, v_mode  :: Mode
, v_flags :: U32
}

type Vnode = VfsInode

-- TODO: missing a few s_ functions

type Vblock = U32

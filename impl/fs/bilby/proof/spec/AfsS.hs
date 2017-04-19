
module AfsS where

import VfsT

import qualified Data.Map as M

type Byte = U8
type Page = [U8]
type Dir = M.Map [U8] Ino
type File_data = [Page]

data Afs_inode_type = IDir Dir
                    | IReg File_data
                    | ILnk [U8]

-- TODO: a few afs_inode_is_ definitions

data Afs_inode = Afs_inode {
  i_type  :: Afs_inode_type
, i_ino   :: Ino
, i_nlink :: U32
, i_size  :: U64
, i_mtime :: TimeT
, i_ctime :: TimeT
, i_uid   :: U32
, i_gid   :: U32
, i_mode  :: Mode
, i_flags :: U32
}


type Readdir_ctx = (U32, Dir)

type Afs_map = M.Map Ino Afs_inode

data Afs_state = Afs_state {
  a_is_readonly :: Bool
, a_current_time :: TimeT
, a_medium_afs :: Afs_map
, a_medium_updates :: [Afs_map -> Afs_map]
}

a_afs_update_n :: Int -> Afs_map -> [Afs_map -> Afs_map] -> Afs_map
a_afs_update_n n afs_st updates = foldr id afs_st (take n updates)

a_afs_updated :: Afs_map -> [Afs_map -> Afs_map] -> Afs_map
a_afs_updated afs_st updates = a_afs_update_n (length updates) afs_st updates

updated_afs :: Afs_state -> Afs_map
updated_afs adata = a_afs_updated (a_medium_afs adata) (a_medium_updates adata)

i_type_dir :: Afs_inode_type -> Dir
i_type_dir it = case it of IDir dir -> dir

i_dir :: Afs_inode -> Dir
i_dir = i_type_dir . i_type

i_dir_update :: (Dir -> Dir) -> Afs_inode -> Afs_inode
i_dir_update m i = i { i_type = IDir (m $ i_dir i) }

i_type_data :: Afs_inode_type -> File_data
i_type_data it = case it of IReg dat -> dat  -- change from `data` to `dat` to avoid keyword

i_data :: Afs_inode -> File_data
i_data = i_type_data . i_type

i_data_update :: (File_data -> File_data) -> Afs_inode -> Afs_inode
i_data_update m i = i { i_type = IReg (m $ i_data i) }

i_type_path :: Afs_inode_type -> [Byte]
i_type_path it = case it of ILnk path -> path

i_path :: Afs_inode -> [Byte]
i_path = i_type_path . i_type

i_path_update :: ([Byte] -> [Byte]) -> Afs_inode -> Afs_inode
i_path_update m i = i { i_type = ILnk (m $ i_path i) }


-- up to L115

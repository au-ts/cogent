{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}

module AfsS where

import CogentMonad as C
import qualified Fsop_Shallow_Desugar as D
import FunBucket
import List
import VfsT
import WordArrayT

import Data.Bits
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.Set as S (Set, singleton, map, fromList)
import Prelude as P

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

a_medium_afs_update :: (Afs_map -> Afs_map) -> Afs_state -> Afs_state
a_medium_afs_update f s = let Afs_state a b c d = s
                           in Afs_state a b (f c) d

a_medium_updates_update :: ([Afs_map -> Afs_map] -> [Afs_map -> Afs_map]) -> Afs_state -> Afs_state
a_medium_updates_update f s = let Afs_state a b c d = s
                               in Afs_state a b c (f d)


a_afs_update_n :: Int -> Afs_map -> [Afs_map -> Afs_map] -> Afs_map
a_afs_update_n n afs_st updates = foldr P.id afs_st (take n updates)

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


i_size_from_afs_inode_type :: Afs_inode_type -> U64
i_size_from_afs_inode_type (IDir dir) = undefined
i_size_from_afs_inode_type (IReg dat) = count (concat dat)
i_size_from_afs_inode_type (ILnk path) = count path

i_size_from_type :: Afs_inode -> U64
i_size_from_type = i_size_from_afs_inode_type . i_type

afs_inode_to_vnode :: Afs_inode -> VfsInode
afs_inode_to_vnode i = VfsInode {
    v_ino = i_ino i
  , v_nlink = i_nlink i
  , v_size = i_size i
  , v_mtime = i_mtime i
  , v_ctime = i_ctime i
  , v_uid = i_uid i
  , v_gid = i_gid i
  , v_mode = i_mode i
  , v_flags = i_flags i
  }

afs_inode_from_vnode :: Vnode -> Afs_inode
afs_inode_from_vnode v = Afs_inode {
    i_type = if | v_mode v .&. s_IFREG /= 0 -> IReg [] 
                | v_mode v .&. s_IFDIR /= 0 -> IDir M.empty
                | otherwise -> ILnk []
  , i_ino = v_ino v
  , i_nlink = v_nlink v
  , i_size = v_size v
  , i_mtime = v_mtime v
  , i_ctime = v_ctime v
  , i_uid = v_uid v
  , i_gid = v_gid v
  , i_mode = v_mode v
  , i_flags = v_flags v
  }

error_if_readonly :: Afs_state -> Cogent_monad (D.R Afs_state (D.ErrCode, Afs_state))
error_if_readonly as = return $ if a_is_readonly as
                                  then D.Error (eRoFs, as)
                                  else D.Success as

nondet_error :: Set D.ErrCode -> (D.ErrCode -> a) -> Cogent_monad a
nondet_error errs f = C.select errs >>= (return . f)

afs_alloc_inum :: Afs_map -> Cogent_monad (D.R Ino ())
afs_alloc_inum as = do
  let avail_inums = S.map negate $ M.keysSet as
  opt_inum <- select $ S.singleton Nothing `union` (Just `image` avail_inums)
  return $ if opt_inum == Nothing then D.Error () else D.Success (fromJust opt_inum)

afs_get_current_time :: Afs_state -> Cogent_monad (Afs_state, TimeT)
afs_get_current_time afs = do
  time' <- return $ a_current_time afs
  time <- select (S.fromList [ i | i <- [time' ..] ])
  return (afs {a_current_time = time}, time')

afs_init_inode :: Afs_state -> Vnode -> Vnode -> D.VfsMode
               -> Cogent_monad (D.R (Afs_state, Vnode) (Afs_state, Vnode))
afs_init_inode adata vdir vnode mode = do
  (adata, time) <- afs_get_current_time adata
  uid <- return (v_uid vdir)
  gid <- return (v_gid vdir)
  vnode <- return (vnode {v_ctime = time, v_mtime = time, v_uid = uid, v_gid = gid, 
                          v_mode = mode, v_nlink = 1, v_size = 0})
  r <- afs_alloc_inum (updated_afs adata)
  return (case r of D.Error () -> D.Error (adata, vnode)
                    D.Success inum -> D.Success (adata, vnode {v_ino = inum}))

read_afs_inode :: Afs_state -> Ino -> Cogent_monad (D.R Afs_inode ErrCode)
read_afs_inode adata ino = return (D.Success $ fromJust $ ino `M.lookup` updated_afs adata) `alternative`
                           nondet_error (fromList [eIO, eNoMem, eInval, eBadF]) D.Error

afs_apply_updates_nondet :: Afs_state -> Cogent_monad Afs_state
afs_apply_updates_nondet afs = do
  let upds = a_medium_updates afs
  (to_apply, updates) <- fmap (\i -> splitAt i upds) (fromList [0 .. length upds - 1])
  return $ afs {a_medium_afs = fold P.id to_apply (a_medium_afs afs),
                a_medium_updates = updates}

afs_update :: Afs_state -> (Afs_map -> Afs_map) -> Cogent_monad (Afs_state, D.R () D.ErrCode)
afs_update afs upd = do
  afs <- afs_apply_updates_nondet (afs {a_medium_updates = a_medium_updates afs ++ [upd]})
  if null $ a_medium_updates afs
    then return (afs, D.Success ())
    else return (afs, D.Success ()) `alternative`
         nondet_error (fromList $ [eIO, eNoSpc, eNoMem]) (\e -> (afs {a_medium_updates = butlast (a_medium_updates afs)}, D.Error e))

afs_create :: Afs_state -> Vnode -> D.WordArray U8 -> D.VfsMode -> Vnode
           -> Cogent_monad ((Afs_state, Vnode, Vnode), D.R () D.ErrCode)
afs_create afs parentdir name mode vnode =
  if a_is_readonly afs
    then return ((afs, parentdir, vnode), D.Error eRoFs)
    else do
      r <- afs_init_inode afs parentdir vnode (mode .|. s_IFREG)
      case r of
        D.Error (afs, vnode) -> return ((afs, parentdir, vnode), D.Error eNFile)
        D.Success (afs, vnode) -> do
          r <- read_afs_inode afs (v_ino parentdir)
          case r of
            D.Error e -> return ((afs, parentdir, vnode), D.Error e)
            D.Success dir -> do
              r <- return (D.Success $ i_dir_update (\d -> M.adjust (\_ -> v_ino vnode) (alpha_wa name) d) dir) `alternative` return (D.Error eNameTooLong)
              case r of
                D.Error e -> return ((afs, parentdir, vnode), D.Error e)
                D.Success dir -> do
                  r <- select (D.Success `image` fromList [ sz | sz <- [v_size parentdir .. ] ]) `alternative`
                       return (D.Error eOverflow)
                  case r of
                    D.Error e -> return ((afs, parentdir, vnode), D.Error e)
                    D.Success newsz -> do
                      time <- return $ v_ctime vnode
                      dir <- return $ dir {i_ctime = time, i_mtime = time}
                      inode <- return $ afs_inode_from_vnode vnode
                      (afs, r) <- afs_update afs (\f -> M.adjust (flip const inode) (i_ino inode) $
                                                          M.adjust (flip const dir) (i_ino dir) f)
                      case r of
                        D.Error e -> return ((afs, parentdir, vnode), D.Error e)
                        D.Success () -> return ((afs, parentdir {v_ctime = time, v_mtime = time, v_size = newsz}, vnode), D.Success ())

afs_sync :: Afs_state -> Cogent_monad (Afs_state, D.R () D.ErrCode)
afs_sync afs = 
  if a_is_readonly afs
    then return (afs, D.Error eRoFs)
    else do
      n <- select $ fromList [0 .. length (a_medium_updates afs)]
      updates <- return $ a_medium_updates afs
      (to_apply, updates) <- return (take n updates, drop n updates)
      afs <- return $ a_medium_afs_update (fold (\upd med -> upd med) to_apply) afs
      afs <- return $ a_medium_updates_update (\_ -> updates) afs
      if null updates
        then return (afs, D.Success ())
        else do
          e <- select $ fromList [eIO, eNoMem, eNoSpc, eOverflow]
          return (afs {a_is_readonly = (e == eIO)}, D.Error e)

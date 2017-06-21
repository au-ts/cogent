{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{- LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Fsop where

import Fsop_Shallow_Desugar


hs_fsop_sync_fs :: FsopFsP -> RR FsopFsP () ErrCode
hs_fsop_sync_fs arg@(R28 ex fs_st) = 
  if is_ro $ (fsop_st :: R78 _ _ _ -> R87 Bool) fs_st
    then R100 arg (Error eRoFs)
    else let mount_st'  = (mount_st  :: FsState -> _) fs_st
             ostore_st' = (ostore_st :: FsState -> _) fs_st
             fsop_st'   = (fsop_st   :: FsState -> _) fs_st
             R100 (R100 ex ostore_st'') r = ostore_sync (R102 ex mount_st' ostore_st' ostoreWriteNone)
          in case r of
               Error err -> R100 (R28 ex (fs_st {ostore_st = ostore_st'', fsop_st = fsop_st' {is_ro = err == eIO}})) (Error err)
               Success _ -> R100 (R28 ex (fs_st {ostore_st = ostore_st'', fsop_st = fsop_st'})) (Success ())

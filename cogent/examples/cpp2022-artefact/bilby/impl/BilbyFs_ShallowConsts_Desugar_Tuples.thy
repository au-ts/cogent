(*
This file is generated by Cogent

*)

theory BilbyFs_ShallowConsts_Desugar_Tuples
imports "BilbyFs_Shallow_Desugar_Tuples"
begin

definition
  x_NOCMTIME :: "32 word"
where
  "x_NOCMTIME \<equiv> (0 :: 32 word)"

definition
  word64Max :: "64 word"
where
  "word64Max \<equiv> (18446744073709551615 :: 64 word)"

definition
  word32Max :: "32 word"
where
  "word32Max \<equiv> (4294967295 :: 32 word)"

definition
  vfs_ATTR_UID :: "32 word"
where
  "vfs_ATTR_UID \<equiv> checked_shift shiftl (1 :: 32 word) (1 :: 32 word)"

definition
  vfs_ATTR_TIMES_SET :: "32 word"
where
  "vfs_ATTR_TIMES_SET \<equiv> checked_shift shiftl (1 :: 32 word) (16 :: 32 word)"

definition
  vfs_ATTR_SIZE :: "32 word"
where
  "vfs_ATTR_SIZE \<equiv> checked_shift shiftl (1 :: 32 word) (3 :: 32 word)"

definition
  vfs_ATTR_OPEN :: "32 word"
where
  "vfs_ATTR_OPEN \<equiv> checked_shift shiftl (1 :: 32 word) (15 :: 32 word)"

definition
  vfs_ATTR_MTIME_SET :: "32 word"
where
  "vfs_ATTR_MTIME_SET \<equiv> checked_shift shiftl (1 :: 32 word) (8 :: 32 word)"

definition
  vfs_ATTR_MTIME :: "32 word"
where
  "vfs_ATTR_MTIME \<equiv> checked_shift shiftl (1 :: 32 word) (5 :: 32 word)"

definition
  vfs_ATTR_MODE :: "32 word"
where
  "vfs_ATTR_MODE \<equiv> checked_shift shiftl (1 :: 32 word) (0 :: 32 word)"

definition
  vfs_ATTR_KILL_SUID :: "32 word"
where
  "vfs_ATTR_KILL_SUID \<equiv> checked_shift shiftl (1 :: 32 word) (11 :: 32 word)"

definition
  vfs_ATTR_KILL_SGID :: "32 word"
where
  "vfs_ATTR_KILL_SGID \<equiv> checked_shift shiftl (1 :: 32 word) (12 :: 32 word)"

definition
  vfs_ATTR_KILL_PRIV :: "32 word"
where
  "vfs_ATTR_KILL_PRIV \<equiv> checked_shift shiftl (1 :: 32 word) (14 :: 32 word)"

definition
  vfs_ATTR_GID :: "32 word"
where
  "vfs_ATTR_GID \<equiv> checked_shift shiftl (1 :: 32 word) (2 :: 32 word)"

definition
  vfs_ATTR_FORCE :: "32 word"
where
  "vfs_ATTR_FORCE \<equiv> checked_shift shiftl (1 :: 32 word) (9 :: 32 word)"

definition
  vfs_ATTR_FILE :: "32 word"
where
  "vfs_ATTR_FILE \<equiv> checked_shift shiftl (1 :: 32 word) (13 :: 32 word)"

definition
  vfs_ATTR_CTIME :: "32 word"
where
  "vfs_ATTR_CTIME \<equiv> checked_shift shiftl (1 :: 32 word) (6 :: 32 word)"

definition
  vfs_ATTR_ATTR_FLAG :: "32 word"
where
  "vfs_ATTR_ATTR_FLAG \<equiv> checked_shift shiftl (1 :: 32 word) (10 :: 32 word)"

definition
  vfs_ATTR_ATIME_SET :: "32 word"
where
  "vfs_ATTR_ATIME_SET \<equiv> checked_shift shiftl (1 :: 32 word) (7 :: 32 word)"

definition
  vfs_ATTR_ATIME :: "32 word"
where
  "vfs_ATTR_ATIME \<equiv> checked_shift shiftl (1 :: 32 word) (4 :: 32 word)"

definition
  s_IXUSR :: "32 word"
where
  "s_IXUSR \<equiv> (64 :: 32 word)"

definition
  s_IXOTH :: "32 word"
where
  "s_IXOTH \<equiv> (1 :: 32 word)"

definition
  s_IXGRP :: "32 word"
where
  "s_IXGRP \<equiv> (8 :: 32 word)"

definition
  s_IXUGO :: "32 word"
where
  "s_IXUGO \<equiv> (OR) ((OR) (64 :: 32 word) (8 :: 32 word)) (1 :: 32 word)"

definition
  s_IWUSR :: "32 word"
where
  "s_IWUSR \<equiv> (128 :: 32 word)"

definition
  s_IWOTH :: "32 word"
where
  "s_IWOTH \<equiv> (2 :: 32 word)"

definition
  s_IWGRP :: "32 word"
where
  "s_IWGRP \<equiv> (16 :: 32 word)"

definition
  s_IWUGO :: "32 word"
where
  "s_IWUGO \<equiv> (OR) ((OR) (128 :: 32 word) (16 :: 32 word)) (2 :: 32 word)"

definition
  s_ISVTX :: "32 word"
where
  "s_ISVTX \<equiv> (512 :: 32 word)"

definition
  s_ISUID :: "32 word"
where
  "s_ISUID \<equiv> (2048 :: 32 word)"

definition
  s_ISGID :: "32 word"
where
  "s_ISGID \<equiv> (1024 :: 32 word)"

definition
  s_IRWXU :: "32 word"
where
  "s_IRWXU \<equiv> (448 :: 32 word)"

definition
  s_IRWXO :: "32 word"
where
  "s_IRWXO \<equiv> (7 :: 32 word)"

definition
  s_IRWXG :: "32 word"
where
  "s_IRWXG \<equiv> (56 :: 32 word)"

definition
  s_IRWXUGO :: "32 word"
where
  "s_IRWXUGO \<equiv> (OR) ((OR) (448 :: 32 word) (56 :: 32 word)) (7 :: 32 word)"

definition
  s_IRUSR :: "32 word"
where
  "s_IRUSR \<equiv> (256 :: 32 word)"

definition
  s_IROTH :: "32 word"
where
  "s_IROTH \<equiv> (4 :: 32 word)"

definition
  s_IRGRP :: "32 word"
where
  "s_IRGRP \<equiv> (32 :: 32 word)"

definition
  s_IRUGO :: "32 word"
where
  "s_IRUGO \<equiv> (OR) ((OR) (256 :: 32 word) (32 :: 32 word)) (4 :: 32 word)"

definition
  s_IMMUTABLE :: "32 word"
where
  "s_IMMUTABLE \<equiv> (8 :: 32 word)"

definition
  s_IFSOCK :: "32 word"
where
  "s_IFSOCK \<equiv> (49152 :: 32 word)"

definition
  s_IFREG :: "32 word"
where
  "s_IFREG \<equiv> (32768 :: 32 word)"

definition
  s_IFMT :: "32 word"
where
  "s_IFMT \<equiv> (61440 :: 32 word)"

definition
  s_IFLNK :: "32 word"
where
  "s_IFLNK \<equiv> (40960 :: 32 word)"

definition
  s_IFIFO :: "32 word"
where
  "s_IFIFO \<equiv> (4096 :: 32 word)"

definition
  s_IFDIR :: "32 word"
where
  "s_IFDIR \<equiv> (16384 :: 32 word)"

definition
  s_IFCHR :: "32 word"
where
  "s_IFCHR \<equiv> (8192 :: 32 word)"

definition
  s_IFBLK :: "32 word"
where
  "s_IFBLK \<equiv> (24576 :: 32 word)"

definition
  s_APPEND :: "32 word"
where
  "s_APPEND \<equiv> (4 :: 32 word)"

definition
  ostoreWriteNone :: "32 word"
where
  "ostoreWriteNone \<equiv> (0 :: 32 word)"

definition
  ostoreWriteNewEb :: "32 word"
where
  "ostoreWriteNewEb \<equiv> (4 :: 32 word)"

definition
  ostoreWriteGC :: "32 word"
where
  "ostoreWriteGC \<equiv> (1 :: 32 word)"

definition
  ostoreWriteForceSync :: "32 word"
where
  "ostoreWriteForceSync \<equiv> (16 :: 32 word)"

definition
  ostoreWriteDel :: "32 word"
where
  "ostoreWriteDel \<equiv> (2 :: 32 word)"

definition
  ostoreWriteAtomEb :: "32 word"
where
  "ostoreWriteAtomEb \<equiv> (8 :: 32 word)"

definition
  os_PAGE_CACHE_SIZE :: "64 word"
where
  "os_PAGE_CACHE_SIZE \<equiv> (4096 :: 64 word)"

definition
  os_PAGE_CACHE_SHIFT :: "64 word"
where
  "os_PAGE_CACHE_SHIFT \<equiv> (12 :: 64 word)"

definition
  os_PAGE_CACHE_MASK :: "64 word"
where
  "os_PAGE_CACHE_MASK \<equiv> NOT ((-) (4096 :: 64 word) (1 :: 64 word))"

definition
  os_MAX_LFS_FILESIZE :: "64 word"
where
  "os_MAX_LFS_FILESIZE \<equiv> (-) (checked_shift shiftl (4096 :: 64 word) ((-) (32 :: 64 word) (1 :: 64 word))) (1 :: 64 word)"

definition
  os_MAX_FILESIZE :: "64 word"
where
  "os_MAX_FILESIZE \<equiv> (-) (checked_shift shiftl (4096 :: 64 word) ((-) (32 :: 64 word) (1 :: 64 word))) (1 :: 64 word)"

definition
  nilObjId :: "64 word"
where
  "nilObjId \<equiv> (18446744073709551615 :: 64 word)"

definition
  cogent_LOG_LEVEL :: "32 word"
where
  "cogent_LOG_LEVEL \<equiv> (0 :: 32 word)"

definition
  bilbyFsXinfoShift :: "64 word"
where
  "bilbyFsXinfoShift \<equiv> (29 :: 64 word)"

definition
  bilbyFsXinfoMask :: "64 word"
where
  "bilbyFsXinfoMask \<equiv> (536870911 :: 64 word)"

definition
  bilbyFsSuperEbNum :: "32 word"
where
  "bilbyFsSuperEbNum \<equiv> (0 :: 32 word)"

definition
  bilbyFsSumEntryDelFlagMask :: "32 word"
where
  "bilbyFsSumEntryDelFlagMask \<equiv> (2147483648 :: 32 word)"

definition
  bilbyFsRootIno :: "32 word"
where
  "bilbyFsRootIno \<equiv> (24 :: 32 word)"

definition
  bilbyFsPadByte :: "8 word"
where
  "bilbyFsPadByte \<equiv> (66 :: 8 word)"

definition
  bilbyFsOidMaskInum :: "64 word"
where
  "bilbyFsOidMaskInum \<equiv> checked_shift shiftl (4294967295 :: 64 word) (32 :: 64 word)"

definition
  bilbyFsOidMaskAll :: "64 word"
where
  "bilbyFsOidMaskAll \<equiv> checked_shift shiftl (7 :: 64 word) (29 :: 64 word)"

definition
  bilbyFsObjTypeSuper :: "8 word"
where
  "bilbyFsObjTypeSuper \<equiv> (4 :: 8 word)"

definition
  bilbyFsObjTypeSum :: "8 word"
where
  "bilbyFsObjTypeSum \<equiv> (6 :: 8 word)"

definition
  bilbyFsOidMaskSum :: "64 word"
where
  "bilbyFsOidMaskSum \<equiv> checked_shift shiftl (6 :: 64 word) (29 :: 64 word)"

definition
  bilbyFsObjTypePad :: "8 word"
where
  "bilbyFsObjTypePad \<equiv> (5 :: 8 word)"

definition
  bilbyFsOidMaskPad :: "64 word"
where
  "bilbyFsOidMaskPad \<equiv> checked_shift shiftl (5 :: 64 word) (29 :: 64 word)"

definition
  bilbyFsObjTypeInode :: "8 word"
where
  "bilbyFsObjTypeInode \<equiv> (0 :: 8 word)"

definition
  bilbyFsOidMaskInode :: "64 word"
where
  "bilbyFsOidMaskInode \<equiv> checked_shift shiftl (0 :: 64 word) (29 :: 64 word)"

definition
  bilbyFsObjTypeDentarr :: "8 word"
where
  "bilbyFsObjTypeDentarr \<equiv> (2 :: 8 word)"

definition
  bilbyFsOidMaskDentarr :: "64 word"
where
  "bilbyFsOidMaskDentarr \<equiv> checked_shift shiftl (2 :: 64 word) (29 :: 64 word)"

definition
  bilbyFsObjTypeDel :: "8 word"
where
  "bilbyFsObjTypeDel \<equiv> (3 :: 8 word)"

definition
  bilbyFsOidMaskDel :: "64 word"
where
  "bilbyFsOidMaskDel \<equiv> checked_shift shiftl (3 :: 64 word) (29 :: 64 word)"

definition
  bilbyFsObjTypeData :: "8 word"
where
  "bilbyFsObjTypeData \<equiv> (1 :: 8 word)"

definition
  bilbyFsOidMaskData :: "64 word"
where
  "bilbyFsOidMaskData \<equiv> checked_shift shiftl (1 :: 64 word) (29 :: 64 word)"

definition
  bilbyFsObjSuperSize :: "32 word"
where
  "bilbyFsObjSuperSize \<equiv> (40 :: 32 word)"

definition
  bilbyFsObjSummaryOffsSize :: "32 word"
where
  "bilbyFsObjSummaryOffsSize \<equiv> (4 :: 32 word)"

definition
  bilbyFsObjSummaryHeaderSize :: "32 word"
where
  "bilbyFsObjSummaryHeaderSize \<equiv> (4 :: 32 word)"

definition
  bilbyFsObjSumEntrySize :: "32 word"
where
  "bilbyFsObjSumEntrySize \<equiv> (26 :: 32 word)"

definition
  bilbyFsObjInode :: "32 word"
where
  "bilbyFsObjInode \<equiv> (60 :: 32 word)"

definition
  bilbyFsObjHeaderSize :: "32 word"
where
  "bilbyFsObjHeaderSize \<equiv> (24 :: 32 word)"

definition
  bilbyFsObjDentryHeaderSize :: "32 word"
where
  "bilbyFsObjDentryHeaderSize \<equiv> (8 :: 32 word)"

definition
  bilbyFsObjDentarrHeaderSize :: "32 word"
where
  "bilbyFsObjDentarrHeaderSize \<equiv> (12 :: 32 word)"

definition
  bilbyFsObjDelSize :: "32 word"
where
  "bilbyFsObjDelSize \<equiv> (8 :: 32 word)"

definition
  bilbyFsObjDataHeaderSize :: "32 word"
where
  "bilbyFsObjDataHeaderSize \<equiv> (8 :: 32 word)"

definition
  bilbyFsMaxObjPerTrans :: "32 word"
where
  "bilbyFsMaxObjPerTrans \<equiv> (2048 :: 32 word)"

definition
  bilbyFsMaxNbDentarrEntries :: "32 word"
where
  "bilbyFsMaxNbDentarrEntries \<equiv> (16 :: 32 word)"

definition
  bilbyFsMaxNameLen :: "32 word"
where
  "bilbyFsMaxNameLen \<equiv> (255 :: 32 word)"

definition
  bilbyFsMaxInum :: "32 word"
where
  "bilbyFsMaxInum \<equiv> (4294967295 :: 32 word)"

definition
  bilbyFsMagic :: "32 word"
where
  "bilbyFsMagic \<equiv> (186104309 :: 32 word)"

definition
  bilbyFsItypeSock :: "8 word"
where
  "bilbyFsItypeSock \<equiv> (6 :: 8 word)"

definition
  bilbyFsItypeReg :: "8 word"
where
  "bilbyFsItypeReg \<equiv> (0 :: 8 word)"

definition
  bilbyFsItypeLnk :: "8 word"
where
  "bilbyFsItypeLnk \<equiv> (2 :: 8 word)"

definition
  bilbyFsItypeFifo :: "8 word"
where
  "bilbyFsItypeFifo \<equiv> (5 :: 8 word)"

definition
  bilbyFsItypeDir :: "8 word"
where
  "bilbyFsItypeDir \<equiv> (1 :: 8 word)"

definition
  bilbyFsItypeChr :: "8 word"
where
  "bilbyFsItypeChr \<equiv> (4 :: 8 word)"

definition
  bilbyFsItypeBlk :: "8 word"
where
  "bilbyFsItypeBlk \<equiv> (3 :: 8 word)"

definition
  bilbyFsITypeSock :: "8 word"
where
  "bilbyFsITypeSock \<equiv> (6 :: 8 word)"

definition
  bilbyFsITypeReg :: "8 word"
where
  "bilbyFsITypeReg \<equiv> (0 :: 8 word)"

definition
  bilbyFsITypeLnk :: "8 word"
where
  "bilbyFsITypeLnk \<equiv> (2 :: 8 word)"

definition
  bilbyFsITypeFifo :: "8 word"
where
  "bilbyFsITypeFifo \<equiv> (5 :: 8 word)"

definition
  bilbyFsITypeDir :: "8 word"
where
  "bilbyFsITypeDir \<equiv> (1 :: 8 word)"

definition
  bilbyFsITypeCnt :: "8 word"
where
  "bilbyFsITypeCnt \<equiv> (7 :: 8 word)"

definition
  bilbyFsITypeChr :: "8 word"
where
  "bilbyFsITypeChr \<equiv> (4 :: 8 word)"

definition
  bilbyFsITypeBlk :: "8 word"
where
  "bilbyFsITypeBlk \<equiv> (3 :: 8 word)"

definition
  bilbyFsFirstLogEbNum :: "32 word"
where
  "bilbyFsFirstLogEbNum \<equiv> (2 :: 32 word)"

definition
  bilbyFsDefaultNbReservedGc :: "32 word"
where
  "bilbyFsDefaultNbReservedGc \<equiv> (3 :: 32 word)"

definition
  bilbyFsDefaultNbReservedDel :: "32 word"
where
  "bilbyFsDefaultNbReservedDel \<equiv> (3 :: 32 word)"

definition
  bilbyFsBlockSize :: "32 word"
where
  "bilbyFsBlockSize \<equiv> (4096 :: 32 word)"

definition
  bilbyFsBlockShift :: "32 word"
where
  "bilbyFsBlockShift \<equiv> (12 :: 32 word)"

definition
  vfs_type_blk :: "32 word"
where
  "vfs_type_blk \<equiv> (24576 :: 32 word)"

definition
  vfs_type_chr :: "32 word"
where
  "vfs_type_chr \<equiv> (8192 :: 32 word)"

definition
  vfs_type_dir :: "32 word"
where
  "vfs_type_dir \<equiv> (16384 :: 32 word)"

definition
  vfs_type_fifo :: "32 word"
where
  "vfs_type_fifo \<equiv> (4096 :: 32 word)"

definition
  vfs_type_link :: "32 word"
where
  "vfs_type_link \<equiv> (40960 :: 32 word)"

definition
  vfs_type_reg :: "32 word"
where
  "vfs_type_reg \<equiv> (32768 :: 32 word)"

definition
  vfs_type_sock :: "32 word"
where
  "vfs_type_sock \<equiv> (49152 :: 32 word)"

definition
  vfs_MS_RDONLY :: "32 word"
where
  "vfs_MS_RDONLY \<equiv> (1 :: 32 word)"

definition
  ubiExclusive :: "32 word"
where
  "ubiExclusive \<equiv> (3 :: 32 word)"

definition
  ubiReadOnly :: "32 word"
where
  "ubiReadOnly \<equiv> (1 :: 32 word)"

definition
  ubiReadWrite :: "32 word"
where
  "ubiReadWrite \<equiv> (2 :: 32 word)"

definition
  bilbyFsTransCommit :: "8 word"
where
  "bilbyFsTransCommit \<equiv> (2 :: 8 word)"

definition
  bilbyFsTransIn :: "8 word"
where
  "bilbyFsTransIn \<equiv> (1 :: 8 word)"

definition
  bilbyFsPadObjId :: "64 word"
where
  "bilbyFsPadObjId \<equiv> (18446744073709551615 :: 64 word)"

definition
  mkObjAddr :: "(32 word, 32 word, 32 word, 64 word) ObjAddr"
where
  "mkObjAddr \<equiv> ObjAddr.make (0 :: 32 word) (0 :: 32 word) (0 :: 32 word) (0 :: 64 word)"

definition
  eAcces :: "32 word"
where
  "eAcces \<equiv> (13 :: 32 word)"

definition
  eAgain :: "32 word"
where
  "eAgain \<equiv> (11 :: 32 word)"

definition
  eBadF :: "32 word"
where
  "eBadF \<equiv> (9 :: 32 word)"

definition
  eBusy :: "32 word"
where
  "eBusy \<equiv> (16 :: 32 word)"

definition
  eChild :: "32 word"
where
  "eChild \<equiv> (10 :: 32 word)"

definition
  eCrap :: "32 word"
where
  "eCrap \<equiv> (66 :: 32 word)"

definition
  eDom :: "32 word"
where
  "eDom \<equiv> (33 :: 32 word)"

definition
  eExist :: "32 word"
where
  "eExist \<equiv> (17 :: 32 word)"

definition
  eFBig :: "32 word"
where
  "eFBig \<equiv> (27 :: 32 word)"

definition
  eFault :: "32 word"
where
  "eFault \<equiv> (14 :: 32 word)"

definition
  eIO :: "32 word"
where
  "eIO \<equiv> (5 :: 32 word)"

definition
  eIntr :: "32 word"
where
  "eIntr \<equiv> (4 :: 32 word)"

definition
  eInval :: "32 word"
where
  "eInval \<equiv> (22 :: 32 word)"

definition
  eIsDir :: "32 word"
where
  "eIsDir \<equiv> (21 :: 32 word)"

definition
  eMFile :: "32 word"
where
  "eMFile \<equiv> (24 :: 32 word)"

definition
  eMLink :: "32 word"
where
  "eMLink \<equiv> (31 :: 32 word)"

definition
  eNFile :: "32 word"
where
  "eNFile \<equiv> (23 :: 32 word)"

definition
  eNXIO :: "32 word"
where
  "eNXIO \<equiv> (6 :: 32 word)"

definition
  eNameTooLong :: "32 word"
where
  "eNameTooLong \<equiv> (36 :: 32 word)"

definition
  eNoData :: "32 word"
where
  "eNoData \<equiv> (42 :: 32 word)"

definition
  eNoDev :: "32 word"
where
  "eNoDev \<equiv> (19 :: 32 word)"

definition
  eNoEnt :: "32 word"
where
  "eNoEnt \<equiv> (2 :: 32 word)"

definition
  eNoExec :: "32 word"
where
  "eNoExec \<equiv> (8 :: 32 word)"

definition
  eNoMem :: "32 word"
where
  "eNoMem \<equiv> (12 :: 32 word)"

definition
  eNoSpc :: "32 word"
where
  "eNoSpc \<equiv> (28 :: 32 word)"

definition
  eNoTty :: "32 word"
where
  "eNoTty \<equiv> (25 :: 32 word)"

definition
  eNotBlk :: "32 word"
where
  "eNotBlk \<equiv> (15 :: 32 word)"

definition
  eNotDir :: "32 word"
where
  "eNotDir \<equiv> (20 :: 32 word)"

definition
  eNotEmpty :: "32 word"
where
  "eNotEmpty \<equiv> (39 :: 32 word)"

definition
  eOverflow :: "32 word"
where
  "eOverflow \<equiv> (75 :: 32 word)"

definition
  ePerm :: "32 word"
where
  "ePerm \<equiv> (1 :: 32 word)"

definition
  ePipe :: "32 word"
where
  "ePipe \<equiv> (32 :: 32 word)"

definition
  eRange :: "32 word"
where
  "eRange \<equiv> (34 :: 32 word)"

definition
  eRecover :: "32 word"
where
  "eRecover \<equiv> (88 :: 32 word)"

definition
  eRoFs :: "32 word"
where
  "eRoFs \<equiv> (30 :: 32 word)"

definition
  eSPipe :: "32 word"
where
  "eSPipe \<equiv> (29 :: 32 word)"

definition
  eSrch :: "32 word"
where
  "eSrch \<equiv> (3 :: 32 word)"

definition
  eTooBig :: "32 word"
where
  "eTooBig \<equiv> (7 :: 32 word)"

definition
  eTxtBsy :: "32 word"
where
  "eTxtBsy \<equiv> (26 :: 32 word)"

definition
  eXDev :: "32 word"
where
  "eXDev \<equiv> (18 :: 32 word)"

end

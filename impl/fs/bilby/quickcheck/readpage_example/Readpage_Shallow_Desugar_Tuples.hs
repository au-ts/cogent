{-
This build info header is now disabled by --fno-gen-header.
--------------------------------------------------------------------------------
We strongly discourage users from generating individual files for Isabelle
proofs, as it will end up with an inconsistent collection of output files (i.e.
Isabelle input files).
-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PartialTypeSignatures #-}
module Readpage_Shallow_Desugar_Tuples where
import Data.Bits ((.&.), (.|.), complement, xor, shiftL, shiftR)
import qualified Data.Tuple.Select as Tup
import qualified Data.Tuple.Update as Tup
import Data.Word (Word8, Word16, Word32, Word64)
import Prelude (not, div, mod, fromIntegral, undefined, (+), (-), (*), (&&), (||), (>), (>=), (<), (<=), (==), (/=), Char, String, Int, Show, Bool(..), return, ($), zip, repeat, Ord, Eq, Maybe(..), fromIntegral, (.), (++), show, otherwise)
import System.IO.Unsafe
import qualified Test.QuickCheck as Q
import qualified Data.Array as A
import qualified Fsop as Ax
import qualified Data.Map as M
import Data.List (minimum, genericDrop, genericTake, length, drop)

-- import Debug.Trace

data R0 t1 t2 = R0{ex :: t1, obj :: t2}
                  deriving Show

data R1 t1 = R1{dirctx :: t1}
               deriving Show

data V2 t1 t2 t3 = V2_Existing t1
                 | V2_New t2
                 | V2_None t3
                     deriving Show

data R3 t1 t2 = R3{ex :: t1, inode :: t2}
                  deriving Show

data R4 t1 t2 = R4{arr :: t1, acc :: t2}
                  deriving Show

data R5 t1 t2 = R5{arr :: t1, rbrk :: t2}
                  deriving Show

data R6 t1 t2 t3 t4 = R6{ex :: t1, fs_st :: t2, vnode :: t3, addr :: t4}
                        deriving Show

data R7 t1 t2 t3 t4 t5 = R7{ex :: t1, fs_st :: t2, vnode :: t3, block :: t4, addr :: t5}
                           deriving Show

data R8 t1 t2 = R8{data_ :: t1, bound :: t2}
  deriving (Ord, Eq, Show)

data R9 t1 t2 t3 t4 t5 = R9{dirs :: t1, src_inode :: t2, src_name :: t3, dest_inode :: t4, dest_name :: t5}
                           deriving Show

data R10 t1 t2 t3 t4 = R10{dirctx :: t1, name :: t2, ino :: t3, ftype :: t4}
                         deriving Show

data R11 t1 t2 = R11{name :: t1, inode :: t2}
                   deriving Show

data R12 t1 t2 t3 t4 t5 = R12{arr :: t1, idx :: t2, f :: t3, acc :: t4, obsv :: t5}
                            deriving Show

data R13 t1 t2 = R13{elem :: t1, acc :: t2}
                   deriving Show

data R14 t1 t2 t3 t4 t5 t6 = R14{arr :: t1, frm :: t2, to :: t3, f :: t4, acc :: t5, obsv :: t6}
                               deriving Show

data R15 t1 t2 t3 = R15{elem :: t1, acc :: t2, obsv :: t3}
                      deriving Show

data R16 t1 t2 = R16{elem :: t1, rbrk :: t2}
                   deriving Show

data V17 t1 t2 = V17_Found t1
               | V17_NotFound t2
                   deriving Show

data V18 t1 t2 = V18_Dest t1
               | V18_SrcDest t2
                   deriving Show

data R19 t1 t2 = R19{src_dir :: t1, dest_dir :: t2}
                   deriving Show

data R20 t1 t2 = R20{vfs :: t1, fs :: t2}
                   deriving Show

data R21 t1 = R21{a :: t1}
                deriving Show

data R22 t1 t2 t3 = R22{fsop_st :: t1, mount_st :: t2, ostore_st :: t3}
                      deriving Show

data R23 t1 t2 t3 t4 t5 t6 = R23{frm :: t1, to :: t2, stepf :: t3, f :: t4, acc :: t5, obsv :: t6}
                               deriving Show

data R24 t1 t2 t3 t4 t5 t6 = R24{frm :: t1, to :: t2, step :: t3, f :: t4, acc :: t5, obsv :: t6}
                               deriving Show

data V25 t1 t2 = V25_Break t1
               | V25_Iterate t2
                   deriving Show

data R26 t1 t2 = R26{os :: t1, pos :: t2}
                   deriving Show

data R27 t1 t2 = R27{tv_sec :: t1, tv_nsec :: t2}
                   deriving Show

data R28 t1 t2 t3 t4 t5 t6 t7 t8 = R28{magic :: t1, crc :: t2, sqnum :: t3, offs :: t4, len :: t5, trans :: t6, otype :: t7, ounion :: t8}
                                     deriving Show

data V29 t1 t2 t3 t4 t5 t6 t7 = V29_TObjData t1
                              | V29_TObjDel t2
                              | V29_TObjDentarr t3
                              | V29_TObjInode t4
                              | V29_TObjPad t5
                              | V29_TObjSummary t6
                              | V29_TObjSuper t7
                                  deriving Show

data R30 t1 t2 = R30{id :: t1, odata :: t2}
                   deriving Show

data R31 t1 t2 = R31{oelem :: t1, acc :: t2}
                   deriving Show

data R32 t1 t2 t3 = R32{oelem :: t1, acc :: t2, obsv :: t3}
                      deriving Show

data V33 t1 t2 = V33_None t1
               | V33_Some t2
                   deriving Show

data V34 t1 t2 = V34_Error t1
               | V34_Success t2
                   deriving Show

data R35 t1 t2 t3 t4 t5 = R35{frm :: t1, to :: t2, step :: t3, f :: t4, acc :: t5}
                            deriving Show

data R36 t1 t2 t3 = R36{acc :: t1, obsv :: t2, idx :: t3}
                      deriving Show

data R37 t1 t2 = R37{p1 :: t1, p2 :: t2}
                   deriving Show

data R38 t1 t2 t3 t4 t5 t6 t7 t8 = R38{fs_type :: t1, best_blocksize :: t2, blocks_total :: t3, blocks_free :: t4, blocks_available :: t5, files_total :: t6, files_free :: t7, max_namelen :: t8}
                                     deriving Show

data R39 t1 t2 t3 t4 t5 t6 = R39{s_magic :: t1, s_flags :: t2, s_max_links :: t3, s_maxbytes :: t4, s_blocksize :: t5, s_blocksize_bits :: t6}
                               deriving Show

data R40 t1 t2 t3 t4 = R40{p1 :: t1, p2 :: t2, p3 :: t3, p4 :: t4}
                         deriving Show

data R41 t1 t2 t3 = R41{arr :: t1, idx :: t2, val :: t3}
                      deriving Show

data R42 t1 t2 t3 = R42{p1 :: t1, p2 :: t2, p3 :: t3}
                      deriving Show

data R43 t1 t2 t3 t4 t5 = R43{p1 :: t1, p2 :: t2, p3 :: t3, p4 :: t4, p5 :: t5}
                            deriving Show

x_NOCMTIME :: Word32
x_NOCMTIME = (0 :: Word32)

word64Max :: Word64
word64Max = (18446744073709551615 :: Word64)

word32Max :: Word32
word32Max = (4294967295 :: Word32)

vfs_ATTR_UID :: Word32
vfs_ATTR_UID = ((1 :: Word32) `shiftL` fromIntegral (1 :: Word32))

vfs_ATTR_TIMES_SET :: Word32
vfs_ATTR_TIMES_SET = ((1 :: Word32) `shiftL` fromIntegral (16 :: Word32))

vfs_ATTR_SIZE :: Word32
vfs_ATTR_SIZE = ((1 :: Word32) `shiftL` fromIntegral (3 :: Word32))

vfs_ATTR_OPEN :: Word32
vfs_ATTR_OPEN = ((1 :: Word32) `shiftL` fromIntegral (15 :: Word32))

vfs_ATTR_MTIME_SET :: Word32
vfs_ATTR_MTIME_SET = ((1 :: Word32) `shiftL` fromIntegral (8 :: Word32))

vfs_ATTR_MTIME :: Word32
vfs_ATTR_MTIME = ((1 :: Word32) `shiftL` fromIntegral (5 :: Word32))

vfs_ATTR_MODE :: Word32
vfs_ATTR_MODE = ((1 :: Word32) `shiftL` fromIntegral (0 :: Word32))

vfs_ATTR_KILL_SUID :: Word32
vfs_ATTR_KILL_SUID = ((1 :: Word32) `shiftL` fromIntegral (11 :: Word32))

vfs_ATTR_KILL_SGID :: Word32
vfs_ATTR_KILL_SGID = ((1 :: Word32) `shiftL` fromIntegral (12 :: Word32))

vfs_ATTR_KILL_PRIV :: Word32
vfs_ATTR_KILL_PRIV = ((1 :: Word32) `shiftL` fromIntegral (14 :: Word32))

vfs_ATTR_GID :: Word32
vfs_ATTR_GID = ((1 :: Word32) `shiftL` fromIntegral (2 :: Word32))

vfs_ATTR_FORCE :: Word32
vfs_ATTR_FORCE = ((1 :: Word32) `shiftL` fromIntegral (9 :: Word32))

vfs_ATTR_FILE :: Word32
vfs_ATTR_FILE = ((1 :: Word32) `shiftL` fromIntegral (13 :: Word32))

vfs_ATTR_CTIME :: Word32
vfs_ATTR_CTIME = ((1 :: Word32) `shiftL` fromIntegral (6 :: Word32))

vfs_ATTR_ATTR_FLAG :: Word32
vfs_ATTR_ATTR_FLAG = ((1 :: Word32) `shiftL` fromIntegral (10 :: Word32))

vfs_ATTR_ATIME_SET :: Word32
vfs_ATTR_ATIME_SET = ((1 :: Word32) `shiftL` fromIntegral (7 :: Word32))

vfs_ATTR_ATIME :: Word32
vfs_ATTR_ATIME = ((1 :: Word32) `shiftL` fromIntegral (4 :: Word32))

s_IXUSR :: Word32
s_IXUSR = (64 :: Word32)

s_IXOTH :: Word32
s_IXOTH = (1 :: Word32)

s_IXGRP :: Word32
s_IXGRP = (8 :: Word32)

s_IXUGO :: Word32
s_IXUGO = (((64 :: Word32) .|. (8 :: Word32)) .|. (1 :: Word32))

s_IWUSR :: Word32
s_IWUSR = (128 :: Word32)

s_IWOTH :: Word32
s_IWOTH = (2 :: Word32)

s_IWGRP :: Word32
s_IWGRP = (16 :: Word32)

s_IWUGO :: Word32
s_IWUGO = (((128 :: Word32) .|. (16 :: Word32)) .|. (2 :: Word32))

s_ISVTX :: Word32
s_ISVTX = (512 :: Word32)

s_ISUID :: Word32
s_ISUID = (2048 :: Word32)

s_ISGID :: Word32
s_ISGID = (1024 :: Word32)

s_IRWXU :: Word32
s_IRWXU = (448 :: Word32)

s_IRWXO :: Word32
s_IRWXO = (7 :: Word32)

s_IRWXG :: Word32
s_IRWXG = (56 :: Word32)

s_IRWXUGO :: Word32
s_IRWXUGO = (((448 :: Word32) .|. (56 :: Word32)) .|. (7 :: Word32))

s_IRUSR :: Word32
s_IRUSR = (256 :: Word32)

s_IROTH :: Word32
s_IROTH = (4 :: Word32)

s_IRGRP :: Word32
s_IRGRP = (32 :: Word32)

s_IRUGO :: Word32
s_IRUGO = (((256 :: Word32) .|. (32 :: Word32)) .|. (4 :: Word32))

s_IMMUTABLE :: Word32
s_IMMUTABLE = (8 :: Word32)

s_IFSOCK :: Word32
s_IFSOCK = (49152 :: Word32)

s_IFREG :: Word32
s_IFREG = (32768 :: Word32)

s_IFMT :: Word32
s_IFMT = (61440 :: Word32)

s_IFLNK :: Word32
s_IFLNK = (40960 :: Word32)

s_IFIFO :: Word32
s_IFIFO = (4096 :: Word32)

s_IFDIR :: Word32
s_IFDIR = (16384 :: Word32)

s_IFCHR :: Word32
s_IFCHR = (8192 :: Word32)

s_IFBLK :: Word32
s_IFBLK = (24576 :: Word32)

s_APPEND :: Word32
s_APPEND = (4 :: Word32)

os_PAGE_CACHE_SIZE :: Word64
os_PAGE_CACHE_SIZE = (4096 :: Word64)

os_PAGE_CACHE_SHIFT :: Word64
os_PAGE_CACHE_SHIFT = (12 :: Word64)

os_PAGE_CACHE_MASK :: Word64
os_PAGE_CACHE_MASK = complement ((4096 :: Word64) - (1 :: Word64))

os_MAX_LFS_FILESIZE :: Word64
os_MAX_LFS_FILESIZE = (((4096 :: Word64) `shiftL` fromIntegral ((32 :: Word64) - (1 :: Word64))) - (1 :: Word64))

os_MAX_FILESIZE :: Word64
os_MAX_FILESIZE = (((4096 :: Word64) `shiftL` fromIntegral ((32 :: Word64) - (1 :: Word64))) - (1 :: Word64))

bilbyFsXinfoShift :: Word64
bilbyFsXinfoShift = (29 :: Word64)

bilbyFsObjTypeInode :: Word8
bilbyFsObjTypeInode = (0 :: Word8)

bilbyFsOidMaskInode :: Word64
bilbyFsOidMaskInode = ((fromIntegral (0 :: Word8) :: Word64) `shiftL` fromIntegral (29 :: Word64))

bilbyFsObjTypeData :: Word8
bilbyFsObjTypeData = (1 :: Word8)

bilbyFsOidMaskData :: Word64
bilbyFsOidMaskData = ((fromIntegral (1 :: Word8) :: Word64) `shiftL` fromIntegral (29 :: Word64))

bilbyFsBlockSize :: Word32
bilbyFsBlockSize = (4096 :: Word32)

bilbyFsBlockShift :: Word32
bilbyFsBlockShift = (12 :: Word32)

vfs_type_blk :: Word32
vfs_type_blk = (24576 :: Word32)

vfs_type_chr :: Word32
vfs_type_chr = (8192 :: Word32)

vfs_type_dir :: Word32
vfs_type_dir = (16384 :: Word32)

vfs_type_fifo :: Word32
vfs_type_fifo = (4096 :: Word32)

vfs_type_link :: Word32
vfs_type_link = (40960 :: Word32)

vfs_type_reg :: Word32
vfs_type_reg = (32768 :: Word32)

vfs_type_sock :: Word32
vfs_type_sock = (49152 :: Word32)

vfs_MS_RDONLY :: Word32
vfs_MS_RDONLY = (1 :: Word32)

eAcces :: Word32
eAcces = (13 :: Word32)

eAgain :: Word32
eAgain = (11 :: Word32)

eBadF :: Word32
eBadF = (9 :: Word32)

eBusy :: Word32
eBusy = (16 :: Word32)

eChild :: Word32
eChild = (10 :: Word32)

eCrap :: Word32
eCrap = (66 :: Word32)

eDom :: Word32
eDom = (33 :: Word32)

eExist :: Word32
eExist = (17 :: Word32)

eFBig :: Word32
eFBig = (27 :: Word32)

eFault :: Word32
eFault = (14 :: Word32)

eIO :: Word32
eIO = (5 :: Word32)

eIntr :: Word32
eIntr = (4 :: Word32)

eInval :: Word32
eInval = (22 :: Word32)

eIsDir :: Word32
eIsDir = (21 :: Word32)

eMFile :: Word32
eMFile = (24 :: Word32)

eMLink :: Word32
eMLink = (31 :: Word32)

eNFile :: Word32
eNFile = (23 :: Word32)

eNXIO :: Word32
eNXIO = (6 :: Word32)

eNameTooLong :: Word32
eNameTooLong = (36 :: Word32)

eNoData :: Word32
eNoData = (42 :: Word32)

eNoDev :: Word32
eNoDev = (19 :: Word32)

eNoEnt :: Word32
eNoEnt = (2 :: Word32)

eNoExec :: Word32
eNoExec = (8 :: Word32)

eNoMem :: Word32
eNoMem = (12 :: Word32)

eNoSpc :: Word32
eNoSpc = (28 :: Word32)

eNoTty :: Word32
eNoTty = (25 :: Word32)

eNotBlk :: Word32
eNotBlk = (15 :: Word32)

eNotDir :: Word32
eNotDir = (20 :: Word32)

eNotEmpty :: Word32
eNotEmpty = (39 :: Word32)

eOverflow :: Word32
eOverflow = (75 :: Word32)

ePerm :: Word32
ePerm = (1 :: Word32)

ePipe :: Word32
ePipe = (32 :: Word32)

eRange :: Word32
eRange = (34 :: Word32)

eRecover :: Word32
eRecover = (88 :: Word32)

eRoFs :: Word32
eRoFs = (30 :: Word32)

eSPipe :: Word32
eSPipe = (29 :: Word32)

eSrch :: Word32
eSrch = (3 :: Word32)

eTooBig :: Word32
eTooBig = (7 :: Word32)

eTxtBsy :: Word32
eTxtBsy = (26 :: Word32)

eXDev :: Word32
eXDev = (18 :: Word32)

type WordArray a = Ax.WordArray a

data View a

data VfsStat

data VfsMemoryMap

data VfsInodeAbstract = VfsInodeAbstract VfsIno VfsSize 
                      deriving Show

data VfsIattr

data VfsDevice

type SysState = ()

data SpinLock

type OstoreState = M.Map ObjId Obj

type ObjSuper = ()

type ObjSummary = ()

type ObjInode = ()

type ObjDentarr = ()

type ObjDel = ()

data OSDirContext

type MountState = ()

data LE64

data LE32

data LE16

type FsopState = ()

data BE64

data BE32

data BE16

type WordArrayIndex = Word32

type WordArrayCopyP a = (WordArray a, WordArray a, Word32, Word32, Word32)

type WordArrayFindSubP a = (WordArray a, WordArray a, Word32)

type WordArrayPutP a = R41 (WordArray a) Word32 a

type WordArraySetP a = (WordArray a, Word32, Word32, a)

type WordArrayView a = View (WordArray a)

type VfsType = Word32

type VfsSize = Word64

type VfsPosition = Word64

type VfsMountInfoFlag = Word32

type VfsMountInfo = R39 Word64 Word32 Word32 Word64 Word32 Word32

type VfsMode = Word32

type VfsIno = Word32

type VfsFlags = Word32

type VfsExtendedInfo = R38 Word64 Word64 Word64 Word64 Word64 Word64 Word64 Word64

type VfsDeviceMinor = Word32

type VfsDeviceMajor = Word32

type WordArrayCloneP a b = (SysState, WordArray a)

type WordArraySliceP a = (SysState, WordArray a, Word32, Word32)

type Seq64_bodyParam acc obsv rbrk = R36 acc obsv Word64

type Seq32_stepParam = Word32 -> Word32

type Seq32_simple_bodyParam acc = acc

type Seq32_simple_body acc = acc -> acc

type Seq32_bodyParam acc obsv rbrk = R36 acc obsv Word32

type Seq32SimpleParam acc = R35 Word32 Word32 Word32 (acc -> acc) acc

type Result a e = V34 e a

type ResultWith c a e = (c, V34 e a)

type RR c a e = (c, V34 e a)

type R a e = V34 e a

type Option a = V33 () a

type OptElemAO a acc obsv = R32 (V33 () a) acc obsv

type OptElemA a acc = R31 (V33 () a) acc

type ObjType = Word8

type ObjTrans = Word8

type ObjIdInode = Word64

type ObjIdDentarr = Word64

type ObjIdData = Word64

type ObjId = Word64

type ObjData = R30 Word64 (WordArray Word8)

type ObjUnion = V29 (R30 Word64 (WordArray Word8)) ObjDel ObjDentarr ObjInode () ObjSummary ObjSuper

type Obj = R28 Word32 Word32 Word64 Word32 Word32 Word8 Word8 (V29 (R30 Word64 (WordArray Word8)) ObjDel ObjDentarr ObjInode () ObjSummary ObjSuper)

type OSTimeSpec = R27 Word32 Word32

type OSPageOffset = Word64

type VfsDirContext = R26 OSDirContext Word64

type LoopResult a b = V25 b a

type LRR acc brk = (acc, V25 brk ())

type Seq32_body acc obsv rbrk = R36 acc obsv Word32 -> (acc, V25 rbrk ())

type Seq32Param acc obsv rbrk = R24 Word32 Word32 Word32 (R36 acc obsv Word32 -> (acc, V25 rbrk ())) acc obsv

type Seq32StepFParam acc obsv rbrk = R23 Word32 Word32 (Word32 -> Word32) (R36 acc obsv Word32 -> (acc, V25 rbrk ())) acc obsv

type Seq64_body acc obsv rbrk = R36 acc obsv Word64 -> (acc, V25 rbrk ())

type Seq64Param acc obsv rbrk = R24 Word64 Word64 Word64 (R36 acc obsv Word64 -> (acc, V25 rbrk ())) acc obsv

type WordArrayMapRE a acc rbrk = ((WordArray a, acc), V25 rbrk ())

type FsState = R22 FsopState MountState OstoreState

type FsInode = R21 Word32

type VfsInode = R20 VfsInodeAbstract (R21 Word32)

type VfsRenameDirsDiff = R19 (R20 VfsInodeAbstract (R21 Word32)) (R20 VfsInodeAbstract (R21 Word32))

type VfsRenameDirs = V18 (R20 VfsInodeAbstract (R21 Word32)) (R19 (R20 VfsInodeAbstract (R21 Word32)) (R20 VfsInodeAbstract (R21 Word32)))

type FreeF a = (SysState, a) -> SysState

type FreeAccF a acc obsv = (SysState, a, acc, obsv) -> (SysState, acc)

type FindResult = V17 Word32 ()

type ErrCode = Word32

type ElemB a rbrk = R16 a rbrk

type ElemAO a acc obsv = R15 a acc obsv

type WordArrayFoldF a acc obsv rbrk = R15 a acc obsv -> V25 rbrk acc

type WordArrayFoldP a acc obsv rbrk = R14 (WordArray a) Word32 Word32 (R15 a acc obsv -> V25 rbrk acc) acc obsv

type WordArrayFoldNoBreakF a acc obsv = R15 a acc obsv -> acc

type WordArrayFoldNoBreakP a acc obsv = R14 (WordArray a) Word32 Word32 (R15 a acc obsv -> acc) acc obsv

type WordArrayMapF a acc obsv rbrk = R15 a acc obsv -> ((a, acc), V25 rbrk ())

type WordArrayMapP a acc obsv rbrk = R14 (WordArray a) Word32 Word32 (R15 a acc obsv -> ((a, acc), V25 rbrk ())) acc obsv

type WordArrayMapNoBreakF a acc obsv = R15 a acc obsv -> (a, acc)

type WordArrayMapNoBreakP a acc obsv = R14 (WordArray a) Word32 Word32 (R15 a acc obsv -> (a, acc)) acc obsv

type ElemA a acc = R13 a acc

type WordArrayModifyF a acc obsv = R15 a acc obsv -> R13 a acc

type WordArrayModifyP a acc obsv = R12 (WordArray a) Word32 (R15 a acc obsv -> R13 a acc) acc obsv

type CString = WordArray Word8

type VfsDentry = R11 (WordArray Word8) (V33 () (R20 VfsInodeAbstract (R21 Word32)))

type VfsDentryH = R11 (WordArray Word8) (R20 VfsInodeAbstract (R21 Word32))

type VfsDirEmitP = R10 (R26 OSDirContext Word64) (WordArray Word8) Word32 Word32

type VfsRenameContext =
     R9 (V18 (R20 VfsInodeAbstract (R21 Word32)) (R19 (R20 VfsInodeAbstract (R21 Word32)) (R20 VfsInodeAbstract (R21 Word32)))) (R20 VfsInodeAbstract (R21 Word32)) (WordArray Word8)
       (V33 () (R20 VfsInodeAbstract (R21 Word32)))
       (WordArray Word8)

type BufOffs = Word32

type Buffer = R8 (WordArray Word8) Word32

type FsopReadPageP = R7 SysState (R22 FsopState MountState OstoreState) (R20 VfsInodeAbstract (R21 Word32)) Word64 (R8 (WordArray Word8) Word32)

type FsopReadPageRR = R6 SysState (R22 FsopState MountState OstoreState) (R20 VfsInodeAbstract (R21 Word32)) (R8 (WordArray Word8) Word32)

type ArrB a rbrk = R5 a rbrk

type ArrA a acc = R4 a acc

type U64_to_u32_ArgT = Word64

type U64_to_u32_RetT = Word32

u64_to_u32 :: U64_to_u32_ArgT -> U64_to_u32_RetT
u64_to_u32 = fromIntegral

type U64_to_u16_ArgT = Word64

type U64_to_u16_RetT = Word16

u64_to_u16 :: U64_to_u16_ArgT -> U64_to_u16_RetT
u64_to_u16 = undefined

type U32_to_u8_ArgT = Word32

type U32_to_u8_RetT = Word8

u32_to_u8 :: U32_to_u8_ArgT -> U32_to_u8_RetT
u32_to_u8 = undefined

type U32_to_u16_ArgT = Word32

type U32_to_u16_RetT = Word16

u32_to_u16 :: U32_to_u16_ArgT -> U32_to_u16_RetT
u32_to_u16 = undefined

type U16_to_u8_ArgT = Word16

type U16_to_u8_RetT = Word8

u16_to_u8 :: U16_to_u8_ArgT -> U16_to_u8_RetT
u16_to_u8 = undefined

type Random_u32_ArgT = ()

type Random_u32_RetT = Word32

random_u32 :: Random_u32_ArgT -> Random_u32_RetT
random_u32 = undefined

type Cogent_warn_u64_ArgT = Word64

type Cogent_warn_u64_RetT = ()

cogent_warn_u64 :: Cogent_warn_u64_ArgT -> Cogent_warn_u64_RetT
cogent_warn_u64 = undefined

type Cogent_warn_u32_ArgT = Word32

type Cogent_warn_u32_RetT = ()

cogent_warn_u32 :: Cogent_warn_u32_ArgT -> Cogent_warn_u32_RetT
cogent_warn_u32 = undefined

type Cogent_warn_u16_ArgT = Word16

type Cogent_warn_u16_RetT = ()

cogent_warn_u16 :: Cogent_warn_u16_ArgT -> Cogent_warn_u16_RetT
cogent_warn_u16 = undefined

type Cogent_warn_ArgT = String

type Cogent_warn_RetT = ()

cogent_warn :: Cogent_warn_ArgT -> Cogent_warn_RetT
cogent_warn = undefined

type Cogent_log2_ArgT = Word32

type Cogent_log2_RetT = Word32

cogent_log2 :: Cogent_log2_ArgT -> Cogent_log2_RetT
cogent_log2 = undefined

type Cogent_debug_u64_hex_ArgT = Word64

type Cogent_debug_u64_hex_RetT = ()

cogent_debug_u64_hex :: Cogent_debug_u64_hex_ArgT -> Cogent_debug_u64_hex_RetT
cogent_debug_u64_hex = undefined

type Cogent_debug_u64_ArgT = Word64

type Cogent_debug_u64_RetT = ()

cogent_debug_u64 :: Cogent_debug_u64_ArgT -> Cogent_debug_u64_RetT
cogent_debug_u64 = undefined

type Cogent_debug_u32_oct_ArgT = Word32

type Cogent_debug_u32_oct_RetT = ()

cogent_debug_u32_oct :: Cogent_debug_u32_oct_ArgT -> Cogent_debug_u32_oct_RetT
cogent_debug_u32_oct = undefined

type Cogent_debug_u32_hex_ArgT = Word32

type Cogent_debug_u32_hex_RetT = ()

cogent_debug_u32_hex :: Cogent_debug_u32_hex_ArgT -> Cogent_debug_u32_hex_RetT
cogent_debug_u32_hex = undefined

type Cogent_debug_u32_ArgT = Word32

type Cogent_debug_u32_RetT = ()

cogent_debug_u32 :: Cogent_debug_u32_ArgT -> Cogent_debug_u32_RetT
cogent_debug_u32 = undefined

type Cogent_debug_ArgT = String

type Cogent_debug_RetT = ()

cogent_debug :: Cogent_debug_ArgT -> Cogent_debug_RetT
cogent_debug = undefined

type Cogent_assert2_ArgT = (String, Bool)

type Cogent_assert2_RetT = ()

cogent_assert2 :: Cogent_assert2_ArgT -> Cogent_assert2_RetT
cogent_assert2 = undefined

type Cogent_assert_ArgT = Bool

type Cogent_assert_RetT = ()

cogent_assert :: Cogent_assert_ArgT -> Cogent_assert_RetT
cogent_assert = undefined

type Wordarray_cmp_ArgT = (WordArray Word8, WordArray Word8)

type Wordarray_cmp_RetT = Bool

wordarray_cmp :: Wordarray_cmp_ArgT -> Wordarray_cmp_RetT
wordarray_cmp = undefined

type Wordarray_copy_ArgT a = (WordArray a, WordArray a, Word32, Word32, Word32)

type Wordarray_copy_RetT a = WordArray a

wordarray_copy :: Wordarray_copy_ArgT a -> Wordarray_copy_RetT a
wordarray_copy (dst,src,dst_offs,src_offs,n) =
  let (0,u_dst) = A.bounds dst
      (0,u_src) = A.bounds src
      dst_avl = u_dst + 1 - dst_offs
      src_avl = u_src + 1 - src_offs
      n' = minimum [n, dst_avl, src_avl]
      src_cpy = genericTake n' . genericDrop src_offs $ A.elems src 
   in if dst_offs > u_dst - 1 then dst 
      else dst A.// zip [dst_offs .. dst_offs + n' - 1] src_cpy

type Wordarray_fold'_ArgT a acc obsv = (WordArray a, (acc, obsv, a) -> acc, acc, obsv)

type Wordarray_fold'_RetT a acc obsv = acc

wordarray_fold' :: Wordarray_fold'_ArgT a acc obsv -> Wordarray_fold'_RetT a acc obsv
wordarray_fold' = undefined

type Wordarray_get_ArgT a = (WordArray a, Word32)

type Wordarray_get_RetT a = a

wordarray_get :: Wordarray_get_ArgT a -> Wordarray_get_RetT a
wordarray_get = undefined

type Wordarray_length_ArgT a = WordArray a

type Wordarray_length_RetT a = Word32

wordarray_length :: Wordarray_length_ArgT a -> Wordarray_length_RetT a
wordarray_length arr = let (0,u) = A.bounds arr in u + 1

type Wordarray_map'_ArgT a acc obsv = (WordArray a, (acc, obsv, a) -> (acc, a), acc, obsv)

type Wordarray_map'_RetT a acc obsv = (WordArray a, acc)

wordarray_map' :: Wordarray_map'_ArgT a acc obsv -> Wordarray_map'_RetT a acc obsv
wordarray_map' = undefined

type Wordarray_map__ArgT a = (WordArray a, a -> a)

type Wordarray_map__RetT a = WordArray a

wordarray_map_ :: Wordarray_map__ArgT a -> Wordarray_map__RetT a
wordarray_map_ = undefined

type Wordarray_put2_ArgT a = R41 (WordArray a) Word32 a

type Wordarray_put2_RetT a = WordArray a

wordarray_put2 :: Wordarray_put2_ArgT a -> Wordarray_put2_RetT a
wordarray_put2 = undefined

type Wordarray_set_ArgT a = (WordArray a, Word32, Word32, a)

type Wordarray_set_RetT a = WordArray a

wordarray_set :: Wordarray_set_ArgT a -> Wordarray_set_RetT a
wordarray_set (arr, frm, n, a) = 
  let len = wordarray_length arr
      frm' = if frm >= len then len else frm
      to'  = if frm + n > len then len else frm + n
   in arr A.// (zip [frm' .. to' - 1] (repeat a))

type Wordarray_split_ArgT a = (WordArray a, Word32)

type Wordarray_split_RetT a = (WordArray a, WordArray a)

wordarray_split :: Wordarray_split_ArgT a -> Wordarray_split_RetT a
wordarray_split = undefined

type Wordarray_take_ArgT a = (WordArray a, Word32)

type Wordarray_take_RetT a = WordArray a

wordarray_take :: Wordarray_take_ArgT a -> Wordarray_take_RetT a
wordarray_take = undefined

type Wordarray_u8_as_u32_ArgT = WordArray Word8

type Wordarray_u8_as_u32_RetT = Word32

wordarray_u8_as_u32 :: Wordarray_u8_as_u32_ArgT -> Wordarray_u8_as_u32_RetT
wordarray_u8_as_u32 = undefined

type Wordarray_map_view_ArgT a = (View (WordArray a), a -> a)

type Wordarray_map_view_RetT a = View (WordArray a)

wordarray_map_view :: Wordarray_map_view_ArgT a -> Wordarray_map_view_RetT a
wordarray_map_view = undefined

type Wordarray_unview_ArgT a = View (WordArray a)

type Wordarray_unview_RetT a = WordArray a

wordarray_unview :: Wordarray_unview_ArgT a -> Wordarray_unview_RetT a
wordarray_unview = undefined

type Wordarray_view_ArgT a = (WordArray a, Word32, Word32, Word32)

type Wordarray_view_RetT a = View (WordArray a)

wordarray_view :: Wordarray_view_ArgT a -> Wordarray_view_RetT a
wordarray_view = undefined

type Vfs_stat_set_blksize_ArgT = (VfsStat, Word32)

type Vfs_stat_set_blksize_RetT = VfsStat

vfs_stat_set_blksize :: Vfs_stat_set_blksize_ArgT -> Vfs_stat_set_blksize_RetT
vfs_stat_set_blksize = undefined

type Vfs_stat_set_blocks_ArgT = (VfsStat, Word64)

type Vfs_stat_set_blocks_RetT = VfsStat

vfs_stat_set_blocks :: Vfs_stat_set_blocks_ArgT -> Vfs_stat_set_blocks_RetT
vfs_stat_set_blocks = undefined

type Vfs_stat_set_gid_ArgT = (VfsStat, Word32)

type Vfs_stat_set_gid_RetT = VfsStat

vfs_stat_set_gid :: Vfs_stat_set_gid_ArgT -> Vfs_stat_set_gid_RetT
vfs_stat_set_gid = undefined

type Vfs_stat_set_nlink_ArgT = (VfsStat, Word32)

type Vfs_stat_set_nlink_RetT = VfsStat

vfs_stat_set_nlink :: Vfs_stat_set_nlink_ArgT -> Vfs_stat_set_nlink_RetT
vfs_stat_set_nlink = undefined

type Vfs_stat_set_uid_ArgT = (VfsStat, Word32)

type Vfs_stat_set_uid_RetT = VfsStat

vfs_stat_set_uid :: Vfs_stat_set_uid_ArgT -> Vfs_stat_set_uid_RetT
vfs_stat_set_uid = undefined

type Vfs_stat_set_size_ArgT = (VfsStat, Word64)

type Vfs_stat_set_size_RetT = VfsStat

vfs_stat_set_size :: Vfs_stat_set_size_ArgT -> Vfs_stat_set_size_RetT
vfs_stat_set_size = undefined

type Vfs_stat_set_mode_ArgT = (VfsStat, Word32)

type Vfs_stat_set_mode_RetT = VfsStat

vfs_stat_set_mode :: Vfs_stat_set_mode_ArgT -> Vfs_stat_set_mode_RetT
vfs_stat_set_mode = undefined

type Vfs_stat_set_ino_ArgT = (VfsStat, Word32)

type Vfs_stat_set_ino_RetT = VfsStat

vfs_stat_set_ino :: Vfs_stat_set_ino_ArgT -> Vfs_stat_set_ino_RetT
vfs_stat_set_ino = undefined

type Vfs_iattr_get_gid_ArgT = VfsIattr

type Vfs_iattr_get_gid_RetT = Word32

vfs_iattr_get_gid :: Vfs_iattr_get_gid_ArgT -> Vfs_iattr_get_gid_RetT
vfs_iattr_get_gid = undefined

type Vfs_iattr_get_mode_ArgT = VfsIattr

type Vfs_iattr_get_mode_RetT = Word32

vfs_iattr_get_mode :: Vfs_iattr_get_mode_ArgT -> Vfs_iattr_get_mode_RetT
vfs_iattr_get_mode = undefined

type Vfs_iattr_get_size_ArgT = VfsIattr

type Vfs_iattr_get_size_RetT = Word64

vfs_iattr_get_size :: Vfs_iattr_get_size_ArgT -> Vfs_iattr_get_size_RetT
vfs_iattr_get_size = undefined

type Vfs_iattr_get_uid_ArgT = VfsIattr

type Vfs_iattr_get_uid_RetT = Word32

vfs_iattr_get_uid :: Vfs_iattr_get_uid_ArgT -> Vfs_iattr_get_uid_RetT
vfs_iattr_get_uid = undefined

type Vfs_iattr_get_valid_ArgT = VfsIattr

type Vfs_iattr_get_valid_RetT = Word32

vfs_iattr_get_valid :: Vfs_iattr_get_valid_ArgT -> Vfs_iattr_get_valid_RetT
vfs_iattr_get_valid = undefined

type Vfs_stat_set_flags_ArgT = (VfsStat, Word32)

type Vfs_stat_set_flags_RetT = VfsStat

vfs_stat_set_flags :: Vfs_stat_set_flags_ArgT -> Vfs_stat_set_flags_RetT
vfs_stat_set_flags = undefined

type Vfs_create_device_ArgT = (Word32, Word32)

type Vfs_create_device_RetT = VfsDevice

vfs_create_device :: Vfs_create_device_ArgT -> Vfs_create_device_RetT
vfs_create_device = undefined

type Vfs_device_inspect_ArgT = VfsDevice

type Vfs_device_inspect_RetT = (Word32, Word32)

vfs_device_inspect :: Vfs_device_inspect_ArgT -> Vfs_device_inspect_RetT
vfs_device_inspect = undefined

type Os_get_current_fsgid_ArgT = SysState

type Os_get_current_fsgid_RetT = Word32

os_get_current_fsgid :: Os_get_current_fsgid_ArgT -> Os_get_current_fsgid_RetT
os_get_current_fsgid = undefined

type Os_get_current_fsuid_ArgT = SysState

type Os_get_current_fsuid_RetT = Word32

os_get_current_fsuid :: Os_get_current_fsuid_ArgT -> Os_get_current_fsuid_RetT
os_get_current_fsuid = undefined

type Os_get_pid_ArgT = SysState

type Os_get_pid_RetT = Word32

os_get_pid :: Os_get_pid_ArgT -> Os_get_pid_RetT
os_get_pid = undefined

type Wordarray_free_ArgT a = (SysState, WordArray a)

type Wordarray_free_RetT a = SysState

wordarray_free :: Wordarray_free_ArgT a -> Wordarray_free_RetT a
wordarray_free = undefined

type Os_spin_lock_ArgT = (SysState, SpinLock)

type Os_spin_lock_RetT = (SysState, SpinLock)

os_spin_lock :: Os_spin_lock_ArgT -> Os_spin_lock_RetT
os_spin_lock = undefined

type Os_spin_unlock_ArgT = (SysState, SpinLock)

type Os_spin_unlock_RetT = (SysState, SpinLock)

os_spin_unlock :: Os_spin_unlock_ArgT -> Os_spin_unlock_RetT
os_spin_unlock = undefined

type Seq32_simple_ArgT acc = R35 Word32 Word32 Word32 (acc -> acc) acc

type Seq32_simple_RetT acc = acc

seq32_simple :: Seq32_simple_ArgT acc -> Seq32_simple_RetT acc
seq32_simple = undefined

type Wordarray_clone_rr_ArgT a b = (SysState, WordArray a)

type Wordarray_clone_rr_RetT a b = (SysState, V34 () (WordArray b))

wordarray_clone_rr :: Wordarray_clone_rr_ArgT a b -> Wordarray_clone_rr_RetT a b
wordarray_clone_rr = undefined

type Wordarray_slice_ArgT a = (SysState, WordArray a, Word32, Word32)

type Wordarray_slice_RetT a = (SysState, V34 () (WordArray a))

wordarray_slice :: Wordarray_slice_ArgT a -> Wordarray_slice_RetT a
wordarray_slice = undefined

type Wordarray_create_ArgT a = (SysState, Word32)

type Wordarray_create_RetT a = V34 SysState (SysState, WordArray a)

wordarray_create :: Wordarray_create_ArgT a -> Wordarray_create_RetT a
wordarray_create = undefined

type Wordarray_create_nz_ArgT a = (SysState, Word32)

type Wordarray_create_nz_RetT a = V34 SysState (SysState, WordArray a)

wordarray_create_nz :: Wordarray_create_nz_ArgT a -> Wordarray_create_nz_RetT a
wordarray_create_nz = undefined

type Wordarray_put_ArgT a = R41 (WordArray a) Word32 a

type Wordarray_put_RetT a = V34 (WordArray a) (WordArray a)

wordarray_put :: Wordarray_put_ArgT a -> Wordarray_put_RetT a
wordarray_put = undefined

type FreeOstoreState_ArgT = (SysState, OstoreState)

type FreeOstoreState_RetT = SysState

freeOstoreState :: FreeOstoreState_ArgT -> FreeOstoreState_RetT
freeOstoreState = undefined

type NewOstoreState_ArgT = SysState

type NewOstoreState_RetT = V34 SysState (SysState, OstoreState)

newOstoreState :: NewOstoreState_ArgT -> NewOstoreState_RetT
newOstoreState = undefined

type Deep_freeObjData_ArgT = (SysState, R30 Word64 (WordArray Word8))

type Deep_freeObjData_RetT = SysState

deep_freeObjData :: Deep_freeObjData_ArgT -> Deep_freeObjData_RetT
deep_freeObjData = undefined

type Extract_data_from_union_ArgT = (SysState, V29 (R30 Word64 (WordArray Word8)) ObjDel ObjDentarr ObjInode () ObjSummary ObjSuper)

type Extract_data_from_union_RetT = V34 SysState (SysState, R30 Word64 (WordArray Word8))

extract_data_from_union :: Extract_data_from_union_ArgT -> Extract_data_from_union_RetT
extract_data_from_union (st, V29_TObjData odata) = success (st, odata)

type FreeObj_ArgT = (SysState, R28 Word32 Word32 Word64 Word32 Word32 Word8 Word8 (V29 (R30 Word64 (WordArray Word8)) ObjDel ObjDentarr ObjInode () ObjSummary ObjSuper))

type FreeObj_RetT = SysState

freeObj :: FreeObj_ArgT -> FreeObj_RetT
freeObj = undefined

type Os_get_current_time_ArgT = SysState

type Os_get_current_time_RetT = (SysState, R27 Word32 Word32)

os_get_current_time :: Os_get_current_time_ArgT -> Os_get_current_time_RetT
os_get_current_time = undefined

type Vfs_iattr_get_atime_ArgT = VfsIattr

type Vfs_iattr_get_atime_RetT = R27 Word32 Word32

vfs_iattr_get_atime :: Vfs_iattr_get_atime_ArgT -> Vfs_iattr_get_atime_RetT
vfs_iattr_get_atime = undefined

type Vfs_iattr_get_ctime_ArgT = VfsIattr

type Vfs_iattr_get_ctime_RetT = R27 Word32 Word32

vfs_iattr_get_ctime :: Vfs_iattr_get_ctime_ArgT -> Vfs_iattr_get_ctime_RetT
vfs_iattr_get_ctime = undefined

type Vfs_iattr_get_mtime_ArgT = VfsIattr

type Vfs_iattr_get_mtime_RetT = R27 Word32 Word32

vfs_iattr_get_mtime :: Vfs_iattr_get_mtime_ArgT -> Vfs_iattr_get_mtime_RetT
vfs_iattr_get_mtime = undefined

type Vfs_stat_set_atime_ArgT = (VfsStat, R27 Word32 Word32)

type Vfs_stat_set_atime_RetT = VfsStat

vfs_stat_set_atime :: Vfs_stat_set_atime_ArgT -> Vfs_stat_set_atime_RetT
vfs_stat_set_atime = undefined

type Vfs_stat_set_ctime_ArgT = (VfsStat, R27 Word32 Word32)

type Vfs_stat_set_ctime_RetT = VfsStat

vfs_stat_set_ctime :: Vfs_stat_set_ctime_ArgT -> Vfs_stat_set_ctime_RetT
vfs_stat_set_ctime = undefined

type Vfs_stat_set_mtime_ArgT = (VfsStat, R27 Word32 Word32)

type Vfs_stat_set_mtime_RetT = VfsStat

vfs_stat_set_mtime :: Vfs_stat_set_mtime_ArgT -> Vfs_stat_set_mtime_RetT
vfs_stat_set_mtime = undefined

type FreeMountState_ArgT = (SysState, MountState)

type FreeMountState_RetT = SysState

freeMountState :: FreeMountState_ArgT -> FreeMountState_RetT
freeMountState = undefined

type NewMountState_ArgT = SysState

type NewMountState_RetT = V34 SysState (SysState, MountState)

newMountState :: NewMountState_ArgT -> NewMountState_RetT
newMountState = undefined

type Seq32_ArgT acc obsv rbrk = R24 Word32 Word32 Word32 (R36 acc obsv Word32 -> (acc, V25 rbrk ())) acc obsv

type Seq32_RetT acc obsv rbrk = (acc, V25 rbrk ())

seq32 :: Seq32_ArgT acc obsv rbrk -> Seq32_RetT acc obsv rbrk
seq32 = undefined

type Seq32_rev_ArgT acc obsv rbrk = R24 Word32 Word32 Word32 (R36 acc obsv Word32 -> (acc, V25 rbrk ())) acc obsv

type Seq32_rev_RetT acc obsv rbrk = (acc, V25 rbrk ())

seq32_rev :: Seq32_rev_ArgT acc obsv rbrk -> Seq32_rev_RetT acc obsv rbrk
seq32_rev = undefined

type Seq32_stepf_ArgT acc obsv rbrk = R23 Word32 Word32 (Word32 -> Word32) (R36 acc obsv Word32 -> (acc, V25 rbrk ())) acc obsv

type Seq32_stepf_RetT acc obsv rbrk = (acc, V25 rbrk ())

seq32_stepf :: Seq32_stepf_ArgT acc obsv rbrk -> Seq32_stepf_RetT acc obsv rbrk
seq32_stepf = undefined

type Seq64_ArgT acc obsv rbrk = R24 Word64 Word64 Word64 (R36 acc obsv Word64 -> (acc, V25 rbrk ())) acc obsv

type Seq64_RetT acc obsv rbrk = (acc, V25 rbrk ())

seq64 :: Seq64_ArgT acc obsv rbrk -> Seq64_RetT acc obsv rbrk
seq64 = undefined

type FreeFsopState_ArgT = (SysState, FsopState)

type FreeFsopState_RetT = SysState

freeFsopState :: FreeFsopState_ArgT -> FreeFsopState_RetT
freeFsopState = undefined

type NewFsopState_ArgT = SysState

type NewFsopState_RetT = V34 SysState (SysState, FsopState)

newFsopState :: NewFsopState_ArgT -> NewFsopState_RetT
newFsopState = undefined

type FreeFsState_ArgT = (SysState, R22 FsopState MountState OstoreState)

type FreeFsState_RetT = SysState

freeFsState :: FreeFsState_ArgT -> FreeFsState_RetT
freeFsState = undefined

type NewFsState_ArgT = SysState

type NewFsState_RetT = V34 SysState (SysState, R22 FsopState MountState OstoreState)

newFsState :: NewFsState_ArgT -> NewFsState_RetT
newFsState = undefined

type Vfs_inode_bad_ArgT = R3 SysState (R20 VfsInodeAbstract (R21 Word32))

type Vfs_inode_bad_RetT = SysState

vfs_inode_bad :: Vfs_inode_bad_ArgT -> Vfs_inode_bad_RetT
vfs_inode_bad = undefined

type Vfs_inode_bad_taken_ArgT = R3 SysState (R20 VfsInodeAbstract (R21 Word32))

type Vfs_inode_bad_taken_RetT = SysState

vfs_inode_bad_taken :: Vfs_inode_bad_taken_ArgT -> Vfs_inode_bad_taken_RetT
vfs_inode_bad_taken = undefined

type Vfs_inode_dec_nlink_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_dec_nlink_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_dec_nlink :: Vfs_inode_dec_nlink_ArgT -> Vfs_inode_dec_nlink_RetT
vfs_inode_dec_nlink = undefined

type Vfs_inode_get_ArgT = (SysState, Word32)

type Vfs_inode_get_RetT = (SysState, V2 (R20 VfsInodeAbstract (R21 Word32)) (R20 VfsInodeAbstract (R21 Word32)) ())

vfs_inode_get :: Vfs_inode_get_ArgT -> Vfs_inode_get_RetT
vfs_inode_get = undefined

type Vfs_inode_get_atime_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_get_atime_RetT = R27 Word32 Word32

vfs_inode_get_atime :: Vfs_inode_get_atime_ArgT -> Vfs_inode_get_atime_RetT
vfs_inode_get_atime = undefined

type Vfs_inode_get_blocks_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_get_blocks_RetT = Word64

vfs_inode_get_blocks :: Vfs_inode_get_blocks_ArgT -> Vfs_inode_get_blocks_RetT
vfs_inode_get_blocks = undefined

type Vfs_inode_get_bytes_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_get_bytes_RetT = Word16

vfs_inode_get_bytes :: Vfs_inode_get_bytes_ArgT -> Vfs_inode_get_bytes_RetT
vfs_inode_get_bytes = undefined

type Vfs_inode_get_ctime_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_get_ctime_RetT = R27 Word32 Word32

vfs_inode_get_ctime :: Vfs_inode_get_ctime_ArgT -> Vfs_inode_get_ctime_RetT
vfs_inode_get_ctime = undefined

type Vfs_inode_get_device_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_get_device_RetT = VfsDevice

vfs_inode_get_device :: Vfs_inode_get_device_ArgT -> Vfs_inode_get_device_RetT
vfs_inode_get_device = undefined

type Vfs_inode_get_flags_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_get_flags_RetT = Word32

vfs_inode_get_flags :: Vfs_inode_get_flags_ArgT -> Vfs_inode_get_flags_RetT
vfs_inode_get_flags = undefined

type Vfs_inode_get_gid_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_get_gid_RetT = Word32

vfs_inode_get_gid :: Vfs_inode_get_gid_ArgT -> Vfs_inode_get_gid_RetT
vfs_inode_get_gid = undefined

type Vfs_inode_get_ino_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_get_ino_RetT = Word32

vfs_inode_get_ino :: Vfs_inode_get_ino_ArgT -> Vfs_inode_get_ino_RetT
vfs_inode_get_ino (R20 (VfsInodeAbstract ino _) _) = ino

type Vfs_inode_get_ino2_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_get_ino2_RetT = Word32

vfs_inode_get_ino2 :: Vfs_inode_get_ino2_ArgT -> Vfs_inode_get_ino2_RetT
vfs_inode_get_ino2 = undefined

type Vfs_inode_get_mapping_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_get_mapping_RetT = VfsMemoryMap

vfs_inode_get_mapping :: Vfs_inode_get_mapping_ArgT -> Vfs_inode_get_mapping_RetT
vfs_inode_get_mapping = undefined

type Vfs_inode_get_mode_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_get_mode_RetT = Word32

vfs_inode_get_mode :: Vfs_inode_get_mode_ArgT -> Vfs_inode_get_mode_RetT
vfs_inode_get_mode = undefined

type Vfs_inode_get_mode2_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_get_mode2_RetT = Word32

vfs_inode_get_mode2 :: Vfs_inode_get_mode2_ArgT -> Vfs_inode_get_mode2_RetT
vfs_inode_get_mode2 = undefined

type Vfs_inode_get_mtime_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_get_mtime_RetT = R27 Word32 Word32

vfs_inode_get_mtime :: Vfs_inode_get_mtime_ArgT -> Vfs_inode_get_mtime_RetT
vfs_inode_get_mtime = undefined

type Vfs_inode_get_nlink_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_get_nlink_RetT = Word32

vfs_inode_get_nlink :: Vfs_inode_get_nlink_ArgT -> Vfs_inode_get_nlink_RetT
vfs_inode_get_nlink = undefined

type Vfs_inode_get_size_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_get_size_RetT = Word64

vfs_inode_get_size :: Vfs_inode_get_size_ArgT -> Vfs_inode_get_size_RetT
vfs_inode_get_size (R20 (VfsInodeAbstract _ sz) _) = sz

type Vfs_inode_get_uid_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_get_uid_RetT = Word32

vfs_inode_get_uid :: Vfs_inode_get_uid_ArgT -> Vfs_inode_get_uid_RetT
vfs_inode_get_uid = undefined

type Vfs_inode_inc_nlink_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_inc_nlink_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_inc_nlink :: Vfs_inode_inc_nlink_ArgT -> Vfs_inode_inc_nlink_RetT
vfs_inode_inc_nlink = undefined

type Vfs_inode_insert_ArgT = R3 SysState (R20 VfsInodeAbstract (R21 Word32))

type Vfs_inode_insert_RetT = V34 (SysState, R20 VfsInodeAbstract (R21 Word32)) (SysState, R20 VfsInodeAbstract (R21 Word32))

vfs_inode_insert :: Vfs_inode_insert_ArgT -> Vfs_inode_insert_RetT
vfs_inode_insert = undefined

type Vfs_inode_is_sync_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_is_sync_RetT = Bool

vfs_inode_is_sync :: Vfs_inode_is_sync_ArgT -> Vfs_inode_is_sync_RetT
vfs_inode_is_sync = undefined

type Vfs_inode_is_sync_dir_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_is_sync_dir_RetT = Bool

vfs_inode_is_sync_dir :: Vfs_inode_is_sync_dir_ArgT -> Vfs_inode_is_sync_dir_RetT
vfs_inode_is_sync_dir = undefined

type Vfs_inode_link_device_ArgT = (R20 VfsInodeAbstract (R21 Word32), Word32, VfsDevice)

type Vfs_inode_link_device_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_link_device :: Vfs_inode_link_device_ArgT -> Vfs_inode_link_device_RetT
vfs_inode_link_device = undefined

type Vfs_inode_lock_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_lock_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_lock :: Vfs_inode_lock_ArgT -> Vfs_inode_lock_RetT
vfs_inode_lock = undefined

type Vfs_inode_make_bad_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_make_bad_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_make_bad :: Vfs_inode_make_bad_ArgT -> Vfs_inode_make_bad_RetT
vfs_inode_make_bad = undefined

type Vfs_inode_mark_dirty_ArgT = (SysState, R20 VfsInodeAbstract (R21 Word32))

type Vfs_inode_mark_dirty_RetT = (SysState, R20 VfsInodeAbstract (R21 Word32))

vfs_inode_mark_dirty :: Vfs_inode_mark_dirty_ArgT -> Vfs_inode_mark_dirty_RetT
vfs_inode_mark_dirty = undefined

type Vfs_inode_new_ArgT = SysState

type Vfs_inode_new_RetT = V34 SysState (SysState, R20 VfsInodeAbstract (R21 Word32))

vfs_inode_new :: Vfs_inode_new_ArgT -> Vfs_inode_new_RetT
vfs_inode_new = undefined

type Vfs_inode_put_ArgT = R3 SysState (R20 VfsInodeAbstract (R21 Word32))

type Vfs_inode_put_RetT = SysState

vfs_inode_put :: Vfs_inode_put_ArgT -> Vfs_inode_put_RetT
vfs_inode_put = undefined

type Vfs_inode_put_taken_ArgT = R3 SysState (R20 VfsInodeAbstract (R21 Word32))

type Vfs_inode_put_taken_RetT = SysState

vfs_inode_put_taken :: Vfs_inode_put_taken_ArgT -> Vfs_inode_put_taken_RetT
vfs_inode_put_taken = undefined

type Vfs_inode_set_atime_ArgT = (R20 VfsInodeAbstract (R21 Word32), R27 Word32 Word32)

type Vfs_inode_set_atime_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_set_atime :: Vfs_inode_set_atime_ArgT -> Vfs_inode_set_atime_RetT
vfs_inode_set_atime = undefined

type Vfs_inode_set_blocks_ArgT = (R20 VfsInodeAbstract (R21 Word32), Word64)

type Vfs_inode_set_blocks_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_set_blocks :: Vfs_inode_set_blocks_ArgT -> Vfs_inode_set_blocks_RetT
vfs_inode_set_blocks = undefined

type Vfs_inode_set_bytes_ArgT = (R20 VfsInodeAbstract (R21 Word32), Word16)

type Vfs_inode_set_bytes_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_set_bytes :: Vfs_inode_set_bytes_ArgT -> Vfs_inode_set_bytes_RetT
vfs_inode_set_bytes = undefined

type Vfs_inode_set_ctime_ArgT = (R20 VfsInodeAbstract (R21 Word32), R27 Word32 Word32)

type Vfs_inode_set_ctime_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_set_ctime :: Vfs_inode_set_ctime_ArgT -> Vfs_inode_set_ctime_RetT
vfs_inode_set_ctime = undefined

type Vfs_inode_set_flags_ArgT = (R20 VfsInodeAbstract (R21 Word32), Word32)

type Vfs_inode_set_flags_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_set_flags :: Vfs_inode_set_flags_ArgT -> Vfs_inode_set_flags_RetT
vfs_inode_set_flags = undefined

type Vfs_inode_set_gid_ArgT = (R20 VfsInodeAbstract (R21 Word32), Word32)

type Vfs_inode_set_gid_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_set_gid :: Vfs_inode_set_gid_ArgT -> Vfs_inode_set_gid_RetT
vfs_inode_set_gid = undefined

type Vfs_inode_set_ino_ArgT = (R20 VfsInodeAbstract (R21 Word32), Word32)

type Vfs_inode_set_ino_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_set_ino :: Vfs_inode_set_ino_ArgT -> Vfs_inode_set_ino_RetT
vfs_inode_set_ino = undefined

type Vfs_inode_set_mode_ArgT = (R20 VfsInodeAbstract (R21 Word32), Word32)

type Vfs_inode_set_mode_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_set_mode :: Vfs_inode_set_mode_ArgT -> Vfs_inode_set_mode_RetT
vfs_inode_set_mode = undefined

type Vfs_inode_set_mtime_ArgT = (R20 VfsInodeAbstract (R21 Word32), R27 Word32 Word32)

type Vfs_inode_set_mtime_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_set_mtime :: Vfs_inode_set_mtime_ArgT -> Vfs_inode_set_mtime_RetT
vfs_inode_set_mtime = undefined

type Vfs_inode_set_nlink_ArgT = (R20 VfsInodeAbstract (R21 Word32), Word32)

type Vfs_inode_set_nlink_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_set_nlink :: Vfs_inode_set_nlink_ArgT -> Vfs_inode_set_nlink_RetT
vfs_inode_set_nlink = undefined

type Vfs_inode_set_size_ArgT = (R20 VfsInodeAbstract (R21 Word32), Word64)

type Vfs_inode_set_size_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_set_size :: Vfs_inode_set_size_ArgT -> Vfs_inode_set_size_RetT
vfs_inode_set_size = undefined

type Vfs_inode_set_uid_ArgT = (R20 VfsInodeAbstract (R21 Word32), Word32)

type Vfs_inode_set_uid_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_set_uid :: Vfs_inode_set_uid_ArgT -> Vfs_inode_set_uid_RetT
vfs_inode_set_uid = undefined

type Vfs_inode_sync_metadata_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_sync_metadata_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_sync_metadata :: Vfs_inode_sync_metadata_ArgT -> Vfs_inode_sync_metadata_RetT
vfs_inode_sync_metadata = undefined

type Vfs_inode_unlock_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_unlock_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_unlock :: Vfs_inode_unlock_ArgT -> Vfs_inode_unlock_RetT
vfs_inode_unlock = undefined

type Vfs_inode_unlock_new_ArgT = R20 VfsInodeAbstract (R21 Word32)

type Vfs_inode_unlock_new_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_unlock_new :: Vfs_inode_unlock_new_ArgT -> Vfs_inode_unlock_new_RetT
vfs_inode_unlock_new = undefined

type Wordarray_findsub_ArgT a = (WordArray a, WordArray a, Word32)

type Wordarray_findsub_RetT a = V17 Word32 ()

wordarray_findsub :: Wordarray_findsub_ArgT a -> Wordarray_findsub_RetT a
wordarray_findsub = undefined

type Ostore_read_ArgT = (SysState, MountState, OstoreState, Word64)

type Ostore_read_RetT = ((SysState, OstoreState), V34 Word32 (R28 Word32 Word32 Word64 Word32 Word32 Word8 Word8 (V29 (R30 Word64 (WordArray Word8)) ObjDel ObjDentarr ObjInode () ObjSummary ObjSuper)))

ostore_read :: Ostore_read_ArgT -> Ostore_read_RetT
ostore_read (ex, mount_st, ostore_st, oid) =
  let err = unsafePerformIO $ Q.generate $ Q.frequency [ (1, return 0)
                                                       , (1, Q.elements [eIO, eNoMem, eInval, eBadF])]
   in if | err == 0 -> case M.lookup oid ostore_st of
             Nothing  -> ((ex, ostore_st), error eNoEnt)
             Just obj -> ((ex, ostore_st), success obj)
         | otherwise -> ((ex, ostore_st), error err)

type Wordarray_fold_ArgT a acc obsv rbrk = R14 (WordArray a) Word32 Word32 (R15 a acc obsv -> V25 rbrk acc) acc obsv

type Wordarray_fold_RetT a acc obsv rbrk = V25 rbrk acc

wordarray_fold :: Wordarray_fold_ArgT a acc obsv rbrk -> Wordarray_fold_RetT a acc obsv rbrk
wordarray_fold = undefined

type Wordarray_fold_no_break_ArgT a acc obsv = R14 (WordArray a) Word32 Word32 (R15 a acc obsv -> acc) acc obsv

type Wordarray_fold_no_break_RetT a acc obsv = acc

wordarray_fold_no_break :: Wordarray_fold_no_break_ArgT a acc obsv -> Wordarray_fold_no_break_RetT a acc obsv
wordarray_fold_no_break = undefined

type Wordarray_map_ArgT a acc obsv rbrk = R14 (WordArray a) Word32 Word32 (R15 a acc obsv -> ((a, acc), V25 rbrk ())) acc obsv

type Wordarray_map_RetT a acc obsv rbrk = ((WordArray a, acc), V25 rbrk ())

wordarray_map :: Wordarray_map_ArgT a acc obsv rbrk -> Wordarray_map_RetT a acc obsv rbrk
wordarray_map = undefined

type Wordarray_map_no_break_ArgT a acc obsv = R14 (WordArray a) Word32 Word32 (R15 a acc obsv -> (a, acc)) acc obsv

type Wordarray_map_no_break_RetT a acc obsv = (WordArray a, acc)

wordarray_map_no_break :: Wordarray_map_no_break_ArgT a acc obsv -> Wordarray_map_no_break_RetT a acc obsv
wordarray_map_no_break = undefined

type Vfs_dir_emit_ArgT = R10 (R26 OSDirContext Word64) (WordArray Word8) Word32 Word32

type Vfs_dir_emit_RetT = V25 (R1 (R26 OSDirContext Word64)) (R1 (R26 OSDirContext Word64))

vfs_dir_emit :: Vfs_dir_emit_ArgT -> Vfs_dir_emit_RetT
vfs_dir_emit = undefined

type Vfs_page_symlink_ArgT = (SysState, R20 VfsInodeAbstract (R21 Word32), WordArray Word8)

type Vfs_page_symlink_RetT = ((SysState, R20 VfsInodeAbstract (R21 Word32)), V34 Word32 ())

vfs_page_symlink :: Vfs_page_symlink_ArgT -> Vfs_page_symlink_RetT
vfs_page_symlink = undefined

type Wordarray_print_ArgT = WordArray Word8

type Wordarray_print_RetT = ()

wordarray_print :: Wordarray_print_ArgT -> Wordarray_print_RetT
wordarray_print = undefined

type FreeBuffer_ArgT = (SysState, R8 (WordArray Word8) Word32)

type FreeBuffer_RetT = SysState

freeBuffer :: FreeBuffer_ArgT -> FreeBuffer_RetT
freeBuffer = undefined

type NewBuffer_ArgT = SysState

type NewBuffer_RetT = V34 SysState (SysState, R8 (WordArray Word8) Word32)

newBuffer :: NewBuffer_ArgT -> NewBuffer_RetT
newBuffer = undefined

type Wordarray_modify_ArgT a acc obsv = R12 (WordArray a) Word32 (R15 a acc obsv -> R13 a acc) acc obsv

type Wordarray_modify_RetT a acc obsv = R4 (WordArray a) acc

wordarray_modify :: Wordarray_modify_ArgT a acc obsv -> Wordarray_modify_RetT a acc obsv
wordarray_modify = undefined

type Snd_ArgT a b = (a, b)

type Snd_RetT a b = b

snd :: Snd_ArgT a b -> Snd_RetT a b
snd __ds_var_0
  = let __ds_var_2 = __ds_var_0
        __ds_var_1 = Tup.sel1 __ds_var_0
      in
      let __ds_var_3 = __ds_var_2
          b = Tup.sel2 __ds_var_2
        in let __ds_var_4 = __ds_var_1 in b

type Second_ArgT b b' a = (b -> b', (a, b))

type Second_RetT b b' a = (a, b')

second :: Second_ArgT b b' a -> Second_RetT b b' a
second __ds_var_0
  = let __ds_var_2 = __ds_var_0
        f = Tup.sel1 __ds_var_0
      in
      let __ds_var_3 = __ds_var_2
          __ds_var_1 = Tup.sel2 __ds_var_2
        in
        let __ds_var_4 = __ds_var_1
            a = Tup.sel1 __ds_var_1
          in
          let __ds_var_5 = __ds_var_4
              b = Tup.sel2 __ds_var_4
            in (a, f b)

type Min_u64_ArgT = (Word64, Word64)

type Min_u64_RetT = Word64

min_u64 :: Min_u64_ArgT -> Min_u64_RetT
min_u64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = Tup.sel1 __ds_var_0
      in
      let __ds_var_2 = __ds_var_1
          b = Tup.sel2 __ds_var_1
        in if (a < b) then a else b

type Min_u32_ArgT = (Word32, Word32)

type Min_u32_RetT = Word32

min_u32 :: Min_u32_ArgT -> Min_u32_RetT
min_u32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = Tup.sel1 __ds_var_0
      in
      let __ds_var_2 = __ds_var_1
          b = Tup.sel2 __ds_var_1
        in if (a < b) then a else b

type In_range_u32_ArgT = (Word32, Word32, Word32)

type In_range_u32_RetT = Bool

in_range_u32 :: In_range_u32_ArgT -> In_range_u32_RetT
in_range_u32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        needle = Tup.sel1 __ds_var_0
      in
      let __ds_var_2 = __ds_var_1
          from = Tup.sel2 __ds_var_1
        in
        let __ds_var_3 = __ds_var_2
            to = Tup.sel3 __ds_var_2
          in if ((needle >= from) && (needle < to)) then True else False

type Fst_ArgT a b = (a, b)

type Fst_RetT a b = a

fst :: Fst_ArgT a b -> Fst_RetT a b
fst __ds_var_0
  = let __ds_var_2 = __ds_var_0
        a = Tup.sel1 __ds_var_0
      in
      let __ds_var_3 = __ds_var_2
          __ds_var_1 = Tup.sel2 __ds_var_2
        in let __ds_var_4 = __ds_var_1 in a

type First_ArgT a a' b = (a -> a', (a, b))

type First_RetT a a' b = (a', b)

first :: First_ArgT a a' b -> First_RetT a a' b
first __ds_var_0
  = let __ds_var_2 = __ds_var_0
        f = Tup.sel1 __ds_var_0
      in
      let __ds_var_3 = __ds_var_2
          __ds_var_1 = Tup.sel2 __ds_var_2
        in
        let __ds_var_4 = __ds_var_1
            a = Tup.sel1 __ds_var_1
          in
          let __ds_var_5 = __ds_var_4
              b = Tup.sel2 __ds_var_4
            in (f a, b)

type Cogent_low_16_bits_ArgT = Word32

type Cogent_low_16_bits_RetT = Word16

cogent_low_16_bits :: Cogent_low_16_bits_ArgT -> Cogent_low_16_bits_RetT
cogent_low_16_bits __ds_var_0 = let x = __ds_var_0 in u32_to_u16 (x .&. (65535 :: Word32))

type Cogent_high_16_bits_ArgT = Word32

type Cogent_high_16_bits_RetT = Word16

cogent_high_16_bits :: Cogent_high_16_bits_ArgT -> Cogent_high_16_bits_RetT
cogent_high_16_bits __ds_var_0 = let x = __ds_var_0 in u32_to_u16 ((x .&. (4294901760 :: Word32)) `shiftR` fromIntegral (16 :: Word32))

type Cogent_debug_u8_ArgT = Word8

type Cogent_debug_u8_RetT = ()

cogent_debug_u8 :: Cogent_debug_u8_ArgT -> Cogent_debug_u8_RetT
cogent_debug_u8 __ds_var_0 = let x = __ds_var_0 in cogent_debug_u32 (fromIntegral x :: Word32)

type Cogent_debug_u16_ArgT = Word16

type Cogent_debug_u16_RetT = ()

cogent_debug_u16 :: Cogent_debug_u16_ArgT -> Cogent_debug_u16_RetT
cogent_debug_u16 __ds_var_0 = let x = __ds_var_0 in cogent_debug_u32 (fromIntegral x :: Word32)

type Cogent_debug_bool_ArgT = Bool

type Cogent_debug_bool_RetT = ()

cogent_debug_bool :: Cogent_debug_bool_ArgT -> Cogent_debug_bool_RetT
cogent_debug_bool __ds_var_0 = let bool = __ds_var_0 in if bool then cogent_debug "true" else cogent_debug "false"

type Buffer_memset_loop_ArgT = R15 Word8 () Word8

type Buffer_memset_loop_RetT = (Word8, ())

buffer_memset_loop :: Buffer_memset_loop_ArgT -> Buffer_memset_loop_RetT
buffer_memset_loop __ds_var_0
  = let __ds_var_2 = __ds_var_0
        __ds_var_3 = let R15{elem = __shallow_v44, acc = __shallow_v45, obsv = __shallow_v46} = __ds_var_0 in __shallow_v44
      in
      let __ds_var_4 = __ds_var_3 in
        let __ds_var_5 = __ds_var_2
            __ds_var_6 = let R15{elem = __shallow_v47, acc = __shallow_v48, obsv = __shallow_v49} = __ds_var_2 in __shallow_v48
          in
          let __ds_var_7 = __ds_var_6 in
            let __ds_var_1 = __ds_var_5
                val = let R15{elem = __shallow_v50, acc = __shallow_v51, obsv = __shallow_v52} = __ds_var_5 in __shallow_v52
              in (val, ())

type Align64_ArgT = (Word64, Word64)

type Align64_RetT = Word64

align64 :: Align64_ArgT -> Align64_RetT
align64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        x = Tup.sel1 __ds_var_0
      in
      let __ds_var_2 = __ds_var_1
          powof2 = Tup.sel2 __ds_var_1
        in ((x + (powof2 - (1 :: Word64))) .&. complement (powof2 - (1 :: Word64)))

type Align32_ArgT = (Word32, Word32)

type Align32_RetT = Word32

align32 :: Align32_ArgT -> Align32_RetT
align32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        x = Tup.sel1 __ds_var_0
      in
      let __ds_var_2 = __ds_var_1
          powof2 = Tup.sel2 __ds_var_1
        in ((x + (powof2 - (1 :: Word32))) .&. complement (powof2 - (1 :: Word32)))

type Vmode_is_blk_ArgT = Word32

type Vmode_is_blk_RetT = Bool

vmode_is_blk :: Vmode_is_blk_ArgT -> Vmode_is_blk_RetT
vmode_is_blk __ds_var_0 = let mode = __ds_var_0 in ((mode .&. (61440 :: Word32)) == (24576 :: Word32))

type Vmode_is_chr_ArgT = Word32

type Vmode_is_chr_RetT = Bool

vmode_is_chr :: Vmode_is_chr_ArgT -> Vmode_is_chr_RetT
vmode_is_chr __ds_var_0 = let mode = __ds_var_0 in ((mode .&. (61440 :: Word32)) == (8192 :: Word32))

type Vmode_is_dir_ArgT = Word32

type Vmode_is_dir_RetT = Bool

vmode_is_dir :: Vmode_is_dir_ArgT -> Vmode_is_dir_RetT
vmode_is_dir __ds_var_0 = let mode = __ds_var_0 in ((mode .&. (61440 :: Word32)) == (16384 :: Word32))

type Vmode_is_reg_ArgT = Word32

type Vmode_is_reg_RetT = Bool

vmode_is_reg :: Vmode_is_reg_ArgT -> Vmode_is_reg_RetT
vmode_is_reg __ds_var_0 = let mode = __ds_var_0 in ((mode .&. (61440 :: Word32)) == (32768 :: Word32))

type Linux_decode_device_new_ArgT = Word32

type Linux_decode_device_new_RetT = (Word32, Word32)

linux_decode_device_new :: Linux_decode_device_new_ArgT -> Linux_decode_device_new_RetT
linux_decode_device_new __ds_var_0
  = let val = __ds_var_0 in (((val .&. (1048320 :: Word32)) `shiftR` fromIntegral (8 :: Word32)), ((val .&. (255 :: Word32)) .|. ((val `shiftR` fromIntegral (12 :: Word32)) .&. (1048320 :: Word32))))

type Linux_decode_device_old_ArgT = Word16

type Linux_decode_device_old_RetT = (Word32, Word32)

linux_decode_device_old :: Linux_decode_device_old_ArgT -> Linux_decode_device_old_RetT
linux_decode_device_old __ds_var_0 = let val = __ds_var_0 in ((((fromIntegral val :: Word32) `shiftR` fromIntegral (8 :: Word32)) .&. (255 :: Word32)), ((fromIntegral val :: Word32) .&. (255 :: Word32)))

type Linux_encode_device_new_ArgT = VfsDevice

type Linux_encode_device_new_RetT = Word32

linux_encode_device_new :: Linux_encode_device_new_ArgT -> Linux_encode_device_new_RetT
linux_encode_device_new __ds_var_0
  = let dev = __ds_var_0 in
      let __ds_var_1 = vfs_device_inspect dev
          maj = Tup.sel1 (vfs_device_inspect dev)
        in
        let __ds_var_2 = __ds_var_1
            min = Tup.sel2 __ds_var_1
          in (((min .&. (255 :: Word32)) .|. (maj `shiftL` fromIntegral (8 :: Word32))) .|. ((min .&. complement (255 :: Word32)) `shiftL` fromIntegral (12 :: Word32)))

type Linux_encode_device_old_ArgT = VfsDevice

type Linux_encode_device_old_RetT = Word16

linux_encode_device_old :: Linux_encode_device_old_ArgT -> Linux_encode_device_old_RetT
linux_encode_device_old __ds_var_0
  = let dev = __ds_var_0 in
      let __ds_var_1 = vfs_device_inspect dev
          maj = Tup.sel1 (vfs_device_inspect dev)
        in
        let __ds_var_2 = __ds_var_1
            min = Tup.sel2 __ds_var_1
          in (u32_to_u16 maj `shiftL` fromIntegral ((8 :: Word16) .|. u32_to_u16 min))

type Linux_valid_old_dev_ArgT = VfsDevice

type Linux_valid_old_dev_RetT = Bool

linux_valid_old_dev :: Linux_valid_old_dev_ArgT -> Linux_valid_old_dev_RetT
linux_valid_old_dev __ds_var_0
  = let dev = __ds_var_0 in
      let __ds_var_1 = vfs_device_inspect dev
          maj = Tup.sel1 (vfs_device_inspect dev)
        in
        let __ds_var_2 = __ds_var_1
            min = Tup.sel2 __ds_var_1
          in ((maj < (256 :: Word32)) && (min < (256 :: Word32)))

type Wordarray_free'_ArgT a = R0 SysState (WordArray a)

type Wordarray_free'_RetT a = SysState

wordarray_free' :: Wordarray_free'_ArgT a -> Wordarray_free'_RetT a
wordarray_free' __ds_var_0
  = let __ds_var_2 = __ds_var_0
        ex = let R0{ex = __shallow_v53, obj = __shallow_v54} = __ds_var_0 in __shallow_v53
      in
      let __ds_var_1 = __ds_var_2
          obj = let R0{ex = __shallow_v55, obj = __shallow_v56} = __ds_var_2 in __shallow_v56
        in wordarray_free (ex, obj)

type Error_ArgT b a = b

type Error_RetT b a = V34 b a

error :: Error_ArgT b a -> Error_RetT b a
error __ds_var_0 = let b = __ds_var_0 in V34_Error b

type Safe_add32_ArgT = (Word32, Word32)

type Safe_add32_RetT = V34 () Word32

safe_add32 :: Safe_add32_ArgT -> Safe_add32_RetT
safe_add32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = Tup.sel1 __ds_var_0
      in
      let __ds_var_2 = __ds_var_1
          b = Tup.sel2 __ds_var_1
        in let r = (a + b) in if ((r < a) || (r < b)) then V34_Error () else V34_Success r

type Safe_add64_ArgT = (Word64, Word64)

type Safe_add64_RetT = V34 () Word64

safe_add64 :: Safe_add64_ArgT -> Safe_add64_RetT
safe_add64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = Tup.sel1 __ds_var_0
      in
      let __ds_var_2 = __ds_var_1
          b = Tup.sel2 __ds_var_1
        in let r = (a + b) in if ((r < a) || (r < b)) then V34_Error () else V34_Success r

type Safe_sub32_ArgT = (Word32, Word32)

type Safe_sub32_RetT = V34 () Word32

safe_sub32 :: Safe_sub32_ArgT -> Safe_sub32_RetT
safe_sub32 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = Tup.sel1 __ds_var_0
      in
      let __ds_var_2 = __ds_var_1
          b = Tup.sel2 __ds_var_1
        in let r = (a - b) in if (r > a) then V34_Error () else V34_Success r

type Safe_sub64_ArgT = (Word64, Word64)

type Safe_sub64_RetT = V34 () Word64

safe_sub64 :: Safe_sub64_ArgT -> Safe_sub64_RetT
safe_sub64 __ds_var_0
  = let __ds_var_1 = __ds_var_0
        a = Tup.sel1 __ds_var_0
      in
      let __ds_var_2 = __ds_var_1
          b = Tup.sel2 __ds_var_1
        in let r = (a - b) in if (r > a) then V34_Error () else V34_Success r

type Success_ArgT a b = a

type Success_RetT a b = V34 b a

success :: Success_ArgT a b -> Success_RetT a b
success __ds_var_0 = let a = __ds_var_0 in V34_Success a

type Wordarray_clone_ArgT a = (SysState, WordArray a)

type Wordarray_clone_RetT a = V34 SysState (SysState, WordArray a)

wordarray_clone :: Wordarray_clone_ArgT a -> Wordarray_clone_RetT a
wordarray_clone __ds_var_0
  = let __ds_var_1 = __ds_var_0
        ex = Tup.sel1 __ds_var_0
      in
      let __ds_var_2 = __ds_var_1
          src = Tup.sel2 __ds_var_1
        in
        let size = wordarray_length src in
          let __ds_var_3 = wordarray_create (ex, size) in
            case __ds_var_3 of
              V34_Error ex57 -> V34_Error ex57
              __ds_var_4 -> let __ds_var_5 = (\ (V34_Success __shallow_v58) -> __shallow_v58) __ds_var_4 in
                              let __ds_var_6 = __ds_var_5
                                  ex59 = Tup.sel1 __ds_var_5
                                in
                                let __ds_var_7 = __ds_var_6
                                    dest = Tup.sel2 __ds_var_6
                                  in V34_Success (ex59, wordarray_copy (dest, src, (0 :: Word32), (0 :: Word32), size))

type Wordarray_get_bounded_ArgT a = (WordArray a, Word32)

type Wordarray_get_bounded_RetT a = V34 () a

wordarray_get_bounded :: Wordarray_get_bounded_ArgT a -> Wordarray_get_bounded_RetT a
wordarray_get_bounded __ds_var_0
  = let __ds_var_1 = __ds_var_0
        arr = Tup.sel1 __ds_var_0
      in
      let __ds_var_2 = __ds_var_1
          idx = Tup.sel2 __ds_var_1
        in if (idx < wordarray_length arr) then V34_Success (wordarray_get (arr, idx)) else V34_Error ()

type OptionToResult_ArgT a = V33 () a

type OptionToResult_RetT a = V34 () a

optionToResult :: OptionToResult_ArgT a -> OptionToResult_RetT a
optionToResult __ds_var_0
  = case __ds_var_0 of
      V33_None __ds_var_1 -> let __ds_var_3 = __ds_var_1 in V34_Error ()
      __ds_var_2 -> let a = (\ (V33_Some __shallow_v60) -> __shallow_v60) __ds_var_2 in V34_Success a

type ResultToOption_ArgT e a = V34 e a

type ResultToOption_RetT e a = V33 () a

resultToOption :: ResultToOption_ArgT e a -> ResultToOption_RetT e a
resultToOption __ds_var_0
  = case __ds_var_0 of
      V34_Error __ds_var_1 -> let __ds_var_3 = __ds_var_1 in V33_None ()
      __ds_var_2 -> let a = (\ (V34_Success __shallow_v61) -> __shallow_v61) __ds_var_2 in V33_Some a

type Obj_id_inode_mk_ArgT = Word32

type Obj_id_inode_mk_RetT = Word64

obj_id_inode_mk :: Obj_id_inode_mk_ArgT -> Obj_id_inode_mk_RetT
obj_id_inode_mk __ds_var_0 = let ino = __ds_var_0 in (((fromIntegral ino :: Word64) `shiftL` fromIntegral (32 :: Word64)) .|. ((fromIntegral (0 :: Word8) :: Word64) `shiftL` fromIntegral (29 :: Word64)))

type Obj_id_data_mk_ArgT = (Word32, Word32)

type Obj_id_data_mk_RetT = Word64

obj_id_data_mk :: Obj_id_data_mk_ArgT -> Obj_id_data_mk_RetT
obj_id_data_mk __ds_var_0
  = let __ds_var_1 = __ds_var_0
        ino = Tup.sel1 __ds_var_0
      in
      let __ds_var_2 = __ds_var_1
          blk = Tup.sel2 __ds_var_1
        in ((obj_id_inode_mk ino .|. ((fromIntegral (1 :: Word8) :: Word64) `shiftL` fromIntegral (29 :: Word64))) .|. (fromIntegral blk :: Word64))

type U64_to_TimeSpec_ArgT = Word64

type U64_to_TimeSpec_RetT = R27 Word32 Word32

u64_to_TimeSpec :: U64_to_TimeSpec_ArgT -> U64_to_TimeSpec_RetT
u64_to_TimeSpec __ds_var_0 = let v = __ds_var_0 in R27{tv_sec = u64_to_u32 (v `shiftR` fromIntegral (32 :: Word64)), tv_nsec = u64_to_u32 v}

type Vfs_inode_put_tuple_ArgT = (SysState, R20 VfsInodeAbstract (R21 Word32))

type Vfs_inode_put_tuple_RetT = SysState

vfs_inode_put_tuple :: Vfs_inode_put_tuple_ArgT -> Vfs_inode_put_tuple_RetT
vfs_inode_put_tuple __ds_var_0
  = let __ds_var_1 = __ds_var_0
        ex = Tup.sel1 __ds_var_0
      in
      let __ds_var_2 = __ds_var_1
          inode = Tup.sel2 __ds_var_1
        in vfs_inode_put R3{ex = ex, inode = inode}

type Vfs_inode_add_bytes_ArgT = (R20 VfsInodeAbstract (R21 Word32), Word64)

type Vfs_inode_add_bytes_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_add_bytes :: Vfs_inode_add_bytes_ArgT -> Vfs_inode_add_bytes_RetT
vfs_inode_add_bytes __ds_var_0
  = let __ds_var_1 = __ds_var_0
        inode = Tup.sel1 __ds_var_0
      in
      let __ds_var_2 = __ds_var_1
          bytes = Tup.sel2 __ds_var_1
        in
        let inode62 = vfs_inode_lock inode in
          let curblocks = vfs_inode_get_blocks inode62 in
            let newblocks = (curblocks + (bytes `shiftR` fromIntegral (9 :: Word64))) in
              let inode63 = vfs_inode_set_blocks (inode62, newblocks) in
                let bytes64 = u64_to_u16 (bytes .&. (511 :: Word64)) in
                  let curbytes = vfs_inode_get_bytes inode63 in
                    let newbytes = (curbytes + bytes64) in
                      let inode65 = vfs_inode_set_bytes (inode63, newbytes) in
                        if (newbytes >= (512 :: Word16)) then
                          let inode66 = vfs_inode_set_blocks (inode65, (newblocks + (1 :: Word64))) in let inode67 = vfs_inode_set_bytes (inode66, (newbytes - (512 :: Word16))) in vfs_inode_unlock inode67 else
                          vfs_inode_unlock inode65

type Vfs_inode_sub_bytes_ArgT = (R20 VfsInodeAbstract (R21 Word32), Word64)

type Vfs_inode_sub_bytes_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_inode_sub_bytes :: Vfs_inode_sub_bytes_ArgT -> Vfs_inode_sub_bytes_RetT
vfs_inode_sub_bytes __ds_var_0
  = let __ds_var_1 = __ds_var_0
        inode = Tup.sel1 __ds_var_0
      in
      let __ds_var_2 = __ds_var_1
          bytes = Tup.sel2 __ds_var_1
        in
        let inode68 = vfs_inode_lock inode in
          let curblocks = vfs_inode_get_blocks inode68 in
            let newblocks = (curblocks - (bytes `shiftR` fromIntegral (9 :: Word64))) in
              let inode69 = vfs_inode_set_blocks (inode68, newblocks) in
                let bytes70 = u64_to_u16 (bytes .&. (511 :: Word64)) in
                  let curbytes = vfs_inode_get_bytes inode69 in
                    let newbytes = (curbytes - bytes70) in
                      let inode71 = vfs_inode_set_bytes (inode69, newbytes) in
                        if (curbytes < bytes70) then
                          let inode72 = vfs_inode_set_blocks (inode71, (newblocks - (1 :: Word64))) in let inode73 = vfs_inode_set_bytes (inode72, (newbytes + (512 :: Word16))) in vfs_inode_unlock inode73 else
                          vfs_inode_unlock inode71

type Vfs_rename_get_dest_dir2_ArgT = V18 (R20 VfsInodeAbstract (R21 Word32)) (R19 (R20 VfsInodeAbstract (R21 Word32)) (R20 VfsInodeAbstract (R21 Word32)))

type Vfs_rename_get_dest_dir2_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_rename_get_dest_dir2 :: Vfs_rename_get_dest_dir2_ArgT -> Vfs_rename_get_dest_dir2_RetT
vfs_rename_get_dest_dir2 __ds_var_0
  = let dirs = __ds_var_0 in
      case dirs of
        V18_SrcDest both -> let R19{src_dir = __shallow_v74, dest_dir = __shallow_v75} = both in __shallow_v75
        __ds_var_1 -> let dest_dir = (\ (V18_Dest __shallow_v76) -> __shallow_v76) __ds_var_1 in dest_dir

type Copy_n_ArgT a = R15 a Word32 (WordArray a)

type Copy_n_RetT a = (a, Word32)

copy_n :: Copy_n_ArgT a -> Copy_n_RetT a
copy_n __ds_var_0
  = let __ds_var_2 = __ds_var_0
        elem = let R15{elem = __shallow_v77, acc = __shallow_v78, obsv = __shallow_v79} = __ds_var_0 in __shallow_v77
      in
      let __ds_var_3 = __ds_var_2
          idx = let R15{elem = __shallow_v80, acc = __shallow_v81, obsv = __shallow_v82} = __ds_var_2 in __shallow_v81
        in
        let __ds_var_1 = __ds_var_3
            afrm = let R15{elem = __shallow_v83, acc = __shallow_v84, obsv = __shallow_v85} = __ds_var_3 in __shallow_v85
          in (wordarray_get (afrm, idx), (idx + (1 :: Word32)))

type Vfs_rename_get_dest_dir_ArgT =
     R9 (V18 (R20 VfsInodeAbstract (R21 Word32)) (R19 (R20 VfsInodeAbstract (R21 Word32)) (R20 VfsInodeAbstract (R21 Word32)))) (R20 VfsInodeAbstract (R21 Word32)) (WordArray Word8)
       (V33 () (R20 VfsInodeAbstract (R21 Word32)))
       (WordArray Word8)

type Vfs_rename_get_dest_dir_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_rename_get_dest_dir :: Vfs_rename_get_dest_dir_ArgT -> Vfs_rename_get_dest_dir_RetT
vfs_rename_get_dest_dir __ds_var_0
  = let ctx = __ds_var_0 in
      let __ds_var_1 = let R9{dirs = __shallow_v86, src_inode = __shallow_v87, src_name = __shallow_v88, dest_inode = __shallow_v89, dest_name = __shallow_v90} = ctx in __shallow_v86 in
        case __ds_var_1 of
          V18_SrcDest both -> let R19{src_dir = __shallow_v91, dest_dir = __shallow_v92} = both in __shallow_v92
          __ds_var_2 -> let dest_dir = (\ (V18_Dest __shallow_v93) -> __shallow_v93) __ds_var_2 in dest_dir

type Vfs_rename_get_src_dir_ArgT =
     R9 (V18 (R20 VfsInodeAbstract (R21 Word32)) (R19 (R20 VfsInodeAbstract (R21 Word32)) (R20 VfsInodeAbstract (R21 Word32)))) (R20 VfsInodeAbstract (R21 Word32)) (WordArray Word8)
       (V33 () (R20 VfsInodeAbstract (R21 Word32)))
       (WordArray Word8)

type Vfs_rename_get_src_dir_RetT = R20 VfsInodeAbstract (R21 Word32)

vfs_rename_get_src_dir :: Vfs_rename_get_src_dir_ArgT -> Vfs_rename_get_src_dir_RetT
vfs_rename_get_src_dir __ds_var_0
  = let ctx = __ds_var_0 in
      let __ds_var_1 = let R9{dirs = __shallow_v94, src_inode = __shallow_v95, src_name = __shallow_v96, dest_inode = __shallow_v97, dest_name = __shallow_v98} = ctx in __shallow_v94 in
        case __ds_var_1 of
          V18_SrcDest both -> let R19{src_dir = __shallow_v99, dest_dir = __shallow_v100} = both in __shallow_v99
          __ds_var_2 -> let dest_dir = (\ (V18_Dest __shallow_v101) -> __shallow_v101) __ds_var_2 in dest_dir

type Buf_length_ArgT = R8 (WordArray Word8) Word32

type Buf_length_RetT = Word32

buf_length :: Buf_length_ArgT -> Buf_length_RetT
buf_length __ds_var_0 = let buf = __ds_var_0 in wordarray_length (let R8{data_ = __shallow_v102, bound = __shallow_v103} = buf in __shallow_v102)

type Buf_memset_ArgT = (R8 (WordArray Word8) Word32, Word32, Word32, Word8)

type Buf_memset_RetT = R8 (WordArray Word8) Word32

buf_memset :: Buf_memset_ArgT -> Buf_memset_RetT
buf_memset __ds_var_0
  = let __ds_var_2 = __ds_var_0
        __ds_var_1 = Tup.sel1 __ds_var_0
      in
      let __ds_var_3 = __ds_var_2
          frm = Tup.sel2 __ds_var_2
        in
        let __ds_var_4 = __ds_var_3
            len = Tup.sel3 __ds_var_3
          in
          let __ds_var_5 = __ds_var_4
              val = Tup.sel4 __ds_var_4
            in
            let buf = __ds_var_1
                data_ = let R8{data_ = __shallow_v104, bound = __shallow_v105} = __ds_var_1 in __shallow_v104
              in
              let frm106 = if (frm < let R8{data_ = __shallow_v107, bound = __shallow_v108} = buf in __shallow_v108) then frm else let R8{data_ = __shallow_v109, bound = __shallow_v110} = buf in __shallow_v110 in
                let len111
                      = if ((frm106 + len) < let R8{data_ = __shallow_v112, bound = __shallow_v113} = buf in __shallow_v113) then len else
                          (let R8{data_ = __shallow_v114, bound = __shallow_v115} = buf in __shallow_v115 - frm106)
                  in let data116 = wordarray_set (data_, frm106, len111, val) in (buf :: R8 (WordArray Word8) Word32){data_ = data116}

type Buf_free_ArgT = (SysState, R8 (WordArray Word8) Word32)

type Buf_free_RetT = SysState

buf_free :: Buf_free_ArgT -> Buf_free_RetT
buf_free __ds_var_0
  = let __ds_var_2 = __ds_var_0
        ex = Tup.sel1 __ds_var_0
      in
      let __ds_var_3 = __ds_var_2
          __ds_var_1 = Tup.sel2 __ds_var_2
        in
        let __ds_var_4 = __ds_var_1
            data_ = let R8{data_ = __shallow_v117, bound = __shallow_v118} = __ds_var_1 in __shallow_v117
          in
          let buf = __ds_var_4
              bound = let R8{data_ = __shallow_v119, bound = __shallow_v120} = __ds_var_4 in __shallow_v120
            in let ex121 = wordarray_free (ex, data_) in freeBuffer (ex121, buf)

type Buf_create_ArgT = (SysState, Word32)

type Buf_create_RetT = V34 SysState (SysState, R8 (WordArray Word8) Word32)

buf_create :: Buf_create_ArgT -> Buf_create_RetT
buf_create __ds_var_0
  = let __ds_var_1 = __ds_var_0
        ex = Tup.sel1 __ds_var_0
      in
      let __ds_var_2 = __ds_var_1
          buffer_length = Tup.sel2 __ds_var_1
        in
        let __ds_var_3 = wordarray_create (ex, buffer_length) in
          case __ds_var_3 of
            V34_Error ex122 -> V34_Error ex122
            __ds_var_4 -> let __ds_var_5 = (\ (V34_Success __shallow_v123) -> __shallow_v123) __ds_var_4 in
                            let __ds_var_6 = __ds_var_5
                                ex124 = Tup.sel1 __ds_var_5
                              in
                              let __ds_var_7 = __ds_var_6
                                  data_ = Tup.sel2 __ds_var_6
                                in
                                let __ds_var_8 = newBuffer ex124 in
                                  case __ds_var_8 of
                                    V34_Success __ds_var_9 -> let __ds_var_11 = __ds_var_9
                                                                  ex125 = Tup.sel1 __ds_var_9
                                                                in
                                                                let __ds_var_12 = __ds_var_11
                                                                    buf = Tup.sel2 __ds_var_11
                                                                  in V34_Success (ex125, ((buf :: R8 (WordArray Word8) Word32){data_ = data_} :: R8 (WordArray Word8) Word32){bound = buffer_length})
                                    __ds_var_10 -> let ex126 = (\ (V34_Error __shallow_v127) -> __shallow_v127) __ds_var_10 in V34_Error (wordarray_free (ex126, data_))

type Read_block_ArgT = (SysState, R22 FsopState MountState OstoreState, R20 VfsInodeAbstract (R21 Word32), R8 (WordArray Word8) Word32, Word64)

type Read_block_RetT = ((SysState, R22 FsopState MountState OstoreState, R8 (WordArray Word8) Word32), V34 Word32 ())

read_block :: Read_block_ArgT -> Read_block_RetT
read_block __ds_var_0
  = let __ds_var_2 = __ds_var_0
        ex = Tup.sel1 __ds_var_0
      in
      let __ds_var_3 = __ds_var_2
          __ds_var_1 = Tup.sel2 __ds_var_2
        in
        let __ds_var_4 = __ds_var_3
            vnode = Tup.sel3 __ds_var_3
          in
          let __ds_var_5 = __ds_var_4
              buf = Tup.sel4 __ds_var_4
            in
            let __ds_var_6 = __ds_var_5
                block = Tup.sel5 __ds_var_5
              in
              let fs_st = __ds_var_1
                  ostore_st = let R22{fsop_st = __shallow_v128, mount_st = __shallow_v129, ostore_st = __shallow_v130} = __ds_var_1 in __shallow_v130
                in
                let oid = obj_id_data_mk (vfs_inode_get_ino vnode, u64_to_u32 block) in
                  let __ds_var_7 = ostore_read (ex, let R22{fsop_st = __shallow_v131, mount_st = __shallow_v132, ostore_st = __shallow_v133} = fs_st in __shallow_v132, ostore_st, oid) in
                    let __ds_var_9 = __ds_var_7
                        __ds_var_8 = Tup.sel1 __ds_var_7
                      in
                      let __ds_var_10 = __ds_var_9
                          r = Tup.sel2 __ds_var_9
                        in
                        let __ds_var_11 = __ds_var_8
                            ex134 = Tup.sel1 __ds_var_8
                          in
                          let __ds_var_12 = __ds_var_11
                              ostore_st135 = Tup.sel2 __ds_var_11
                            in
                            let fs_st136 = (fs_st :: R22 FsopState MountState OstoreState){ostore_st = ostore_st135} in
                              case r of
                                V34_Error e -> if (e == (2 :: Word32)) then let buf137 = buf_memset (buf, (0 :: Word32), (4096 :: Word32), (0 :: Word8)) in ((ex134, fs_st136, buf137), V34_Success ()) else
                                                 ((ex134, fs_st136, buf), V34_Error e)
                                __ds_var_13 -> let __ds_var_14 = (\ (V34_Success __shallow_v138) -> __shallow_v138) __ds_var_13 in
                                                 let obj = __ds_var_14
                                                     ounion
                                                       = let R28{magic = __shallow_v139, crc = __shallow_v140, sqnum = __shallow_v141, offs = __shallow_v142, len = __shallow_v143, trans = __shallow_v144,
                                                                 otype = __shallow_v145, ounion = __shallow_v146}
                                                               = __ds_var_14
                                                           in __shallow_v146
                                                   in
                                                   let __ds_var_15 = extract_data_from_union (ex134, ounion) in
                                                     case __ds_var_15 of
                                                       V34_Error ex147 -> let __ds_var_17 = cogent_assert False in let ex148 = freeObj (ex147, obj) in ((ex148, fs_st136, buf), V34_Error (22 :: Word32))
                                                       __ds_var_16 -> let __ds_var_17 = (\ (V34_Success __shallow_v149) -> __shallow_v149) __ds_var_16 in
                                                                        let __ds_var_18 = __ds_var_17
                                                                            ex150 = Tup.sel1 __ds_var_17
                                                                          in
                                                                          let __ds_var_19 = __ds_var_18
                                                                              od = Tup.sel2 __ds_var_18
                                                                            in
                                                                            let ex151 = freeObj (ex150, obj) in
                                                                              let size = wordarray_length (let R30{id = __shallow_v152, odata = __shallow_v153} = od in __shallow_v153) in
                                                                                if (size > (4096 :: Word32)) then
                                                                                  let __ds_var_20 = cogent_debug "bad object data" in
                                                                                    let ex154 = deep_freeObjData (ex151, od) in ((ex154, fs_st136, buf), V34_Error (22 :: Word32))
                                                                                  else
                                                                                  let buf155 = buf
                                                                                      data_ = let R8{data_ = __shallow_v156, bound = __shallow_v157} = buf in __shallow_v156
                                                                                    in
                                                                                    let data158
                                                                                          = wordarray_copy
                                                                                              (data_, let R30{id = __shallow_v159, odata = __shallow_v160} = od in __shallow_v160, (0 :: Word32), (0 :: Word32), size)
                                                                                      in
                                                                                      let buf161 = (buf155 :: R8 (WordArray Word8) Word32){data_ = data158} in
                                                                                        let buf162 = buf_memset (buf161, size, ((4096 :: Word32) - size), (0 :: Word8)) in
                                                                                          let ex163 = deep_freeObjData (ex151, od) in ((ex163, fs_st136, buf162), V34_Success ())

type Fsop_readpage_ArgT = R7 SysState (R22 FsopState MountState OstoreState) (R20 VfsInodeAbstract (R21 Word32)) Word64 (R8 (WordArray Word8) Word32)

type Fsop_readpage_RetT = (R6 SysState (R22 FsopState MountState OstoreState) (R20 VfsInodeAbstract (R21 Word32)) (R8 (WordArray Word8) Word32), V34 Word32 ())

fsop_readpage :: Fsop_readpage_ArgT -> Fsop_readpage_RetT
fsop_readpage __ds_var_0
  = let __ds_var_2 = __ds_var_0
        ex = let R7{ex = __shallow_v164, fs_st = __shallow_v165, vnode = __shallow_v166, block = __shallow_v167, addr = __shallow_v168} = __ds_var_0 in __shallow_v164
      in
      let __ds_var_3 = __ds_var_2
          fs_st = let R7{ex = __shallow_v169, fs_st = __shallow_v170, vnode = __shallow_v171, block = __shallow_v172, addr = __shallow_v173} = __ds_var_2 in __shallow_v170
        in
        let __ds_var_4 = __ds_var_3
            vnode = let R7{ex = __shallow_v174, fs_st = __shallow_v175, vnode = __shallow_v176, block = __shallow_v177, addr = __shallow_v178} = __ds_var_3 in __shallow_v176
          in
          let __ds_var_5 = __ds_var_4
              block = let R7{ex = __shallow_v179, fs_st = __shallow_v180, vnode = __shallow_v181, block = __shallow_v182, addr = __shallow_v183} = __ds_var_4 in __shallow_v182
            in
            let __ds_var_1 = __ds_var_5
                addr = let R7{ex = __shallow_v184, fs_st = __shallow_v185, vnode = __shallow_v186, block = __shallow_v187, addr = __shallow_v188} = __ds_var_5 in __shallow_v188
              in
              let size = vfs_inode_get_size vnode in
                let limit = (size `shiftR` fromIntegral (fromIntegral (12 :: Word32) :: Word64)) in
                  if (block > limit) then let addr189 = buf_memset (addr, (0 :: Word32), (4096 :: Word32), (0 :: Word8)) in (R6{ex = ex, fs_st = fs_st, vnode = vnode, addr = addr189}, V34_Error (2 :: Word32)) else
                    if ((block == limit) && ((size `mod` (fromIntegral (4096 :: Word32) :: Word64)) == (0 :: Word64))) then (R6{ex = ex, fs_st = fs_st, vnode = vnode, addr = addr}, V34_Success ()) else
                      let __ds_var_6 = read_block (ex, fs_st, vnode, addr, block) in
                        let __ds_var_8 = __ds_var_6
                            __ds_var_7 = Tup.sel1 __ds_var_6
                          in
                          let __ds_var_9 = __ds_var_8
                              r = Tup.sel2 __ds_var_8
                            in
                            let __ds_var_10 = __ds_var_7
                                ex190 = Tup.sel1 __ds_var_7
                              in
                              let __ds_var_11 = __ds_var_10
                                  fs_st191 = Tup.sel2 __ds_var_10
                                in
                                let __ds_var_12 = __ds_var_11
                                    addr192 = Tup.sel3 __ds_var_11
                                  in (R6{ex = ex190, fs_st = fs_st191, vnode = vnode, addr = addr192}, r)

type Buf_bound_ArgT = R8 (WordArray Word8) Word32

type Buf_bound_RetT = Word32

buf_bound :: Buf_bound_ArgT -> Buf_bound_RetT
buf_bound __ds_var_0 = let buf = __ds_var_0 in let R8{data_ = __shallow_v193, bound = __shallow_v194} = buf in __shallow_v194

type Buf_set_bound_ArgT = (R8 (WordArray Word8) Word32, Word32)

type Buf_set_bound_RetT = V34 (R8 (WordArray Word8) Word32) (R8 (WordArray Word8) Word32)

buf_set_bound :: Buf_set_bound_ArgT -> Buf_set_bound_RetT
buf_set_bound __ds_var_0
  = let __ds_var_1 = __ds_var_0
        buf = Tup.sel1 __ds_var_0
      in
      let __ds_var_2 = __ds_var_1
          newbound = Tup.sel2 __ds_var_1
        in
        let len = buf_length buf in
          if (newbound > len) then V34_Error buf else
            let buf195 = buf
                bound = let R8{data_ = __shallow_v196, bound = __shallow_v197} = buf in __shallow_v197
              in V34_Success (buf195 :: R8 (WordArray Word8) Word32){bound = newbound}

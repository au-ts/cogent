/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#ifndef ABSTRACT_H__
#define ABSTRACT_H__

#include <adt.h>

struct Ext2State {
	void* priv;
	struct semaphore iop_lock;
	// struct semaphore sop_lock;
	// struct semaphore aop_lock;
	struct super_block* sb;
};

/* include vfs.h */
typedef void VfsIWriteResult;
typedef void VfsIWriteArgs;

typedef void VfsISeekResult;
typedef void VfsISeekArgs;

typedef void VfsIReadlinkResult;
typedef void VfsIReadlinkArgs;

typedef void VfsIReadResult;
typedef void VfsIReadArgs;

typedef void VfsIPutLinkResult;
typedef void VfsIPutLinkArgs;

typedef void VfsIOpenResult;
typedef void VfsIOpenArgs;

typedef void VfsIMmapResult;
typedef void VfsIMmapArgs;

typedef void VfsIFsyncResult;
typedef void VfsIFsyncArgs;

typedef void VfsIFollowLinkResult;
typedef void VfsIFollowLinkArgs;

typedef void VfsISetAttrResult;
typedef void VfsISetAttrArgs;

// really all of type `enum untyped_func_enum' but can't forward declare enums (because size unknown)
struct cogent_inode_operations {
	int create; // Option ((ExState, FsState, VfsInode, CString!, VfsMode) -> RR (ExState, FsState, VfsInode) VfsInode U32),
  	int link; // Option ((ExState, FsState, VfsInode, VfsInode, CString!) -> RR (ExState, FsState, VfsInode, VfsInode) () U32),
	int unlink; // Option ((ExState, FsState, VfsInode, VfsInode, CString!) -> RR (ExState, FsState, VfsInode, VfsInode) () U32),
	int symlink; // Option ((ExState, FsState, VfsInode, CString!) -> RR (ExState, FsState, VfsInode) VfsInode U32),
	int mkdir; // Option ((ExState, FsState, VfsInode, CString!, VfsMode) -> RR (ExState, FsState, VfsInode) VfsInode U32),
	int rmdir; // Option ((ExState, FsState, VfsInode, VfsInode, CString!) -> RR (ExState, FsState, VfsInode, VfsInode) () U32),
	int rename; // Option ((ExState, FsState, VfsRenameContext) -> RR (ExState, FsState, VfsRenameContext) () U32),
	int mknod; // Option ((ExState, FsState, VfsInode, CString!, VfsMode, #VfsDevice) -> RR (ExState, FsState, VfsInode) VfsInode U32),

	int readlink; // Option (VfsIReadlinkArgs -> VfsIReadlinkResult),
	int followlink; // Option (VfsIFollowLinkArgs -> VfsIFollowLinkResult),
	int putlink; // Option (VfsIPutLinkArgs -> VfsIPutLinkResult)
};

struct cogent_file_operations {
	int iterate; // Option ((#{ex: ExState, state: FsState, parent_inode: VfsInode, dirctx: VfsDirContext}) -> RR #{ex: ExState, state: FsState, parent_inode: VfsInode, dirctx: VfsDirContext} () U32),

	// the rest are bools
	int llseek; // Option (VfsISeekArgs -> VfsISeekResult),
	int open; // Option (VfsIOpenArgs -> VfsIOpenResult),
	int mmap; // Option (VfsIMmapArgs -> VfsIMmapResult),
	int fsync; // Option (VfsIFsyncArgs -> VfsIFsyncResult),

	// these two are special -- they are essentially bools; if we have these set,
	// then we setup a LOT more Linux VFS function pointers (ie read_iter, etc).
	// we also setup address_space_operations if one of these are set.
	//
	int read; // Option (VfsIReadArgs -> VfsIReadResult),
	int write; // Option (VfsIWriteArgs -> VfsIWriteResult)
};
/* end include vfs.h */

struct VfsInodeAbstract {
	struct inode inode_lin;

	// these ones, as opposed to the struct inode ones,
	// NOT const, they are ours to modify. each inode
	// gets their own set.
	//
	// we don't cast directly since the inode ops may
	// point elsewhere and we don't want to overwrite them.
	struct inode_operations iops;
	struct cogent_inode_operations cogent_iops; // this is NOT a cogent type but records its values (otherwise recursive types?)

	struct file_operations fops;
	struct cogent_file_operations cogent_fops;
};

typedef struct VfsInodeAbstract VfsInodeAbstract;

typedef struct buffer_head OSBuffer;
typedef struct Ext2State ExState;
typedef struct Ext2State Ext2State;
typedef struct dir_context OSDirContext;
typedef dev_t VfsDevice;

typedef struct ubi_volume_desc UbiVol;

typedef struct page OSPage;

typedef struct page OSPageBuffer;

typedef struct address_space VfsMemoryMap;

typedef void File;

typedef void VfsStat;
typedef void VfsIattr;

#define likely(x)       __builtin_expect(!!(x), 1)
#define unlikely(x)     __builtin_expect(!!(x), 0)

void *cogent_malloc(size_t sz);
void *cogent_calloc(int n, size_t sz);
void cogent_free(void *s);
void cogent_malloc_freeall(void);

#endif  /* ABSTRACT_H__ */

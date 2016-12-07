/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */
/*
 * abstract.h
 * This file contains the abstract data type definitions.
 */

#ifndef _ABSTRACT_H
#define _ABSTRACT_H

#include <linux_hdrs.h>                /* In cogent/plat/linux/ */

#include "abstract_vfs.h"

/* Wrapper state, that needs to be carried around in addition the
   FS State(filesystem state)
*/
struct WrapperState {
        void *priv;
        struct semaphore iop_lock;
        struct super_block *sb;
};

typedef struct WrapperState ExState; /* External State */
typedef struct WrapperState SkelfsState;


/* Abstract inode structure */
struct VfsInodeAbstract {
        struct inode inode;

        struct inode_operations inodeops;
        struct cogent_inode_operations cogent_inodeops;

        struct file_operations fileops;
        struct cogent_file_operations cogent_fileops;
};

typedef struct VfsInodeAbstract VfsInodeAbstract;

/* typedefs for convenience. TODO: Cleanup???*/
typedef struct dir_context OSDirContext;
typedef struct buffer_head OSBuffer;
typedef struct page OSPage;
typedef struct page OSPageBuffer;
typedef struct address_space VfsMemoryMap;
typedef struct ubi_volume_desc UbiVol;

typedef void File;
typedef void VfsStat;
typedef void VfsIattr;

#define likely(x)       __builtin_expect(!!(x), 1)
#define unlikely(x)     __builtin_expect(!!(x), 0)


#endif  /* _ABSTRACT_H */

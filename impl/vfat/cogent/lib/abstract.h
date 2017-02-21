/*
 * Copyright 2017, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#ifndef _ABSTRACT_H
#define _ABSTRACT_H

#define likely(x)       __builtin_expect(!!(x), 1)
#define unlikely(x)     __builtin_expect(!!(x), 0)

typedef struct super_block *Superblock;
typedef void *ExState;
typedef struct inode *VfsInode;
typedef void *ErrPtr;
typedef struct dentry *VfsDentry;

#endif  /* _ABSTRACT_H */

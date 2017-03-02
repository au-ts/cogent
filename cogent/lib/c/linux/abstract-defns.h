/*
 * Copyright 2017, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */
/*
 * abstract-defns.h
 * This file contains the abstract data type definitions that all linux kernel
 * modules will need.
 */

#ifndef ABSTRACT_DEFNS_H_
#define ABSTRACT_DEFNS_H_

typedef int Int;
typedef unsigned int UInt;
typedef u8 * U8Ptr;

typedef __le16 LE16;
typedef __le32 LE32;
typedef __le64 LE64;
typedef __be16 BE16;
typedef __be32 BE32;
typedef __be64 BE64;

typedef rwlock_t RWLock;
typedef kuid_t KUID;
typedef kgid_t KGID;
typedef spinlock_t SpinLock;

typedef struct rw_semaphore RWSemaphore;
typedef struct mutex Mutex;
typedef struct list_head ListHead;
typedef struct quota DQuota;
typedef struct buffer_head BufferHead;
typedef struct buffer_head * BufferHeadPtr;
typedef struct percpu_counter PerCPUCounter;
typedef struct blockgroup_lock BlockGroupLock;
typedef struct rb_root RBRoot;
typedef struct mb_cache MBCache;
typedef struct super_block VfsSuperBlock;
typedef struct inode Inode;
typedef struct dir_context DirContext;
typedef struct page Page;
typedef struct page PageBuffer;
typedef struct address_space AddressSpace;

typedef struct ubi_volume_desc UbiVolDesc;

#endif  /* ABSTRACT_DEFNS_H_ */

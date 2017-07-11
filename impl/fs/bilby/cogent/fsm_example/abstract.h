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

// #include <adt.h>

struct WrapperState {
    void* priv; // FIXME: unboxed?
    struct semaphore lock;
    struct super_block* sb;
};

typedef struct inode VfsInodeAbstract;
typedef struct kstat VfsStat;
typedef struct iattr VfsIattr;

typedef struct buffer_head OSBuffer;
typedef struct WrapperState SysState;
typedef struct WrapperState WrapperState;
typedef struct dir_context OSDirContext;
typedef struct page OSPageBuffer;
typedef struct address_space VfsMemoryMap;
typedef struct page OSPage;

typedef struct ubi_volume_desc UbiVol;
typedef struct ubi_volume_info UbiVolInfo;
typedef struct ubi_device_info UbiDevInfo;
#endif /* !ABSTRACT_H__ */

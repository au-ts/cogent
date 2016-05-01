/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#ifndef _WRAP_LINUX_H_
# define _WRAP_LINUX_H_

#include <asm/div64.h>
#include <linux/statfs.h>
#include <linux/fs.h>
#include <linux/err.h>
#include <linux/slab.h>
#include <linux/vmalloc.h>
#include <linux/mtd/ubi.h>
#include <linux/pagemap.h>
#include <linux/backing-dev.h>
#include <linux/crc32.h>

#define kmalloc(sz) kmalloc(sz, GFP_NOFS)
#define krealloc(p,sz) krealloc(p, sz, GFP_NOFS)
#define kzalloc(sz) kzalloc(sz, GFP_NOFS)

struct wrapper_data {
        struct semaphore lock;
        struct backing_dev_info bdi;
};

static inline void wrapper_init(struct wrapper_data *wd)
{
        sema_init(&wd->lock, 1);
}

extern const struct inode_operations bilbyfs_dir_inode_operations;
extern const struct inode_operations bilbyfs_file_inode_operations;
extern const struct inode_operations bilbyfs_symlink_inode_operations;
extern const struct file_operations bilbyfs_file_operations;
extern const struct file_operations bilbyfs_dir_operations;
extern const struct address_space_operations bilbyfs_file_address_operations;

#endif /* _WRAP_LINUX_H_ */

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

#include <adt.h>

#define ext2fs_assert(v) BUG_ON(!(v))

#define ext2fs_err(...) \
        printk(KERN_ERR __VA_ARGS__)

#define ext2fs_msg(...) \
        printk(KERN_INFO __VA_ARGS__)

#ifndef EXT2FS_DEBUG
#define ext2fs_debug(...) \
        do {} while (0)
#else
#define ext2fs_debug(...) \
        printk(KERN_ERR __VA_ARGS__)
#endif /* !EXT2FS_DEBUG */


static inline struct inode* RCU_I(struct rcu_head *head)
{
        return container_of(head, struct inode, i_rcu);
}

#endif /* _WRAP_LINUX_H_ */

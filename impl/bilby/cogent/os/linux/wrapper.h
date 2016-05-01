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
#include <lib/rbt.h>

#define bilbyfs_assert(v) BUG_ON(!(v))

#define bilbyfs_err(...) \
        printk(KERN_ERR __VA_ARGS__)

#define bilbyfs_msg(...) \
        printk(KERN_INFO __VA_ARGS__)

#ifndef BILBYFS_DEBUG
#define bilbyfs_debug(...) \
        do {} while (0)
#else
#define bilbyfs_debug(...) \
        printk(KERN_ERR __VA_ARGS__)
#endif /* !BILBYFS_DEBUG */

#define kmalloc(sz) kmalloc(sz, GFP_NOFS)
#define krealloc(p,sz) krealloc(p, sz, GFP_NOFS)
#define kzalloc(sz) kzalloc(sz, GFP_NOFS)
        
#endif /* _WRAP_LINUX_H_ */

/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#ifndef ADT_H__
# define ADT_H__
/* Linux headers have to be included only if __KERNEL__
 * is defined because cogent's C parser does not support
 * all gcc extensions in Linux headers.
 */
#ifdef __KERNEL__ 
# include <linux/list.h>
# include <asm/div64.h>
# include <linux/statfs.h>
# include <linux/fs.h>
# include <linux/err.h>
# include <linux/slab.h>
# include <linux/vmalloc.h>
# include <linux/mtd/ubi.h>
# include <linux/pagemap.h>
# include <linux/backing-dev.h>
# include <linux/crc32.h>
# include <linux/ctype.h>
# include <linux/buffer_head.h>
# include <linux/semaphore.h>
# include <linux/init.h>
# include <linux/module.h>
# include <linux/namei.h>
# include <linux/seq_file.h>
# include <linux/mount.h>
# include <linux/version.h>
#if LINUX_VERSION_CODE >= KERNEL_VERSION(4,5,0)
# include <linux/delayed_call.h>
#endif
#if LINUX_VERSION_CODE >= KERNEL_VERSION(5,0,0)
#include <uapi/linux/mount.h>
#endif

#include <lib/allocpool.h>

#ifndef __LINUX_PARSER_H__
#define __LINUX_PARSER_H__
/* Why isn't that header protected? */
# include <linux/parser.h>
#endif

#endif

/* FIXME this is a hack */
#ifndef NULL
#define NULL ((void *)0)
#endif 
#endif /* !ADT_H__ */

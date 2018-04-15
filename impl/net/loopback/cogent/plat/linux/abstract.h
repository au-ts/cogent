/*
 * Copyright 2018, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#ifndef _ABSTRACT_H
#define _ABSTRACT_H

#include <linux_hdrs.h> /* In cogent/plat/linux/ */
#include <abstract-defns.h> /* In cogent/plat/linux/ */

/* The global state */
struct _State {
        void *priv;
};

typedef struct _State SysState;

/* Types in the Linux Kernel */
typedef struct u64_stats_sync U64StatsSyncAbstractType;
typedef struct net NetAbstractType;
typedef struct net_device NetDeviceAbstractType;

#define likely(x)       __builtin_expect(!!(x), 1)
#define unlikely(x)     __builtin_expect(!!(x), 0)

#endif  /* _ABSTRACT_H */

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

typedef struct WrapperState SysState;

#endif /* !ABSTRACT_H__ */

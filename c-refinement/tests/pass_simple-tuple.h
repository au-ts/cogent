/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include "../../cogent/tests/cogent.h" /* FIXME: Change to the proper path */

#ifndef PASS_SIMPLE_TUPLE_H__
#define PASS_SIMPLE_TUPLE_H__

enum t6 {
    FUN_ENUM_foo
};
typedef enum t6 t6;
struct t3 {
    u32 p1;
    u32 p2;
};
typedef struct t3 t3;
t3 dispatch_t6(t6, u32);
t3 foo(u32);
typedef u32 foo_arg;
typedef t3 foo_ret;
#endif



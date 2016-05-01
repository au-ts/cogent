/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#ifndef FUN2_H__
#define FUN2_H__

#include <cogent.h>  /* FIXME: Change to or search for the proper path */

enum {
    LETBANG_TRUE = 1
};
enum untyped_func_enum {
    FUN_ENUM_bar,
    FUN_ENUM_foo
};
typedef enum untyped_func_enum untyped_func_enum;
typedef untyped_func_enum t2;
typedef untyped_func_enum t3;
struct t1 {
    u32 p1;
    u32 p2;
};
typedef struct t1 t1;
static inline t1 foo(u16);
static inline unit_t bar(unit_t);
static inline t1 dispatch_t2(untyped_func_enum a9, u16 a10)
{
    return foo(a10);
}
static inline unit_t dispatch_t3(untyped_func_enum a11, unit_t a12)
{
    return bar(a12);
}
typedef unit_t bar_arg;
typedef unit_t bar_ret;
typedef u16 foo_arg;
typedef t1 foo_ret;
#endif



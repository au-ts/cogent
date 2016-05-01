/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#ifndef PASS_VERY_SIMPLE_SPLIT_H__
#define PASS_VERY_SIMPLE_SPLIT_H__

#include <cogent.h>  /* FIXME: Change to or search for the proper path */

enum {
    LET_TRUE = 1
};
enum {
    LETBANG_TRUE = 1
};
enum untyped_func_enum {
    FUN_ENUM_foo
};
typedef enum untyped_func_enum untyped_func_enum;
typedef untyped_func_enum t2;
#define FUN_DISP_MACRO_dispatch_t2(a1, a2, a3)\
{\
    {\
        a1 = foo(a3);\
    }\
}
struct t1 {
    u32 p1;
    u16 p2;
};
typedef struct t1 t1;
static inline u32 foo(t1);
static inline u32 dispatch_t2(untyped_func_enum a2, t1 a3)
{
    return foo(a3);
}
typedef t1 foo_arg;
typedef u32 foo_ret;
#endif



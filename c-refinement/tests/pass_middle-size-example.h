/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#ifndef PASS_MIDDLE_SIZE_EXAMPLE_H__
#define PASS_MIDDLE_SIZE_EXAMPLE_H__

#include "../../cogent/lib/cogent.h" /* FIXME: Change to or search for the proper path */

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
typedef untyped_func_enum t5;
#define FUN_DISP_MACRO_dispatch_t5(a1, a2, a3)\
{\
    {\
        a1 = foo(a3);\
    }\
}
struct t1 {
    u32 a1;
    u32 a2;
};
typedef struct t1 t1;
struct t2 {
    t1* a;
    bool_t b;
};
typedef struct t2 t2;
struct t3 {
    t2* p1;
    bool_t p2;
};
typedef struct t3 t3;
struct t4 {
    t2* p1;
    t1* p2;
    bool_t p3;
    u32 p4;
};
typedef struct t4 t4;
static inline t4 foo(t3);
static inline t4 dispatch_t5(untyped_func_enum a2, t3 a3)
{
    return foo(a3);
}
typedef t3 foo_arg;
typedef t4 foo_ret;
#endif



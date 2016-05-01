/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#ifndef PASS_SIMPLE_CASE3_H__
#define PASS_SIMPLE_CASE3_H__

#include <cogent.h>  /* FIXME: Change to or search for the proper path */

enum {
    LETBANG_TRUE = 1
};
enum tag_t {
    TAG_ENUM_Atag,
    TAG_ENUM_Btag,
    TAG_ENUM_Ctag
};
typedef enum tag_t tag_t;
enum untyped_func_enum {
    FUN_ENUM_foo
};
typedef enum untyped_func_enum untyped_func_enum;
typedef untyped_func_enum t4;
struct t1 {
    tag_t tag;
    u8 Atag;
    u8 Btag;
    u8 Ctag;
};
typedef struct t1 t1;
struct t2 {
    tag_t tag;
    u8 Btag;
    u8 Ctag;
};
typedef struct t2 t2;
struct t3 {
    tag_t tag;
    u8 Ctag;
};
typedef struct t3 t3;
static inline u8 foo(t1);
static inline u8 dispatch_t4(untyped_func_enum a8, t1 a9)
{
    return foo(a9);
}
typedef t1 foo_arg;
typedef u8 foo_ret;
#endif



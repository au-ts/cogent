/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#ifndef PASS_PRIM_OPS_H__
#define PASS_PRIM_OPS_H__

#include <cogent.h>  /* FIXME: Change to or search for the proper path */

enum {
    LETBANG_TRUE = 1
};
enum untyped_func_enum {
    FUN_ENUM_bool_ops,
    FUN_ENUM_ops16,
    FUN_ENUM_ops32,
    FUN_ENUM_ops64,
    FUN_ENUM_ops8
};
typedef enum untyped_func_enum untyped_func_enum;
typedef untyped_func_enum t1;
typedef untyped_func_enum t2;
typedef untyped_func_enum t3;
typedef untyped_func_enum t4;
typedef untyped_func_enum t5;
static inline u8 ops8(u8);
static inline u64 ops64(u64);
static inline u32 ops32(u32);
static inline u16 ops16(u16);
static inline bool_t bool_ops(u32);
static inline u16 dispatch_t1(untyped_func_enum a2, u16 a3)
{
    return ops16(a3);
}
static inline bool_t dispatch_t2(untyped_func_enum a2, u32 a3)
{
    return bool_ops(a3);
}
static inline u32 dispatch_t3(untyped_func_enum a2, u32 a3)
{
    return ops32(a3);
}
static inline u64 dispatch_t4(untyped_func_enum a2, u64 a3)
{
    return ops64(a3);
}
static inline u8 dispatch_t5(untyped_func_enum a2, u8 a3)
{
    return ops8(a3);
}
typedef u32 bool_ops_arg;
typedef bool_t bool_ops_ret;
typedef u16 ops16_arg;
typedef u16 ops16_ret;
typedef u32 ops32_arg;
typedef u32 ops32_ret;
typedef u64 ops64_arg;
typedef u64 ops64_ret;
typedef u8 ops8_arg;
typedef u8 ops8_ret;
#endif



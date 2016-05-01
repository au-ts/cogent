/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#ifndef FUN_DSL_H__
#define FUN_DSL_H__

#include <cogent.h>  /* FIXME: Change to or search for the proper path */

enum {
    LETBANG_TRUE = 1
};
enum untyped_func_enum {
    FUN_ENUM_abs,
    FUN_ENUM_f,
    FUN_ENUM_i,
    FUN_ENUM_i2
};
typedef enum untyped_func_enum untyped_func_enum;
typedef untyped_func_enum t2;
typedef untyped_func_enum t1;
static inline t1 abs(unit_t);
static inline unit_t i(unit_t);
static inline unit_t i2(unit_t);
static inline unit_t f(unit_t);
static inline t1 dispatch_t2(untyped_func_enum a5, unit_t a6)
{
    return abs(a6);
}
static inline unit_t dispatch_t1(untyped_func_enum a7, unit_t a8)
{
    switch (a7) {
        
        
      case FUN_ENUM_f:
        return f(a8);
        
        
      case FUN_ENUM_i:
        return i(a8);
        
      default:
        return i2(a8);
    }
}
typedef unit_t abs_arg;
typedef t1 abs_ret;
typedef unit_t f_arg;
typedef unit_t f_ret;
typedef unit_t i2_arg;
typedef unit_t i2_ret;
typedef unit_t i_arg;
typedef unit_t i_ret;
#endif



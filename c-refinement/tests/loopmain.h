/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#ifndef LOOPMAIN_H__
#define LOOPMAIN_H__

#include <cogent.h>  /* FIXME: Change to or search for the proper path */

enum {
    LET_TRUE = 1
};
enum {
    LETBANG_TRUE = 1
};
enum untyped_func_enum {
    FUN_ENUM_id_f,
    FUN_ENUM_id_loopbody,
    FUN_ENUM_seq32_0,
    FUN_ENUM_triangular,
    FUN_ENUM_triangular_loopbody
};
typedef enum untyped_func_enum untyped_func_enum;
typedef untyped_func_enum t2;
#define FUN_DISP_MACRO_dispatch_t2(a1, a2, a3)\
{\
    {\
        switch (a2) {\
            \
            \
          case FUN_ENUM_id_loopbody:\
            {\
                a1 = id_loopbody(a3);\
                break;\
            }\
            \
          default:\
            {\
                a1 = triangular_loopbody(a3);\
                break;\
            }\
        }\
    }\
}
typedef untyped_func_enum t4;
#define FUN_DISP_MACRO_dispatch_t4(a1, a2, a3)\
{\
    {\
        a1 = seq32_0(a3);\
    }\
}
typedef untyped_func_enum t5;
#define FUN_DISP_MACRO_dispatch_t5(a1, a2, a3)\
{\
    {\
        switch (a2) {\
            \
            \
          case FUN_ENUM_id_f:\
            {\
                a1 = id_f(a3);\
                break;\
            }\
            \
          default:\
            {\
                a1 = triangular(a3);\
                break;\
            }\
        }\
    }\
}
struct t1 {
    u32 acc;
    u32 idx;
};
typedef struct t1 t1;
struct t3 {
    u32 frm;
    u32 to;
    t2 f;
    u32 acc;
};
typedef struct t3 t3;
static inline u32 seq32_0(t3);
static inline u32 id_loopbody(t1);
static inline u32 id_f(u32);
static inline u32 triangular_loopbody(t1);
static inline u32 triangular(u32);
static inline u32 dispatch_t2(untyped_func_enum a2, t1 a3)
{
    switch (a2) {
        
        
      case FUN_ENUM_id_loopbody:
        return id_loopbody(a3);
        
      default:
        return triangular_loopbody(a3);
    }
}
static inline u32 dispatch_t4(untyped_func_enum a2, t3 a3)
{
    return seq32_0(a3);
}
static inline u32 dispatch_t5(untyped_func_enum a2, u32 a3)
{
    switch (a2) {
        
        
      case FUN_ENUM_id_f:
        return id_f(a3);
        
      default:
        return triangular(a3);
    }
}
typedef u32 id_f_arg;
typedef u32 id_f_ret;
typedef t1 id_loopbody_arg;
typedef u32 id_loopbody_ret;
typedef t3 seq32_0_arg;
typedef u32 seq32_0_ret;
typedef u32 triangular_arg;
typedef t1 triangular_loopbody_arg;
typedef u32 triangular_loopbody_ret;
typedef u32 triangular_ret;
#endif



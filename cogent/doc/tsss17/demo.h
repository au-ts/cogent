// This build info header is now disabled by --fno-gen-header.
// --------------------------------------------------------------------------------
// We strongly discourage users from generating individual files for Isabelle
// proofs, as it will end up with an inconsistent collection of output files (i.e.
// Isabelle input files).

#ifndef DEMO_H__
#define DEMO_H__

#include <cogent.h>  /* FIXME: Change to or search for the proper path */

enum {
    LET_TRUE = 1,
} ;
enum {
    LETBANG_TRUE = 1,
} ;
enum tag_t {
    TAG_ENUM_Break,
    TAG_ENUM_Error,
    TAG_ENUM_Iterate,
    TAG_ENUM_None,
    TAG_ENUM_Some,
    TAG_ENUM_Success,
} ;
typedef enum tag_t tag_t;
enum untyped_func_enum {
    FUN_ENUM_align32,
    FUN_ENUM_align64,
    FUN_ENUM_cmp_inc,
    FUN_ENUM_cogent_high_16_bits,
    FUN_ENUM_cogent_log2,
    FUN_ENUM_cogent_low_16_bits,
    FUN_ENUM_deserialise_CString,
    FUN_ENUM_deserialise_Chain,
    FUN_ENUM_deserialise_U32,
    FUN_ENUM_find_str,
    FUN_ENUM_free_CString,
    FUN_ENUM_free_Chain,
    FUN_ENUM_in_range_u32,
    FUN_ENUM_malloc_Chain,
    FUN_ENUM_min_u32,
    FUN_ENUM_min_u64,
    FUN_ENUM_random_u32,
    FUN_ENUM_safe_add32,
    FUN_ENUM_safe_add64,
    FUN_ENUM_safe_sub32,
    FUN_ENUM_safe_sub64,
    FUN_ENUM_seq32_0,
    FUN_ENUM_string_cmp,
    FUN_ENUM_to_u16,
    FUN_ENUM_to_u32,
    FUN_ENUM_to_u64,
    FUN_ENUM_u16_to_u32,
    FUN_ENUM_u16_to_u64,
    FUN_ENUM_u16_to_u8,
    FUN_ENUM_u32_to_u16,
    FUN_ENUM_u32_to_u64,
    FUN_ENUM_u32_to_u8,
    FUN_ENUM_u64_to_u16,
    FUN_ENUM_u64_to_u32,
    FUN_ENUM_u8_to_u16,
    FUN_ENUM_u8_to_u32,
    FUN_ENUM_u8_to_u64,
    FUN_ENUM_wordarray_cmp,
    FUN_ENUM_wordarray_print,
    FUN_ENUM_wordarray_u8_as_u32,
} ;
typedef enum untyped_func_enum untyped_func_enum;
typedef untyped_func_enum t39;
#define FUN_DISP_MACRO_dispatch_t39(a1, a2, a3)\
{\
    {\
        a1 = malloc_Chain(a3);\
    }\
}
typedef untyped_func_enum t40;
#define FUN_DISP_MACRO_dispatch_t40(a1, a2, a3)\
{\
    {\
        a1 = wordarray_u8_as_u32(a3);\
    }\
}
typedef untyped_func_enum t41;
#define FUN_DISP_MACRO_dispatch_t41(a1, a2, a3)\
{\
    {\
        a1 = wordarray_print(a3);\
    }\
}
typedef untyped_func_enum t42;
#define FUN_DISP_MACRO_dispatch_t42(a1, a2, a3)\
{\
    {\
        switch (a2) {\
            \
          case FUN_ENUM_string_cmp:\
            {\
                a1 = string_cmp(a3);\
                break;\
            }\
            \
          default:\
            {\
                a1 = wordarray_cmp(a3);\
                break;\
            }\
        }\
    }\
}
typedef untyped_func_enum t43;
#define FUN_DISP_MACRO_dispatch_t43(a1, a2, a3)\
{\
    {\
        a1 = free_CString(a3);\
    }\
}
typedef untyped_func_enum t44;
#define FUN_DISP_MACRO_dispatch_t44(a1, a2, a3)\
{\
    {\
        a1 = deserialise_CString(a3);\
    }\
}
typedef untyped_func_enum t45;
#define FUN_DISP_MACRO_dispatch_t45(a1, a2, a3)\
{\
    {\
        a1 = deserialise_U32(a3);\
    }\
}
typedef untyped_func_enum t46;
#define FUN_DISP_MACRO_dispatch_t46(a1, a2, a3)\
{\
    {\
        a1 = deserialise_Chain(a3);\
    }\
}
typedef untyped_func_enum t47;
#define FUN_DISP_MACRO_dispatch_t47(a1, a2, a3)\
{\
    {\
        switch (a2) {\
            \
          case FUN_ENUM_safe_add64:\
            {\
                a1 = safe_add64(a3);\
                break;\
            }\
            \
          default:\
            {\
                a1 = safe_sub64(a3);\
                break;\
            }\
        }\
    }\
}
typedef untyped_func_enum t48;
#define FUN_DISP_MACRO_dispatch_t48(a1, a2, a3)\
{\
    {\
        switch (a2) {\
            \
          case FUN_ENUM_align64:\
            {\
                a1 = align64(a3);\
                break;\
            }\
            \
          default:\
            {\
                a1 = min_u64(a3);\
                break;\
            }\
        }\
    }\
}
typedef untyped_func_enum t49;
#define FUN_DISP_MACRO_dispatch_t49(a1, a2, a3)\
{\
    {\
        switch (a2) {\
            \
          case FUN_ENUM_safe_add32:\
            {\
                a1 = safe_add32(a3);\
                break;\
            }\
            \
          default:\
            {\
                a1 = safe_sub32(a3);\
                break;\
            }\
        }\
    }\
}
typedef untyped_func_enum t50;
#define FUN_DISP_MACRO_dispatch_t50(a1, a2, a3)\
{\
    {\
        switch (a2) {\
            \
          case FUN_ENUM_align32:\
            {\
                a1 = align32(a3);\
                break;\
            }\
            \
          default:\
            {\
                a1 = min_u32(a3);\
                break;\
            }\
        }\
    }\
}
typedef untyped_func_enum t51;
#define FUN_DISP_MACRO_dispatch_t51(a1, a2, a3)\
{\
    {\
        a1 = in_range_u32(a3);\
    }\
}
typedef untyped_func_enum t7;
#define FUN_DISP_MACRO_dispatch_t7(a1, a2, a3)\
{\
    {\
        a1 = cmp_inc(a3);\
    }\
}
typedef untyped_func_enum t52;
#define FUN_DISP_MACRO_dispatch_t52(a1, a2, a3)\
{\
    {\
        a1 = find_str(a3);\
    }\
}
typedef untyped_func_enum t53;
#define FUN_DISP_MACRO_dispatch_t53(a1, a2, a3)\
{\
    {\
        a1 = seq32_0(a3);\
    }\
}
typedef untyped_func_enum t54;
#define FUN_DISP_MACRO_dispatch_t54(a1, a2, a3)\
{\
    {\
        a1 = free_Chain(a3);\
    }\
}
typedef untyped_func_enum t55;
#define FUN_DISP_MACRO_dispatch_t55(a1, a2, a3)\
{\
    {\
        a1 = to_u16(a3);\
    }\
}
typedef untyped_func_enum t56;
#define FUN_DISP_MACRO_dispatch_t56(a1, a2, a3)\
{\
    {\
        a1 = u16_to_u32(a3);\
    }\
}
typedef untyped_func_enum t57;
#define FUN_DISP_MACRO_dispatch_t57(a1, a2, a3)\
{\
    {\
        a1 = u16_to_u64(a3);\
    }\
}
typedef untyped_func_enum t58;
#define FUN_DISP_MACRO_dispatch_t58(a1, a2, a3)\
{\
    {\
        a1 = u16_to_u8(a3);\
    }\
}
typedef untyped_func_enum t59;
#define FUN_DISP_MACRO_dispatch_t59(a1, a2, a3)\
{\
    {\
        switch (a2) {\
            \
          case FUN_ENUM_cogent_high_16_bits:\
            {\
                a1 = cogent_high_16_bits(a3);\
                break;\
            }\
            \
          case FUN_ENUM_cogent_low_16_bits:\
            {\
                a1 = cogent_low_16_bits(a3);\
                break;\
            }\
            \
          default:\
            {\
                a1 = u32_to_u16(a3);\
                break;\
            }\
        }\
    }\
}
typedef untyped_func_enum t60;
#define FUN_DISP_MACRO_dispatch_t60(a1, a2, a3)\
{\
    {\
        switch (a2) {\
            \
          case FUN_ENUM_cogent_log2:\
            {\
                a1 = cogent_log2(a3);\
                break;\
            }\
            \
          default:\
            {\
                a1 = to_u32(a3);\
                break;\
            }\
        }\
    }\
}
typedef untyped_func_enum t61;
#define FUN_DISP_MACRO_dispatch_t61(a1, a2, a3)\
{\
    {\
        a1 = u32_to_u64(a3);\
    }\
}
typedef untyped_func_enum t62;
#define FUN_DISP_MACRO_dispatch_t62(a1, a2, a3)\
{\
    {\
        a1 = u32_to_u8(a3);\
    }\
}
typedef untyped_func_enum t63;
#define FUN_DISP_MACRO_dispatch_t63(a1, a2, a3)\
{\
    {\
        a1 = u64_to_u16(a3);\
    }\
}
typedef untyped_func_enum t64;
#define FUN_DISP_MACRO_dispatch_t64(a1, a2, a3)\
{\
    {\
        a1 = u64_to_u32(a3);\
    }\
}
typedef untyped_func_enum t65;
#define FUN_DISP_MACRO_dispatch_t65(a1, a2, a3)\
{\
    {\
        a1 = to_u64(a3);\
    }\
}
typedef untyped_func_enum t66;
#define FUN_DISP_MACRO_dispatch_t66(a1, a2, a3)\
{\
    {\
        a1 = u8_to_u16(a3);\
    }\
}
typedef untyped_func_enum t67;
#define FUN_DISP_MACRO_dispatch_t67(a1, a2, a3)\
{\
    {\
        a1 = u8_to_u32(a3);\
    }\
}
typedef untyped_func_enum t68;
#define FUN_DISP_MACRO_dispatch_t68(a1, a2, a3)\
{\
    {\
        a1 = u8_to_u64(a3);\
    }\
}
typedef untyped_func_enum t69;
#define FUN_DISP_MACRO_dispatch_t69(a1, a2, a3)\
{\
    {\
        a1 = random_u32(a3);\
    }\
}
#include <abstract/WordArray_u8.h>
struct t1 {
    WordArray_u8 *p1;
    WordArray_u8 *p2;
} ;
typedef struct t1 t1;
struct t2 {
    Buffer *p1;
    WordArray_u8 *p2;
} ;
typedef struct t2 t2;
struct t3 {
    ExState *acc;
    t2 obsv;
    u32 idx;
} ;
typedef struct t3 t3;
struct t4 {
    u32 len;
    WordArray_u8 *key;
} ;
typedef struct t4 t4;
struct t5 {
    tag_t tag;
    t4 *Break;
    unit_t Iterate;
} ;
typedef struct t5 t5;
struct t6 {
    ExState *p1;
    t5 p2;
} ;
typedef struct t6 t6;
struct t8 {
    u32 frm;
    u32 to;
    u32 step;
    t7 f;
    ExState *acc;
    t2 obsv;
} ;
typedef struct t8 t8;
struct t9 {
    ExState *p1;
    t4 *p2;
} ;
typedef struct t9 t9;
struct t10 {
    tag_t tag;
    u32 Error;
    t4 *Success;
} ;
typedef struct t10 t10;
struct t11 {
    ExState *p1;
    t10 p2;
} ;
typedef struct t11 t11;
struct t12 {
    ExState *p1;
    WordArray_u8 *p2;
} ;
typedef struct t12 t12;
struct t13 {
    ExState *p1;
    Buffer *p2;
    u32 p3;
    u32 p4;
} ;
typedef struct t13 t13;
struct t14 {
    WordArray_u8 *p1;
    u32 p2;
} ;
typedef struct t14 t14;
struct t15 {
    tag_t tag;
    u32 Error;
    t14 Success;
} ;
typedef struct t15 t15;
struct t16 {
    ExState *p1;
    t15 p2;
} ;
typedef struct t16 t16;
struct t17 {
    ExState *p1;
    Buffer *p2;
    u32 p3;
} ;
typedef struct t17 t17;
struct t18 {
    ExState *p1;
    u32 p2;
} ;
typedef struct t18 t18;
struct t19 {
    u64 p1;
    u64 p2;
} ;
typedef struct t19 t19;
struct t20 {
    u32 p1;
    u32 p2;
} ;
typedef struct t20 t20;
struct t21 {
    u32 p1;
    u32 p2;
    u32 p3;
} ;
typedef struct t21 t21;
struct t22 {
    tag_t tag;
    unit_t Error;
    u32 Success;
} ;
typedef struct t22 t22;
struct t23 {
    tag_t tag;
    unit_t Error;
} ;
typedef struct t23 t23;
struct t24 {
    tag_t tag;
    u32 Success;
} ;
typedef struct t24 t24;
struct t25 {
    tag_t tag;
    unit_t Error;
    u64 Success;
} ;
typedef struct t25 t25;
struct t26 {
    tag_t tag;
    u64 Success;
} ;
typedef struct t26 t26;
struct t27 {
    t4 *p1;
    u32 p2;
} ;
typedef struct t27 t27;
struct t28 {
    tag_t tag;
    u32 Error;
    t27 Success;
} ;
typedef struct t28 t28;
struct t29 {
    ExState *p1;
    t28 p2;
} ;
typedef struct t29 t29;
struct t30 {
    tag_t tag;
    t27 Success;
} ;
typedef struct t30 t30;
struct t31 {
    tag_t tag;
    u32 Error;
} ;
typedef struct t31 t31;
struct t32 {
    tag_t tag;
    t4 *Break;
} ;
typedef struct t32 t32;
struct t33 {
    tag_t tag;
    unit_t Iterate;
} ;
typedef struct t33 t33;
struct t34 {
    ExState *p1;
    Buffer *p2;
    WordArray_u8 *p3;
} ;
typedef struct t34 t34;
struct t35 {
    tag_t tag;
    unit_t None;
    t4 *Some;
} ;
typedef struct t35 t35;
struct t36 {
    ExState *p1;
    t35 p2;
} ;
typedef struct t36 t36;
struct t37 {
    tag_t tag;
    unit_t None;
} ;
typedef struct t37 t37;
struct t38 {
    tag_t tag;
    t4 *Some;
} ;
typedef struct t38 t38;
static inline u64 u8_to_u64(u8);
static inline u32 u8_to_u32(u8);
static inline u16 u8_to_u16(u8);
static inline u32 u64_to_u32(u64);
static inline u16 u64_to_u16(u64);
static inline u8 u32_to_u8(u32);
static inline u64 u32_to_u64(u32);
static inline u16 u32_to_u16(u32);
static inline u8 u16_to_u8(u16);
static inline u32 u16_to_u32(u16);
static inline u32 random_u32(unit_t);
static inline u32 cogent_log2(u32);
static inline bool_t wordarray_cmp(t1);
static inline u32 wordarray_u8_as_u32(WordArray_u8 *);
static inline t6 seq32_0(t8);
static inline ExState *free_Chain(t9);
static inline t11 malloc_Chain(ExState *);
static inline ExState *free_CString(t12);
static inline bool_t string_cmp(t1);
static inline unit_t wordarray_print(WordArray_u8 *);
static inline t16 deserialise_CString(t13);
static inline t18 deserialise_U32(t17);
static inline u64 u16_to_u64(u16);
static inline u64 to_u64(u64);
static inline u32 to_u32(u32);
static inline u16 to_u16(u16);
static inline u64 min_u64(t19);
static inline u32 min_u32(t20);
static inline bool_t in_range_u32(t21);
static inline u16 cogent_low_16_bits(u32);
static inline u16 cogent_high_16_bits(u32);
static inline u64 align64(t19);
static inline u32 align32(t20);
static inline t22 safe_add32(t20);
static inline t25 safe_add64(t19);
static inline t22 safe_sub32(t20);
static inline t25 safe_sub64(t19);
static inline t29 deserialise_Chain(t17);
static inline t6 cmp_inc(t3);
static inline t36 find_str(t34);
static inline t11 dispatch_t39(untyped_func_enum a2, ExState *a3)
{
    return malloc_Chain(a3);
}
static inline u32 dispatch_t40(untyped_func_enum a2, WordArray_u8 *a3)
{
    return wordarray_u8_as_u32(a3);
}
static inline unit_t dispatch_t41(untyped_func_enum a2, WordArray_u8 *a3)
{
    return wordarray_print(a3);
}
static inline bool_t dispatch_t42(untyped_func_enum a2, t1 a3)
{
    switch (a2) {
        
      case FUN_ENUM_string_cmp:
        return string_cmp(a3);
        
      default:
        return wordarray_cmp(a3);
    }
}
static inline ExState *dispatch_t43(untyped_func_enum a2, t12 a3)
{
    return free_CString(a3);
}
static inline t16 dispatch_t44(untyped_func_enum a2, t13 a3)
{
    return deserialise_CString(a3);
}
static inline t18 dispatch_t45(untyped_func_enum a2, t17 a3)
{
    return deserialise_U32(a3);
}
static inline t29 dispatch_t46(untyped_func_enum a2, t17 a3)
{
    return deserialise_Chain(a3);
}
static inline t25 dispatch_t47(untyped_func_enum a2, t19 a3)
{
    switch (a2) {
        
      case FUN_ENUM_safe_add64:
        return safe_add64(a3);
        
      default:
        return safe_sub64(a3);
    }
}
static inline u64 dispatch_t48(untyped_func_enum a2, t19 a3)
{
    switch (a2) {
        
      case FUN_ENUM_align64:
        return align64(a3);
        
      default:
        return min_u64(a3);
    }
}
static inline t22 dispatch_t49(untyped_func_enum a2, t20 a3)
{
    switch (a2) {
        
      case FUN_ENUM_safe_add32:
        return safe_add32(a3);
        
      default:
        return safe_sub32(a3);
    }
}
static inline u32 dispatch_t50(untyped_func_enum a2, t20 a3)
{
    switch (a2) {
        
      case FUN_ENUM_align32:
        return align32(a3);
        
      default:
        return min_u32(a3);
    }
}
static inline bool_t dispatch_t51(untyped_func_enum a2, t21 a3)
{
    return in_range_u32(a3);
}
static inline t6 dispatch_t7(untyped_func_enum a2, t3 a3)
{
    return cmp_inc(a3);
}
static inline t36 dispatch_t52(untyped_func_enum a2, t34 a3)
{
    return find_str(a3);
}
static inline t6 dispatch_t53(untyped_func_enum a2, t8 a3)
{
    return seq32_0(a3);
}
static inline ExState *dispatch_t54(untyped_func_enum a2, t9 a3)
{
    return free_Chain(a3);
}
static inline u16 dispatch_t55(untyped_func_enum a2, u16 a3)
{
    return to_u16(a3);
}
static inline u32 dispatch_t56(untyped_func_enum a2, u16 a3)
{
    return u16_to_u32(a3);
}
static inline u64 dispatch_t57(untyped_func_enum a2, u16 a3)
{
    return u16_to_u64(a3);
}
static inline u8 dispatch_t58(untyped_func_enum a2, u16 a3)
{
    return u16_to_u8(a3);
}
static inline u16 dispatch_t59(untyped_func_enum a2, u32 a3)
{
    switch (a2) {
        
      case FUN_ENUM_cogent_high_16_bits:
        return cogent_high_16_bits(a3);
        
      case FUN_ENUM_cogent_low_16_bits:
        return cogent_low_16_bits(a3);
        
      default:
        return u32_to_u16(a3);
    }
}
static inline u32 dispatch_t60(untyped_func_enum a2, u32 a3)
{
    switch (a2) {
        
      case FUN_ENUM_cogent_log2:
        return cogent_log2(a3);
        
      default:
        return to_u32(a3);
    }
}
static inline u64 dispatch_t61(untyped_func_enum a2, u32 a3)
{
    return u32_to_u64(a3);
}
static inline u8 dispatch_t62(untyped_func_enum a2, u32 a3)
{
    return u32_to_u8(a3);
}
static inline u16 dispatch_t63(untyped_func_enum a2, u64 a3)
{
    return u64_to_u16(a3);
}
static inline u32 dispatch_t64(untyped_func_enum a2, u64 a3)
{
    return u64_to_u32(a3);
}
static inline u64 dispatch_t65(untyped_func_enum a2, u64 a3)
{
    return to_u64(a3);
}
static inline u16 dispatch_t66(untyped_func_enum a2, u8 a3)
{
    return u8_to_u16(a3);
}
static inline u32 dispatch_t67(untyped_func_enum a2, u8 a3)
{
    return u8_to_u32(a3);
}
static inline u64 dispatch_t68(untyped_func_enum a2, u8 a3)
{
    return u8_to_u64(a3);
}
static inline u32 dispatch_t69(untyped_func_enum a2, unit_t a3)
{
    return random_u32(a3);
}
typedef WordArray_u8 CString;
typedef t4 Chain;
typedef u32 ErrCode;
typedef u32 Index;
typedef u32 WordArrayIndex;
typedef t20 align32_arg;
typedef u32 align32_ret;
typedef t19 align64_arg;
typedef u64 align64_ret;
typedef t3 cmp_inc_arg;
typedef t6 cmp_inc_ret;
typedef u32 cogent_high_16_bits_arg;
typedef u16 cogent_high_16_bits_ret;
typedef u32 cogent_log2_arg;
typedef u32 cogent_log2_ret;
typedef u32 cogent_low_16_bits_arg;
typedef u16 cogent_low_16_bits_ret;
typedef t13 deserialise_CString_arg;
typedef t16 deserialise_CString_ret;
typedef t17 deserialise_Chain_arg;
typedef t29 deserialise_Chain_ret;
typedef t17 deserialise_U32_arg;
typedef t18 deserialise_U32_ret;
typedef t34 find_str_arg;
typedef t36 find_str_ret;
typedef t12 free_CString_arg;
typedef ExState *free_CString_ret;
typedef t9 free_Chain_arg;
typedef ExState *free_Chain_ret;
typedef t21 in_range_u32_arg;
typedef bool_t in_range_u32_ret;
typedef ExState *malloc_Chain_arg;
typedef t11 malloc_Chain_ret;
typedef t20 min_u32_arg;
typedef u32 min_u32_ret;
typedef t19 min_u64_arg;
typedef u64 min_u64_ret;
typedef unit_t random_u32_arg;
typedef u32 random_u32_ret;
typedef t20 safe_add32_arg;
typedef t22 safe_add32_ret;
typedef t19 safe_add64_arg;
typedef t25 safe_add64_ret;
typedef t20 safe_sub32_arg;
typedef t22 safe_sub32_ret;
typedef t19 safe_sub64_arg;
typedef t25 safe_sub64_ret;
typedef t8 seq32_0_arg;
typedef t6 seq32_0_ret;
typedef t1 string_cmp_arg;
typedef bool_t string_cmp_ret;
typedef u16 to_u16_arg;
typedef u16 to_u16_ret;
typedef u32 to_u32_arg;
typedef u32 to_u32_ret;
typedef u64 to_u64_arg;
typedef u64 to_u64_ret;
typedef u16 u16_to_u32_arg;
typedef u32 u16_to_u32_ret;
typedef u16 u16_to_u64_arg;
typedef u64 u16_to_u64_ret;
typedef u16 u16_to_u8_arg;
typedef u8 u16_to_u8_ret;
typedef u32 u32_to_u16_arg;
typedef u16 u32_to_u16_ret;
typedef u32 u32_to_u64_arg;
typedef u64 u32_to_u64_ret;
typedef u32 u32_to_u8_arg;
typedef u8 u32_to_u8_ret;
typedef u64 u64_to_u16_arg;
typedef u16 u64_to_u16_ret;
typedef u64 u64_to_u32_arg;
typedef u32 u64_to_u32_ret;
typedef u8 u8_to_u16_arg;
typedef u16 u8_to_u16_ret;
typedef u8 u8_to_u32_arg;
typedef u32 u8_to_u32_ret;
typedef u8 u8_to_u64_arg;
typedef u64 u8_to_u64_ret;
typedef t1 wordarray_cmp_arg;
typedef bool_t wordarray_cmp_ret;
typedef WordArray_u8 *wordarray_print_arg;
typedef unit_t wordarray_print_ret;
typedef WordArray_u8 *wordarray_u8_as_u32_arg;
typedef u32 wordarray_u8_as_u32_ret;
#endif



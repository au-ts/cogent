/*
This build info header is now disabled by --fno-gen-header.
--------------------------------------------------------------------------------
We strongly discourage users from generating individual files for Isabelle
proofs, as it will end up with an inconsistent collection of output files (i.e.
Isabelle input files).
*/

#include <adt.h>
#include <stdio.h>
struct WrapperState {
    void *priv;
    struct semaphore lock;
    struct super_block *sb;
} ;
typedef struct WrapperState SysState;
typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef unsigned long long u64;
typedef struct unit_t {
            int dummy;
        } unit_t;
typedef struct bool_t {
            u8 boolean;
        } bool_t;
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
    TAG_ENUM_Success,
} ;
typedef enum tag_t tag_t;
enum untyped_func_enum {
    FUN_ENUM_map_body_f,
    FUN_ENUM_modify_body_f,
    FUN_ENUM_wordarray_clone_0,
    FUN_ENUM_wordarray_clone_u8,
    FUN_ENUM_wordarray_copy_0,
    FUN_ENUM_wordarray_create_0,
    FUN_ENUM_wordarray_create_u8,
    FUN_ENUM_wordarray_free_0,
    FUN_ENUM_wordarray_free_u8,
    FUN_ENUM_wordarray_get_0,
    FUN_ENUM_wordarray_get_bounded_0,
    FUN_ENUM_wordarray_get_bounded_u8,
    FUN_ENUM_wordarray_length_0,
    FUN_ENUM_wordarray_length_u8,
    FUN_ENUM_wordarray_map_0,
    FUN_ENUM_wordarray_map_u8,
    FUN_ENUM_wordarray_modify_0,
    FUN_ENUM_wordarray_modify_u8,
    FUN_ENUM_wordarray_put_0,
    FUN_ENUM_wordarray_put_u8,
} ;
typedef enum untyped_func_enum untyped_func_enum;
typedef untyped_func_enum t22;
typedef untyped_func_enum t23;
typedef untyped_func_enum t24;
typedef untyped_func_enum t18;
typedef untyped_func_enum t25;
typedef untyped_func_enum t26;
typedef untyped_func_enum t27;
typedef untyped_func_enum t28;
typedef untyped_func_enum t29;
typedef untyped_func_enum t30;
typedef untyped_func_enum t31;
typedef untyped_func_enum t12;
struct WordArray_u8 {
    int len;
    u8 *values;
} ;
typedef struct WordArray_u8 WordArray_u8;
struct t1 {
    WordArray_u8 *p1;
    WordArray_u8 *p2;
    u32 p3;
    u32 p4;
    u32 p5;
} ;
typedef struct t1 t1;
struct t2 {
    WordArray_u8 *p1;
    u32 p2;
} ;
typedef struct t2 t2;
struct t3 {
    SysState *p1;
    WordArray_u8 *p2;
} ;
typedef struct t3 t3;
struct t4 {
    SysState *p1;
    u32 p2;
} ;
typedef struct t4 t4;
struct t5 {
    tag_t tag;
    SysState *Error;
    t3 Success;
} ;
typedef struct t5 t5;
struct t6 {
    WordArray_u8 *arr;
    u32 idx;
    u8 val;
} ;
typedef struct t6 t6;
struct t7 {
    tag_t tag;
    WordArray_u8 *Error;
    WordArray_u8 *Success;
} ;
typedef struct t7 t7;
struct t8 {
    u8 elem;
    u8 acc;
    u8 obsv;
} ;
typedef struct t8 t8;
struct t9 {
    u8 p1;
    u8 p2;
} ;
typedef struct t9 t9;
struct t10 {
    tag_t tag;
    unit_t Break;
    unit_t Iterate;
} ;
typedef struct t10 t10;
struct t11 {
    t9 p1;
    t10 p2;
} ;
typedef struct t11 t11;
struct t13 {
    WordArray_u8 *arr;
    u32 frm;
    u32 to;
    t12 f;
    u8 acc;
    u8 obsv;
} ;
typedef struct t13 t13;
struct t14 {
    WordArray_u8 *p1;
    u8 p2;
} ;
typedef struct t14 t14;
struct t15 {
    t14 p1;
    t10 p2;
} ;
typedef struct t15 t15;
struct t16 {
    u8 elem;
    u8 acc;
    bool_t obsv;
} ;
typedef struct t16 t16;
struct t17 {
    u8 elem;
    u8 acc;
} ;
typedef struct t17 t17;
struct t19 {
    WordArray_u8 *arr;
    u32 idx;
    t18 f;
    u8 acc;
    bool_t obsv;
} ;
typedef struct t19 t19;
struct t20 {
    WordArray_u8 *arr;
    u8 acc;
} ;
typedef struct t20 t20;
struct t21 {
    tag_t tag;
    unit_t Error;
    u8 Success;
} ;
typedef struct t21 t21;
WordArray_u8 *ffi_wordarray_copy_0(t1 *);
WordArray_u8 *wordarray_copy_0(t1);
u8 *ffi_wordarray_get_0(t2 *);
static inline u8 wordarray_get_0(t2);
u32 *ffi_wordarray_length_0(WordArray_u8 *);
static inline u32 wordarray_length_0(WordArray_u8 *);
SysState *ffi_wordarray_free_0(t3 *);
static inline SysState *wordarray_free_0(t3);
t5 *ffi_wordarray_create_0(t4 *);
static inline t5 wordarray_create_0(t4);
t7 *ffi_wordarray_put_0(t6 *);
static inline t7 wordarray_put_0(t6);
t15 *ffi_wordarray_map_0(t13 *);
static inline t15 wordarray_map_0(t13);
t20 *ffi_wordarray_modify_0(t19 *);
static inline t20 wordarray_modify_0(t19);
u32 *ffi_wordarray_length_u8(WordArray_u8 *);
__attribute__((pure)) u32 wordarray_length_u8(WordArray_u8 *);
SysState *ffi_wordarray_free_u8(t3 *);
SysState *wordarray_free_u8(t3);
t5 *ffi_wordarray_clone_0(t3 *);
static inline t5 wordarray_clone_0(t3);
t5 *ffi_wordarray_clone_u8(t3 *);
t5 wordarray_clone_u8(t3);
t5 *ffi_wordarray_create_u8(t4 *);
t5 wordarray_create_u8(t4);
t21 *ffi_wordarray_get_bounded_0(t2 *);
static inline __attribute__((pure)) t21 wordarray_get_bounded_0(t2);
t21 *ffi_wordarray_get_bounded_u8(t2 *);
__attribute__((pure)) t21 wordarray_get_bounded_u8(t2);
t7 *ffi_wordarray_put_u8(t6 *);
t7 wordarray_put_u8(t6);
t15 *ffi_wordarray_map_u8(t13 *);
t15 wordarray_map_u8(t13);
t11 *ffi_map_body_f(t8 *);
__attribute__((const)) t11 map_body_f(t8);
t17 *ffi_modify_body_f(t16 *);
__attribute__((const)) t17 modify_body_f(t16);
t20 *ffi_wordarray_modify_u8(t19 *);
t20 wordarray_modify_u8(t19);
static inline u32 dispatch_t22(untyped_func_enum a2, WordArray_u8 *a3)
{
    switch (a2) {
        
      case FUN_ENUM_wordarray_length_0:
        return wordarray_length_0(a3);
        
      default:
        return wordarray_length_u8(a3);
    }
}
static inline WordArray_u8 *dispatch_t23(untyped_func_enum a2, t1 a3)
{
    return wordarray_copy_0(a3);
}
static inline t15 dispatch_t24(untyped_func_enum a2, t13 a3)
{
    switch (a2) {
        
      case FUN_ENUM_wordarray_map_0:
        return wordarray_map_0(a3);
        
      default:
        return wordarray_map_u8(a3);
    }
}
static inline t17 dispatch_t18(untyped_func_enum a2, t16 a3)
{
    return modify_body_f(a3);
}
static inline t20 dispatch_t25(untyped_func_enum a2, t19 a3)
{
    switch (a2) {
        
      case FUN_ENUM_wordarray_modify_0:
        return wordarray_modify_0(a3);
        
      default:
        return wordarray_modify_u8(a3);
    }
}
static inline t21 dispatch_t26(untyped_func_enum a2, t2 a3)
{
    switch (a2) {
        
      case FUN_ENUM_wordarray_get_bounded_0:
        return wordarray_get_bounded_0(a3);
        
      default:
        return wordarray_get_bounded_u8(a3);
    }
}
static inline u8 dispatch_t27(untyped_func_enum a2, t2 a3)
{
    return wordarray_get_0(a3);
}
static inline SysState *dispatch_t28(untyped_func_enum a2, t3 a3)
{
    switch (a2) {
        
      case FUN_ENUM_wordarray_free_0:
        return wordarray_free_0(a3);
        
      default:
        return wordarray_free_u8(a3);
    }
}
static inline t5 dispatch_t29(untyped_func_enum a2, t3 a3)
{
    switch (a2) {
        
      case FUN_ENUM_wordarray_clone_0:
        return wordarray_clone_0(a3);
        
      default:
        return wordarray_clone_u8(a3);
    }
}
static inline t5 dispatch_t30(untyped_func_enum a2, t4 a3)
{
    switch (a2) {
        
      case FUN_ENUM_wordarray_create_0:
        return wordarray_create_0(a3);
        
      default:
        return wordarray_create_u8(a3);
    }
}
static inline t7 dispatch_t31(untyped_func_enum a2, t6 a3)
{
    switch (a2) {
        
      case FUN_ENUM_wordarray_put_0:
        return wordarray_put_0(a3);
        
      default:
        return wordarray_put_u8(a3);
    }
}
static inline t11 dispatch_t12(untyped_func_enum a2, t8 a3)
{
    return map_body_f(a3);
}
typedef WordArray_u8 CString;
typedef u32 ErrCode;
typedef u32 WordArrayIndex;
typedef t8 map_body_f_arg;
typedef t11 map_body_f_ret;
typedef t16 modify_body_f_arg;
typedef t17 modify_body_f_ret;
typedef t3 wordarray_clone_0_arg;
typedef t5 wordarray_clone_0_ret;
typedef t3 wordarray_clone_u8_arg;
typedef t5 wordarray_clone_u8_ret;
typedef t1 wordarray_copy_0_arg;
typedef WordArray_u8 *wordarray_copy_0_ret;
typedef t4 wordarray_create_0_arg;
typedef t5 wordarray_create_0_ret;
typedef t4 wordarray_create_u8_arg;
typedef t5 wordarray_create_u8_ret;
typedef t3 wordarray_free_0_arg;
typedef SysState *wordarray_free_0_ret;
typedef t3 wordarray_free_u8_arg;
typedef SysState *wordarray_free_u8_ret;
typedef t2 wordarray_get_0_arg;
typedef u8 wordarray_get_0_ret;
typedef t2 wordarray_get_bounded_0_arg;
typedef t21 wordarray_get_bounded_0_ret;
typedef t2 wordarray_get_bounded_u8_arg;
typedef t21 wordarray_get_bounded_u8_ret;
typedef WordArray_u8 *wordarray_length_0_arg;
typedef u32 wordarray_length_0_ret;
typedef WordArray_u8 *wordarray_length_u8_arg;
typedef u32 wordarray_length_u8_ret;
typedef t13 wordarray_map_0_arg;
typedef t15 wordarray_map_0_ret;
typedef t13 wordarray_map_u8_arg;
typedef t15 wordarray_map_u8_ret;
typedef t19 wordarray_modify_0_arg;
typedef t20 wordarray_modify_0_ret;
typedef t19 wordarray_modify_u8_arg;
typedef t20 wordarray_modify_u8_ret;
typedef t6 wordarray_put_0_arg;
typedef t7 wordarray_put_0_ret;
typedef t6 wordarray_put_u8_arg;
typedef t7 wordarray_put_u8_ret;
WordArray_u8 *ffi_wordarray_copy_0(t1 *a1)
{
    WordArray_u8 *r2;
    
    ;
    r2 = wordarray_copy_0(*a1);
    return r2;
}
u8 *ffi_wordarray_get_0(t2 *a3)
{
    u8 *r4;
    
    r4 = malloc(sizeof(u8));
    *r4 = wordarray_get_0(*a3);
    return r4;
}
u32 *ffi_wordarray_length_0(WordArray_u8 *a5)
{
    u32 *r6;
    
    r6 = malloc(sizeof(u32));
    *r6 = wordarray_length_0(a5);
    return r6;
}
SysState *ffi_wordarray_free_0(t3 *a7)
{
    SysState *r8;
    
    ;
    r8 = wordarray_free_0(*a7);
    return r8;
}
t5 *ffi_wordarray_create_0(t4 *a9)
{
    t5 *r10;
    
    r10 = malloc(sizeof(t5));
    *r10 = wordarray_create_0(*a9);
    return r10;
}
t7 *ffi_wordarray_put_0(t6 *a11)
{
    t7 *r12;
    
    r12 = malloc(sizeof(t7));
    *r12 = wordarray_put_0(*a11);
    return r12;
}
t15 *ffi_wordarray_map_0(t13 *a13)
{
    t15 *r14;
    
    r14 = malloc(sizeof(t15));
    *r14 = wordarray_map_0(*a13);
    return r14;
}
t20 *ffi_wordarray_modify_0(t19 *a15)
{
    t20 *r16;
    
    r16 = malloc(sizeof(t20));
    *r16 = wordarray_modify_0(*a15);
    return r16;
}
u32 *ffi_wordarray_length_u8(WordArray_u8 *a4)
{
    u32 *r5;
    
    r5 = malloc(sizeof(u32));
    *r5 = wordarray_length_u8(a4);
    return r5;
}
__attribute__((pure)) u32 wordarray_length_u8(WordArray_u8 *a1)
{
    WordArray_u8 *r2 = a1;
    u32 r3 = wordarray_length_0(r2);
    
    return r3;
}
SysState *ffi_wordarray_free_u8(t3 *a4)
{
    SysState *r5;
    
    ;
    r5 = wordarray_free_u8(*a4);
    return r5;
}
SysState *wordarray_free_u8(t3 a1)
{
    t3 r2 = a1;
    SysState *r3 = wordarray_free_0(r2);
    
    return r3;
}
t5 *ffi_wordarray_clone_0(t3 *a24)
{
    t5 *r25;
    
    r25 = malloc(sizeof(t5));
    *r25 = wordarray_clone_0(*a24);
    return r25;
}
static inline t5 wordarray_clone_0(t3 a1)
{
    SysState *r2 = a1.p1;
    WordArray_u8 *r3 = a1.p2;
    u32 r4 = wordarray_length_0(r3);
    t5 r5;
    
    if (LET_TRUE) {
        t4 r6;
        
        r6.p1 = r2;
        r6.p2 = r4;
        
        t4 r7 = r6;
        
        r5 = wordarray_create_0(r7);
    } else
        ;
    
    t5 r8;
    
    if (r5.tag == TAG_ENUM_Error) {
        t5 r9;
        
        r9.tag = TAG_ENUM_Error;
        r9.Error = r5.Error;
        
        t5 r10 = r9;
        
        r8 = r10;
    } else {
        t3 r11 = r5.Success;
        SysState *r12 = r11.p1;
        WordArray_u8 *r13 = r11.p2;
        u32 r14 = 0U;
        u32 r15 = 0U;
        t1 r16;
        
        r16.p1 = r13;
        r16.p2 = r3;
        r16.p3 = r14;
        r16.p4 = r15;
        r16.p5 = r4;
        
        t1 r17 = r16;
        WordArray_u8 *r18 = wordarray_copy_0(r17);
        t3 r19;
        
        r19.p1 = r12;
        r19.p2 = r18;
        
        t3 r20 = r19;
        t5 r21;
        
        r21.tag = TAG_ENUM_Success;
        r21.Success = r20;
        
        t5 r22 = r21;
        
        r8 = r22;
    }
    
    t5 r23 = r8;
    
    return r23;
}
t5 *ffi_wordarray_clone_u8(t3 *a4)
{
    t5 *r5;
    
    r5 = malloc(sizeof(t5));
    *r5 = wordarray_clone_u8(*a4);
    return r5;
}
t5 wordarray_clone_u8(t3 a1)
{
    t3 r2 = a1;
    t5 r3 = wordarray_clone_0(r2);
    
    return r3;
}
t5 *ffi_wordarray_create_u8(t4 *a4)
{
    t5 *r5;
    
    r5 = malloc(sizeof(t5));
    *r5 = wordarray_create_u8(*a4);
    return r5;
}
t5 wordarray_create_u8(t4 a1)
{
    t4 r2 = a1;
    t5 r3 = wordarray_create_0(r2);
    
    return r3;
}
t21 *ffi_wordarray_get_bounded_0(t2 *a16)
{
    t21 *r17;
    
    r17 = malloc(sizeof(t21));
    *r17 = wordarray_get_bounded_0(*a16);
    return r17;
}
static inline __attribute__((pure)) t21 wordarray_get_bounded_0(t2 a1)
{
    WordArray_u8 *r2 = a1.p1;
    u32 r3 = a1.p2;
    u32 r4 = wordarray_length_0(r2);
    bool_t r5 = (bool_t) {.boolean = r3 < r4};
    t21 r6;
    
    if (r5.boolean) {
        t2 r7;
        
        r7.p1 = r2;
        r7.p2 = r3;
        
        t2 r8 = r7;
        u8 r9 = wordarray_get_0(r8);
        t21 r10;
        
        r10.tag = TAG_ENUM_Success;
        r10.Success = r9;
        
        t21 r11 = r10;
        
        r6 = r11;
    } else {
        unit_t r12 = (unit_t) {.dummy = 0};
        t21 r13;
        
        r13.tag = TAG_ENUM_Error;
        r13.Error = r12;
        
        t21 r14 = r13;
        
        r6 = r14;
    }
    
    t21 r15 = r6;
    
    return r15;
}
t21 *ffi_wordarray_get_bounded_u8(t2 *a4)
{
    t21 *r5;
    
    r5 = malloc(sizeof(t21));
    *r5 = wordarray_get_bounded_u8(*a4);
    return r5;
}
__attribute__((pure)) t21 wordarray_get_bounded_u8(t2 a1)
{
    t2 r2 = a1;
    t21 r3 = wordarray_get_bounded_0(r2);
    
    return r3;
}
t7 *ffi_wordarray_put_u8(t6 *a4)
{
    t7 *r5;
    
    r5 = malloc(sizeof(t7));
    *r5 = wordarray_put_u8(*a4);
    return r5;
}
t7 wordarray_put_u8(t6 a1)
{
    t6 r2 = a1;
    t7 r3 = wordarray_put_0(r2);
    
    return r3;
}
t15 *ffi_wordarray_map_u8(t13 *a4)
{
    t15 *r5;
    
    r5 = malloc(sizeof(t15));
    *r5 = wordarray_map_u8(*a4);
    return r5;
}
t15 wordarray_map_u8(t13 a1)
{
    t13 r2 = a1;
    t15 r3 = wordarray_map_0(r2);
    
    return r3;
}
t11 *ffi_map_body_f(t8 *a23)
{
    t11 *r24;
    
    r24 = malloc(sizeof(t11));
    *r24 = map_body_f(*a23);
    return r24;
}
__attribute__((const)) t11 map_body_f(t8 a1)
{
    u8 r2 = a1.elem;
    u8 r3 = a1.acc;
    u8 r4 = a1.obsv;
    u8 r5 = (u8) ((u32) r3 + (u32) r2);
    bool_t r6 = (bool_t) {.boolean = r5 < r4};
    t11 r7;
    
    if (r6.boolean) {
        t9 r8;
        
        r8.p1 = r5;
        r8.p2 = r5;
        
        t9 r9 = r8;
        unit_t r10 = (unit_t) {.dummy = 0};
        t10 r11;
        
        r11.tag = TAG_ENUM_Iterate;
        r11.Iterate = r10;
        
        t10 r12 = r11;
        t11 r13;
        
        r13.p1 = r9;
        r13.p2 = r12;
        
        t11 r14 = r13;
        
        r7 = r14;
    } else {
        t9 r15;
        
        r15.p1 = r2;
        r15.p2 = r3;
        
        t9 r16 = r15;
        unit_t r17 = (unit_t) {.dummy = 0};
        t10 r18;
        
        r18.tag = TAG_ENUM_Break;
        r18.Break = r17;
        
        t10 r19 = r18;
        t11 r20;
        
        r20.p1 = r16;
        r20.p2 = r19;
        
        t11 r21 = r20;
        
        r7 = r21;
    }
    
    t11 r22 = r7;
    
    return r22;
}
t17 *ffi_modify_body_f(t16 *a11)
{
    t17 *r12;
    
    r12 = malloc(sizeof(t17));
    *r12 = modify_body_f(*a11);
    return r12;
}
__attribute__((const)) t17 modify_body_f(t16 a1)
{
    u8 r2 = a1.elem;
    u8 r3 = a1.acc;
    bool_t r4 = a1.obsv;
    t17 r5;
    
    if (r4.boolean) {
        u8 r6 = (u8) ((u32) r2 + (u32) r3);
        u8 r7 = (u8) ((u32) r2 + (u32) r3);
        t17 r8;
        
        r8.elem = r6;
        r8.acc = r7;
        r5 = r8;
    } else {
        t17 r9;
        
        r9.elem = r2;
        r9.acc = r3;
        r5 = r9;
    }
    
    t17 r10 = r5;
    
    return r10;
}
t20 *ffi_wordarray_modify_u8(t19 *a4)
{
    t20 *r5;
    
    r5 = malloc(sizeof(t20));
    *r5 = wordarray_modify_u8(*a4);
    return r5;
}
t20 wordarray_modify_u8(t19 a1)
{
    t19 r2 = a1;
    t20 r3 = wordarray_modify_0(r2);
    
    return r3;
}
u16 u8_to_u16(u8 x)
{
    return (u16) x;
}
u32 u8_to_u32(u8 x)
{
    return (u32) x;
}
u64 u8_to_u64(u8 x)
{
    return (u64) x;
}
u8 u16_to_u8(u16 x)
{
    return (u8) x;
}
u32 u16_to_u32(u16 x)
{
    return (u32) x;
}
u8 u32_to_u8(u32 x)
{
    return (u8) x;
}
u16 u32_to_u16(u32 x)
{
    return (u16) x;
}
u64 u32_to_u64(u32 x)
{
    return (u64) x;
}
u32 u64_to_u32(u64 x)
{
    return (u32) x;
}
u8 u64_to_u8(u64 x)
{
    return (u8) x;
}
u16 u64_to_u16(u64 x)
{
    return (u16) x;
}
unit_t cogent_assert(bool_t arg)
{
    unit_t ret;
    
    ;
    return ret;
}
unit_t cogent_debug(char *str)
{
    unit_t ret;
    
    printf("%s", str);
    return ret;
}
unit_t cogent_debug_u32(u32 arg)
{
    unit_t ret;
    
    printf("%u", arg);
    return ret;
}
unit_t cogent_debug_u64(u64 arg)
{
    unit_t ret;
    
    printf("%llu", arg);
    return ret;
}
unit_t cogent_debug_u32_hex(u32 arg)
{
    unit_t ret;
    
    printf("%x", arg);
    return ret;
}
unit_t cogent_debug_u64_hex(u64 arg)
{
    unit_t ret;
    
    printf("%llx", arg);
    return ret;
}
u8 wordarray_get_0(t2 args)
{
    if (args.p2 >= args.p1->len)
        return 0;
    return args.p1->values[args.p2];
}
t7 wordarray_put_0(t6 args)
{
    t7 ret;
    
    if (args.idx >= args.arr->len) {
        ret.tag = TAG_ENUM_Error;
        ret.Error = args.arr;
    } else {
        args.arr->values[args.idx] = args.val;
        ret.tag = TAG_ENUM_Success;
        ret.Success = args.arr;
    }
    return ret;
}
u32 wordarray_length_0(WordArray_u8 *array)
{
    return array->len;
}
t20 wordarray_modify_0(t19 args)
{
    t20 ret;
    t16 fargs;
    t17 fret;
    
    if (args.idx >= args.arr->len) {
        ret.acc = args.acc;
        ret.arr = args.arr;
        return ret;
    }
    fargs.elem = args.arr->values[args.idx];
    fargs.acc = args.acc;
    fargs.obsv = args.obsv;
    fret = dispatch_t18(args.f, fargs);
    args.arr->values[args.idx] = fret.elem;
    ret.acc = fret.acc;
    ret.arr = args.arr;
    return ret;
}
t15 wordarray_map_0(t13 args)
{
    t10 default_variant = {.tag =TAG_ENUM_Iterate};
    t14 init_ret = {.p1 =args.arr, .p2 =args.acc};
    t15 ret = {.p1 =init_ret, .p2 =default_variant};
    
    ret.p2.tag = TAG_ENUM_Iterate;
    
    t8 fargs = {.obsv =args.obsv};
    u32 i;
    
    for (i = args.frm; i < args.to && i < args.arr->len; i++) {
        fargs.elem = args.arr->values[i];
        fargs.acc = ret.p1.p2;
        
        t11 fret = dispatch_t12(args.f, fargs);
        
        args.arr->values[i] = fret.p1.p1;
        ret.p1.p2 = fret.p1.p2;
        ret.p2 = fret.p2;
        if (fret.p2.tag == TAG_ENUM_Break)
            break;
    }
    return ret;
}
WordArray_u8 *wordarray_copy_0(t1 args)
{
    WordArray_u8 *dst = args.p1;
    WordArray_u8 *src = args.p2;
    u32 dst_index = args.p3;
    u32 src_index = args.p4;
    u32 len = args.p5;
    
    if (dst_index > dst->len)
        return dst;
    
    int dst_avail = dst->len - dst_index;
    
    if (len > dst_avail)
        len = dst_avail;
    
    int src_avail = src->len - src_index;
    
    if (len > src_avail)
        len = src_avail;
    memcpy(dst->values + dst_index, src->values + src_index, len);
    return dst;
}
t5 wordarray_create_0(t4 args)
{
    SysState *ex = args.p1;
    u32 size = args.p2;
    t5 ret;
    WordArray_u8 *array = kmalloc(sizeof(*array));
    
    if (array == NULL || !size) {
        ret.tag = TAG_ENUM_Error;
        ret.Error = ex;
    } else {
        array->values = kzalloc(size * sizeof(*array->values));
        if (array->values == NULL) {
            kfree(array);
            ret.tag = TAG_ENUM_Error;
            ret.Error = ex;
        } else {
            array->len = size;
            ret.tag = TAG_ENUM_Success;
            ret.Success.p1 = ex;
            ret.Success.p2 = array;
        }
    }
    return ret;
}
SysState *wordarray_free_0(t3 args)
{
    WordArray_u8 *array = args.p2;
    
    if (array->values)
        kfree(array->values);
    kfree(array);
    return args.p1;
}



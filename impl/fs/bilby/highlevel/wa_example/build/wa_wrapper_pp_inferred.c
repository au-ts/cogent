/*
This build info header is now disabled by --fno-gen-header.
--------------------------------------------------------------------------------
We strongly discourage users from generating individual files for Isabelle
proofs, as it will end up with an inconsistent collection of output files (i.e.
Isabelle input files).
*/

#include <adt.h>
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
    FUN_ENUM_wordarray_create_0,
    FUN_ENUM_wordarray_create_u8,
    FUN_ENUM_wordarray_free_0,
    FUN_ENUM_wordarray_free_u8,
    FUN_ENUM_wordarray_map_0,
    FUN_ENUM_wordarray_map_u8,
} ;
typedef enum untyped_func_enum untyped_func_enum;
typedef untyped_func_enum t14;
typedef untyped_func_enum t15;
typedef untyped_func_enum t16;
typedef untyped_func_enum t8;
typedef untyped_func_enum t17;
struct WordArray_u8 {
    int len;
    u8 *values;
} ;
typedef struct WordArray_u8 WordArray_u8;
struct t1 {
    SysState *p1;
    WordArray_u8 *p2;
} ;
typedef struct t1 t1;
struct t2 {
    SysState *p1;
    u32 p2;
} ;
typedef struct t2 t2;
struct t3 {
    tag_t tag;
    SysState *Error;
    t1 Success;
} ;
typedef struct t3 t3;
struct t4 {
    u8 elem;
    u8 acc;
    u8 obsv;
} ;
typedef struct t4 t4;
struct t5 {
    u8 p1;
    u8 p2;
} ;
typedef struct t5 t5;
struct t6 {
    tag_t tag;
    unit_t Break;
    unit_t Iterate;
} ;
typedef struct t6 t6;
struct t7 {
    t5 p1;
    t6 p2;
} ;
typedef struct t7 t7;
struct t9 {
    WordArray_u8 *arr;
    u32 frm;
    u32 to;
    t8 f;
    u8 acc;
    u8 obsv;
} ;
typedef struct t9 t9;
struct t10 {
    WordArray_u8 *p1;
    u8 p2;
} ;
typedef struct t10 t10;
struct t11 {
    t10 p1;
    t6 p2;
} ;
typedef struct t11 t11;
struct t12 {
    tag_t tag;
    unit_t Iterate;
} ;
typedef struct t12 t12;
struct t13 {
    tag_t tag;
    unit_t Break;
} ;
typedef struct t13 t13;
static inline SysState *wordarray_free_0(t1);
static inline t3 wordarray_create_0(t2);
static inline t11 wordarray_map_0(t9);
SysState *wordarray_free_u8(t1);
t3 wordarray_create_u8(SysState *);
t11 wordarray_map_u8(t9);
__attribute__((const)) t7 map_body_f(t4);
static inline t3 dispatch_t14(untyped_func_enum a2, SysState *a3)
{
    return wordarray_create_u8(a3);
}
static inline SysState *dispatch_t15(untyped_func_enum a2, t1 a3)
{
    switch (a2) {
        
      case FUN_ENUM_wordarray_free_0:
        return wordarray_free_0(a3);
        
      default:
        return wordarray_free_u8(a3);
    }
}
static inline t3 dispatch_t16(untyped_func_enum a2, t2 a3)
{
    return wordarray_create_0(a3);
}
static inline t7 dispatch_t8(untyped_func_enum a2, t4 a3)
{
    return map_body_f(a3);
}
static inline t11 dispatch_t17(untyped_func_enum a2, t9 a3)
{
    switch (a2) {
        
      case FUN_ENUM_wordarray_map_0:
        return wordarray_map_0(a3);
        
      default:
        return wordarray_map_u8(a3);
    }
}
typedef WordArray_u8 CString;
typedef u32 ErrCode;
typedef u32 WordArrayIndex;
typedef t4 map_body_f_arg;
typedef t7 map_body_f_ret;
typedef t2 wordarray_create_0_arg;
typedef t3 wordarray_create_0_ret;
typedef SysState *wordarray_create_u8_arg;
typedef t3 wordarray_create_u8_ret;
typedef t1 wordarray_free_0_arg;
typedef SysState *wordarray_free_0_ret;
typedef t1 wordarray_free_u8_arg;
typedef SysState *wordarray_free_u8_ret;
typedef t9 wordarray_map_0_arg;
typedef t11 wordarray_map_0_ret;
typedef t9 wordarray_map_u8_arg;
typedef t11 wordarray_map_u8_ret;
SysState *wordarray_free_u8(t1 a1)
{
    t1 r2 = a1;
    SysState *r3 = wordarray_free_0(r2);
    
    return r3;
}
t3 wordarray_create_u8(SysState *a1)
{
    SysState *r2 = a1;
    u8 r3 = 1U;
    u32 r4 = (u32) r3;
    t2 r5 = (t2) {.p1 = r2, .p2 = r4};
    t3 r6 = wordarray_create_0(r5);
    
    return r6;
}
t11 wordarray_map_u8(t9 a1)
{
    t9 r2 = a1;
    t11 r3 = wordarray_map_0(r2);
    
    return r3;
}
__attribute__((const)) t7 map_body_f(t4 a1)
{
    u8 r2 = a1.elem;
    u8 r3 = a1.acc;
    u8 r4 = a1.obsv;
    u8 r5 = (u8) ((u32) r3 + (u32) r2);
    bool_t r6 = (bool_t) {.boolean = r5 < r4};
    t7 r7;
    
    if (r6.boolean) {
        t5 r8 = (t5) {.p1 = r5, .p2 = r5};
        unit_t r9 = (unit_t) {.dummy = 0};
        t12 r10 = (t12) {.tag = TAG_ENUM_Iterate, .Iterate = r9};
        t6 r11 = (t6) {.tag = r10.tag, .Iterate = r10.Iterate};
        
        r7 = (t7) {.p1 = r8, .p2 = r11};
    } else {
        t5 r12 = (t5) {.p1 = r2, .p2 = r3};
        unit_t r13 = (unit_t) {.dummy = 0};
        t13 r14 = (t13) {.tag = TAG_ENUM_Break, .Break = r13};
        t6 r15 = (t6) {.tag = r14.tag, .Break = r14.Break};
        
        r7 = (t7) {.p1 = r12, .p2 = r15};
    }
    
    t7 r16 = r7;
    
    return r16;
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
t11 wordarray_map_0(t9 args)
{
    t6 default_variant = {.tag =TAG_ENUM_Iterate};
    t10 init_ret = {.p1 =args.arr, .p2 =args.acc};
    t11 ret = {.p1 =init_ret, .p2 =default_variant};
    
    ret.p2.tag = TAG_ENUM_Iterate;
    
    t4 fargs = {.obsv =args.obsv};
    u32 i;
    
    for (i = args.frm; i < args.to && i < args.arr->len; i++) {
        fargs.elem = args.arr->values[i];
        fargs.acc = ret.p1.p2;
        
        t7 fret = dispatch_t8(args.f, fargs);
        
        args.arr->values[i] = fret.p1.p1;
        ret.p1.p2 = fret.p1.p2;
        ret.p2 = fret.p2;
        if (fret.p2.tag == TAG_ENUM_Break)
            break;
    }
    return ret;
}
t3 wordarray_create_0(t2 args)
{
    SysState *ex = args.p1;
    u32 size = args.p2;
    t3 ret;
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
SysState *wordarray_free_0(t1 args)
{
    WordArray_u8 *array = args.p2;
    
    if (array->values)
        kfree(array->values);
    kfree(array);
    return args.p1;
}



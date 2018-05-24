/*
This build info header is now disabled by --fno-gen-header.
--------------------------------------------------------------------------------
We strongly discourage users from generating individual files for Isabelle
proofs, as it will end up with an inconsistent collection of output files (i.e.
Isabelle input files).
*/

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
struct SysState_t {
    char dummy;
} ;
typedef struct SysState_t SysState;
typedef void Buffer;
typedef char *CString;
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
    TAG_ENUM_None,
    TAG_ENUM_Some,
    TAG_ENUM_Success,
} ;
typedef enum tag_t tag_t;
enum untyped_func_enum {
    FUN_ENUM_array_print,
    FUN_ENUM_cmp_inc,
    FUN_ENUM_deserialise_CString,
    FUN_ENUM_deserialise_Node,
    FUN_ENUM_deserialise_U32,
    FUN_ENUM_find_str,
    FUN_ENUM_free_Node,
    FUN_ENUM_malloc_Node,
    FUN_ENUM_seq32_0,
    FUN_ENUM_string_cmp,
} ;
typedef enum untyped_func_enum untyped_func_enum;
typedef untyped_func_enum t26;
typedef untyped_func_enum t27;
typedef untyped_func_enum t28;
typedef untyped_func_enum t29;
typedef untyped_func_enum t30;
typedef untyped_func_enum t31;
typedef untyped_func_enum t32;
typedef untyped_func_enum t7;
typedef untyped_func_enum t33;
typedef untyped_func_enum t34;
struct t1 {
    SysState *p1;
    u32 p2;
} ;
typedef struct t1 t1;
struct t2 {
    Buffer *p1;
    CString p2;
} ;
typedef struct t2 t2;
struct t3 {
    t1 acc;
    t2 obsv;
    u32 idx;
} ;
typedef struct t3 t3;
struct t4 {
    u32 len;
    CString key;
} ;
typedef struct t4 t4;
struct t5 {
    tag_t tag;
    t4 *Break;
    unit_t Iterate;
} ;
typedef struct t5 t5;
struct t6 {
    t1 p1;
    t5 p2;
} ;
typedef struct t6 t6;
struct t8 {
    u32 frm;
    u32 to;
    u32 step;
    t7 f;
    t1 acc;
    t2 obsv;
} ;
typedef struct t8 t8;
struct t9 {
    SysState *p1;
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
    SysState *p1;
    t10 p2;
} ;
typedef struct t11 t11;
struct t12 {
    SysState *p1;
    CString p2;
} ;
typedef struct t12 t12;
struct t13 {
    CString p1;
    CString p2;
} ;
typedef struct t13 t13;
struct t14 {
    SysState *p1;
    Buffer *p2;
    u32 p3;
    u32 p4;
} ;
typedef struct t14 t14;
struct t15 {
    CString p1;
    u32 p2;
} ;
typedef struct t15 t15;
struct t16 {
    tag_t tag;
    u32 Error;
    t15 Success;
} ;
typedef struct t16 t16;
struct t17 {
    SysState *p1;
    t16 p2;
} ;
typedef struct t17 t17;
struct t18 {
    SysState *p1;
    Buffer *p2;
    u32 p3;
} ;
typedef struct t18 t18;
struct t19 {
    SysState *p1;
    u32 p2;
    u32 p3;
} ;
typedef struct t19 t19;
struct t20 {
    t4 *p1;
    u32 p2;
} ;
typedef struct t20 t20;
struct t21 {
    tag_t tag;
    u32 Error;
    t20 Success;
} ;
typedef struct t21 t21;
struct t22 {
    SysState *p1;
    t21 p2;
} ;
typedef struct t22 t22;
struct t23 {
    SysState *p1;
    Buffer *p2;
    CString p3;
} ;
typedef struct t23 t23;
struct t24 {
    tag_t tag;
    unit_t None;
    t4 *Some;
} ;
typedef struct t24 t24;
struct t25 {
    SysState *p1;
    t24 p2;
} ;
typedef struct t25 t25;
static inline t6 seq32_0(t8);
static inline SysState *free_Node(t9);
static inline t11 malloc_Node(SysState *);
static inline SysState *array_print(t12);
static inline bool_t string_cmp(t13);
static inline t17 deserialise_CString(t14);
static inline t19 deserialise_U32(t18);
static inline t22 deserialise_Node(t18);
static inline t6 cmp_inc(t3);
static inline t25 find_str(t23);
static inline t11 dispatch_t26(untyped_func_enum a2, SysState *a3)
{
    return malloc_Node(a3);
}
static inline SysState *dispatch_t27(untyped_func_enum a2, t12 a3)
{
    return array_print(a3);
}
static inline bool_t dispatch_t28(untyped_func_enum a2, t13 a3)
{
    return string_cmp(a3);
}
static inline t17 dispatch_t29(untyped_func_enum a2, t14 a3)
{
    return deserialise_CString(a3);
}
static inline t19 dispatch_t30(untyped_func_enum a2, t18 a3)
{
    return deserialise_U32(a3);
}
static inline t22 dispatch_t31(untyped_func_enum a2, t18 a3)
{
    return deserialise_Node(a3);
}
static inline t25 dispatch_t32(untyped_func_enum a2, t23 a3)
{
    return find_str(a3);
}
static inline t6 dispatch_t7(untyped_func_enum a2, t3 a3)
{
    return cmp_inc(a3);
}
static inline t6 dispatch_t33(untyped_func_enum a2, t8 a3)
{
    return seq32_0(a3);
}
static inline SysState *dispatch_t34(untyped_func_enum a2, t9 a3)
{
    return free_Node(a3);
}
typedef u32 ErrCode;
typedef u32 Index;
typedef t4 Node;
typedef u32 WordArrayIndex;
typedef t12 array_print_arg;
typedef SysState *array_print_ret;
typedef t3 cmp_inc_arg;
typedef t6 cmp_inc_ret;
typedef t14 deserialise_CString_arg;
typedef t17 deserialise_CString_ret;
typedef t18 deserialise_Node_arg;
typedef t22 deserialise_Node_ret;
typedef t18 deserialise_U32_arg;
typedef t19 deserialise_U32_ret;
typedef t23 find_str_arg;
typedef t25 find_str_ret;
typedef t9 free_Node_arg;
typedef SysState *free_Node_ret;
typedef SysState *malloc_Node_arg;
typedef t11 malloc_Node_ret;
typedef t8 seq32_0_arg;
typedef t6 seq32_0_ret;
typedef t13 string_cmp_arg;
typedef bool_t string_cmp_ret;
static inline t22 deserialise_Node(t18 a1)
{
    SysState *r2 = a1.p1;
    Buffer *r3 = a1.p2;
    u32 r4 = a1.p3;
    t11 r5 = malloc_Node(r2);
    SysState *r6 = r5.p1;
    t10 r7 = r5.p2;
    t22 r8;
    
    if (r7.tag == TAG_ENUM_Success) {
        t18 r9;
        
        r9.p1 = r6;
        r9.p2 = r3;
        r9.p3 = r4;
        
        t18 r10 = r9;
        t19 r11 = deserialise_U32(r10);
        SysState *r12 = r11.p1;
        u32 r13 = r11.p2;
        u32 r14 = r11.p3;
        t17 r15;
        
        if (LETBANG_TRUE) {
            t14 r16;
            
            r16.p1 = r12;
            r16.p2 = r3;
            r16.p3 = r14;
            r16.p4 = r13;
            
            t14 r17 = r16;
            
            r15 = deserialise_CString(r17);
        } else
            ;
        
        SysState *r18 = r15.p1;
        t16 r19 = r15.p2;
        t22 r20;
        
        if (r19.tag == TAG_ENUM_Success) {
            CString r21 = r19.Success.p1;
            u32 r22 = r19.Success.p2;
            t4 *r23 = r7.Success;
            
            (*r23).len = r13;
            
            t4 *r24 = r23;
            t4 *r25 = r24;
            
            (*r25).key = r21;
            
            t4 *r26 = r25;
            t20 r27;
            
            r27.p1 = r26;
            r27.p2 = r22;
            
            t20 r28 = r27;
            t21 r29;
            
            r29.tag = TAG_ENUM_Success;
            r29.Success = r28;
            
            t21 r30 = r29;
            t22 r31;
            
            r31.p1 = r18;
            r31.p2 = r30;
            
            t22 r32 = r31;
            
            r20 = r32;
        } else {
            u32 r33 = r19.Error;
            t9 r34;
            
            r34.p1 = r18;
            r34.p2 = r7.Success;
            
            t9 r35 = r34;
            SysState *r36 = free_Node(r35);
            t21 r37;
            
            r37.tag = TAG_ENUM_Error;
            r37.Error = r33;
            
            t21 r38 = r37;
            t22 r39;
            
            r39.p1 = r36;
            r39.p2 = r38;
            
            t22 r40 = r39;
            
            r20 = r40;
        }
        r8 = r20;
    } else {
        u32 r41 = r7.Error;
        t21 r42;
        
        r42.tag = TAG_ENUM_Error;
        r42.Error = r41;
        
        t21 r43 = r42;
        t22 r44;
        
        r44.p1 = r6;
        r44.p2 = r43;
        
        t22 r45 = r44;
        
        r8 = r45;
    }
    
    t22 r46 = r8;
    
    return r46;
}
static inline t6 cmp_inc(t3 a1)
{
    t1 r2 = a1.acc;
    SysState *r3 = r2.p1;
    u32 r4 = r2.p2;
    t2 r5 = a1.obsv;
    Buffer *r6 = r5.p1;
    CString r7 = r5.p2;
    t18 r8;
    
    r8.p1 = r3;
    r8.p2 = r6;
    r8.p3 = r4;
    
    t18 r9 = r8;
    t22 r10 = deserialise_Node(r9);
    SysState *r11 = r10.p1;
    t21 r12 = r10.p2;
    t6 r13;
    
    if (r12.tag == TAG_ENUM_Success) {
        t4 *r14 = r12.Success.p1;
        u32 r15 = r12.Success.p2;
        bool_t r16;
        
        if (LETBANG_TRUE) {
            CString r17 = (*r14).key;
            t13 r18;
            
            r18.p1 = r17;
            r18.p2 = r7;
            
            t13 r19 = r18;
            
            r16 = string_cmp(r19);
        } else
            ;
        
        t6 r20;
        
        if (r16.boolean) {
            t1 r21;
            
            r21.p1 = r11;
            r21.p2 = r15;
            
            t1 r22 = r21;
            t5 r23;
            
            r23.tag = TAG_ENUM_Break;
            r23.Break = r14;
            
            t5 r24 = r23;
            t6 r25;
            
            r25.p1 = r22;
            r25.p2 = r24;
            
            t6 r26 = r25;
            
            r20 = r26;
        } else {
            u32 r27 = (*r14).len;
            CString r28 = (*r14).key;
            t9 r29;
            
            r29.p1 = r11;
            r29.p2 = r14;
            
            t9 r30 = r29;
            SysState *r31 = free_Node(r30);
            t1 r32;
            
            r32.p1 = r31;
            r32.p2 = r15;
            
            t1 r33 = r32;
            unit_t r34 = (unit_t) {.dummy = 0};
            t5 r35;
            
            r35.tag = TAG_ENUM_Iterate;
            r35.Iterate = r34;
            
            t5 r36 = r35;
            t6 r37;
            
            r37.p1 = r33;
            r37.p2 = r36;
            
            t6 r38 = r37;
            
            r20 = r38;
        }
        r13 = r20;
    } else {
        u32 r39 = r12.Error;
        t1 r40;
        
        r40.p1 = r11;
        r40.p2 = r4;
        
        t1 r41 = r40;
        unit_t r42 = (unit_t) {.dummy = 0};
        t5 r43;
        
        r43.tag = TAG_ENUM_Iterate;
        r43.Iterate = r42;
        
        t5 r44 = r43;
        t6 r45;
        
        r45.p1 = r41;
        r45.p2 = r44;
        
        t6 r46 = r45;
        
        r13 = r46;
    }
    
    t6 r47 = r13;
    
    return r47;
}
static inline t25 find_str(t23 a1)
{
    SysState *r2 = a1.p1;
    Buffer *r3 = a1.p2;
    CString r4 = a1.p3;
    u32 r5 = 0U;
    u32 r6 = (u32) r5;
    u32 r7 = 3U;
    u32 r8 = (u32) r7;
    u32 r9 = 1U;
    u32 r10 = (u32) r9;
    t7 r11 = FUN_ENUM_cmp_inc;
    u32 r12 = 0U;
    t1 r13;
    
    r13.p1 = r2;
    r13.p2 = r12;
    
    t1 r14 = r13;
    t2 r15;
    
    r15.p1 = r3;
    r15.p2 = r4;
    
    t2 r16 = r15;
    t8 r17;
    
    r17.frm = r6;
    r17.to = r8;
    r17.step = r10;
    r17.f = r11;
    r17.acc = r14;
    r17.obsv = r16;
    
    t8 r18 = r17;
    t6 r19 = seq32_0(r18);
    t1 r20 = r19.p1;
    t5 r21 = r19.p2;
    SysState *r22 = r20.p1;
    u32 r23 = r20.p2;
    u32 r24 = r23;
    t25 r25;
    
    if (r21.tag == TAG_ENUM_Iterate) {
        unit_t r26 = r21.Iterate;
        unit_t r27 = (unit_t) {.dummy = 0};
        t24 r28;
        
        r28.tag = TAG_ENUM_None;
        r28.None = r27;
        
        t24 r29 = r28;
        t25 r30;
        
        r30.p1 = r22;
        r30.p2 = r29;
        
        t25 r31 = r30;
        
        r25 = r31;
    } else {
        t4 *r32 = r21.Break;
        t24 r33;
        
        r33.tag = TAG_ENUM_Some;
        r33.Some = r32;
        
        t24 r34 = r33;
        t25 r35;
        
        r35.p1 = r22;
        r35.p2 = r34;
        
        t25 r36 = r35;
        
        r25 = r36;
    }
    
    t25 r37 = r25;
    
    return r37;
}
t17 deserialise_CString(t14 args)
{
    deserialise_CString_ret ret;
    char *dst = malloc(sizeof(char) * args.p4);
    
    memcpy(dst, args.p2 + args.p3, args.p4);
    ret.p1 = args.p1;
    ret.p2.tag = TAG_ENUM_Success;
    
    CString wa = dst;
    
    ret.p2.Success.p1 = wa;
    ret.p2.Success.p2 = args.p3 + args.p4 * sizeof(char);
    return ret;
}
t19 deserialise_U32(t18 args)
{
    t19 ret;
    
    ret.p1 = args.p1;
    ret.p2 = ((char *) args.p2)[args.p3];
    ret.p3 = args.p3 + sizeof(u32);
    return ret;
}
t11 malloc_Node(SysState *args)
{
    t11 ret;
    t4 *node = malloc(sizeof(t4 *));
    
    ret.p1 = args;
    if (node) {
        ret.p2.tag = TAG_ENUM_Success;
        ret.p2.Success = node;
    } else {
        ret.p2.tag = TAG_ENUM_Error;
        ret.p2.Error = 1;
    }
    return ret;
}
SysState *free_Node(t9 args)
{
    SysState *ret = args.p1;
    
    free(args.p2);
    return ret;
}
SysState *free_CString(t12 args)
{
    SysState *ret = args.p1;
    
    free(args.p2);
    return ret;
}
bool_t string_cmp(t13 args)
{
    int r = strcmp(args.p1, args.p2);
    
    if (r == 0)
        return ({
                    (bool_t) {.boolean = 1U};
                });
    else
        return ({
                    (bool_t) {.boolean = 0U};
                });
}
SysState *array_print(t12 args)
{
    printf("%s", args.p2);
    return args.p1;
}
t6 seq32_0(t8 args)
{
    u32 i;
    t6 ret;
    t3 fargs;
    
    ret.p2.tag = TAG_ENUM_Iterate;
    ret.p1 = args.acc;
    if (!args.step)
        return ret;
    fargs.acc = args.acc;
    fargs.obsv = args.obsv;
    for (i = args.frm; i < args.to; i += args.step) {
        fargs.idx = i;
        ret = dispatch_t7(args.f, fargs);
        if (ret.p2.tag == TAG_ENUM_Break)
            return ret;
        else
            fargs.acc = ret.p1;
    }
    return ret;
}
int main(void)
{
    t4 n1, n2, n3;
    
    n1.len = 7;
    n2.len = 3;
    n3.len = 7;
    n1.key = "Data61";
    n2.key = "TS";
    n3.key = "Cogent";
    
    Buffer *buf = malloc(100);
    
    if (!buf)
        return 1;
    memset(buf, '\0', 100);
    
    Buffer *curr = buf;
    
    memcpy(curr, &n1, sizeof(u32));
    curr += sizeof(u32);
    memcpy(curr, n1.key, n1.len);
    curr += n1.len;
    memcpy(curr, &n2, sizeof(u32));
    curr += sizeof(u32);
    memcpy(curr, n2.key, n2.len);
    curr += n2.len;
    memcpy(curr, &n3, sizeof(u32));
    curr += sizeof(u32);
    memcpy(curr, n3.key, n3.len);
    curr += n3.len;
    
    SysState *ex;
    t23 find_args;
    
    find_args.p1 = ex;
    find_args.p2 = buf;
    find_args.p3 = "Cogent";
    
    t25 r = dispatch_t32(FUN_ENUM_find_str, find_args);
    
    if (r.p2.tag == TAG_ENUM_None)
        printf("Not found!\n");
    else {
        printf("Found element ");
        
        t12 print_arg;
        
        print_arg.p1 = r.p1;
        print_arg.p2 = r.p2.Some->key;
        dispatch_t27(FUN_ENUM_array_print, print_arg);
        printf("\n");
    }
    return 0;
}



// This build info header is now disabled by --fno-gen-header.
// --------------------------------------------------------------------------------
// We strongly discourage users from generating individual files for Isabelle
// proofs, as it will end up with an inconsistent collection of output files (i.e.
// Isabelle input files).

#include "demo.h"

static inline u64 u16_to_u64(u16 a1)
{
    u16 r2 = a1;
    u32 r3 = u16_to_u32(r2);
    u64 r4 = u32_to_u64(r3);
    
    return r4;
}
static inline u64 to_u64(u64 a1)
{
    u64 r2 = a1;
    u64 r3 = r2;
    
    return r3;
}
static inline u32 to_u32(u32 a1)
{
    u32 r2 = a1;
    u32 r3 = r2;
    
    return r3;
}
static inline u16 to_u16(u16 a1)
{
    u16 r2 = a1;
    u16 r3 = r2;
    
    return r3;
}
static inline u64 min_u64(t19 a1)
{
    u64 r2 = a1.p1;
    u64 r3 = a1.p2;
    bool_t r4 = (bool_t) {.boolean = r2 < r3};
    u64 r5;
    
    if (r4.boolean) {
        r5 = r2;
    } else {
        r5 = r3;
    }
    
    u64 r6 = r5;
    
    return r6;
}
static inline u32 min_u32(t20 a1)
{
    u32 r2 = a1.p1;
    u32 r3 = a1.p2;
    bool_t r4 = (bool_t) {.boolean = r2 < r3};
    u32 r5;
    
    if (r4.boolean) {
        r5 = r2;
    } else {
        r5 = r3;
    }
    
    u32 r6 = r5;
    
    return r6;
}
static inline bool_t in_range_u32(t21 a1)
{
    u32 r2 = a1.p1;
    u32 r3 = a1.p2;
    u32 r4 = a1.p3;
    bool_t r5 = (bool_t) {.boolean = r2 >= r3};
    bool_t r6 = (bool_t) {.boolean = r2 < r4};
    bool_t r7 = (bool_t) {.boolean = r5.boolean && r6.boolean};
    bool_t r8;
    
    if (r7.boolean) {
        r8 = (bool_t) {.boolean = 1U};
    } else {
        r8 = (bool_t) {.boolean = 0U};
    }
    
    bool_t r9 = r8;
    
    return r9;
}
static inline u16 cogent_low_16_bits(u32 a1)
{
    u32 r2 = a1;
    u16 r3 = 65535U;
    u32 r4 = (u32) r3;
    u32 r5 = r2 & r4;
    u16 r6 = u32_to_u16(r5);
    
    return r6;
}
static inline u16 cogent_high_16_bits(u32 a1)
{
    u32 r2 = a1;
    u32 r3 = 4294901760UL;
    u32 r4 = r2 & r3;
    u8 r5 = 16U;
    u32 r6 = u8_to_u32(r5);
    u32 r7 = r6 >= 32U ? 0U : r4 >> r6;
    u16 r8 = u32_to_u16(r7);
    
    return r8;
}
static inline u64 align64(t19 a1)
{
    u64 r2 = a1.p1;
    u64 r3 = a1.p2;
    u8 r4 = 1U;
    u64 r5 = (u64) r4;
    u64 r6 = r3 - r5;
    u64 r7 = r2 + r6;
    u8 r8 = 1U;
    u64 r9 = (u64) r8;
    u64 r10 = r3 - r9;
    u64 r11 = ~r10;
    u64 r12 = r7 & r11;
    
    return r12;
}
static inline u32 align32(t20 a1)
{
    u32 r2 = a1.p1;
    u32 r3 = a1.p2;
    u8 r4 = 1U;
    u32 r5 = (u32) r4;
    u32 r6 = r3 - r5;
    u32 r7 = r2 + r6;
    u8 r8 = 1U;
    u32 r9 = (u32) r8;
    u32 r10 = r3 - r9;
    u32 r11 = ~r10;
    u32 r12 = r7 & r11;
    
    return r12;
}
static inline t22 safe_add32(t20 a1)
{
    u32 r2 = a1.p1;
    u32 r3 = a1.p2;
    u32 r4 = r2 + r3;
    bool_t r5 = (bool_t) {.boolean = r4 < r2};
    bool_t r6 = (bool_t) {.boolean = r4 < r3};
    bool_t r7 = (bool_t) {.boolean = r5.boolean || r6.boolean};
    t22 r8;
    
    if (r7.boolean) {
        unit_t r9 = (unit_t) {.dummy = 0};
        t23 r10 = (t23) {.tag = TAG_ENUM_Error, .Error = r9};
        
        r8 = (t22) {.tag = r10.tag, .Error = r10.Error};
    } else {
        t24 r11 = (t24) {.tag = TAG_ENUM_Success, .Success = r4};
        
        r8 = (t22) {.tag = r11.tag, .Success = r11.Success};
    }
    
    t22 r12 = r8;
    
    return r12;
}
static inline t25 safe_add64(t19 a1)
{
    u64 r2 = a1.p1;
    u64 r3 = a1.p2;
    u64 r4 = r2 + r3;
    bool_t r5 = (bool_t) {.boolean = r4 < r2};
    bool_t r6 = (bool_t) {.boolean = r4 < r3};
    bool_t r7 = (bool_t) {.boolean = r5.boolean || r6.boolean};
    t25 r8;
    
    if (r7.boolean) {
        unit_t r9 = (unit_t) {.dummy = 0};
        t23 r10 = (t23) {.tag = TAG_ENUM_Error, .Error = r9};
        
        r8 = (t25) {.tag = r10.tag, .Error = r10.Error};
    } else {
        t26 r11 = (t26) {.tag = TAG_ENUM_Success, .Success = r4};
        
        r8 = (t25) {.tag = r11.tag, .Success = r11.Success};
    }
    
    t25 r12 = r8;
    
    return r12;
}
static inline t22 safe_sub32(t20 a1)
{
    u32 r2 = a1.p1;
    u32 r3 = a1.p2;
    u32 r4 = r2 - r3;
    bool_t r5 = (bool_t) {.boolean = r4 > r2};
    t22 r6;
    
    if (r5.boolean) {
        unit_t r7 = (unit_t) {.dummy = 0};
        t23 r8 = (t23) {.tag = TAG_ENUM_Error, .Error = r7};
        
        r6 = (t22) {.tag = r8.tag, .Error = r8.Error};
    } else {
        t24 r9 = (t24) {.tag = TAG_ENUM_Success, .Success = r4};
        
        r6 = (t22) {.tag = r9.tag, .Success = r9.Success};
    }
    
    t22 r10 = r6;
    
    return r10;
}
static inline t25 safe_sub64(t19 a1)
{
    u64 r2 = a1.p1;
    u64 r3 = a1.p2;
    u64 r4 = r2 - r3;
    bool_t r5 = (bool_t) {.boolean = r4 > r2};
    t25 r6;
    
    if (r5.boolean) {
        unit_t r7 = (unit_t) {.dummy = 0};
        t23 r8 = (t23) {.tag = TAG_ENUM_Error, .Error = r7};
        
        r6 = (t25) {.tag = r8.tag, .Error = r8.Error};
    } else {
        t26 r9 = (t26) {.tag = TAG_ENUM_Success, .Success = r4};
        
        r6 = (t25) {.tag = r9.tag, .Success = r9.Success};
    }
    
    t25 r10 = r6;
    
    return r10;
}
static inline t29 deserialise_Chain(t17 a1)
{
    ExState *r2 = a1.p1;
    Buffer *r3 = a1.p2;
    u32 r4 = a1.p3;
    t11 r5 = malloc_Chain(r2);
    ExState *r6 = r5.p1;
    t10 r7 = r5.p2;
    t29 r8;
    
    if (r7.tag == TAG_ENUM_Success) {
        t17 r9 = (t17) {.p1 = r6, .p2 = r3, .p3 = r4};
        t18 r10 = deserialise_U32(r9);
        ExState *r11 = r10.p1;
        u32 r12 = r10.p2;
        t16 r13;
        
        if (LETBANG_TRUE) {
            t13 r14 = (t13) {.p1 = r11, .p2 = r3, .p3 = r4, .p4 = r12};
            
            r13 = deserialise_CString(r14);
        } else
            ;
        
        ExState *r15 = r13.p1;
        t15 r16 = r13.p2;
        t29 r17;
        
        if (r16.tag == TAG_ENUM_Success) {
            WordArray_u8 *r18 = r16.Success.p1;
            u32 r19 = r16.Success.p2;
            t4 *r20 = r7.Success;
            
            (*r20).len = r12;
            
            t4 *r21 = r20;
            t4 *r22 = r21;
            
            (*r22).key = r18;
            
            t4 *r23 = r22;
            t27 r24 = (t27) {.p1 = r23, .p2 = r19};
            t30 r25 = (t30) {.tag = TAG_ENUM_Success, .Success = r24};
            t28 r26 = (t28) {.tag = r25.tag, .Success = r25.Success};
            
            r17 = (t29) {.p1 = r15, .p2 = r26};
        } else {
            t31 r27 = {.tag =r16.tag, .Error =r16.Error};
            u32 r28 = r27.Error;
            t9 r29 = (t9) {.p1 = r15, .p2 = r7.Success};
            ExState *r30 = free_Chain(r29);
            t31 r31 = (t31) {.tag = TAG_ENUM_Error, .Error = r28};
            t28 r32 = (t28) {.tag = r31.tag, .Error = r31.Error};
            
            r17 = (t29) {.p1 = r30, .p2 = r32};
        }
        r8 = r17;
    } else {
        t31 r33 = {.tag =r7.tag, .Error =r7.Error};
        u32 r34 = r33.Error;
        t31 r35 = (t31) {.tag = TAG_ENUM_Error, .Error = r34};
        t28 r36 = (t28) {.tag = r35.tag, .Error = r35.Error};
        
        r8 = (t29) {.p1 = r6, .p2 = r36};
    }
    
    t29 r37 = r8;
    
    return r37;
}
static inline t6 cmp_inc(t3 a1)
{
    ExState *r2 = a1.acc;
    t2 r3 = a1.obsv;
    Buffer *r4 = r3.p1;
    WordArray_u8 *r5 = r3.p2;
    u32 r6 = a1.idx;
    u8 r7 = 0U;
    u32 r8 = (u32) r7;
    t17 r9 = (t17) {.p1 = r2, .p2 = r4, .p3 = r8};
    t29 r10 = deserialise_Chain(r9);
    ExState *r11 = r10.p1;
    t28 r12 = r10.p2;
    t6 r13;
    
    if (r12.tag == TAG_ENUM_Success) {
        t4 *r14 = r12.Success.p1;
        u32 r15 = r12.Success.p2;
        bool_t r16;
        
        if (LETBANG_TRUE) {
            WordArray_u8 *r17 = (*r14).key;
            t1 r18 = (t1) {.p1 = r17, .p2 = r5};
            
            r16 = string_cmp(r18);
        } else
            ;
        
        t6 r19;
        
        if (r16.boolean) {
            t32 r20 = (t32) {.tag = TAG_ENUM_Break, .Break = r14};
            t5 r21 = (t5) {.tag = r20.tag, .Break = r20.Break};
            
            r19 = (t6) {.p1 = r11, .p2 = r21};
        } else {
            u32 r22 = (*r14).len;
            WordArray_u8 *r23 = (*r14).key;
            t12 r24 = (t12) {.p1 = r11, .p2 = r23};
            ExState *r25 = free_CString(r24);
            t9 r26 = (t9) {.p1 = r25, .p2 = r14};
            ExState *r27 = free_Chain(r26);
            unit_t r28 = (unit_t) {.dummy = 0};
            t33 r29 = (t33) {.tag = TAG_ENUM_Iterate, .Iterate = r28};
            t5 r30 = (t5) {.tag = r29.tag, .Iterate = r29.Iterate};
            
            r19 = (t6) {.p1 = r27, .p2 = r30};
        }
        r13 = r19;
    } else {
        t31 r31 = {.tag =r12.tag, .Error =r12.Error};
        u32 r32 = r31.Error;
        unit_t r33 = (unit_t) {.dummy = 0};
        t33 r34 = (t33) {.tag = TAG_ENUM_Iterate, .Iterate = r33};
        t5 r35 = (t5) {.tag = r34.tag, .Iterate = r34.Iterate};
        
        r13 = (t6) {.p1 = r11, .p2 = r35};
    }
    
    t6 r36 = r13;
    
    return r36;
}
static inline t36 find_str(t34 a1)
{
    ExState *r2 = a1.p1;
    Buffer *r3 = a1.p2;
    WordArray_u8 *r4 = a1.p3;
    u8 r5 = 0U;
    u32 r6 = u8_to_u32(r5);
    u8 r7 = 2U;
    u32 r8 = u8_to_u32(r7);
    u8 r9 = 1U;
    u32 r10 = u8_to_u32(r9);
    t7 r11 = FUN_ENUM_cmp_inc;
    t2 r12 = (t2) {.p1 = r3, .p2 = r4};
    t8 r13 = (t8) {.frm = r6, .to = r8, .step = r10, .f = r11, .acc = r2,
                   .obsv = r12};
    t6 r14 = seq32_0(r13);
    ExState *r15 = r14.p1;
    t5 r16 = r14.p2;
    t36 r17;
    
    if (r16.tag == TAG_ENUM_Iterate) {
        unit_t r18 = r16.Iterate;
        unit_t r19 = (unit_t) {.dummy = 0};
        t37 r20 = (t37) {.tag = TAG_ENUM_None, .None = r19};
        t37 r21 = (t37) {.tag = r20.tag, .None = r20.None};
        t35 r22 = (t35) {.tag = r21.tag, .None = r21.None};
        
        r17 = (t36) {.p1 = r15, .p2 = r22};
    } else {
        t32 r23 = {.tag =r16.tag, .Break =r16.Break};
        t4 *r24 = r23.Break;
        t38 r25 = (t38) {.tag = TAG_ENUM_Some, .Some = r24};
        t35 r26 = (t35) {.tag = r25.tag, .Some = r25.Some};
        
        r17 = (t36) {.p1 = r15, .p2 = r26};
    }
    
    t36 r27 = r17;
    
    return r27;
}



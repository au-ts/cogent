/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include "pass_prim-ops.h"

static inline u8 ops8(u8 a1)
{
    u8 r2 = a1;
    u8 r3 = 1U;
    u8 r4 = (u8) ((u32) r2 + (u32) r3);
    u8 r5 = (u8) ((u32) r4 * (u32) r2);
    u8 r6 = (u8) ((u32) r5 - (u32) r4);
    u8 r7 = (u8) ((u32) r6 | (u32) r5);
    u8 r8 = (u8) ((u32) r7 & (u32) r6);
    u8 r9 = (u8) ((u32) r7 ^ (u32) r6);
    u8 r10 = (u8) ~(u32) r9;
    u8 r11 = r10 >= 8U ? 0U : (u8) ((u32) r9 << (u32) r10);
    u8 r12 = r11 >= 8U ? 0U : (u8) ((u32) r10 >> (u32) r11);
    u8 r13 = r11 ? (u8) ((u32) r12 / (u32) r11) : 0U;
    u8 r14 = r13 ? (u8) ((u32) r12 % (u32) r13) : 0U;
    bool_t r15 = (bool_t) {.boolean = r12 < r13};
    bool_t r16 = (bool_t) {.boolean = r13 <= r14};
    bool_t r17 = (bool_t) {.boolean = r12 == r14};
    bool_t r18 = (bool_t) {.boolean = r16.boolean && r17.boolean};
    bool_t r19 = (bool_t) {.boolean = r15.boolean && r18.boolean};
    u8 r20;
    
    if (r19.boolean) {
        r20 = 0U;
    } else {
        r20 = 1U;
    }
    
    u8 r21 = r20;
    
    return r21;
}
static inline u64 ops64(u64 a1)
{
    u64 r2 = a1;
    u8 r3 = 1U;
    u64 r4 = (u64) r3;
    u64 r5 = r2 + r4;
    u64 r6 = r5 * r2;
    u64 r7 = r6 - r5;
    u64 r8 = r7 | r6;
    u64 r9 = r8 & r7;
    u64 r10 = r8 ^ r9;
    u64 r11 = ~r10;
    u64 r12 = r11 >= 64U ? 0U : r10 << r11;
    u64 r13 = r12 >= 64U ? 0U : r11 >> r12;
    u64 r14 = r12 ? r13 / r12 : 0U;
    u64 r15 = r14 ? r13 % r14 : 0U;
    bool_t r16 = (bool_t) {.boolean = r13 < r14};
    bool_t r17 = (bool_t) {.boolean = r14 <= r15};
    bool_t r18 = (bool_t) {.boolean = r13 == r15};
    bool_t r19 = (bool_t) {.boolean = r17.boolean && r18.boolean};
    bool_t r20 = (bool_t) {.boolean = r16.boolean && r19.boolean};
    u64 r21;
    
    if (r20.boolean) {
        u8 r22 = 0U;
        
        r21 = (u64) r22;
    } else {
        u8 r23 = 1U;
        
        r21 = (u64) r23;
    }
    
    u64 r24 = r21;
    
    return r24;
}
static inline u32 ops32(u32 a1)
{
    u32 r2 = a1;
    u8 r3 = 1U;
    u32 r4 = (u32) r3;
    u32 r5 = r2 + r4;
    u32 r6 = r5 * r2;
    u32 r7 = r6 - r5;
    u32 r8 = r7 | r6;
    u32 r9 = r8 & r7;
    u32 r10 = r8 ^ r7;
    u32 r11 = ~r10;
    u32 r12 = r11 >= 32U ? 0U : r10 << r11;
    u32 r13 = r12 >= 32U ? 0U : r11 >> r12;
    u32 r14 = r12 ? r13 / r12 : 0U;
    u32 r15 = r14 ? r13 % r14 : 0U;
    bool_t r16 = (bool_t) {.boolean = r13 < r14};
    bool_t r17 = (bool_t) {.boolean = r14 <= r15};
    bool_t r18 = (bool_t) {.boolean = r13 == r15};
    bool_t r19 = (bool_t) {.boolean = r17.boolean && r18.boolean};
    bool_t r20 = (bool_t) {.boolean = r16.boolean && r19.boolean};
    u32 r21;
    
    if (r20.boolean) {
        u8 r22 = 0U;
        
        r21 = (u32) r22;
    } else {
        u8 r23 = 1U;
        
        r21 = (u32) r23;
    }
    
    u32 r24 = r21;
    
    return r24;
}
static inline u16 ops16(u16 a1)
{
    u16 r2 = a1;
    u8 r3 = 1U;
    u16 r4 = (u16) r3;
    u16 r5 = (u16) ((u32) r2 + (u32) r4);
    u16 r6 = (u16) ((u32) r5 * (u32) r2);
    u16 r7 = (u16) ((u32) r6 - (u32) r5);
    u16 r8 = (u16) ((u32) r7 | (u32) r6);
    u16 r9 = (u16) ((u32) r8 & (u32) r7);
    u16 r10 = (u16) ((u32) r8 ^ (u32) r7);
    u16 r11 = (u16) ~(u32) r10;
    u16 r12 = r11 >= 16U ? 0U : (u16) ((u32) r10 << (u32) r11);
    u16 r13 = r12 >= 16U ? 0U : (u16) ((u32) r11 >> (u32) r12);
    u16 r14 = r12 ? (u16) ((u32) r13 / (u32) r12) : 0U;
    u16 r15 = r14 ? (u16) ((u32) r13 % (u32) r14) : 0U;
    bool_t r16 = (bool_t) {.boolean = r13 < r14};
    bool_t r17 = (bool_t) {.boolean = r14 <= r15};
    bool_t r18 = (bool_t) {.boolean = r13 == r15};
    bool_t r19 = (bool_t) {.boolean = r17.boolean && r18.boolean};
    bool_t r20 = (bool_t) {.boolean = r16.boolean && r19.boolean};
    u16 r21;
    
    if (r20.boolean) {
        u8 r22 = 0U;
        
        r21 = (u16) r22;
    } else {
        u8 r23 = 1U;
        
        r21 = (u16) r23;
    }
    
    u16 r24 = r21;
    
    return r24;
}
static inline bool_t bool_ops(u32 a1)
{
    u32 r2 = a1;
    u8 r3 = 1U;
    u32 r4 = (u32) r3;
    u32 r5 = r2 + r4;
    u32 r6 = r5 * r2;
    bool_t r7 = (bool_t) {.boolean = r2 < r5};
    bool_t r8 = (bool_t) {.boolean = r5 <= r6};
    bool_t r9 = (bool_t) {.boolean = r6 == r2};
    bool_t r10 = (bool_t) {.boolean = r8.boolean && r9.boolean};
    bool_t r11 = (bool_t) {.boolean = r10.boolean || r9.boolean};
    bool_t r12 = (bool_t) {.boolean = !r11.boolean};
    bool_t r13 = (bool_t) {.boolean = 1U};
    bool_t r14 = (bool_t) {.boolean = r12.boolean || r13.boolean};
    bool_t r15 = (bool_t) {.boolean = !r14.boolean};
    bool_t r16 = (bool_t) {.boolean = 0U};
    bool_t r17 = (bool_t) {.boolean = r15.boolean && r16.boolean};
    bool_t r18 = r17;
    
    return r18;
}



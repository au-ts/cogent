/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include "pass_middle-size-example.h"

static inline t4 foo(t3 a1)
{
    t2* r2 = a1.p1;
    bool_t r3 = a1.p2;
    bool_t r4 = (*r2).b;
    t4 r5;
    
    if (r3.boolean) {
        t2* r6 = r2;
        
        (*r6).b = r3;
        
        t2* r7 = r6;
        t1* r8 = (*r7).a;
        u32 r9 = (*r8).a2;
        u8 r10 = 0U;
        u32 r11 = (u32) r10;
        t1* r12 = r8;
        
        (*r12).a2 = r11;
        
        t1* r13 = r12;
        
        r5 = (t4) {.p1 = r7, .p2 = r13, .p3 = r4, .p4 = r9};
    } else {
        bool_t r14 = (bool_t) {.boolean = 1U};
        t2* r15 = r2;
        
        (*r15).b = r14;
        
        t2* r16 = r15;
        t1* r17 = (*r16).a;
        u8 r18 = 0U;
        u32 r19 = (u32) r18;
        t1* r20 = r17;
        
        (*r20).a1 = r19;
        
        t1* r21 = r20;
        t2* r22 = r16;
        
        (*r22).a = r21;
        
        t2* r23 = r22;
        t1* r24 = (*r23).a;
        u32 r25 = (*r24).a2;
        u8 r26 = 0U;
        u32 r27 = (u32) r26;
        t1* r28 = r24;
        
        (*r28).a2 = r27;
        
        t1* r29 = r28;
        
        r5 = (t4) {.p1 = r23, .p2 = r29, .p3 = r4, .p4 = r25};
    }
    
    t4 r30 = r5;
    
    return r30;
}



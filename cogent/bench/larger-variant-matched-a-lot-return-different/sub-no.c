// This build info header is now disabled by --fno-gen-header.
// --------------------------------------------------------------------------------
// We strongly discourage users from generating individual files for Isabelle
// proofs, as it will end up with an inconsistent collection of output files (i.e.
// Isabelle input files).

#include "sub-no.h"

extern t1 foo(t2 a1)
{
    t1 r2;
    
    if (a1.tag == TAG_ENUM_A) {
        bool_t r3 = (bool_t) {.boolean = 1U};
        
        r2 = (t1) {.p1 = r3, .p2 = a1.A};
    } else {
        t3 r4 = {.tag =a1.tag, .B =a1.B, .C =a1.C, .D =a1.D, .E =a1.E, .F =
                 a1.F};
        t1 r5;
        
        if (r4.tag == TAG_ENUM_B) {
            u8 r6 = 127U;
            u32 r7 = (u32) r6;
            
            r5 = (t1) {.p1 = r4.B, .p2 = r7};
        } else {
            t4 r8 = {.tag =r4.tag, .C =r4.C, .D =r4.D, .E =r4.E, .F =r4.F};
            t1 r9;
            
            if (r8.tag == TAG_ENUM_C) {
                unit_t r10 = r8.C;
                bool_t r11 = (bool_t) {.boolean = 1U};
                u8 r12 = 127U;
                u32 r13 = (u32) r12;
                
                r9 = (t1) {.p1 = r11, .p2 = r13};
            } else {
                t5 r14 = {.tag =r8.tag, .D =r8.D, .E =r8.E, .F =r8.F};
                t1 r15;
                
                if (r14.tag == TAG_ENUM_D) {
                    bool_t r16 = (bool_t) {.boolean = 0U};
                    
                    r15 = (t1) {.p1 = r16, .p2 = r14.D};
                } else {
                    t6 r17 = {.tag =r14.tag, .E =r14.E, .F =r14.F};
                    t1 r18;
                    
                    if (r17.tag == TAG_ENUM_E) {
                        u8 r19 = 42U;
                        u64 r20 = (u64) r19;
                        bool_t r21 = (bool_t) {.boolean = r17.E != r20};
                        u8 r22 = 0U;
                        u32 r23 = (u32) r22;
                        
                        r18 = (t1) {.p1 = r21, .p2 = r23};
                    } else {
                        t7 r24 = {.tag =r17.tag, .F =r17.F};
                        t7 r25 = r24;
                        bool_t r26 = (bool_t) {.boolean = 0U};
                        u8 r27 = 1U;
                        u32 r28 = (u32) r27;
                        
                        r18 = (t1) {.p1 = r26, .p2 = r28};
                    }
                    r15 = r18;
                }
                r9 = r15;
            }
            r5 = r9;
        }
        r2 = r5;
    }
    
    t1 r29 = r2;
    
    return r29;
}



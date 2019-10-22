// This build info header is now disabled by --fno-gen-header.
// --------------------------------------------------------------------------------
// We strongly discourage users from generating individual files for Isabelle
// proofs, as it will end up with an inconsistent collection of output files (i.e.
// Isabelle input files).

#include "sub-no.h"

extern t3 foo(t2 a1)
{
    t3 r2;
    
    if (a1.tag == TAG_ENUM_A) {
        bool_t r3 = (bool_t) {.boolean = 1U};
        t1 r4 = (t1) {.p1 = r3, .p2 = a1.A};
        
        r2 = (t3) {.tag = TAG_ENUM_F, .F = r4};
    } else {
        t4 r5 = {.tag =a1.tag, .B =a1.B, .C =a1.C, .D =a1.D, .E =a1.E, .F =
                 a1.F};
        t3 r6;
        
        if (r5.tag == TAG_ENUM_B) {
            u8 r7 = 127U;
            u32 r8 = (u32) r7;
            t1 r9 = (t1) {.p1 = r5.B, .p2 = r8};
            
            r6 = (t3) {.tag = TAG_ENUM_F, .F = r9};
        } else {
            t5 r10 = {.tag =r5.tag, .C =r5.C, .D =r5.D, .E =r5.E, .F =r5.F};
            t3 r11;
            
            if (r10.tag == TAG_ENUM_C) {
                unit_t r12 = r10.C;
                bool_t r13 = (bool_t) {.boolean = 1U};
                u8 r14 = 127U;
                u32 r15 = (u32) r14;
                t1 r16 = (t1) {.p1 = r13, .p2 = r15};
                
                r11 = (t3) {.tag = TAG_ENUM_F, .F = r16};
            } else {
                t6 r17 = {.tag =r10.tag, .D =r10.D, .E =r10.E, .F =r10.F};
                t3 r18;
                
                if (r17.tag == TAG_ENUM_D) {
                    bool_t r19 = (bool_t) {.boolean = 0U};
                    t1 r20 = (t1) {.p1 = r19, .p2 = r17.D};
                    
                    r18 = (t3) {.tag = TAG_ENUM_F, .F = r20};
                } else {
                    t7 r21 = {.tag =r17.tag, .E =r17.E, .F =r17.F};
                    t3 r22;
                    
                    if (r21.tag == TAG_ENUM_E) {
                        u8 r23 = 42U;
                        u64 r24 = (u64) r23;
                        bool_t r25 = (bool_t) {.boolean = r21.E != r24};
                        u8 r26 = 0U;
                        u32 r27 = (u32) r26;
                        t1 r28 = (t1) {.p1 = r25, .p2 = r27};
                        
                        r22 = (t3) {.tag = TAG_ENUM_F, .F = r28};
                    } else {
                        t3 r29 = {.tag =r21.tag, .F =r21.F};
                        t3 r30 = r29;
                        
                        r22 = r30;
                    }
                    r18 = r22;
                }
                r11 = r18;
            }
            r6 = r11;
        }
        r2 = r6;
    }
    
    t3 r31 = r2;
    
    return r31;
}



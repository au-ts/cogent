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
        u8 r3 = 42U;
        u32 r4 = (u32) r3;
        bool_t r5 = (bool_t) {.boolean = a1.A != r4};
        t4 r6 = (t4) {.tag = TAG_ENUM_B, .B = r5};
        
        r2 = (t3) {.tag = r6.tag, .B = r6.B};
    } else {
        t3 r7 = {.tag =a1.tag, .B =a1.B, .C =a1.C, .D =a1.D, .E =a1.E, .F =
                 a1.F};
        t3 r8 = r7;
        
        r2 = r8;
    }
    
    t3 r9 = r2;
    
    return r9;
}



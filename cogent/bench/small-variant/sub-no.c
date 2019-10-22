// This build info header is now disabled by --fno-gen-header.
// --------------------------------------------------------------------------------
// We strongly discourage users from generating individual files for Isabelle
// proofs, as it will end up with an inconsistent collection of output files (i.e.
// Isabelle input files).

#include "sub-no.h"

extern t2 foo(t1 a1)
{
    t2 r2;
    
    if (a1.tag == TAG_ENUM_A) {
        u8 r3 = 42U;
        u32 r4 = (u32) r3;
        bool_t r5 = (bool_t) {.boolean = a1.A != r4};
        t3 r6 = (t3) {.tag = TAG_ENUM_B, .B = r5};
        
        r2 = (t2) {.tag = r6.tag, .B = r6.B};
    } else {
        t2 r7 = {.tag =a1.tag, .B =a1.B, .C =a1.C};
        t2 r8 = r7;
        
        r2 = r8;
    }
    
    t2 r9 = r2;
    
    return r9;
}



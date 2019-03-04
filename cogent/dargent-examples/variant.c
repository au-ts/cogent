// This build info header is now disabled by --fno-gen-header.
// --------------------------------------------------------------------------------
// We strongly discourage users from generating individual files for Isabelle
// proofs, as it will end up with an inconsistent collection of output files (i.e.
// Isabelle input files).

#include "variant.h"

static inline unsigned int d4_get_f1_part0(t1 b)
{
    return (*b).data[0U] >> 0U & 4294967295U;
}
static inline u32 d3_get_f1(t1 b)
{
    return (u32) d4_get_f1_part0(b) << 0U;
}
static inline unsigned int d6_get_f2_part0(t1 b)
{
    return (*b).data[1U] >> 0U & 4294967295U;
}
static inline unsigned int d7_get_f2_part1(t1 b)
{
    return (*b).data[2U] >> 0U & 4294967295U;
}
static inline u64 d5_get_f2(t1 b)
{
    return (u64) d6_get_f2_part0(b) << 0U | (u64) d7_get_f2_part1(b) << 32U;
}
static inline u64 foo(t2 a1)
{
    u64 r2;
    
    if (a1.tag == TAG_ENUM_A) {
        r2 = (u64) a1.A;
    } else {
        t1 r3 = a1.B;
        u32 r4 = d3_get_f1(r3);
        u64 r5 = (u64) r4;
        u64 r6 = d5_get_f2(r3);
        
        r2 = r5 + r6;
    }
    
    u64 r7 = r2;
    
    return r7;
}



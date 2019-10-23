// This build info header is now disabled by --fno-gen-header.
// --------------------------------------------------------------------------------
// We strongly discourage users from generating individual files for Isabelle
// proofs, as it will end up with an inconsistent collection of output files (i.e.
// Isabelle input files).

#include "variant_0.h"

static inline unsigned int d5_get_a_tag_part0(t1 b)
{
    return (*b).data[0U] >> 0U & 4294967295U;
}
static inline unsigned int d4_get_a_tag(t1 b)
{
    return (unsigned int) d5_get_a_tag_part0(b) << 0U;
}
static inline unsigned int d7_get_a_A_part0(t1 b)
{
    return (*b).data[1U] >> 0U & 255U;
}
static inline u8 d6_get_a_A(t1 b)
{
    return (u8) d7_get_a_A_part0(b) << 0U;
}
static inline t2 d3_get_a(t1 b)
{
    return (t2) {.tag = TAG_ENUM_A, .A = d6_get_a_A(b)};
}
static inline unsigned int d11_get_b_tag_part0(t1 b)
{
    return (*b).data[2U] >> 0U & 4294967295U;
}
static inline unsigned int d10_get_b_tag(t1 b)
{
    return (unsigned int) d11_get_b_tag_part0(b) << 0U;
}
static inline unsigned int d13_get_b_A_part0(t1 b)
{
    return (*b).data[3U] >> 0U & 255U;
}
static inline u8 d12_get_b_A(t1 b)
{
    return (u8) d13_get_b_A_part0(b) << 0U;
}
static inline unsigned int d15_get_b_B_part0(t1 b)
{
    return (*b).data[4U] >> 0U & 65535U;
}
static inline u16 d14_get_b_B(t1 b)
{
    return (u16) d15_get_b_B_part0(b) << 0U;
}
static inline unsigned int d17_get_b_C_part0(t1 b)
{
    return (*b).data[5U] >> 0U & 4294967295U;
}
static inline u32 d16_get_b_C(t1 b)
{
    return (u32) d17_get_b_C_part0(b) << 0U;
}
static inline unsigned int d19_get_b_D_part0(t1 b)
{
    return (*b).data[6U] >> 0U & 4294967295U;
}
static inline unsigned int d20_get_b_D_part1(t1 b)
{
    return (*b).data[7U] >> 0U & 4294967295U;
}
static inline u64 d18_get_b_D(t1 b)
{
    return (u64) d19_get_b_D_part0(b) << 0U | (u64) d20_get_b_D_part1(b) << 32U;
}
static inline unsigned int d22_get_b_E_part0(t1 b)
{
    return (*b).data[8U] >> 0U & 255U;
}
static inline bool_t d21_get_b_E(t1 b)
{
    return (bool_t) {.boolean = (unsigned char) d22_get_b_E_part0(b) << 0U};
}
static inline t8 d9_get_b(t1 b)
{
    return d10_get_b_tag(b) == 4U ? (t8) {.tag = TAG_ENUM_E, .E =
                                          d21_get_b_E(b)} : d10_get_b_tag(b) ==
        3U ? (t8) {.tag = TAG_ENUM_D, .D = d18_get_b_D(b)} : d10_get_b_tag(b) ==
        2U ? (t8) {.tag = TAG_ENUM_C, .C = d16_get_b_C(b)} : d10_get_b_tag(b) ==
        1U ? (t8) {.tag = TAG_ENUM_B, .B = d14_get_b_B(b)} : (t8) {.tag =
                                                                   TAG_ENUM_A,
                                                                   .A =
                                                                   d12_get_b_A(b)};
}
static inline void d27_set_a_tag_part0(t1 b, unsigned int v)
{
    (*b).data[0U] = ((*b).data[0U] & ~(4294967295U << 0U)) | (4294967295U &
                                                              v) << 0U;
}
static inline void d26_set_a_tag(t1 b, unsigned int v)
{
    d27_set_a_tag_part0(b, (unsigned int) (v >> 0U & 4294967295U));
}
static inline void d29_set_a_A_part0(t1 b, unsigned int v)
{
    (*b).data[1U] = ((*b).data[1U] & ~(255U << 0U)) | (255U & v) << 0U;
}
static inline void d28_set_a_A(t1 b, u8 v)
{
    d29_set_a_A_part0(b, (unsigned int) (v >> 0U & 255U));
}
static inline void d25_set_a(t1 b, t2 v)
{
    d26_set_a_tag(b, 0U);
    d28_set_a_A(b, v.A);
}
static inline void d32_set_b_tag_part0(t1 b, unsigned int v)
{
    (*b).data[2U] = ((*b).data[2U] & ~(4294967295U << 0U)) | (4294967295U &
                                                              v) << 0U;
}
static inline void d31_set_b_tag(t1 b, unsigned int v)
{
    d32_set_b_tag_part0(b, (unsigned int) (v >> 0U & 4294967295U));
}
static inline void d34_set_b_A_part0(t1 b, unsigned int v)
{
    (*b).data[3U] = ((*b).data[3U] & ~(255U << 0U)) | (255U & v) << 0U;
}
static inline void d33_set_b_A(t1 b, u8 v)
{
    d34_set_b_A_part0(b, (unsigned int) (v >> 0U & 255U));
}
static inline void d36_set_b_B_part0(t1 b, unsigned int v)
{
    (*b).data[4U] = ((*b).data[4U] & ~(65535U << 0U)) | (65535U & v) << 0U;
}
static inline void d35_set_b_B(t1 b, u16 v)
{
    d36_set_b_B_part0(b, (unsigned int) (v >> 0U & 65535U));
}
static inline void d38_set_b_C_part0(t1 b, unsigned int v)
{
    (*b).data[5U] = ((*b).data[5U] & ~(4294967295U << 0U)) | (4294967295U &
                                                              v) << 0U;
}
static inline void d37_set_b_C(t1 b, u32 v)
{
    d38_set_b_C_part0(b, (unsigned int) (v >> 0U & 4294967295U));
}
static inline void d40_set_b_D_part0(t1 b, unsigned int v)
{
    (*b).data[6U] = ((*b).data[6U] & ~(4294967295U << 0U)) | (4294967295U &
                                                              v) << 0U;
}
static inline void d41_set_b_D_part1(t1 b, unsigned int v)
{
    (*b).data[7U] = ((*b).data[7U] & ~(4294967295U << 0U)) | (4294967295U &
                                                              v) << 0U;
}
static inline void d39_set_b_D(t1 b, u64 v)
{
    d40_set_b_D_part0(b, (unsigned int) (v >> 0U & 4294967295U));
    d41_set_b_D_part1(b, (unsigned int) (v >> 32U & 4294967295U));
}
static inline void d43_set_b_E_part0(t1 b, unsigned int v)
{
    (*b).data[8U] = ((*b).data[8U] & ~(255U << 0U)) | (255U & v) << 0U;
}
static inline void d42_set_b_E(t1 b, bool_t v)
{
    d43_set_b_E_part0(b, (unsigned int) (v.boolean >> 0U & 255U));
}
static inline void d30_set_b(t1 b, t8 v)
{
    if (v.tag == TAG_ENUM_E) {
        d31_set_b_tag(b, 4U);
        d42_set_b_E(b, v.E);
    } else if (v.tag == TAG_ENUM_D) {
        d31_set_b_tag(b, 3U);
        d39_set_b_D(b, v.D);
    } else if (v.tag == TAG_ENUM_C) {
        d31_set_b_tag(b, 2U);
        d37_set_b_C(b, v.C);
    } else if (v.tag == TAG_ENUM_B) {
        d31_set_b_tag(b, 1U);
        d35_set_b_B(b, v.B);
    } else {
        d31_set_b_tag(b, 0U);
        d33_set_b_A(b, v.A);
    }
}
static inline t24 getVals(t1 a1)
{
    t2 r2 = d3_get_a(a1);
    t8 r3 = d9_get_b(a1);
    t23 r4;
    
    if (LETBANG_TRUE) {
        t23 r5;
        
        r5.a = r2;
        r5.b = r3;
        r4 = r5;
    } else
        ;
    
    t24 r6;
    
    r6.p1 = a1;
    r6.p2 = r4;
    
    t24 r7 = r6;
    
    return r7;
}
static inline t1 putVals(t1 a1)
{
    t1 r2 = a1;
    u8 r3 = 18U;
    t2 r4;
    
    r4.tag = TAG_ENUM_A;
    r4.A = r3;
    
    t2 r5 = r4;
    t1 r6 = r2;
    
    d25_set_a(r6, r5);
    
    t1 r7 = r6;
    u32 r8 = 2022747085U;
    t8 r9;
    
    r9.tag = TAG_ENUM_C;
    r9.C = r8;
    
    t8 r10 = r9;
    t8 r11 = r10;
    t1 r12 = r7;
    
    d30_set_b(r12, r11);
    
    t1 r13 = r12;
    
    return r13;
}



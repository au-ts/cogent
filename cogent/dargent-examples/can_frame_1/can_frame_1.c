#include "can_frame_1.h"

static inline unsigned int d4_get_ident_part0(t1 b)
{
    return (*b).data[0U] >> 0U & 4294967295U;
}
static inline unsigned int d5_get_ident_part1(t1 b)
{
    return (*b).data[1U] >> 0U & 4294967295U;
}
static inline t2 d3_get_ident(t1 b)
{
    return (t2) ((unsigned long) d4_get_ident_part0(b) << 0U |
                 (unsigned long) d5_get_ident_part1(b) << 32U);
}
static inline unsigned int d7_get_eff_part0(t2 b)
{
    return (*b).data[0U] >> 30U & 1U;
}
static inline u32 d6_get_eff(t2 b)
{
    return (u32) d7_get_eff_part0(b) << 0U;
}
static inline unsigned int d9_get_id_part0(t2 b)
{
    return (*b).data[0U] >> 0U & 536870911U;
}
static inline u32 d8_get_id(t2 b)
{
    return (u32) d9_get_id_part0(b) << 0U;
}
static inline t10 get_sid_eid(t1 a1)
{
    t1 r2 = a1;
    t2 r3 = d3_get_ident(r2);
    u32 r4 = d6_get_eff(r3);
    t2 r5 = d3_get_ident(r2);
    u32 r6 = d8_get_id(r5);
    u32 r7 = 0U;
    bool_t r8 = (bool_t) {.boolean = r4 != r7};
    t10 r9;
    
    if (r8.boolean) {
        u32 r10 = 18U;
        u32 r11 = r10 >= 32U ? 0U : r6 >> r10;
        u32 r12 = 262143U;
        u32 r13 = r6 & r12;
        t10 r14;
        
        r14.p1 = r11;
        r14.p2 = r13;
        r9 = r14;
    } else {
        u32 r15 = 0U;
        t10 r16;
        
        r16.p1 = r6;
        r16.p2 = r15;
        r9 = r16;
    }
    
    t10 r17 = r9;
    
    return r17;
}

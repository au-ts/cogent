/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include "fun2.h"

static inline t1 foo(u16 a1)
{
    u16 r2 = a1;
    u32 r3 = (u32) r2;
    u32 r4 = (u32) r2;
    t1 r5 = (t1) {.p1 = r3, .p2 = r4};
    
    return r5;
}
static inline unit_t bar(unit_t a1)
{
    unit_t r2 = a1;
    u8 r3 = 32U;
    u16 r4 = (u16) r3;
    t1 r5 = foo(r4);
    u32 r6 = r5.p1;
    u32 r7 = r5.p2;
    unit_t r8 = (unit_t) {.dummy = 0};
    
    return r8;
}



/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include "loopmain.h"

static inline u32 id_loopbody(t1 a1)
{
    u32 r2 = a1.acc;
    u32 r3 = a1.idx;
    u8 r4 = 1U;
    u32 r5 = (u32) r4;
    u32 r6 = r2 + r5;
    
    return r6;
}
static inline u32 id_f(u32 a1)
{
    u32 r2 = a1;
    u8 r3 = 0U;
    u32 r4 = (u32) r3;
    t2 r5 = FUN_ENUM_id_loopbody;
    u8 r6 = 0U;
    u32 r7 = (u32) r6;
    t3 r8 = (t3) {.frm = r4, .to = r2, .f = r5, .acc = r7};
    u32 r9 = seq32_0(r8);
    
    return r9;
}
static inline u32 triangular_loopbody(t1 a1)
{
    u32 r2 = a1.acc;
    u32 r3 = a1.idx;
    u32 r4 = id_f(r3);
    u32 r5 = r2 + r4;
    
    return r5;
}
static inline u32 triangular(u32 a1)
{
    u32 r2 = a1;
    u8 r3 = 0U;
    u32 r4 = (u32) r3;
    t2 r5 = FUN_ENUM_triangular_loopbody;
    u8 r6 = 0U;
    u32 r7 = (u32) r6;
    t3 r8 = (t3) {.frm = r4, .to = r2, .f = r5, .acc = r7};
    u32 r9 = seq32_0(r8);
    
    return r9;
}


#include "../../cogent/lib/cogent.h"
#include <stdio.h>
static inline u32 seq32_0(t3 args)
{
    unsigned int i;
    t1 fargs;
    
    fargs.acc = args.acc;
    for (i = args.frm; i < args.to; i++) {
        fargs.idx = i;
        fargs.acc = dispatch_t2(args.f, fargs);
    }
    return fargs.acc;
}
int main(void)
{
    unsigned int i;
    
    for (i = 0; i < 10; i++) {
        printf("triangular(%u) = %u\n", i, triangular(i));
    }
    return 0;
}



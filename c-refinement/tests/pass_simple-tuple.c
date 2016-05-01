/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include "pass_simple-tuple.h"

t3 dispatch_t6(t6 a7, u32 a8)
{
    return foo(a8);
}
t3 foo(u32 a1)
{
    u32 r2 = a1;
    t3 r4 = {.p1 =r2, .p2 =r2};
    t3 r5 = r4;
    
    return r5;
}



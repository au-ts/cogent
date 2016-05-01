/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include "pass_very-simple-split.h"

static inline u32 foo(t1 a1)
{
    u32 r2 = a1.p1;
    u16 r3 = a1.p2;
    u32 r4 = r2;
    
    return r4;
}



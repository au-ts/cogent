/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include "fun_dsl.h"

static inline unit_t i(unit_t a1)
{
    unit_t r2 = a1;
    unit_t r3 = r2;
    
    return r3;
}
static inline unit_t i2(unit_t a1)
{
    unit_t r2 = a1;
    unit_t r3 = i(r2);
    
    return r3;
}
static inline unit_t f(unit_t a1)
{
    unit_t r2 = a1;
    t1 r3 = abs(r2);
    unit_t r4 = dispatch_t1(r3, r2);
    
    return r4;
}


t1 abs(unit_t arg)
{
    return FUN_ENUM_f;
}



/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include "pass_simple-case3.h"

static inline u8 foo(t1 a1)
{
    u8 r2;
    
    if (a1.tag == TAG_ENUM_Atag) {
        r2 = a1.Atag;
    } else {
        t2 r3 = {.tag =a1.tag, .Btag =a1.Btag, .Ctag =a1.Ctag};
        u8 r4;
        
        if (r3.tag == TAG_ENUM_Btag) {
            r4 = r3.Btag;
        } else {
            t3 r5 = {.tag =r3.tag, .Ctag =r3.Ctag};
            u8 r6 = r5.Ctag;
            
            r4 = r6;
        }
        r2 = r4;
    }
    
    u8 r7 = r2;
    
    return r7;
}



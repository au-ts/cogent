#include "abstract.h"
#include "kitchen_sink.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

u8 abst(u8 x)
{
    return x * 2;
}

Poly_bool_t *imp(Poly_unit_t *x)
{
    Poly_bool_t *p = malloc(sizeof(*p));
    p->a = true;
    p->b = false;
    return p;
}

Poly_unit_t *mkPoly(unit_t x)
{
    return malloc(sizeof(Poly_unit_t));
}

int main(void)
{
    prim_ret r1 = prim(unit);
    assert(r1.p1 == true);
    assert(r1.p2 == 92);
    assert(r1.p3 == 42652);
    assert(r1.p4 == 363415312);
    assert(r1.p5 == 9573591166087831551llu);

    units_ret r2 = units(unit);
    assert(r2 == unit);

    arith_ret r3 = arith((arith_arg){138, 91});
    assert(r3.p1 == 138 + 91);
    assert(r3.p2 == 138 - 91);
    assert(r3.p3 == 138 * 91);
    assert(r3.p4 == 138 / 91);
    assert(r3.p5 == 138 % 91);

    logic_ret r4 = logic((logic_arg){true, false});
    assert(r4.p1 == false);
    assert(r4.p2 == true);

    compare_ret r5 = compare((compare_arg){4, 5});
    assert(r5.p1 == false);
    assert(r5.p2 == true);
    assert(r5.p3 == true);
    assert(r5.p4 == false);
    assert(r5.p5 == false);
    assert(r5.p6 == true);

    bitwise_ret r6 = bitwise((bitwise_arg){21132, 11});
    assert(r6.p1 == (21132 & 11));
    assert(r6.p2 == (21132 | 11));
    assert(r6.p3 == (21132 ^ 11));
    assert(r6.p4 == 24576);
    assert(r6.p5 == (21132 >> 11));

    unary_ret r7 = unary((unary_arg){6653173486142213361ull, false});
    assert(r7.p1 == 11793570587567338254ull);
    assert(r7.p2 == true);

    bind_ret r8 = bind(235789);
    assert(r8 == 943160);

    cast_ret r9 = cast(200);
    assert(r9.p1 == 200);
    assert(r9.p2 == 200);
    assert(r9.p3 == 200);

    branch_ret r10 = branch((branch_arg){true, true, 2357, 890});
    assert(r10 == 2357 + 890);
    r10 = branch((branch_arg){false, true, 2357, 890});
    assert(r10 == 2097730);
    r10 = branch((branch_arg){false, false, 2357, 890});
    assert(r10 == 2);
    r10 = branch((branch_arg){true, false, 2357, 890});
    assert(r10 == 1467);

    member_ret r11 = member((member_arg){.a = 67});
    assert(r11 == 67);

    B r12 = takeput((B){.a = 155890});
    assert(r12.a == 155891);

    B a13 = {.a = 155890};
    B *r13 = takeput_prime(&a13);
    assert(r13 == &a13);
    assert(r13->a == 155891);

    reclit_ret r14 = reclit(unit);
    assert(r14.a == 283397);
    assert(r14.b == 760882904);

    con_ret r15 = con(400);
    assert(r15.p1.tag == Z);
    assert(r15.p2.tag == O);
    assert(r15.p2.val.O == 400);
    assert(r15.p3.tag == T);
    assert(r15.p3.val.T.p1 == 400);
    assert(r15.p3.val.T.p2 == 400);

    both_ret r16 = both((both_arg){{No}, {No}});
    assert(r16.tag == No);
    r16 = both((both_arg){{No}, {Yes}});
    assert(r16.tag == No);
    r16 = both((both_arg){{Yes}, {No}});
    assert(r16.tag == No);
    r16 = both((both_arg){{Yes}, {Yes}});
    assert(r16.tag == Yes);

    inc_ret r17 = inc(2);
    assert(r17 == 3);

    call_ret r18 = call((call_arg){inc, 2});
    assert(r18 == 3);

    run_ret r19 = run(2);
    assert(r19 == 3);

    call_ret r20 = call((call_arg){abst, 2});
    assert(r20 == 4);

    Abs a21 = {.val = 20};
    Abs *r21 = id(&a21);
    assert(r21 == &a21);
    assert(r21->val == 20);

    Poly_u32 a22 = {.a = 23, .b = 12};
    Poly_u32 *r22 = id_prime_prime(&a22);
    assert(r22 == &a22);
    assert(r22->a == 23);
    assert(r22->b == 12);

    Poly_bool_t *r23 = useImp(unit);
    assert(r23->a == true);
    assert(r23->b == false);

    printf("All tests passed\n");

    return 0;
}
